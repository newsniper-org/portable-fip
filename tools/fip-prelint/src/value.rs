// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Value analysis of one MIR body, used to drop `Assert` terminators that cannot
//! fire (bounds, overflow, division and negation checks behind guards) and every
//! site in a block that no feasible path reaches. Calls are related to their
//! callees through return summaries computed by the same analysis.
//!
//! **Domain.** Difference bounds (`x - y ≤ c`, a zone) over mathematical integers
//! between tracked values: integer locals, the length `len(p)` of the slice behind a
//! slice pointer local `p` (its metadata), the result `t.0` of a checked operation
//! `t = AddWithOverflow(a, b)`, `start`/`end` of a `Range<integer>` local, the
//! payload of an `Option<integer>` local, the metadata of the slice pointer fields of
//! a tuple local, access paths `(*p).f1.f2…` (an integer, or a slice pointer's
//! metadata) through a local `p: &T` with `T: Freeze`, and the constant 0. Only
//! locals connected to some `Assert` condition, to the discriminant of a `SwitchInt`
//! on a comparison, or (for a summary) to the return place, through assignments and
//! summarised calls are tracked. Every tracked value carries the bounds of its type
//! (`len(p)` lies in `0..=usize::MAX`). Besides the matrix, the state records which
//! boolean locals hold which comparison (`c = Lt(a, b)`), which tuple locals hold
//! which checked operation together with the verdict "cannot overflow" computed when
//! the operation ran, which pointer locals share the metadata of which slice local
//! (`q = &(*p)`), and which shared reference locals point to which access path
//! (`q = &(*p).f`, `q = copy p`).
//!
//! **Transfer.** Copies and casts that preserve the value are equalities; constants
//! fix a value; `PtrMetadata` of a slice pointer is its `len`; a raw slice pointer
//! built from `(data, meta)` has length `meta`; a pointer cast between slice
//! pointers keeps the length, an unsizing coercion of `&[T; N]` has length `N`; an
//! unchecked addition or subtraction (overflow is undefined behaviour) is the
//! mathematical result; a `SwitchInt` on a recorded comparison adds the comparison
//! (or its negation) on each edge, and an infeasible edge is dropped; the success
//! edge of an `Assert` adds the checked condition (and, for a checked operation,
//! `t.0 = a op b`). A `for` loop over `a..b` is modelled from the contract of
//! `Range<integer>`: `into_iter` is the identity, `next(&mut r)` returns
//! `Some(r.start)` and increments `start` if `start < end`, else `None`, and never
//! changes `end`. A call whose callee has a return summary gets the summary's facts
//! over its argument values; any other call's destination, any other assignment,
//! `StorageLive`/`StorageDead` and partial writes forget the local (a comparison
//! that mentions a forgotten value is rewritten through a value equal to it, if
//! any). Writes through pointers cannot change a tracked local: locals whose address
//! is taken (`&mut x`, `&raw x`, also of a field; `&x` too unless the place has no
//! interior mutability, since writing through a shared reference to such a place is
//! undefined behaviour) are never tracked, except a `Range` whose only borrows are
//! passed directly to `next`. Slice lengths never change while the pointer local is
//! unchanged, nor does an access path while its reference local is unchanged (the
//! pointee is `Freeze` and shared). Cleanup (unwind) edges are not followed. Joins
//! take the weaker bound; at loop heads, after two visits, bounds that grew are
//! dropped (widening), so the fixpoint terminates.
//!
//! **Return summaries** ([`Summaries`]). For a callee with MIR in `core`/`alloc`/
//! `std` or an analysed crate (not a source, whose body is out of scope), whose
//! result is an integer, a `bool`, a slice pointer or a tuple with slice pointer
//! fields: the same analysis of its body, tracking the return place, joined over the
//! reachable `return`s and projected onto the result (its value, its metadata, the
//! metadata of its tuple fields, or the comparison a `bool` holds) and the
//! parameters the body never changes (their values, slice metadata and access
//! paths). No reachable `return` means the call does not return. Intrinsics (no MIR)
//! use the audited table `fip_lint_rules::mir::INTRINSIC_RESULT_BOUNDS`. Recursion
//! and nesting deeper than [`MAX_SUMMARY_DEPTH`] give no summary.
//!
//! **Use.** An `Assert` whose condition is decided equal to `expected` in the state
//! reaching it, or whose block no feasible path reaches, cannot fire. A block that no
//! feasible path reaches (no feasible edge into it, or its statements contradict the
//! state) is dead: its terminator never runs, so its call, drop, panic or allocation
//! is not counted. Anything not modelled keeps the assert and the block: unknown
//! rvalues, calls without a summary, signed division overflow
//! (`BitAnd` of two comparisons), 128-bit arithmetic, bodies with more than
//! [`MAX_VARS`] tracked values or [`MAX_CELLS`] matrix entries, coroutines; inline
//! assembly resets the state.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    self, BasicBlock, BinOp, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind, UnOp,
};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{self, EarlyBinder, Instance, InstanceKind, Ty, TyCtxt, TypingEnv};

use crate::analysis::{Crates, is_std_crate};

/// "No bound". Far above every bound of a 64-bit type, far below `i128::MAX`, so
/// sums of a few bounds cannot overflow.
const INF: i128 = 1 << 100;
/// Bodies with more tracked values are not analysed (all their asserts stay).
pub const MAX_VARS: usize = 128;
/// Nor are bodies whose per-block matrices would exceed this many entries
/// (blocks × values²; 16 bytes each).
const MAX_CELLS: usize = 1 << 22;

fn add(a: i128, b: i128) -> i128 {
    if a >= INF || b >= INF {
        INF
    } else {
        (a + b).max(-INF)
    }
}

/// Up to [`MAX_PATH`] field indices: the fields of an access path `(*p).f1.f2…`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Fields {
    n: u8,
    f: [u32; MAX_PATH],
}

/// Longest access path tracked (fields after the dereference).
const MAX_PATH: usize = 4;

impl Fields {
    const EMPTY: Fields = Fields {
        n: 0,
        f: [0; MAX_PATH],
    };
    fn new(fs: &[u32]) -> Option<Fields> {
        if fs.len() > MAX_PATH {
            return None;
        }
        let mut f = [0; MAX_PATH];
        f[..fs.len()].copy_from_slice(fs);
        Some(Fields {
            n: u8::try_from(fs.len()).ok()?,
            f,
        })
    }
    fn as_slice(&self) -> &[u32] {
        &self.f[..usize::from(self.n)]
    }
    fn concat(&self, o: &Fields) -> Option<Fields> {
        let mut v = self.as_slice().to_vec();
        v.extend_from_slice(o.as_slice());
        Fields::new(&v)
    }
}

/// A tracked value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Var {
    Local(Local),
    /// Metadata (length) of the slice behind a slice pointer local.
    Len(Local),
    /// Field 0 (the result) of a checked operation's tuple local.
    Field0(Local),
    /// `start` and `end` of a `Range<integer>` local.
    RangeStart(Local),
    RangeEnd(Local),
    /// `(o as Some).0` of an `Option<integer>` local.
    SomeVal(Local),
    /// For an `Option<integer>` local `o = <Range as Iterator>::next(&mut r)`: the
    /// value of `r.start` when `next` was called.
    NextOld(Local),
    /// The integer at `(*p).f1.f2…` for a local `p: &T` with `T: Freeze`: nothing
    /// can change it while `p` holds the same reference.
    Path(Local, Fields),
    /// The metadata of the slice pointer stored at such a path.
    PathLen(Local, Fields),
    /// The metadata of the slice pointer in field `k` of a tuple local.
    FieldLen(Local, u32),
}

/// A value of a callee's interface, as seen from outside its body: its return value
/// and its parameters (`Arg(i)` is the `i`-th parameter, 0-based), as they were on
/// entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SVar {
    Zero,
    /// The returned integer.
    Ret,
    /// The metadata of the returned slice pointer.
    RetLen,
    /// The metadata of the slice pointer in field `k` of the returned tuple.
    RetFieldLen(u32),
    Arg(u32),
    ArgLen(u32),
    ArgPath(u32, Fields),
    ArgPathLen(u32, Fields),
}

/// `a - b ≤ c` over interface values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Fact {
    pub a: SVar,
    pub b: SVar,
    pub c: i128,
}

/// What a call returns, in terms of the callee's parameters (a return summary,
/// computed from the callee's MIR by this analysis).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RetSummary {
    /// Difference bounds between the return value and the parameters that hold
    /// whenever the call returns.
    facts: Vec<Fact>,
    /// For a `bool` result: the comparison it holds.
    cond: Option<(CmpOp, SVar, i128, SVar, i128)>,
    /// No feasible path reaches a `return`: the call does not return.
    never_returns: bool,
}

/// Return summaries of the callees met while analysing the bodies of one root,
/// memoized per instance. A callee is summarised only if it has MIR, is not a
/// source (whose body is out of scope), and lies in `core`/`alloc`/`std` or a crate
/// the driver analyses; recursion and nesting deeper than [`MAX_SUMMARY_DEPTH`] give
/// no summary (the destination is forgotten).
pub struct Summaries<'a, 'tcx> {
    map: RefCell<HashMap<Instance<'tcx>, Option<Rc<RetSummary>>>>,
    stack: RefCell<Vec<Instance<'tcx>>>,
    crates: &'a Crates,
}

/// Nested summary computations before a callee is left unknown.
const MAX_SUMMARY_DEPTH: usize = 8;

impl<'a, 'tcx> Summaries<'a, 'tcx> {
    pub fn new(crates: &'a Crates) -> Summaries<'a, 'tcx> {
        Summaries {
            map: RefCell::new(HashMap::new()),
            stack: RefCell::new(Vec::new()),
            crates,
        }
    }

    /// `true` if the body of `def_id` may be used for a summary.
    fn usable(&self, tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
        let name = tcx.crate_name(def_id.krate);
        (is_std_crate(name.as_str()) || self.crates.exported(def_id.krate))
            && self.crates.source_of(tcx, def_id).is_none()
    }

    /// The summary of `callee`, computed on first use.
    fn get(
        &self,
        tcx: TyCtxt<'tcx>,
        env: TypingEnv<'tcx>,
        callee: Instance<'tcx>,
    ) -> Option<Rc<RetSummary>> {
        if let Some(s) = self.map.borrow().get(&callee) {
            return s.clone();
        }
        {
            let stack = self.stack.borrow();
            if stack.contains(&callee) || stack.len() >= MAX_SUMMARY_DEPTH {
                return None;
            }
        }
        if let InstanceKind::Intrinsic(def_id) = callee.def {
            let s = intrinsic_summary(tcx, def_id, callee).map(Rc::new);
            self.map.borrow_mut().insert(callee, s.clone());
            return s;
        }
        let InstanceKind::Item(def_id) = callee.def else {
            return None;
        };
        if tcx.is_foreign_item(def_id) || !tcx.is_mir_available(def_id) || !self.usable(tcx, def_id)
        {
            self.map.borrow_mut().insert(callee, None);
            return None;
        }
        let body = tcx.instance_mir(callee.def);
        if !summarisable(tcx, body.local_decls[mir::RETURN_PLACE].ty) {
            self.map.borrow_mut().insert(callee, None);
            return None;
        }
        self.stack.borrow_mut().push(callee);
        let s = summarise(tcx, env, callee, body, self).map(Rc::new);
        self.stack.borrow_mut().pop();
        self.map.borrow_mut().insert(callee, s.clone());
        s
    }
}

/// The summary of an intrinsic from `fip_lint_rules::mir::INTRINSIC_RESULT_BOUNDS`:
/// the result lies in `0..=w - k` for the bit width `w` of its integer type argument.
fn intrinsic_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    callee: Instance<'tcx>,
) -> Option<RetSummary> {
    let width = match callee.args.types().next()?.kind() {
        ty::Uint(u) => u.bit_width(),
        ty::Int(i) => i.bit_width(),
        _ => None,
    }
    .unwrap_or(tcx.data_layout.pointer_size().bits());
    let hi = fip_lint_rules::mir::intrinsic_result_bound(
        tcx.item_name(def_id).as_str(),
        u32::try_from(width).ok()?,
    )?;
    let fact = |a, b, c| Fact { a, b, c };
    Some(RetSummary {
        facts: vec![
            fact(SVar::Ret, SVar::Zero, i128::from(hi)),
            fact(SVar::Zero, SVar::Ret, 0),
        ],
        cond: None,
        never_returns: false,
    })
}

/// Return types a summary can say something about: integers, `bool`, slice pointers
/// and tuples with a slice pointer field.
fn summarisable<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    int_range(tcx, ty).is_some()
        || ty.is_bool()
        || is_slice_ptr(ty)
        || matches!(ty.kind(), ty::Tuple(fs) if fs.iter().any(is_slice_ptr))
}

/// `var + c`; `var = 0` is the constant zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Lin {
    v: usize,
    c: i128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CmpOp {
    Lt,
    Le,
    Eq,
    Ne,
}

/// `a op b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Cmp {
    op: CmpOp,
    a: Lin,
    b: Lin,
}

impl Cmp {
    fn negate(self) -> Cmp {
        match self.op {
            CmpOp::Lt => Cmp {
                op: CmpOp::Le,
                a: self.b,
                b: self.a,
            },
            CmpOp::Le => Cmp {
                op: CmpOp::Lt,
                a: self.b,
                b: self.a,
            },
            CmpOp::Eq => Cmp {
                op: CmpOp::Ne,
                ..self
            },
            CmpOp::Ne => Cmp {
                op: CmpOp::Eq,
                ..self
            },
        }
    }
    fn mentions(&self, v: usize) -> bool {
        (self.a.v == v || self.b.v == v) && v != 0
    }
    /// `self` with `v` replaced by `u + k` (where `v = u + k` holds).
    fn rewrite(self, v: usize, u: usize, k: i128) -> Cmp {
        let r = |x: Lin| {
            if x.v == v {
                Lin { v: u, c: x.c + k }
            } else {
                x
            }
        };
        Cmp {
            op: self.op,
            a: r(self.a),
            b: r(self.b),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ArithOp {
    Add,
    Sub,
    Mul,
}

/// `t = op(a, b)` with overflow check; `safe`: it cannot overflow (decided when it
/// ran, from the state before it).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Ovf {
    op: ArithOp,
    a: Lin,
    b: Lin,
    safe: bool,
}

/// Difference-bound matrix: `m[i * n + j]` bounds `v_i - v_j`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Dbm {
    n: usize,
    m: Vec<i128>,
}

impl Dbm {
    fn top(n: usize) -> Dbm {
        let mut m = vec![INF; n * n];
        for i in 0..n {
            m[i * n + i] = 0;
        }
        Dbm { n, m }
    }
    fn get(&self, i: usize, j: usize) -> i128 {
        self.m[i * self.n + j]
    }
    /// Full shortest-path closure; `false` if infeasible (negative cycle).
    fn close(&mut self) -> bool {
        let n = self.n;
        for k in 0..n {
            for i in 0..n {
                let ik = self.m[i * n + k];
                if ik >= INF {
                    continue;
                }
                for j in 0..n {
                    let v = add(ik, self.m[k * n + j]);
                    if v < self.m[i * n + j] {
                        self.m[i * n + j] = v;
                    }
                }
            }
        }
        (0..n).all(|i| self.m[i * n + i] >= 0)
    }
    /// Adds `v_i - v_j ≤ c` to a closed matrix, keeping it closed; `false` if
    /// infeasible.
    fn constrain(&mut self, i: usize, j: usize, c: i128) -> bool {
        let n = self.n;
        if c >= INF || c >= self.get(i, j) {
            return true;
        }
        if i == j {
            return c >= 0;
        }
        if add(self.get(j, i), c) < 0 {
            return false;
        }
        let col_i: Vec<i128> = (0..n).map(|p| self.m[p * n + i]).collect();
        let row_j: Vec<i128> = (0..n).map(|q| self.m[j * n + q]).collect();
        for (p, &pi) in col_i.iter().enumerate() {
            if pi >= INF {
                continue;
            }
            let base = add(pi, c);
            for (cell, &jq) in self.m[p * n..(p + 1) * n].iter_mut().zip(&row_j) {
                let v = add(base, jq);
                if v < *cell {
                    *cell = v;
                }
            }
        }
        true
    }
    /// Drops every constraint on `v` (closed matrices stay closed).
    fn forget(&mut self, v: usize) {
        let n = self.n;
        for k in 0..n {
            self.m[v * n + k] = INF;
            self.m[k * n + v] = INF;
        }
        self.m[v * n + v] = 0;
    }
    fn join(&self, o: &Dbm) -> Dbm {
        Dbm {
            n: self.n,
            m: self.m.iter().zip(&o.m).map(|(a, b)| *a.max(b)).collect(),
        }
    }
    /// Keeps the bounds of `self` that `next` does not exceed, drops the others.
    fn widen(&self, next: &Dbm) -> Dbm {
        Dbm {
            n: self.n,
            m: self
                .m
                .iter()
                .zip(&next.m)
                .map(|(a, b)| if b <= a { *a } else { INF })
                .collect(),
        }
    }
}

/// What `o = <Range<_> as Iterator>::next(&mut r)` implies once `o`'s variant is
/// known (`Range::next`: `Some(start)` and `start += 1` if `start < end`, else
/// `None` and nothing changes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OptFacts {
    some: [Cmp; 3],
    none: [Cmp; 2],
}

impl OptFacts {
    fn mentions(&self, v: usize) -> bool {
        self.some.iter().chain(&self.none).any(|c| c.mentions(v))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct State {
    d: Dbm,
    /// Boolean local → the comparison it holds.
    cond: BTreeMap<Local, Cmp>,
    /// Tuple local → the checked operation it holds.
    ovf: BTreeMap<Local, Ovf>,
    /// Pointer local → slice local whose metadata it has (`q = &(*p)`).
    slice: BTreeMap<Local, Local>,
    /// `b = &mut r` of a `Range` local `r` (used only by `next`).
    borrow: BTreeMap<Local, Local>,
    /// `Option` local → facts of the `Range::next` call that produced it.
    opt: BTreeMap<Local, OptFacts>,
    /// `d = discriminant(o)`.
    disc: BTreeMap<Local, Local>,
    /// Shared reference local → the access path it points to: `q = &(*p).f1…` or
    /// `q = copy p` for `p: &T`, `T: Freeze` (so `(*q).g` is `(*p).f1….g`).
    refs: BTreeMap<Local, (Local, Fields)>,
}

impl State {
    fn join(&self, o: &State) -> State {
        State {
            d: self.d.join(&o.d),
            cond: intersect(&self.cond, &o.cond),
            ovf: intersect(&self.ovf, &o.ovf),
            slice: intersect(&self.slice, &o.slice),
            borrow: intersect(&self.borrow, &o.borrow),
            opt: intersect(&self.opt, &o.opt),
            disc: intersect(&self.disc, &o.disc),
            refs: intersect(&self.refs, &o.refs),
        }
    }
    fn widen(&self, next: &State) -> State {
        State {
            d: self.d.widen(&next.d),
            cond: intersect(&self.cond, &next.cond),
            ovf: intersect(&self.ovf, &next.ovf),
            slice: intersect(&self.slice, &next.slice),
            borrow: intersect(&self.borrow, &next.borrow),
            opt: intersect(&self.opt, &next.opt),
            disc: intersect(&self.disc, &next.disc),
            refs: intersect(&self.refs, &next.refs),
        }
    }
}

fn intersect<K: Ord + Copy, V: PartialEq + Copy>(
    a: &BTreeMap<K, V>,
    b: &BTreeMap<K, V>,
) -> BTreeMap<K, V> {
    a.iter()
        .filter(|(k, v)| b.get(k) == Some(v))
        .map(|(k, v)| (*k, *v))
        .collect()
}

struct Ctx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    body: &'a Body<'tcx>,
    /// Tracked value → index (1-based; 0 is the constant zero).
    index: HashMap<Var, usize>,
    /// Indices of the tracked values of each local (all forgotten when it changes).
    of_local: HashMap<Local, Vec<usize>>,
    /// Type bounds per index.
    bounds: Vec<(i128, i128)>,
    /// Discriminant values of `Option::Some` and `Option::None`.
    some_none: Option<(u128, u128)>,
    /// Return summaries of the callees of call terminators, per block.
    calls: HashMap<BasicBlock, Rc<RetSummary>>,
    /// Shared reference locals to a `Freeze` type.
    shared: HashSet<Local>,
}

/// Bounds of an integer type, `None` for other types.
fn int_range<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(i128, i128)> {
    let ptr = tcx.data_layout.pointer_size().bits();
    let (signed, bits) = match ty.kind() {
        ty::Uint(u) => (false, u.bit_width().unwrap_or(ptr)),
        ty::Int(i) => (true, i.bit_width().unwrap_or(ptr)),
        _ => return None,
    };
    if bits >= 128 {
        return Some((if signed { -INF } else { 0 }, INF));
    }
    Some(if signed {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    } else {
        (0, (1i128 << bits) - 1)
    })
}

/// `true` for a pointer or reference to a slice or `str` (metadata = length).
fn is_slice_ptr(ty: Ty<'_>) -> bool {
    ty.builtin_deref(true)
        .is_some_and(|t| matches!(t.kind(), ty::Slice(_) | ty::Str))
}

/// The integer type `T` of `core::ops::Range<T>`.
fn range_int<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let ty::Adt(def, args) = ty.kind() else {
        return None;
    };
    let t = args.types().next()?;
    (tcx.is_lang_item(def.did(), LangItem::Range) && t.is_integral()).then_some(t)
}

/// The integer type `T` of `Option<T>`.
fn option_int<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let ty::Adt(def, args) = ty.kind() else {
        return None;
    };
    let t = args.types().next()?;
    (tcx.is_lang_item(def.did(), LangItem::Option) && t.is_integral()).then_some(t)
}

/// `func` is `<Range<integer> as Iterator>::next` (`lang`: `IteratorNext`) or
/// `<Range<integer> as IntoIterator>::into_iter` (`IntoIterIntoIter`, the identity
/// for an iterator).
fn is_range_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    lang: LangItem,
) -> bool {
    let ty::FnDef(def_id, args) = *func.ty(&body.local_decls, tcx).kind() else {
        return false;
    };
    let Some(args) = args.no_bound_vars() else {
        return false;
    };
    tcx.is_lang_item(def_id, lang)
        && args
            .types()
            .next()
            .is_some_and(|t| range_int(tcx, t).is_some())
}

/// Counts the uses of each local that read or write it other than by a plain
/// assignment (`Store`) or storage markers.
struct Uses {
    reads: HashMap<Local, usize>,
    stores: HashMap<Local, usize>,
}

impl<'tcx> Visitor<'tcx> for Uses {
    fn visit_local(&mut self, local: Local, ctxt: PlaceContext, _: mir::Location) {
        match ctxt {
            PlaceContext::NonUse(_) => {}
            PlaceContext::MutatingUse(MutatingUseContext::Store) => {
                *self.stores.entry(local).or_default() += 1;
            }
            _ => *self.reads.entry(local).or_default() += 1,
        }
    }
}

/// `Range` locals whose only borrows are `b = &mut r` with `b` used once, as the
/// argument of `<Range<_> as Iterator>::next` (a `for` loop): `next` changes only
/// `start`, which the transfer models.
fn ranges_borrowed_only_by_next<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    let mut uses = Uses {
        reads: HashMap::new(),
        stores: HashMap::new(),
    };
    uses.visit_body(body);
    let mut next_args: HashSet<Local> = HashSet::new();
    for data in body.basic_blocks.iter() {
        if let TerminatorKind::Call { func, args, .. } = &data.terminator().kind
            && let [arg] = &**args
            && let Operand::Copy(p) | Operand::Move(p) = &arg.node
            && let Some(b) = p.as_local()
            && is_range_call(tcx, body, func, LangItem::IteratorNext)
        {
            next_args.insert(b);
        }
    }
    let mut ok: HashSet<Local> = HashSet::new();
    let mut bad: HashSet<Local> = HashSet::new();
    for data in body.basic_blocks.iter() {
        for st in &data.statements {
            let StatementKind::Assign(assign) = &st.kind else {
                continue;
            };
            let (dest, rv) = &**assign;
            let (Rvalue::Ref(_, _, p) | Rvalue::RawPtr(_, p)) = rv else {
                continue;
            };
            if p.is_indirect_first_projection() {
                continue;
            }
            let only_next = matches!(rv, Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, _))
                && p.projection.is_empty()
                && range_int(tcx, body.local_decls[p.local].ty).is_some()
                && dest.as_local().is_some_and(|b| {
                    next_args.contains(&b)
                        && uses.reads.get(&b).copied() == Some(1)
                        && uses.stores.get(&b).copied() == Some(1)
                });
            if only_next {
                ok.insert(p.local);
            } else {
                bad.insert(p.local);
            }
        }
    }
    ok.retain(|l| !bad.contains(l));
    ok
}

/// Locals whose address is taken (`&x`, `&mut x`, `&raw x`, also of a field), or that
/// are operands of inline assembly: never tracked. `Range` locals borrowed only by
/// `next` are exempt, and so are shared borrows of places without interior
/// mutability.
fn address_taken<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    body: &Body<'tcx>,
) -> HashSet<Local> {
    let exempt = ranges_borrowed_only_by_next(tcx, body);
    let mut out = HashSet::new();
    for data in body.basic_blocks.iter() {
        for st in &data.statements {
            if let StatementKind::Assign(assign) = &st.kind {
                match &assign.1 {
                    // A shared borrow of a place without interior mutability cannot
                    // change it (writing through it is undefined behaviour), e.g. the
                    // `&x` that `format_args!` takes for a panic message.
                    Rvalue::Ref(_, mir::BorrowKind::Shared, p)
                        if p.ty(&body.local_decls, tcx).ty.is_freeze(tcx, env) => {}
                    Rvalue::Ref(_, _, p) | Rvalue::RawPtr(_, p)
                        if !p.is_indirect_first_projection() && !exempt.contains(&p.local) =>
                    {
                        out.insert(p.local);
                    }
                    _ => {}
                }
            }
        }
        if let TerminatorKind::InlineAsm { operands, .. } = &data.terminator().kind {
            for op in operands.iter() {
                match op {
                    mir::InlineAsmOperand::Out { place: Some(p), .. } => {
                        out.insert(p.local);
                    }
                    mir::InlineAsmOperand::InOut {
                        out_place: Some(p), ..
                    } => {
                        out.insert(p.local);
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// What the value analysis proves about one body, per basic block. Both vectors are
/// empty (nothing proved) if the body is not analysed.
#[derive(Clone, Debug, Default)]
pub struct Proved {
    /// The block's terminator is an `Assert` that cannot fire.
    pub asserts: Vec<bool>,
    /// No feasible path reaches the block's terminator.
    pub dead: Vec<bool>,
}

impl Proved {
    pub fn assert_cannot_fire(&self, b: usize) -> bool {
        self.asserts.get(b).copied().unwrap_or(false)
    }
    pub fn dead(&self, b: usize) -> bool {
        self.dead.get(b).copied().unwrap_or(false)
    }
}

/// `true` if `body` branches (`SwitchInt`) on a local assigned from a comparison:
/// the analysis may then prove a branch infeasible.
fn switches_on_comparison(body: &Body<'_>) -> bool {
    let cmp: HashSet<Local> = body
        .basic_blocks
        .iter()
        .flat_map(|d| d.statements.iter())
        .filter_map(|st| {
            let StatementKind::Assign(assign) = &st.kind else {
                return None;
            };
            let (place, rv) = &**assign;
            match rv {
                Rvalue::BinaryOp(op, _) if Ctx::cmp_op(*op).is_some() => place.as_local(),
                _ => None,
            }
        })
        .collect();
    body.basic_blocks.iter().any(|d| {
        !d.is_cleanup
            && matches!(&d.terminator().kind, TerminatorKind::SwitchInt { discr, .. }
                if discr.place().and_then(|p| p.as_local()).is_some_and(|l| cmp.contains(&l)))
    })
}

/// `true` if `body` is a coroutine (not analysed).
fn is_coroutine(body: &Body<'_>) -> bool {
    body.coroutine.is_some()
        || body
            .basic_blocks
            .iter()
            .any(|d| matches!(d.terminator().kind, TerminatorKind::Yield { .. }))
}

/// With `FIP_PRELINT_DUMP_MIR=<text>`: prints the MIR of every analysed body whose
/// path contains `<text>` (a debugging aid for the transfer functions).
fn dump_mir<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    let Some(filter) = std::env::var_os("FIP_PRELINT_DUMP_MIR") else {
        return;
    };
    let path = tcx.def_path_str(body.source.def_id());
    if !path.contains(filter.to_string_lossy().as_ref()) {
        return;
    }
    let mut out = Vec::new();
    if mir::pretty::MirWriter::new(tcx)
        .write_mir_fn(body, &mut out)
        .is_ok()
    {
        eprintln!(
            "fip-prelint mir ({:?}):\n{}",
            body.source.instance,
            String::from_utf8_lossy(&out)
        );
    }
}

/// Runs the value analysis on the body of `inst` if it has an `Assert` or a
/// `SwitchInt` on a comparison. If tracking the locals of both exceeds the size
/// limits, the analysis is retried with the locals of the asserts only (what was
/// tracked before feasibility was used). Calls with a return summary (`sums`) relate
/// their result to their arguments.
pub fn analyse<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    inst: Instance<'tcx>,
    body: &Body<'tcx>,
    sums: &Summaries<'_, 'tcx>,
) -> Proved {
    let has_assert = body
        .basic_blocks
        .iter()
        .any(|d| !d.is_cleanup && matches!(d.terminator().kind, TerminatorKind::Assert { .. }));
    let switches = switches_on_comparison(body);
    if !(has_assert || switches) || is_coroutine(body) {
        return Proved::default();
    }
    dump_mir(tcx, body);
    let calls = call_summaries(tcx, env, inst, body, sums);
    let mode = |switches| Mode {
        switches,
        ret: false,
    };
    if let Some((_, o)) = analyse_with(tcx, env, inst, body, mode(switches), &calls) {
        return o.proved;
    }
    if switches && has_assert {
        return analyse_with(tcx, env, inst, body, mode(false), &calls)
            .map(|(_, o)| o.proved)
            .unwrap_or_default();
    }
    Proved::default()
}

/// The return summary of `inst` (whose body is `body`): the analysis tracking the
/// return place, the parameters connected to it and the comparisons switched on,
/// projected at the reachable `return`s onto the return value and the parameters
/// that the body never changes.
fn summarise<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    inst: Instance<'tcx>,
    body: &Body<'tcx>,
    sums: &Summaries<'_, 'tcx>,
) -> Option<RetSummary> {
    if is_coroutine(body) {
        return None;
    }
    dump_mir(tcx, body);
    let calls = call_summaries(tcx, env, inst, body, sums);
    let mode = |switches| Mode {
        switches,
        ret: true,
    };
    let (cx, out) = analyse_with(tcx, env, inst, body, mode(true), &calls)
        .or_else(|| analyse_with(tcx, env, inst, body, mode(false), &calls))?;
    cx.summary(out.returns?)
}

/// The callee of the call terminating `bb`, resolved with the arguments of `inst`.
fn callee_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    inst: Instance<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
) -> Option<Instance<'tcx>> {
    let fty = inst
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            env,
            EarlyBinder::bind(tcx, func.ty(&body.local_decls, tcx)),
        )
        .ok()?;
    let ty::FnDef(def_id, args) = *fty.kind() else {
        return None;
    };
    Instance::try_resolve(tcx, env, def_id, args.no_bound_vars()?)
        .ok()
        .flatten()
}

/// Return summaries of the callees of the call terminators of `body` whose
/// destination has a summarisable type.
fn call_summaries<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    inst: Instance<'tcx>,
    body: &Body<'tcx>,
    sums: &Summaries<'_, 'tcx>,
) -> HashMap<BasicBlock, Rc<RetSummary>> {
    let mut out = HashMap::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        let TerminatorKind::Call {
            func,
            destination,
            target: Some(_),
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        if !summarisable(tcx, destination.ty(&body.local_decls, tcx).ty) {
            continue;
        }
        if let Some(callee) = callee_at(tcx, env, inst, body, func)
            && let Some(s) = sums.get(tcx, env, callee)
        {
            out.insert(bb, s);
        }
    }
    out
}

/// What is tracked: with `switches`, the locals of comparisons switched on (besides
/// those of asserts); with `ret`, the return place (a summary is computed).
#[derive(Clone, Copy)]
struct Mode {
    switches: bool,
    ret: bool,
}

/// The result of [`Ctx::run`]: per-block facts, and the states at the terminators
/// of the reachable `return` blocks (`None` if the analysis gave up).
struct Outcome {
    proved: Proved,
    returns: Option<Vec<State>>,
}

/// The type of `ty` instantiated with the arguments of `inst`, or `ty` itself.
fn inst_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    inst: Instance<'tcx>,
    ty: Ty<'tcx>,
) -> Ty<'tcx> {
    inst.try_instantiate_mir_and_normalize_erasing_regions(tcx, env, EarlyBinder::bind(tcx, ty))
        .unwrap_or(ty)
}

/// `p` is `(*b).f1.f2…` (a dereference, then fields only).
fn path_of(p: &Place<'_>) -> Option<(Local, Fields)> {
    let [ProjectionElem::Deref, rest @ ..] = p.projection.as_slice() else {
        return None;
    };
    let mut fs = Vec::new();
    for e in rest {
        let ProjectionElem::Field(f, _) = e else {
            return None;
        };
        fs.push(f.as_u32());
    }
    Some((p.local, Fields::new(&fs)?))
}

/// Static definitions of shared reference locals: `q = &(*b).f…` and `q = copy b`
/// for `b` in `shared` (several if `q` is assigned several times).
fn ref_defs(body: &Body<'_>, shared: &HashSet<Local>) -> HashMap<Local, Vec<(Local, Fields)>> {
    let mut out: HashMap<Local, Vec<(Local, Fields)>> = HashMap::new();
    for data in body.basic_blocks.iter() {
        for st in &data.statements {
            let StatementKind::Assign(assign) = &st.kind else {
                continue;
            };
            let (place, rv) = &**assign;
            let Some(q) = place.as_local() else {
                continue;
            };
            let def = match rv {
                Rvalue::Ref(_, mir::BorrowKind::Shared, p) => path_of(p),
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..) => {
                    p.as_local().map(|b| (b, Fields::EMPTY))
                }
                _ => None,
            };
            if let Some((b, fs)) = def
                && b != q
                && shared.contains(&b)
            {
                out.entry(q).or_default().push((b, fs));
            }
        }
    }
    out
}

/// `(q, g)` and the paths it stands for through the static definitions of `q`.
fn expand_path(
    defs: &HashMap<Local, Vec<(Local, Fields)>>,
    q: Local,
    g: Fields,
    out: &mut BTreeSet<(Local, Fields)>,
    depth: usize,
) {
    if !out.insert((q, g)) || depth == 0 {
        return;
    }
    for (b, fs) in defs.get(&q).map(Vec::as_slice).unwrap_or_default() {
        if let Some(f) = fs.concat(&g) {
            expand_path(defs, *b, f, out, depth - 1);
        }
    }
}

/// Access paths worth tracking: those read in the body, and those that the summary
/// of a callee mentions for an argument; each with the paths it stands for through
/// shared references copied or reborrowed in the body. `(base, fields, len)`: `len`
/// for the metadata of a slice pointer at the path.
fn path_candidates<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    shared: &HashSet<Local>,
    calls: &HashMap<BasicBlock, Rc<RetSummary>>,
) -> BTreeSet<Var> {
    struct Reads<'b, 'tcx> {
        tcx: TyCtxt<'tcx>,
        body: &'b Body<'tcx>,
        shared: &'b HashSet<Local>,
        found: Vec<(Local, Fields, bool)>,
    }
    impl<'tcx> Visitor<'tcx> for Reads<'_, 'tcx> {
        fn visit_place(&mut self, p: &Place<'tcx>, _: PlaceContext, _: mir::Location) {
            if let Some((b, fs)) = path_of(p)
                && self.shared.contains(&b)
            {
                let ty = p.ty(&self.body.local_decls, self.tcx).ty;
                if int_range(self.tcx, ty).is_some() {
                    self.found.push((b, fs, false));
                } else if is_slice_ptr(ty) {
                    self.found.push((b, fs, true));
                }
            }
        }
    }
    let mut reads = Reads {
        tcx,
        body,
        shared,
        found: Vec::new(),
    };
    reads.visit_body(body);
    let mut found = reads.found;
    for (bb, s) in calls {
        let TerminatorKind::Call { args, .. } = &body.basic_blocks[*bb].terminator().kind else {
            continue;
        };
        for sv in s.svars() {
            let (i, fs, len) = match sv {
                SVar::ArgPath(i, fs) => (i, fs, false),
                SVar::ArgPathLen(i, fs) => (i, fs, true),
                _ => continue,
            };
            if let Some(a) = args.get(i as usize)
                && let Operand::Copy(p) | Operand::Move(p) = &a.node
                && let Some(q) = p.as_local()
            {
                found.push((q, fs, len));
            }
        }
    }
    let defs = ref_defs(body, shared);
    let mut out = BTreeSet::new();
    for (q, g, len) in found {
        let mut paths = BTreeSet::new();
        expand_path(&defs, q, g, &mut paths, 3);
        for (b, fs) in paths {
            if shared.contains(&b) {
                out.insert(if len {
                    Var::PathLen(b, fs)
                } else {
                    Var::Path(b, fs)
                });
            }
        }
    }
    out
}

/// The analysis tracking the locals connected to asserts, to comparisons switched on
/// if `mode.switches`, and to the return place if `mode.ret`; `None` if that exceeds
/// the size limits.
fn analyse_with<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    inst: Instance<'tcx>,
    body: &'a Body<'tcx>,
    mode: Mode,
    calls: &HashMap<BasicBlock, Rc<RetSummary>>,
) -> Option<(Ctx<'a, 'tcx>, Outcome)> {
    let n_blocks = body.basic_blocks.len();
    let taken = address_taken(tcx, env, body);
    let relevant = relevant_locals(tcx, body, mode, calls);
    let shared: HashSet<Local> = body
        .local_decls
        .iter_enumerated()
        .filter(|(l, _)| relevant.contains(l) && !taken.contains(l))
        .filter(|(_, d)| {
            matches!(inst_ty(tcx, env, inst, d.ty).kind(),
                ty::Ref(_, t, ty::Mutability::Not) if t.is_freeze(tcx, env))
        })
        .map(|(l, _)| l)
        .collect();
    let mut index = HashMap::new();
    let mut of_local: HashMap<Local, Vec<usize>> = HashMap::new();
    let mut bounds = vec![(0, 0)];
    let usize_max = int_range(tcx, tcx.types.usize).map_or(INF, |r| r.1);
    let mut push = |v: Var, r: (i128, i128)| {
        let l = match v {
            Var::Local(l)
            | Var::Len(l)
            | Var::Field0(l)
            | Var::RangeStart(l)
            | Var::RangeEnd(l)
            | Var::SomeVal(l)
            | Var::NextOld(l)
            | Var::Path(l, _)
            | Var::PathLen(l, _)
            | Var::FieldLen(l, _) => l,
        };
        of_local.entry(l).or_default().push(bounds.len());
        index.insert(v, bounds.len());
        bounds.push(r);
    };
    for (local, decl) in body.local_decls.iter_enumerated() {
        if taken.contains(&local) || !relevant.contains(&local) {
            continue;
        }
        if let Some(r) = int_range(tcx, decl.ty) {
            push(Var::Local(local), r);
        } else if is_slice_ptr(decl.ty) {
            push(Var::Len(local), (0, usize_max));
        } else if let ty::Tuple(fields) = decl.ty.kind()
            && fields.len() == 2
            && fields[1].is_bool()
            && let Some(r) = int_range(tcx, fields[0])
        {
            push(Var::Field0(local), r);
        } else if let ty::Tuple(fields) = decl.ty.kind()
            && fields.iter().any(is_slice_ptr)
        {
            for (k, f) in fields.iter().enumerate() {
                if is_slice_ptr(f)
                    && let Ok(k) = u32::try_from(k)
                {
                    push(Var::FieldLen(local, k), (0, usize_max));
                }
            }
        } else if let Some(r) = range_int(tcx, decl.ty).and_then(|t| int_range(tcx, t)) {
            push(Var::RangeStart(local), r);
            push(Var::RangeEnd(local), r);
        } else if let Some(r) = option_int(tcx, decl.ty).and_then(|t| int_range(tcx, t)) {
            push(Var::SomeVal(local), r);
            push(Var::NextOld(local), r);
        }
    }
    for v in path_candidates(tcx, body, &shared, calls) {
        let (b, fs, len) = match v {
            Var::Path(b, fs) => (b, fs, false),
            Var::PathLen(b, fs) => (b, fs, true),
            _ => continue,
        };
        let ty = path_ty(tcx, body.local_decls[b].ty, fs);
        let r = match ty {
            Some(t) if len && is_slice_ptr(t) => Some((0, usize_max)),
            Some(t) if !len => int_range(tcx, t),
            _ => None,
        };
        if let Some(r) = r {
            push(v, r);
        }
    }
    let n = bounds.len();
    if n > MAX_VARS || n_blocks.saturating_mul(n * n) > MAX_CELLS {
        return None;
    }
    let cx = Ctx {
        tcx,
        env,
        body,
        index,
        of_local,
        bounds,
        some_none: option_discriminants(tcx),
        calls: calls.clone(),
        shared,
    };
    let out = cx.run(n_blocks);
    Some((cx, out))
}

/// The type at `(*b).f1.f2…` for `b: base` (a reference), through struct and tuple
/// fields only.
fn path_ty<'tcx>(tcx: TyCtxt<'tcx>, base: Ty<'tcx>, fs: Fields) -> Option<Ty<'tcx>> {
    let ty::Ref(_, mut t, _) = *base.kind() else {
        return None;
    };
    for &f in fs.as_slice() {
        t = match t.kind() {
            ty::Adt(def, args) if def.is_struct() => def
                .non_enum_variant()
                .fields
                .iter()
                .nth(usize::try_from(f).ok()?)?
                .ty(tcx, args)
                .skip_normalization(),
            ty::Tuple(ts) => *ts.get(usize::try_from(f).ok()?)?,
            _ => return None,
        };
    }
    Some(t)
}

/// Locals connected to an `Assert` condition, or with `switches` to the discriminant
/// of a `SwitchInt`, through assignments (copies, casts, operations, comparisons,
/// borrows, discriminants, the two `Range` calls of a `for` loop): only these are
/// tracked. The others cannot constrain a checked value or a branch, so leaving them
/// untracked loses nothing the analysis could use.
fn relevant_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    mode: Mode,
    calls: &HashMap<BasicBlock, Rc<RetSummary>>,
) -> HashSet<Local> {
    let n = body.local_decls.len();
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    let union = |parent: &mut Vec<usize>, a: Local, b: Local| {
        let (ra, rb) = (find(parent, a.as_usize()), find(parent, b.as_usize()));
        if ra != rb {
            parent[ra] = rb;
        }
    };
    let op_local = |op: &Operand<'tcx>| match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p.local),
        _ => None,
    };
    let mut seeds: Vec<Local> = Vec::new();
    if mode.ret {
        seeds.push(mir::RETURN_PLACE);
    }
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for st in &data.statements {
            let StatementKind::Assign(assign) = &st.kind else {
                continue;
            };
            let (place, rv) = &**assign;
            let l = place.local;
            let mut used: Vec<Local> = Vec::new();
            match rv {
                Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) | Rvalue::UnaryOp(_, op) => {
                    used.extend(op_local(op));
                }
                Rvalue::BinaryOp(_, ops) => {
                    used.extend(op_local(&ops.0));
                    used.extend(op_local(&ops.1));
                }
                Rvalue::Ref(_, _, p)
                | Rvalue::RawPtr(_, p)
                | Rvalue::Discriminant(p)
                | Rvalue::CopyForDeref(p) => {
                    used.push(p.local);
                }
                Rvalue::Aggregate(_, ops) => used.extend(ops.iter().filter_map(op_local)),
                _ => {}
            }
            for u in used {
                union(&mut parent, l, u);
            }
        }
        match &data.terminator().kind {
            TerminatorKind::Assert { cond, .. } => seeds.extend(op_local(cond)),
            TerminatorKind::SwitchInt { discr, .. } if mode.switches && !data.is_cleanup => {
                seeds.extend(op_local(discr));
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } if is_range_call(tcx, body, func, LangItem::IteratorNext)
                || is_range_call(tcx, body, func, LangItem::IntoIterIntoIter)
                || calls.contains_key(&bb) =>
            {
                for a in args.iter() {
                    if let Some(u) = op_local(&a.node) {
                        union(&mut parent, destination.local, u);
                    }
                }
            }
            _ => {}
        }
    }
    let roots: HashSet<usize> = seeds
        .iter()
        .map(|s| find(&mut parent, s.as_usize()))
        .collect();
    (0..n)
        .filter(|&i| roots.contains(&find(&mut parent, i)))
        .map(Local::from_usize)
        .collect()
}

/// Discriminant values of `Option::Some` and `Option::None`.
fn option_discriminants(tcx: TyCtxt<'_>) -> Option<(u128, u128)> {
    let items = tcx.lang_items();
    let option = tcx.adt_def(items.option_type()?);
    let some = option.variant_index_with_id(items.option_some_variant()?);
    let none = option.variant_index_with_id(items.option_none_variant()?);
    Some((
        option.discriminant_for_variant(tcx, some).val,
        option.discriminant_for_variant(tcx, none).val,
    ))
}

impl<'a, 'tcx> Ctx<'a, 'tcx> {
    fn n(&self) -> usize {
        self.bounds.len()
    }

    /// The state at function entry: type bounds only.
    fn entry(&self) -> State {
        let mut d = Dbm::top(self.n());
        for (v, &(lo, hi)) in self.bounds.iter().enumerate().skip(1) {
            d.m[v * d.n] = hi;
            d.m[v] = if lo <= -INF { INF } else { -lo };
        }
        d.close();
        State {
            d,
            cond: BTreeMap::new(),
            ovf: BTreeMap::new(),
            slice: BTreeMap::new(),
            borrow: BTreeMap::new(),
            opt: BTreeMap::new(),
            disc: BTreeMap::new(),
            refs: BTreeMap::new(),
        }
    }

    fn var(&self, v: Var) -> Option<usize> {
        self.index.get(&v).copied()
    }

    /// Drops the recorded comparisons, operations and `next` facts that mention `v`.
    /// A comparison is kept if `v` equals another value `u` plus a constant: it is
    /// rewritten in terms of `u` (which keeps its value when `v` changes).
    fn invalidate(&self, st: &mut State, v: usize) {
        let n = st.d.n;
        let same = (0..n)
            .find(|&u| u != v && st.d.get(v, u) < INF && st.d.get(v, u) == -st.d.get(u, v))
            .map(|u| (u, st.d.get(v, u)));
        st.cond = std::mem::take(&mut st.cond)
            .into_iter()
            .filter_map(|(l, c)| {
                if !c.mentions(v) {
                    Some((l, c))
                } else {
                    same.map(|(u, k)| (l, c.rewrite(v, u, k)))
                }
            })
            .collect();
        st.ovf
            .retain(|_, o| !(o.a.v == v && v != 0) && !(o.b.v == v && v != 0));
        st.opt.retain(|_, f| !f.mentions(v));
    }

    /// Forgets `v` and restores its type bounds.
    fn forget_var(&self, st: &mut State, v: usize) {
        self.invalidate(st, v);
        st.d.forget(v);
        let (lo, hi) = self.bounds[v];
        st.d.constrain(v, 0, hi);
        if lo > -INF {
            st.d.constrain(0, v, -lo);
        }
    }

    /// Forgets everything known about local `l`.
    fn kill(&self, st: &mut State, l: Local) {
        if let Some(vs) = self.of_local.get(&l) {
            for &i in vs {
                self.forget_var(st, i);
            }
        }
        st.cond.remove(&l);
        st.ovf.remove(&l);
        st.slice.remove(&l);
        st.slice.retain(|_, base| *base != l);
        st.borrow.remove(&l);
        st.borrow.retain(|_, r| *r != l);
        st.opt.remove(&l);
        st.disc.remove(&l);
        st.disc.retain(|_, o| *o != l);
        st.refs.remove(&l);
        st.refs.retain(|_, (b, _)| *b != l);
    }

    fn reset(&self, st: &mut State) {
        *st = self.entry();
    }

    /// Value of a constant integer operand.
    fn const_value(&self, c: &mir::ConstOperand<'tcx>) -> Option<i128> {
        let ty = c.const_.ty();
        let (lo, _) = int_range(self.tcx, ty)?;
        let bits = c.const_.try_eval_bits(self.tcx, self.env)?;
        let v = if lo < 0 {
            let size = self.tcx.layout_of(self.env.as_query_input(ty)).ok()?.size;
            size.sign_extend(bits)
        } else {
            i128::try_from(bits).ok()?
        };
        (v.unsigned_abs() < (INF / 4).unsigned_abs()).then_some(v)
    }

    /// The value an operand stands for, if tracked.
    fn lin(&self, st: &State, op: &Operand<'tcx>) -> Option<Lin> {
        match op {
            Operand::Constant(c) => self.const_value(c).map(|c| Lin { v: 0, c }),
            Operand::Copy(p) | Operand::Move(p) => self.place_lin(st, p),
            _ => None,
        }
    }

    fn place_lin(&self, st: &State, p: &Place<'tcx>) -> Option<Lin> {
        if let Some(l) = p.as_local() {
            return self.var(Var::Local(l)).map(|v| Lin { v, c: 0 });
        }
        if let Some((b, fs)) = path_of(p) {
            return self.path_var(st, b, fs, false).map(|v| Lin { v, c: 0 });
        }
        match p.projection.as_slice() {
            [ProjectionElem::Field(f, _)] if f.as_usize() == 0 => {
                self.var(Var::Field0(p.local)).map(|v| Lin { v, c: 0 })
            }
            // `(o as Some).0`: only read where `o` is `Some`.
            [ProjectionElem::Downcast(..), ProjectionElem::Field(f, _)] if f.as_usize() == 0 => {
                self.var(Var::SomeVal(p.local)).map(|v| Lin { v, c: 0 })
            }
            _ => None,
        }
    }

    /// The tracked value at `(*q).fs` (its slice metadata if `len`): through the path
    /// `q` points to (`st.refs`) if tracked, else directly; only for a shared
    /// reference `q` to a `Freeze` type.
    fn path_var(&self, st: &State, q: Local, fs: Fields, len: bool) -> Option<usize> {
        let mk = |b: Local, f: Fields| {
            if len {
                Var::PathLen(b, f)
            } else {
                Var::Path(b, f)
            }
        };
        if let Some((b, f0)) = st.refs.get(&q)
            && let Some(f) = f0.concat(&fs)
            && let Some(v) = self.var(mk(*b, f))
        {
            return Some(v);
        }
        if !self.shared.contains(&q) {
            return None;
        }
        self.var(mk(q, fs))
    }

    /// The tracked length of the slice pointer `op`: of a local (or the slice local
    /// it was derived from), or stored at an access path.
    fn len_of(&self, st: &State, op: &Operand<'tcx>) -> Option<usize> {
        if let Some(b) = self.slice_base(st, op) {
            return self.var(Var::Len(b));
        }
        let (Operand::Copy(p) | Operand::Move(p)) = op else {
            return None;
        };
        if let Some((b, fs)) = path_of(p) {
            return self.path_var(st, b, fs, true);
        }
        if let [ProjectionElem::Field(f, _)] = p.projection.as_slice() {
            return self.var(Var::FieldLen(p.local, f.as_u32()));
        }
        None
    }

    /// The slice local whose length `op` (a slice pointer) has.
    fn slice_base(&self, st: &State, op: &Operand<'tcx>) -> Option<Local> {
        let (Operand::Copy(p) | Operand::Move(p)) = op else {
            return None;
        };
        let l = p.as_local()?;
        let base = st.slice.get(&l).copied().unwrap_or(l);
        self.var(Var::Len(base)).map(|_| base)
    }

    /// `a - b ≤ k` holds in every state described by `st`.
    fn entails(&self, st: &State, a: Lin, b: Lin, k: i128) -> bool {
        let rhs = k - a.c + b.c;
        if a.v == b.v {
            return 0 <= rhs;
        }
        st.d.get(a.v, b.v) <= rhs
    }

    /// Adds `a - b ≤ k`; `false` if infeasible.
    fn add_le(&self, st: &mut State, a: Lin, b: Lin, k: i128) -> bool {
        let rhs = k - a.c + b.c;
        if a.v == b.v {
            return 0 <= rhs;
        }
        st.d.constrain(a.v, b.v, rhs)
    }

    fn decide(&self, st: &State, c: Cmp) -> Option<bool> {
        let (a, b) = (c.a, c.b);
        match c.op {
            CmpOp::Lt => {
                if self.entails(st, a, b, -1) {
                    Some(true)
                } else if self.entails(st, b, a, 0) {
                    Some(false)
                } else {
                    None
                }
            }
            CmpOp::Le => {
                if self.entails(st, a, b, 0) {
                    Some(true)
                } else if self.entails(st, b, a, -1) {
                    Some(false)
                } else {
                    None
                }
            }
            CmpOp::Eq => {
                if self.entails(st, a, b, 0) && self.entails(st, b, a, 0) {
                    Some(true)
                } else if self.entails(st, a, b, -1) || self.entails(st, b, a, -1) {
                    Some(false)
                } else {
                    None
                }
            }
            CmpOp::Ne => self.decide(st, c.negate()).map(|v| !v),
        }
    }

    /// Restricts `st` to the states where `c` holds; `false` if none.
    fn assume(&self, st: &mut State, c: Cmp) -> bool {
        let (a, b) = (c.a, c.b);
        match c.op {
            CmpOp::Lt => self.add_le(st, a, b, -1),
            CmpOp::Le => self.add_le(st, a, b, 0),
            CmpOp::Eq => self.add_le(st, a, b, 0) && self.add_le(st, b, a, 0),
            CmpOp::Ne => {
                // `a ≠ b` with `a ≤ b` known is `a < b` (and symmetrically).
                if self.entails(st, a, b, 0) && !self.add_le(st, a, b, -1) {
                    return false;
                }
                if self.entails(st, b, a, 0) && !self.add_le(st, b, a, -1) {
                    return false;
                }
                true
            }
        }
    }

    fn upper(&self, st: &State, x: Lin) -> i128 {
        add(st.d.get(x.v, 0), x.c)
    }

    fn lower(&self, st: &State, x: Lin) -> i128 {
        let m = st.d.get(0, x.v);
        if m >= INF { -INF } else { x.c - m }
    }

    /// `a op b` stays within `(lo, hi)`.
    fn cannot_overflow(
        &self,
        st: &State,
        op: ArithOp,
        a: Lin,
        b: Lin,
        (lo, hi): (i128, i128),
    ) -> bool {
        // 128-bit types have no finite bound here: nothing is proved for them.
        if hi >= INF || lo <= -INF {
            return false;
        }
        match op {
            ArithOp::Add => {
                let up = add(self.upper(st, a), self.upper(st, b));
                let low = self.lower(st, a) + self.lower(st, b);
                up <= hi && low >= lo && self.lower(st, a) > -INF && self.lower(st, b) > -INF
            }
            ArithOp::Sub => {
                // `a - b ≥ lo` is `b - a ≤ -lo`; `a - b ≤ hi`.
                self.entails(st, b, a, -lo) && self.entails(st, a, b, hi)
            }
            ArithOp::Mul => {
                let (la, lb) = (self.lower(st, a), self.lower(st, b));
                let (ua, ub) = (self.upper(st, a), self.upper(st, b));
                la >= 0
                    && lb >= 0
                    && ua < INF
                    && ub < INF
                    && ua.checked_mul(ub).is_some_and(|p| p <= hi)
            }
        }
    }

    /// Adds `t.0 = a op b` (after the overflow check of `t` succeeded).
    fn define_result(&self, st: &mut State, t: Local, o: Ovf) -> bool {
        match self.var(Var::Field0(t)) {
            Some(r) => self.define_var(st, r, o.op, o.a, o.b),
            None => true,
        }
    }

    /// Adds `r = a op b` for a result `r` known to be in range (a checked operation
    /// that succeeded, or an unchecked one, whose overflow is undefined behaviour).
    fn define_var(&self, st: &mut State, r: usize, op: ArithOp, a: Lin, b: Lin) -> bool {
        let res = Lin { v: r, c: 0 };
        match op {
            ArithOp::Add => {
                // r - a = b and r - b = a, each within its bounds.
                let (lb, ub) = (self.lower(st, b), self.upper(st, b));
                let (la, ua) = (self.lower(st, a), self.upper(st, a));
                let za = Lin { v: a.v, c: 0 };
                let zb = Lin { v: b.v, c: 0 };
                // r - (a.v) = a.c + b, so r - a.v ≤ a.c + ub and a.v - r ≤ -(a.c + lb).
                (ub >= INF || self.add_le(st, res, za, a.c + ub))
                    && (lb <= -INF || self.add_le(st, za, res, -(a.c + lb)))
                    && (ua >= INF || self.add_le(st, res, zb, b.c + ua))
                    && (la <= -INF || self.add_le(st, zb, res, -(b.c + la)))
            }
            ArithOp::Sub => {
                // r = a - b: r - a.v = a.c - b.
                let (lb, ub) = (self.lower(st, b), self.upper(st, b));
                let za = Lin { v: a.v, c: 0 };
                // And r lies within the bounds known for the difference a - b.
                let zero = Lin { v: 0, c: 0 };
                let (hi, lo) = if a.v == b.v {
                    (a.c - b.c, b.c - a.c)
                } else {
                    (
                        add(st.d.get(a.v, b.v), a.c - b.c),
                        add(st.d.get(b.v, a.v), b.c - a.c),
                    )
                };
                (lb <= -INF || self.add_le(st, res, za, a.c - lb))
                    && (ub >= INF || self.add_le(st, za, res, ub - a.c))
                    && (hi >= INF || self.add_le(st, res, zero, hi))
                    && (lo >= INF || self.add_le(st, zero, res, lo))
            }
            ArithOp::Mul => {
                let (la, lb) = (self.lower(st, a), self.lower(st, b));
                let (ua, ub) = (self.upper(st, a), self.upper(st, b));
                if la >= 0 && lb >= 0 && ua < INF && ub < INF {
                    let zero = Lin { v: 0, c: 0 };
                    match (ua.checked_mul(ub), la.checked_mul(lb)) {
                        (Some(hi), Some(lo)) => {
                            self.add_le(st, res, zero, hi) && self.add_le(st, zero, res, -lo)
                        }
                        _ => true,
                    }
                } else {
                    true
                }
            }
        }
    }

    /// Sets local `l` to the tracked value `x` (forgets `l` if it is not tracked).
    fn set(&self, st: &mut State, l: Local, x: Lin) {
        let Some(v) = self.var(Var::Local(l)) else {
            self.kill(st, l);
            return;
        };
        if x.v == v {
            // `l = l` changes nothing; operands never have the form `l + c`.
            if x.c != 0 {
                self.kill(st, l);
            }
            return;
        }
        self.kill(st, l);
        let me = Lin { v, c: 0 };
        // A value-preserving copy satisfies the type bounds of `l`; if the equality
        // were infeasible the matrix is left unchanged, which over-approximates.
        if self.add_le(st, me, x, 0) {
            self.add_le(st, x, me, 0);
        }
    }

    fn statement(&self, st: &mut State, s: &mir::Statement<'tcx>) -> bool {
        match &s.kind {
            StatementKind::Assign(assign) => {
                let (place, rv) = &**assign;
                let Some(l) = place.as_local() else {
                    if !place.is_indirect_first_projection() {
                        self.kill(st, place.local);
                    }
                    return true;
                };
                self.assign(st, l, rv)
            }
            StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => {
                self.kill(st, *l);
                true
            }
            StatementKind::SetDiscriminant { place, .. } => {
                if !place.is_indirect_first_projection() {
                    self.kill(st, place.local);
                }
                true
            }
            _ => true,
        }
    }

    fn cmp_op(op: BinOp) -> Option<(CmpOp, bool)> {
        Some(match op {
            BinOp::Lt => (CmpOp::Lt, false),
            BinOp::Le => (CmpOp::Le, false),
            BinOp::Gt => (CmpOp::Lt, true),
            BinOp::Ge => (CmpOp::Le, true),
            BinOp::Eq => (CmpOp::Eq, false),
            BinOp::Ne => (CmpOp::Ne, false),
            _ => return None,
        })
    }

    /// `l = op` (a copy or move).
    fn assign_use(&self, st: &mut State, l: Local, op: &Operand<'tcx>) {
        if let Some(x) = self.lin(st, op) {
            self.set(st, l, x);
            return;
        }
        let copied = match op {
            Operand::Copy(p) | Operand::Move(p) => p.as_local(),
            _ => None,
        };
        let cond = copied.and_then(|c| st.cond.get(&c).copied());
        let base = self.slice_base(st, op);
        let len = self.len_of(st, op);
        let range = copied.filter(|c| *c != l).and_then(|c| self.range_vars(c));
        // `q = copy p` of a shared reference: `q` points where `p` does.
        let refd = copied.filter(|c| *c != l).and_then(|c| {
            st.refs
                .get(&c)
                .copied()
                .or_else(|| self.shared.contains(&c).then_some((c, Fields::EMPTY)))
        });
        let own_len = len.is_some_and(|v| self.of_local.get(&l).is_some_and(|vs| vs.contains(&v)));
        self.kill(st, l);
        if let Some(c) = cond {
            st.cond.insert(l, c);
        }
        if let Some(b) = base
            && b != l
        {
            st.slice.insert(l, b);
        }
        if let (Some(v), Some(me)) = (len, self.var(Var::Len(l)))
            && !own_len
        {
            self.equate(st, me, Lin { v, c: 0 });
        }
        if let Some((b, fs)) = refd
            && b != l
        {
            st.refs.insert(l, (b, fs));
        }
        // `r2 = move r` of a `Range`: same `start` and `end`.
        if let (Some((s, e)), Some((s2, e2))) = (range, self.range_vars(l)) {
            self.equate(st, s2, Lin { v: s, c: 0 });
            self.equate(st, e2, Lin { v: e, c: 0 });
        }
    }

    /// `l = op as to` for a slice pointer type `to`: a pointer cast between slice
    /// pointers keeps the metadata; an unsizing coercion of a pointer to `[T; N]`
    /// has the metadata `N`.
    fn assign_slice_cast(&self, st: &mut State, l: Local, kind: mir::CastKind, op: &Operand<'tcx>) {
        let from = op.ty(&self.body.local_decls, self.tcx);
        let len = match kind {
            mir::CastKind::PtrToPtr
            | mir::CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _)
                if is_slice_ptr(from) =>
            {
                self.len_of(st, op).map(|v| Lin { v, c: 0 })
            }
            mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _) => from
                .builtin_deref(true)
                .and_then(|t| match t.kind() {
                    ty::Array(_, n) => n.try_to_target_usize(self.tcx),
                    _ => None,
                })
                .map(|n| Lin {
                    v: 0,
                    c: i128::from(n),
                }),
            _ => None,
        };
        let len = len.filter(|x| !self.mentions_local(*x, l));
        self.kill(st, l);
        if let (Some(x), Some(me)) = (len, self.var(Var::Len(l))) {
            self.equate(st, me, x);
        }
    }

    fn assign(&self, st: &mut State, l: Local, rv: &Rvalue<'tcx>) -> bool {
        // Read the operands in the state before the assignment.
        match rv {
            Rvalue::Use(op, ..) => self.assign_use(st, l, op),
            Rvalue::CopyForDeref(p) => self.assign_use(st, l, &Operand::Copy(*p)),
            Rvalue::Cast(kind, op, to) if is_slice_ptr(*to) => {
                self.assign_slice_cast(st, l, *kind, op);
            }
            Rvalue::Cast(mir::CastKind::IntToInt, op, to) => {
                let from = op.ty(&self.body.local_decls, self.tcx);
                let x = self.lin(st, op);
                let keeps = match (int_range(self.tcx, from), int_range(self.tcx, *to)) {
                    (Some((fl, fh)), Some((tl, th))) => tl <= fl && fh <= th,
                    _ => false,
                };
                match x {
                    Some(x) if keeps => self.set(st, l, x),
                    _ => self.kill(st, l),
                }
            }
            Rvalue::BinaryOp(op @ (BinOp::AddUnchecked | BinOp::SubUnchecked), ops) => {
                // Overflow of an unchecked operation is undefined behaviour: the result
                // is the mathematical one.
                let (a, b) = &**ops;
                let (la, lb) = (self.lin(st, a), self.lin(st, b));
                let aop = if *op == BinOp::AddUnchecked {
                    ArithOp::Add
                } else {
                    ArithOp::Sub
                };
                let fresh = |x: &Lin| !self.mentions_local(*x, l);
                self.kill(st, l);
                if let (Some(x), Some(y), Some(r)) = (la, lb, self.var(Var::Local(l)))
                    && fresh(&x)
                    && fresh(&y)
                    && !self.define_var(st, r, aop, x, y)
                {
                    return false;
                }
            }
            Rvalue::BinaryOp(op, ops) => {
                let (a, b) = &**ops;
                let (la, lb) = (self.lin(st, a), self.lin(st, b));
                if let Some((cop, swap)) = Self::cmp_op(*op) {
                    self.kill(st, l);
                    if let (Some(x), Some(y)) = (la, lb) {
                        let (x, y) = if swap { (y, x) } else { (x, y) };
                        st.cond.insert(
                            l,
                            Cmp {
                                op: cop,
                                a: x,
                                b: y,
                            },
                        );
                    }
                    return true;
                }
                let arith = match op {
                    BinOp::AddWithOverflow => Some(ArithOp::Add),
                    BinOp::SubWithOverflow => Some(ArithOp::Sub),
                    BinOp::MulWithOverflow => Some(ArithOp::Mul),
                    _ => None,
                };
                let range = a.ty(&self.body.local_decls, self.tcx);
                let range = int_range(self.tcx, range);
                // The result must not be expressed through the tuple being assigned.
                let own = |x: Lin| {
                    x.v != 0
                        && (Some(x.v) == self.var(Var::Field0(l))
                            || Some(x.v) == self.var(Var::Local(l)))
                };
                if let (Some(aop), Some(x), Some(y), Some(range)) = (arith, la, lb, range)
                    && !own(x)
                    && !own(y)
                {
                    let safe = self.cannot_overflow(st, aop, x, y, range);
                    self.kill(st, l);
                    st.ovf.insert(
                        l,
                        Ovf {
                            op: aop,
                            a: x,
                            b: y,
                            safe,
                        },
                    );
                    return true;
                }
                self.kill(st, l);
            }
            Rvalue::UnaryOp(UnOp::Not, op) => {
                let c = match op {
                    Operand::Copy(p) | Operand::Move(p) => {
                        p.as_local().and_then(|c| st.cond.get(&c).copied())
                    }
                    _ => None,
                };
                let is_bool = op.ty(&self.body.local_decls, self.tcx).is_bool();
                self.kill(st, l);
                if let Some(c) = c
                    && is_bool
                {
                    st.cond.insert(l, c.negate());
                }
            }
            Rvalue::UnaryOp(UnOp::PtrMetadata, op) => match self.len_of(st, op) {
                Some(v) => self.set(st, l, Lin { v, c: 0 }),
                None => self.kill(st, l),
            },
            Rvalue::Ref(_, kind, p) => {
                // `q = &(*p)`, `&mut (*p)`: same metadata as `p`.
                let base = self.deref_base(st, p);
                // `b = &mut r` of a `Range` borrowed only by `next`.
                let range = (matches!(kind, mir::BorrowKind::Mut { .. })
                    && p.projection.is_empty()
                    && self.range_vars(p.local).is_some())
                .then_some(p.local);
                // `q = &(*p).f…` of a shared reference `p` to a `Freeze` type.
                let refd = match (kind, path_of(p)) {
                    (mir::BorrowKind::Shared, Some((b, fs))) => match st.refs.get(&b) {
                        Some((b0, f0)) => f0.concat(&fs).map(|f| (*b0, f)),
                        None => self.shared.contains(&b).then_some((b, fs)),
                    },
                    _ => None,
                };
                self.kill(st, l);
                self.link_slice(st, l, base);
                if let Some(r) = range
                    && r != l
                {
                    st.borrow.insert(l, r);
                }
                if let Some((b, fs)) = refd
                    && b != l
                {
                    st.refs.insert(l, (b, fs));
                }
            }
            Rvalue::RawPtr(_, p) => {
                // `q = &raw const (*p)`: same metadata as `p`.
                let base = self.deref_base(st, p);
                self.kill(st, l);
                self.link_slice(st, l, base);
            }
            Rvalue::Aggregate(kind, ops) => {
                // `r = Range { start: a, end: b }`.
                let fields = match &**kind {
                    mir::AggregateKind::Adt(def_id, ..)
                        if self.tcx.is_lang_item(*def_id, LangItem::Range) && ops.len() == 2 =>
                    {
                        let mut it = ops.iter();
                        match (it.next(), it.next()) {
                            (Some(a), Some(b)) => self.lin(st, a).zip(self.lin(st, b)),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                // `p = *const [T] from (data, meta)`: the metadata is `meta`.
                let meta = match &**kind {
                    mir::AggregateKind::RawPtr(..) => {
                        ops.iter().nth(1).and_then(|m| self.lin(st, m))
                    }
                    _ => None,
                };
                // `t = (a, b, ..)`: the slice pointer fields keep their metadata.
                let tuple: Vec<(u32, Lin)> = match &**kind {
                    mir::AggregateKind::Tuple => ops
                        .iter()
                        .enumerate()
                        .filter_map(|(k, op)| {
                            let v = self.len_of(st, op)?;
                            Some((u32::try_from(k).ok()?, Lin { v, c: 0 }))
                        })
                        .collect(),
                    _ => Vec::new(),
                };
                self.kill(st, l);
                if let (Some((a, b)), Some((s, e))) = (fields, self.range_vars(l))
                    && !self.mentions_local(a, l)
                    && !self.mentions_local(b, l)
                {
                    self.equate(st, s, a);
                    self.equate(st, e, b);
                }
                if let (Some(m), Some(me)) = (meta, self.var(Var::Len(l)))
                    && !self.mentions_local(m, l)
                {
                    self.equate(st, me, m);
                }
                for (k, x) in tuple {
                    if let Some(me) = self.var(Var::FieldLen(l, k))
                        && !self.mentions_local(x, l)
                    {
                        self.equate(st, me, x);
                    }
                }
            }
            Rvalue::Discriminant(p) => {
                let o = p
                    .as_local()
                    .filter(|o| *o != l && self.var(Var::SomeVal(*o)).is_some());
                self.kill(st, l);
                if let Some(o) = o {
                    st.disc.insert(l, o);
                }
            }
            _ => self.kill(st, l),
        }
        true
    }

    /// `l` now has the metadata of the slice local `base` (`l = &(*base)`, ..).
    fn link_slice(&self, st: &mut State, l: Local, base: Option<Local>) {
        if let Some(b) = base
            && b != l
        {
            st.slice.insert(l, b);
            if let (Some(me), Some(v)) = (self.var(Var::Len(l)), self.var(Var::Len(b))) {
                self.equate(st, me, Lin { v, c: 0 });
            }
        }
    }

    /// The slice local whose metadata `&(*p)` has.
    fn deref_base(&self, st: &State, p: &Place<'tcx>) -> Option<Local> {
        match p.projection.as_slice() {
            [ProjectionElem::Deref] => {
                let b = st.slice.get(&p.local).copied().unwrap_or(p.local);
                self.var(Var::Len(b)).map(|_| b)
            }
            _ => None,
        }
    }

    /// `(start, end)` indices of a tracked `Range` local.
    fn range_vars(&self, r: Local) -> Option<(usize, usize)> {
        self.var(Var::RangeStart(r)).zip(self.var(Var::RangeEnd(r)))
    }

    /// `x` is a value of local `l` (any of its tracked parts).
    fn mentions_local(&self, x: Lin, l: Local) -> bool {
        x.v != 0 && self.of_local.get(&l).is_some_and(|vs| vs.contains(&x.v))
    }

    /// Adds `v = x`.
    fn equate(&self, st: &mut State, v: usize, x: Lin) {
        let me = Lin { v, c: 0 };
        if self.add_le(st, me, x, 0) {
            self.add_le(st, x, me, 0);
        }
    }

    /// The comparison an `Assert`/`SwitchInt` operand stands for: a boolean local with
    /// a recorded comparison, or the overflow flag `t.1` of a checked operation
    /// (`Err(t)`).
    fn cond_of(&self, st: &State, op: &Operand<'tcx>) -> Option<Result<Cmp, Local>> {
        let (Operand::Copy(p) | Operand::Move(p)) = op else {
            return None;
        };
        if let Some(l) = p.as_local() {
            return st.cond.get(&l).copied().map(Ok);
        }
        if let [ProjectionElem::Field(f, _)] = p.projection.as_slice()
            && f.as_usize() == 1
            && st.ovf.contains_key(&p.local)
        {
            return Some(Err(p.local));
        }
        None
    }

    /// The value of `op` in `st` if decided.
    fn decide_operand(&self, st: &State, op: &Operand<'tcx>) -> Option<bool> {
        match self.cond_of(st, op)? {
            Ok(c) => self.decide(st, c),
            Err(t) => st.ovf.get(&t).and_then(|o| o.safe.then_some(false)),
        }
    }

    /// Restricts `st` to `op == value`; `false` if infeasible.
    fn assume_operand(&self, st: &mut State, op: &Operand<'tcx>, value: bool) -> bool {
        match self.cond_of(st, op) {
            Some(Ok(c)) => self.assume(st, if value { c } else { c.negate() }),
            Some(Err(t)) => {
                if value {
                    // Overflow happened: nothing to add.
                    return true;
                }
                match st.ovf.get(&t).copied() {
                    Some(o) => self.define_result(st, t, o),
                    None => true,
                }
            }
            None => true,
        }
    }

    /// Successor states of a block whose statements led to `st`.
    fn successors(
        &self,
        st: &State,
        bb: BasicBlock,
        term: &mir::Terminator<'tcx>,
    ) -> Vec<(BasicBlock, Option<State>)> {
        let mut out = Vec::new();
        let feasible = |s: State, ok: bool| ok.then_some(s);
        match &term.kind {
            TerminatorKind::SwitchInt { discr, targets } => {
                if let Some(edges) = self.option_switch(st, discr, targets) {
                    return edges;
                }
                let ty = discr.ty(&self.body.local_decls, self.tcx);
                for (value, bb) in targets.iter() {
                    let mut s = st.clone();
                    let ok = if ty.is_bool() {
                        self.assume_operand(&mut s, discr, value != 0)
                    } else {
                        self.assume_int(&mut s, discr, |x, s| {
                            let k = i128::try_from(value).ok()?;
                            Some(self.assume(
                                s,
                                Cmp {
                                    op: CmpOp::Eq,
                                    a: x,
                                    b: Lin { v: 0, c: k },
                                },
                            ))
                        })
                    };
                    out.push((bb, feasible(s, ok)));
                }
                let mut s = st.clone();
                let values: Vec<u128> = targets.iter().map(|(v, _)| v).collect();
                let ok = if ty.is_bool() {
                    match values.as_slice() {
                        [0] => self.assume_operand(&mut s, discr, true),
                        [1] => self.assume_operand(&mut s, discr, false),
                        [_, _] => false,
                        _ => true,
                    }
                } else {
                    self.assume_int(&mut s, discr, |x, s| {
                        let mut ok = true;
                        for v in &values {
                            let k = i128::try_from(*v).ok()?;
                            ok &= self.assume(
                                s,
                                Cmp {
                                    op: CmpOp::Ne,
                                    a: x,
                                    b: Lin { v: 0, c: k },
                                },
                            );
                        }
                        Some(ok)
                    })
                };
                out.push((targets.otherwise(), feasible(s, ok)));
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let mut s = st.clone();
                let ok = self.assume_operand(&mut s, cond, *expected);
                out.push((*target, feasible(s, ok)));
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                if let Some(t) = target {
                    let mut s = st.clone();
                    let ok = self.call(&mut s, bb, func, args, destination);
                    out.push((*t, ok.then_some(s)));
                }
            }
            TerminatorKind::InlineAsm { .. } => {
                for bb in term.successors() {
                    if self.body.basic_blocks[bb].is_cleanup {
                        continue;
                    }
                    let mut s = st.clone();
                    self.reset(&mut s);
                    out.push((bb, Some(s)));
                }
            }
            _ => {
                for bb in term.successors() {
                    if self.body.basic_blocks[bb].is_cleanup {
                        continue;
                    }
                    out.push((bb, Some(st.clone())));
                }
            }
        }
        out
    }

    /// Edges of a `SwitchInt` on `discriminant(o)` where `o` came from
    /// `<Range<_> as Iterator>::next`: the `Some` edge gets the `Some` facts, the
    /// `None` edge the `None` facts.
    fn option_switch(
        &self,
        st: &State,
        discr: &Operand<'tcx>,
        targets: &mir::SwitchTargets,
    ) -> Option<Vec<(BasicBlock, Option<State>)>> {
        let (Operand::Copy(p) | Operand::Move(p)) = discr else {
            return None;
        };
        let o = *st.disc.get(&p.as_local()?)?;
        let facts = *st.opt.get(&o)?;
        let (some, none) = self.some_none?;
        let apply = |cmps: &[Cmp]| {
            let mut s = st.clone();
            let ok = cmps.iter().all(|c| self.assume(&mut s, *c));
            ok.then_some(s)
        };
        let mut out = Vec::new();
        let mut listed = (false, false);
        for (value, bb) in targets.iter() {
            let s = if value == some {
                listed.0 = true;
                apply(&facts.some)
            } else if value == none {
                listed.1 = true;
                apply(&facts.none)
            } else {
                // No variant has this discriminant.
                None
            };
            out.push((bb, s));
        }
        let otherwise = match listed {
            (true, true) => None,
            (true, false) => apply(&facts.none),
            (false, true) => apply(&facts.some),
            (false, false) => Some(st.clone()),
        };
        out.push((targets.otherwise(), otherwise));
        Some(out)
    }

    /// The return edge of a call: the two `Range` calls of a `for` loop are
    /// modelled; a callee with a return summary relates the destination to the
    /// arguments; otherwise the destination is forgotten. `false` if the call cannot
    /// return in `st`.
    fn call(
        &self,
        st: &mut State,
        bb: BasicBlock,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
    ) -> bool {
        let tcx = self.tcx;
        let arg = match args {
            [a] => match &a.node {
                Operand::Copy(p) | Operand::Move(p) => p.as_local(),
                Operand::Constant(_) => None,
                _ => None,
            },
            _ => None,
        };
        let dest = destination.as_local();
        // `d = <Range<_> as IntoIterator>::into_iter(r)`: `d = r`.
        if let (Some(src), Some(d)) = (arg, dest)
            && src != d
            && is_range_call(tcx, self.body, func, LangItem::IntoIterIntoIter)
            && let Some((s, e)) = self.range_vars(src)
            && self.range_vars(d).is_some()
        {
            self.kill(st, d);
            if let Some((s2, e2)) = self.range_vars(d) {
                self.equate(st, s2, Lin { v: s, c: 0 });
                self.equate(st, e2, Lin { v: e, c: 0 });
            }
            return true;
        }
        // `d = <Range<_> as Iterator>::next(&mut r)`: `Some(start)` and `start += 1`
        // if `start < end`, else `None`; `end` is unchanged.
        if let (Some(b), Some(d)) = (arg, dest)
            && is_range_call(tcx, self.body, func, LangItem::IteratorNext)
            && let Some(&r) = st.borrow.get(&b)
            && r != d
            && let Some((s, e)) = self.range_vars(r)
            && let (Some(val), Some(old)) = (self.var(Var::SomeVal(d)), self.var(Var::NextOld(d)))
        {
            self.kill(st, d);
            st.borrow.remove(&b);
            self.equate(st, old, Lin { v: s, c: 0 });
            // `start` grows by 0 or 1: its upper bounds grow by 1, lower ones stay.
            self.invalidate(st, s);
            let n = st.d.n;
            for j in 0..n {
                if j != s {
                    st.d.m[s * n + j] = add(st.d.m[s * n + j], 1);
                }
            }
            st.d.constrain(s, 0, self.bounds[s].1);
            let lin = |v: usize, c: i128| Lin { v, c };
            let cmp = |op: CmpOp, a: Lin, b: Lin| Cmp { op, a, b };
            st.opt.insert(
                d,
                OptFacts {
                    some: [
                        cmp(CmpOp::Eq, lin(val, 0), lin(old, 0)),
                        cmp(CmpOp::Lt, lin(val, 0), lin(e, 0)),
                        cmp(CmpOp::Eq, lin(s, 0), lin(old, 1)),
                    ],
                    none: [
                        cmp(CmpOp::Le, lin(e, 0), lin(old, 0)),
                        cmp(CmpOp::Eq, lin(s, 0), lin(old, 0)),
                    ],
                },
            );
            return true;
        }
        if let Some(s) = self.calls.get(&bb) {
            return self.apply_summary(st, s, args, destination);
        }
        if !destination.is_indirect_first_projection() {
            self.kill(st, destination.local);
        }
        true
    }

    /// The value of the callee's interface value `sv` at the call site (arguments
    /// only), read before the call.
    fn arg_value(
        &self,
        st: &State,
        sv: SVar,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
    ) -> Option<Lin> {
        let op = |i: u32| args.get(usize::try_from(i).ok()?).map(|a| &a.node);
        let via_ref = |i: u32, fs: Fields, len: bool| {
            let (Operand::Copy(p) | Operand::Move(p)) = op(i)? else {
                return None;
            };
            self.path_var(st, p.as_local()?, fs, len)
                .map(|v| Lin { v, c: 0 })
        };
        match sv {
            SVar::Zero => Some(Lin { v: 0, c: 0 }),
            SVar::Arg(i) => self.lin(st, op(i)?),
            SVar::ArgLen(i) => self.len_of(st, op(i)?).map(|v| Lin { v, c: 0 }),
            SVar::ArgPath(i, fs) => via_ref(i, fs, false),
            SVar::ArgPathLen(i, fs) => via_ref(i, fs, true),
            SVar::Ret | SVar::RetLen | SVar::RetFieldLen(_) => None,
        }
    }

    /// The return edge of a call with summary `s`: the destination gets the facts
    /// of the summary over the argument values. `false` if the callee cannot return
    /// (or not with these arguments).
    fn apply_summary(
        &self,
        st: &mut State,
        s: &RetSummary,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
    ) -> bool {
        let dest = destination.as_local();
        let mut values: HashMap<SVar, Lin> = HashMap::new();
        for sv in s.svars() {
            if let Some(x) = self.arg_value(st, sv, args)
                && dest.is_none_or(|d| !self.mentions_local(x, d))
            {
                values.insert(sv, x);
            }
        }
        if !destination.is_indirect_first_projection() {
            self.kill(st, destination.local);
        }
        if s.never_returns {
            return false;
        }
        if let Some(d) = dest {
            let ret = |v: Var| self.var(v).map(|v| Lin { v, c: 0 });
            if let Some(x) = ret(Var::Local(d)) {
                values.insert(SVar::Ret, x);
            }
            if let Some(x) = ret(Var::Len(d)) {
                values.insert(SVar::RetLen, x);
            }
            for sv in s.svars() {
                if let SVar::RetFieldLen(k) = sv
                    && let Some(x) = ret(Var::FieldLen(d, k))
                {
                    values.insert(sv, x);
                }
            }
        }
        for f in &s.facts {
            if let (Some(a), Some(b)) = (values.get(&f.a), values.get(&f.b))
                && !self.add_le(st, *a, *b, f.c)
            {
                return false;
            }
        }
        if let (Some(d), Some((op, a, ka, b, kb))) = (dest, s.cond)
            && let (Some(x), Some(y)) = (values.get(&a), values.get(&b))
        {
            st.cond.insert(
                d,
                Cmp {
                    op,
                    a: Lin {
                        v: x.v,
                        c: x.c + ka,
                    },
                    b: Lin {
                        v: y.v,
                        c: y.c + kb,
                    },
                },
            );
        }
        true
    }

    /// Applies `f` to the tracked value of the integer operand `op`, if any (the
    /// discriminant of a `SwitchInt` on an integer). Unsigned values only: the switch
    /// compares the bits.
    fn assume_int(
        &self,
        st: &mut State,
        op: &Operand<'tcx>,
        f: impl FnOnce(Lin, &mut State) -> Option<bool>,
    ) -> bool {
        let ty = op.ty(&self.body.local_decls, self.tcx);
        if !ty.is_integral() || ty.is_signed() {
            return true;
        }
        match self.lin(st, op) {
            Some(x) => f(x, st).unwrap_or(true),
            None => true,
        }
    }

    /// State at the end of `bb`'s statements, from its entry state.
    fn through(&self, entry: &State, bb: BasicBlock) -> Option<State> {
        let mut st = entry.clone();
        for s in &self.body.basic_blocks[bb].statements {
            if !self.statement(&mut st, s) {
                return None;
            }
        }
        Some(st)
    }

    fn run(&self, n_blocks: usize) -> Outcome {
        let body = self.body;
        let rpo: Vec<BasicBlock> = body
            .basic_blocks
            .reverse_postorder()
            .iter()
            .copied()
            .filter(|bb| !body.basic_blocks[*bb].is_cleanup)
            .collect();
        let mut order = vec![usize::MAX; n_blocks];
        for (k, bb) in rpo.iter().enumerate() {
            order[bb.as_usize()] = k;
        }
        // Loop heads: targets of an edge that does not go forward in RPO.
        let mut head = vec![false; n_blocks];
        for bb in &rpo {
            for s in body.basic_blocks[*bb].terminator().successors() {
                if order[s.as_usize()] != usize::MAX && order[s.as_usize()] <= order[bb.as_usize()]
                {
                    head[s.as_usize()] = true;
                }
            }
        }
        let mut entry: Vec<Option<State>> = vec![None; n_blocks];
        // Joins of closed matrices are closed; only widened ones need closing.
        let mut closed = vec![true; n_blocks];
        let mut visits = vec![0u32; n_blocks];
        let Some(&start) = rpo.first() else {
            return Outcome {
                proved: Proved::default(),
                returns: None,
            };
        };
        entry[start.as_usize()] = Some(self.entry());
        let mut work: BTreeSet<usize> = BTreeSet::from([0]);
        // Safety net against non-termination: give up (prove nothing).
        let mut budget = 200 * rpo.len() + 1000;
        while let Some(k) = work.pop_first() {
            if budget == 0 {
                return Outcome {
                    proved: Proved::default(),
                    returns: None,
                };
            }
            budget -= 1;
            let bb = rpo[k];
            let Some(mut in_state) = entry[bb.as_usize()].clone() else {
                continue;
            };
            if !closed[bb.as_usize()] && !in_state.d.close() {
                continue;
            }
            let Some(out) = self.through(&in_state, bb) else {
                continue;
            };
            for (succ, s) in self.successors(&out, bb, body.basic_blocks[bb].terminator()) {
                let Some(s) = s else {
                    continue;
                };
                let i = succ.as_usize();
                if order[i] == usize::MAX {
                    continue;
                }
                let (new, new_closed) = match &entry[i] {
                    None => (s, true),
                    Some(old) => {
                        visits[i] += 1;
                        let joined = old.join(&s);
                        if head[i] && visits[i] > 2 {
                            (old.widen(&joined), false)
                        } else {
                            (joined, closed[i])
                        }
                    }
                };
                if entry[i].as_ref() != Some(&new) {
                    entry[i] = Some(new);
                    closed[i] = new_closed;
                    work.insert(order[i]);
                }
            }
        }
        let mut asserts = vec![false; n_blocks];
        let mut dead = vec![false; n_blocks];
        let mut returns = Vec::new();
        for bb in &rpo {
            let b = bb.as_usize();
            // The state at the terminator; `None` if no feasible path reaches it.
            let at_terminator = match entry[b].clone() {
                None => None,
                Some(mut in_state) => {
                    if !closed[b] && !in_state.d.close() {
                        None
                    } else {
                        self.through(&in_state, *bb)
                    }
                }
            };
            let Some(st) = at_terminator else {
                dead[b] = true;
                asserts[b] = matches!(
                    body.basic_blocks[*bb].terminator().kind,
                    TerminatorKind::Assert { .. }
                );
                continue;
            };
            match &body.basic_blocks[*bb].terminator().kind {
                TerminatorKind::Assert { cond, expected, .. } => {
                    asserts[b] = self.decide_operand(&st, cond) == Some(*expected);
                }
                TerminatorKind::Return => returns.push(st),
                _ => {}
            }
        }
        Outcome {
            proved: Proved { asserts, dead },
            returns: Some(returns),
        }
    }

    /// The interface values tracked in this body, for a summary: the return value
    /// and the values of the parameters that the body never changes.
    fn interface(&self) -> Vec<(SVar, usize)> {
        let mut out = vec![(SVar::Zero, 0)];
        let changed = changed_locals(self.body);
        for (v, &i) in &self.index {
            let sv = match *v {
                Var::Local(l) if l == mir::RETURN_PLACE => SVar::Ret,
                Var::Len(l) if l == mir::RETURN_PLACE => SVar::RetLen,
                Var::FieldLen(l, k) if l == mir::RETURN_PLACE => SVar::RetFieldLen(k),
                Var::Local(l) | Var::Len(l) | Var::Path(l, _) | Var::PathLen(l, _)
                    if l != mir::RETURN_PLACE
                        && l.as_usize() <= self.body.arg_count
                        && !changed.contains(&l) =>
                {
                    let Ok(a) = u32::try_from(l.as_usize() - 1) else {
                        continue;
                    };
                    match *v {
                        Var::Local(_) => SVar::Arg(a),
                        Var::Len(_) => SVar::ArgLen(a),
                        Var::Path(_, fs) => SVar::ArgPath(a, fs),
                        Var::PathLen(_, fs) => SVar::ArgPathLen(a, fs),
                        _ => continue,
                    }
                }
                _ => continue,
            };
            out.push((sv, i));
        }
        out.sort();
        out
    }

    /// `x` in terms of an interface value (itself, or one it equals plus a constant).
    fn express(&self, st: &State, x: Lin, iface: &[(SVar, usize)]) -> Option<(SVar, i128)> {
        if let Some((sv, _)) = iface.iter().find(|(_, i)| *i == x.v) {
            return Some((*sv, x.c));
        }
        iface.iter().find_map(|(sv, u)| {
            let k = st.d.get(x.v, *u);
            (k < INF && k == -st.d.get(*u, x.v)).then_some((*sv, x.c + k))
        })
    }

    /// The return summary from the states at the reachable `return`s.
    fn summary(&self, returns: Vec<State>) -> Option<RetSummary> {
        let iface = self.interface();
        let Some(first) = returns.first() else {
            return Some(RetSummary {
                never_returns: true,
                ..RetSummary::default()
            });
        };
        let joined = returns.iter().skip(1).fold(first.clone(), |a, b| a.join(b));
        let mut facts = Vec::new();
        for (sa, a) in &iface {
            for (sb, b) in &iface {
                let c = joined.d.get(*a, *b);
                if a != b && c < INF {
                    facts.push(Fact { a: *sa, b: *sb, c });
                }
            }
        }
        let mut cond = None;
        for (k, st) in returns.iter().enumerate() {
            let c = st.cond.get(&mir::RETURN_PLACE).and_then(|c| {
                let (a, ka) = self.express(st, c.a, &iface)?;
                let (b, kb) = self.express(st, c.b, &iface)?;
                Some((c.op, a, ka, b, kb))
            });
            if k == 0 {
                cond = c;
            } else if cond != c {
                cond = None;
            }
            if cond.is_none() {
                break;
            }
        }
        if facts.is_empty() && cond.is_none() {
            return None;
        }
        Some(RetSummary {
            facts,
            cond,
            never_returns: false,
        })
    }
}

impl RetSummary {
    /// Every interface value the summary mentions.
    fn svars(&self) -> Vec<SVar> {
        let mut v: Vec<SVar> = self.facts.iter().flat_map(|f| [f.a, f.b]).collect();
        if let Some((_, a, _, b, _)) = self.cond {
            v.push(a);
            v.push(b);
        }
        v.sort();
        v.dedup();
        v
    }
}

/// Locals that the body may change after entry: assigned (also partly, but not
/// through a dereference), borrowed mutably or by raw pointer, or used by inline
/// assembly. A parameter not in this set holds its entry value throughout.
fn changed_locals(body: &Body<'_>) -> HashSet<Local> {
    struct Changed(HashSet<Local>);
    impl<'tcx> Visitor<'tcx> for Changed {
        fn visit_place(&mut self, p: &Place<'tcx>, ctxt: PlaceContext, _: mir::Location) {
            let changes =
                matches!(ctxt, PlaceContext::MutatingUse(_)) && !p.is_indirect_first_projection();
            if changes {
                self.0.insert(p.local);
            }
        }
    }
    let mut c = Changed(HashSet::new());
    c.visit_body(body);
    c.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closure_and_entailment() {
        // v1 - v2 ≤ -1 (v1 < v2), v2 - 0 ≤ 10: v1 ≤ 9.
        let mut d = Dbm::top(3);
        assert!(d.constrain(1, 2, -1));
        assert!(d.constrain(2, 0, 10));
        assert_eq!(d.get(1, 0), 9);
        // v2 - v1 ≤ 0 contradicts v1 < v2.
        let mut e = d.clone();
        assert!(!e.constrain(2, 1, 0));
        // Forgetting v2 keeps the implied bound on v1.
        d.forget(2);
        assert_eq!(d.get(1, 0), 9);
        assert_eq!(d.get(1, 2), INF);
    }

    #[test]
    fn join_and_widening() {
        let mut a = Dbm::top(2);
        assert!(a.constrain(1, 0, 0));
        let mut b = Dbm::top(2);
        assert!(b.constrain(1, 0, 1));
        let j = a.join(&b);
        assert_eq!(j.get(1, 0), 1);
        // A bound that grows is dropped; a stable one is kept.
        let w = a.widen(&j);
        assert_eq!(w.get(1, 0), INF);
        let w = j.widen(&a);
        assert_eq!(w.get(1, 0), 1);
        let mut f = Dbm::top(3);
        assert!(f.constrain(1, 2, 0));
        assert!(f.constrain(2, 1, 0));
        assert!(f.close());
        assert_eq!(f.get(1, 2), 0);
    }

    #[test]
    fn access_path_fields() {
        let a = Fields::new(&[0, 1]).unwrap();
        let b = Fields::new(&[2]).unwrap();
        assert_eq!(a.concat(&b).unwrap().as_slice(), &[0, 1, 2]);
        assert_eq!(Fields::EMPTY.concat(&b), Some(b));
        // Longer than `MAX_PATH`: not a tracked path.
        assert!(a.concat(&a).unwrap().concat(&b).is_none());
        assert!(Fields::new(&[0; MAX_PATH + 1]).is_none());
    }

    #[test]
    fn comparison_rewritten_through_equal_value() {
        // c: v1 < v2 + 3; with v1 = v3 - 2, forgetting v1 gives v3 - 2 < v2 + 3.
        let c = Cmp {
            op: CmpOp::Lt,
            a: Lin { v: 1, c: 0 },
            b: Lin { v: 2, c: 3 },
        };
        let r = c.rewrite(1, 3, -2);
        assert_eq!(r.a, Lin { v: 3, c: -2 });
        assert_eq!(r.b, Lin { v: 2, c: 3 });
        assert!(!r.mentions(1));
    }

    #[test]
    fn saturating_bounds() {
        assert_eq!(add(INF, -5), INF);
        assert_eq!(add(3, 4), 7);
        assert_eq!(add(-INF, -INF), -INF);
    }
}
