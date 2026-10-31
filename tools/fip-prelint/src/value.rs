// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Intraprocedural value analysis of one MIR body, used to drop `Assert`
//! terminators that cannot fire (bounds, overflow, division and negation checks
//! behind guards).
//!
//! **Domain.** Difference bounds (`x - y ≤ c`, a zone) over mathematical integers
//! between tracked values: integer locals, the length `len(p)` of the slice behind a
//! slice pointer local `p` (its metadata), the result `t.0` of a checked operation
//! `t = AddWithOverflow(a, b)`, `start`/`end` of a `Range<integer>` local, the
//! payload of an `Option<integer>` local, and the constant 0. Only locals connected
//! to some `Assert` condition through assignments are tracked. Every tracked value
//! carries the bounds of its type (`len(p)` lies in `0..=usize::MAX`). Besides the
//! matrix, the state records which boolean locals hold which comparison
//! (`c = Lt(a, b)`), which tuple locals hold which checked operation together with
//! the verdict "cannot overflow" computed when the operation ran, and which pointer
//! locals share the metadata of which slice local (`q = &(*p)`).
//!
//! **Transfer.** Copies and casts that preserve the value are equalities; constants
//! fix a value; `PtrMetadata` of a slice pointer is its `len`; a `SwitchInt` on a
//! recorded comparison adds the comparison (or its negation) on each edge, and an
//! infeasible edge is dropped; the success edge of an `Assert` adds the checked
//! condition (and, for a checked operation, `t.0 = a op b`). A `for` loop over
//! `a..b` is modelled from the contract of `Range<integer>`: `into_iter` is the
//! identity, `next(&mut r)` returns `Some(r.start)` and increments `start` if
//! `start < end`, else `None`, and never changes `end`. Any other assignment, a
//! call's destination, `StorageLive`/`StorageDead` and partial writes forget the
//! local. Writes through pointers cannot change a tracked local: locals whose
//! address is taken (`&mut x`, `&raw x`, also of a field; `&x` too unless the place
//! has no interior mutability, since writing through a shared reference to such a
//! place is undefined behaviour) are never tracked, except a `Range` whose only
//! borrows are passed directly to `next`. Slice lengths never change while the
//! pointer local is unchanged. Cleanup (unwind) edges are not followed. Joins take
//! the weaker bound; at loop heads, after two visits, bounds that grew are dropped
//! (widening), so the fixpoint terminates.
//!
//! **Use.** An `Assert` whose condition is decided equal to `expected` in the state
//! reaching it, or whose block no feasible path reaches, cannot fire. Anything not
//! modelled keeps the assert: unknown rvalues, other calls, signed division overflow
//! (`BitAnd` of two comparisons), 128-bit arithmetic, bodies with more than
//! [`MAX_VARS`] tracked values or [`MAX_CELLS`] matrix entries, coroutines; inline
//! assembly resets the state.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use rustc_hir::attrs::lang_items::LangItem;
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    self, BasicBlock, BinOp, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind, UnOp,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TypingEnv};

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
    /// Type bounds per index.
    bounds: Vec<(i128, i128)>,
    /// Discriminant values of `Option::Some` and `Option::None`.
    some_none: Option<(u128, u128)>,
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

/// For each basic block, `true` if its terminator is an `Assert` that cannot fire.
/// Empty (nothing proved) if the body is not analysed.
pub fn asserts_that_cannot_fire<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    body: &Body<'tcx>,
) -> Vec<bool> {
    let n_blocks = body.basic_blocks.len();
    let has_assert = body
        .basic_blocks
        .iter()
        .any(|d| !d.is_cleanup && matches!(d.terminator().kind, TerminatorKind::Assert { .. }));
    if !has_assert
        || body.coroutine.is_some()
        || body
            .basic_blocks
            .iter()
            .any(|d| matches!(d.terminator().kind, TerminatorKind::Yield { .. }))
    {
        return Vec::new();
    }
    let taken = address_taken(tcx, env, body);
    let relevant = relevant_locals(tcx, body);
    let mut index = HashMap::new();
    let mut bounds = vec![(0, 0)];
    let usize_max = int_range(tcx, tcx.types.usize).map_or(INF, |r| r.1);
    let mut push = |v: Var, r: (i128, i128)| {
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
        } else if let Some(r) = range_int(tcx, decl.ty).and_then(|t| int_range(tcx, t)) {
            push(Var::RangeStart(local), r);
            push(Var::RangeEnd(local), r);
        } else if let Some(r) = option_int(tcx, decl.ty).and_then(|t| int_range(tcx, t)) {
            push(Var::SomeVal(local), r);
            push(Var::NextOld(local), r);
        }
    }
    let n = bounds.len();
    if n > MAX_VARS || n_blocks.saturating_mul(n * n) > MAX_CELLS {
        return Vec::new();
    }
    let cx = Ctx {
        tcx,
        env,
        body,
        index,
        bounds,
        some_none: option_discriminants(tcx),
    };
    cx.run(n_blocks)
}

/// Locals connected to an `Assert` condition through assignments (copies, casts,
/// operations, comparisons, borrows, discriminants, the two `Range` calls of a
/// `for` loop): only these are tracked. The others cannot constrain a checked
/// value, so leaving them untracked loses nothing the analysis could use.
fn relevant_locals<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
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
    for data in body.basic_blocks.iter() {
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
                Rvalue::Ref(_, _, p) | Rvalue::RawPtr(_, p) | Rvalue::Discriminant(p) => {
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
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } if is_range_call(tcx, body, func, LangItem::IteratorNext)
                || is_range_call(tcx, body, func, LangItem::IntoIterIntoIter) =>
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
        }
    }

    fn var(&self, v: Var) -> Option<usize> {
        self.index.get(&v).copied()
    }

    /// Drops the recorded comparisons, operations and `next` facts that mention `v`.
    fn invalidate(&self, st: &mut State, v: usize) {
        st.cond.retain(|_, c| !c.mentions(v));
        st.ovf
            .retain(|_, o| !(o.a.v == v && v != 0) && !(o.b.v == v && v != 0));
        st.opt.retain(|_, f| !f.mentions(v));
    }

    /// Forgets `v` and restores its type bounds.
    fn forget_var(&self, st: &mut State, v: usize) {
        st.d.forget(v);
        let (lo, hi) = self.bounds[v];
        st.d.constrain(v, 0, hi);
        if lo > -INF {
            st.d.constrain(0, v, -lo);
        }
        self.invalidate(st, v);
    }

    /// Forgets everything known about local `l`.
    fn kill(&self, st: &mut State, l: Local) {
        for v in [
            Var::Local(l),
            Var::Len(l),
            Var::Field0(l),
            Var::RangeStart(l),
            Var::RangeEnd(l),
            Var::SomeVal(l),
            Var::NextOld(l),
        ] {
            if let Some(i) = self.var(v) {
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

    fn place_lin(&self, _st: &State, p: &Place<'tcx>) -> Option<Lin> {
        if let Some(l) = p.as_local() {
            return self.var(Var::Local(l)).map(|v| Lin { v, c: 0 });
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
        let Some(r) = self.var(Var::Field0(t)) else {
            return true;
        };
        let res = Lin { v: r, c: 0 };
        let (a, b) = (o.a, o.b);
        match o.op {
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
                (lb <= -INF || self.add_le(st, res, za, a.c - lb))
                    && (ub >= INF || self.add_le(st, za, res, ub - a.c))
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

    fn assign(&self, st: &mut State, l: Local, rv: &Rvalue<'tcx>) -> bool {
        // Read the operands in the state before the assignment.
        match rv {
            Rvalue::Use(op, ..) => {
                if let Some(x) = self.lin(st, op) {
                    self.set(st, l, x);
                    return true;
                }
                let copied = match op {
                    Operand::Copy(p) | Operand::Move(p) => p.as_local(),
                    _ => None,
                };
                let cond = copied.and_then(|c| st.cond.get(&c).copied());
                let base = self.slice_base(st, op);
                let range = copied.filter(|c| *c != l).and_then(|c| self.range_vars(c));
                self.kill(st, l);
                if let Some(c) = cond {
                    st.cond.insert(l, c);
                }
                if let Some(b) = base
                    && b != l
                {
                    st.slice.insert(l, b);
                }
                // `r2 = move r` of a `Range`: same `start` and `end`.
                if let (Some((s, e)), Some((s2, e2))) = (range, self.range_vars(l)) {
                    self.equate(st, s2, Lin { v: s, c: 0 });
                    self.equate(st, e2, Lin { v: e, c: 0 });
                }
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
            Rvalue::UnaryOp(UnOp::PtrMetadata, op) => {
                let base = self.slice_base(st, op);
                match base.and_then(|b| self.var(Var::Len(b))) {
                    Some(v) => self.set(st, l, Lin { v, c: 0 }),
                    None => self.kill(st, l),
                }
            }
            Rvalue::Ref(_, kind, p) => {
                // `q = &(*p)`, `&mut (*p)`: same metadata as `p`.
                let base = self.deref_base(st, p);
                // `b = &mut r` of a `Range` borrowed only by `next`.
                let range = (matches!(kind, mir::BorrowKind::Mut { .. })
                    && p.projection.is_empty()
                    && self.range_vars(p.local).is_some())
                .then_some(p.local);
                self.kill(st, l);
                if let Some(b) = base
                    && b != l
                {
                    st.slice.insert(l, b);
                }
                if let Some(r) = range
                    && r != l
                {
                    st.borrow.insert(l, r);
                }
            }
            Rvalue::RawPtr(_, p) => {
                // `q = &raw const (*p)`: same metadata as `p`.
                let base = self.deref_base(st, p);
                self.kill(st, l);
                if let Some(b) = base
                    && b != l
                {
                    st.slice.insert(l, b);
                }
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
                self.kill(st, l);
                if let (Some((a, b)), Some((s, e))) = (fields, self.range_vars(l))
                    && !self.mentions_local(a, l)
                    && !self.mentions_local(b, l)
                {
                    self.equate(st, s, a);
                    self.equate(st, e, b);
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
        x.v != 0
            && [
                Var::Local(l),
                Var::Len(l),
                Var::Field0(l),
                Var::RangeStart(l),
                Var::RangeEnd(l),
                Var::SomeVal(l),
                Var::NextOld(l),
            ]
            .iter()
            .any(|v| self.var(*v) == Some(x.v))
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
                    self.call(&mut s, func, args, destination);
                    out.push((*t, Some(s)));
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

    /// The return edge of a call: the destination is forgotten, except for the two
    /// `Range` calls of a `for` loop, which are modelled.
    fn call(
        &self,
        st: &mut State,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
    ) {
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
            return;
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
            return;
        }
        if !destination.is_indirect_first_projection() {
            self.kill(st, destination.local);
        }
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

    fn run(&self, n_blocks: usize) -> Vec<bool> {
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
            return Vec::new();
        };
        entry[start.as_usize()] = Some(self.entry());
        let mut work: BTreeSet<usize> = BTreeSet::from([0]);
        // Safety net against non-termination: give up (prove nothing).
        let mut budget = 200 * rpo.len() + 1000;
        while let Some(k) = work.pop_first() {
            if budget == 0 {
                return Vec::new();
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
            for (succ, s) in self.successors(&out, body.basic_blocks[bb].terminator()) {
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
        let mut result = vec![false; n_blocks];
        for bb in &rpo {
            let data = &body.basic_blocks[*bb];
            let TerminatorKind::Assert { cond, expected, .. } = &data.terminator().kind else {
                continue;
            };
            let Some(mut in_state) = entry[bb.as_usize()].clone() else {
                // No feasible path reaches the block.
                result[bb.as_usize()] = true;
                continue;
            };
            if !closed[bb.as_usize()] && !in_state.d.close() {
                result[bb.as_usize()] = true;
                continue;
            }
            match self.through(&in_state, *bb) {
                None => result[bb.as_usize()] = true,
                Some(st) => {
                    result[bb.as_usize()] = self.decide_operand(&st, cond) == Some(*expected);
                }
            }
        }
        result
    }
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
    fn saturating_bounds() {
        assert_eq!(add(INF, -5), INF);
        assert_eq!(add(3, 4), 7);
        assert_eq!(add(-INF, -INF), -INF);
    }
}
