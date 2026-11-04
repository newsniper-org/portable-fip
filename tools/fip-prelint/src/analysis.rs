// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Summaries over MIR: the `fip_testkit::summaries` design (lattice `0..N, ∞, ⊤`,
//! strongly connected components with widening, symbolic parameter terms,
//! witnesses) on resolved MIR instances.
//!
//! **Graph.** Nodes are `Instance`s reachable from one root. The root is analysed
//! with its identity generic arguments in its own typing environment
//! (`TypingEnv::post_analysis(root)`); every callee is resolved with
//! `Instance::try_resolve` after substituting the caller's arguments, so a generic
//! callee called from a monomorphic caller is analysed as that instantiation
//! (closures passed as arguments included). `rustc_public`'s `Instance::resolve`
//! works in a fully monomorphized environment only and cannot do this for generic
//! roots, hence `rustc_middle` here.
//!
//! **Costs.** Per body, the allocation bound is the maximum over control-flow paths
//! of the sum of the costs on the path (cleanup/unwind blocks are skipped: they run
//! only after a panic). A block in a control-flow cycle (a loop) multiplies its cost
//! by `∞`. A call costs the callee's bound; a call of a callable generic parameter
//! (`F: Fn*`/`FipFn`) is the symbolic term `alloc(g)`, a trait method on another
//! generic parameter the term `alloc(<T as Trait>::m)`.
//!
//! **Events.** Allocation and deallocation entry points, `Assert` terminators and panic entry points
//! (panic paths), and everything that cannot be resolved or has no usable MIR
//! (`⊤`, with the reason). Tables: `fip_lint_rules::mir`. An `Assert` that the
//! value analysis of its body ([`crate::value`]) proves unable to fire on every path
//! reaching it is not a panic path. A `Drop` terminator is a call of the type's drop
//! glue, analysed like any callee: a drop frees exactly when its glue reaches a
//! deallocation, a free source or `⊤` (a `RefMut` or a guard without heap does not).
//! Glue of a type mentioning a generic parameter is analysed field by field; only
//! the drop of a bare type parameter is the term `drop(T)`.
//!
//! **Sources** ([`Crates::source_of`]): functions declared `fip::alloc_source`/
//! `fip::free_source` (on themselves or on the trait method they implement), the
//! methods of `GlobalAlloc`/`Allocator` implementations, and foreign C allocation
//! functions. A source is an opaque boundary: checked before any table and before
//! MIR, it is a leaf with exactly its declared events, and its body is never
//! analysed (allocation inside an allocator is outside FIP).
//!
//! **Contexts and preconditions.** A callee whose body can use the caller's state
//! (an `Assert`, a branch on a comparison, or `fip::requires(..)`) is the node
//! `(instance, context)`: the caller's value-analysis state at the call projected
//! onto its parameters ([`crate::value`]), used as the callee's entry state; at most
//! [`MAX_CONTEXT_DEPTH`] nested contexts, and a callee already on the path from the
//! root gets none. A root is analysed under its own `fip::requires(..)`; at every
//! call the context must entail the callee's, else the call is a panic path (and the
//! callee is analysed without it there); a function with a precondition used as a
//! value is a panic path.
//!
//! **Declared parameter bounds at call sites.** A call whose resolved callee carries
//! `fip::mark(.., param(g = K))` passes, for `g`, a value of the callee's generic type
//! parameter `F` (`g: F`, `g: &F`, `g: &mut F`). The argument's bound is the bound of
//! one call of it: the instances of the callable methods of `F`'s bounds
//! (`<T as FipFn<A>>::call`, `<T as Fn*<A>>::call*`) for the actual `T` at the call
//! site, analysed like any callee (a closure body, `Certified<N, C>::call` and the
//! closure inside it, a function item through its `Fn` shim), maximum over them. A
//! `T` that is a generic parameter of the analysed function is the term `alloc(h)`,
//! instantiated by that function's own `param(h = K')`. The call site is a violation
//! when the bound is `⊤` or, without terms left, above `K`. Call sites are taken
//! from every body the analysis of a root explores in an analysed crate (the local
//! crate and crates declaring `fip::export`), with that root's instantiation, and
//! from every local function and closure body with identity arguments
//! ([`Analysis::arguments_in`]), so callers that are not roots are checked too.
//!
//! **Indirect calls.** A call through a function pointer, and a dynamic call, is
//! resolved when the pointer's origin in the body is one reified function or closure,
//! or one unsized concrete type, on every path ([`origin_of`], also through fields of
//! local aggregates), or a function pointer read from a constant or from immutable
//! data ([`Analysis::data_targets`]; several candidates cost their maximum). A
//! parameter declared
//! `param(g = K)` of function-pointer or `&dyn Fn*`/`&dyn FipFn` type counts `K` and
//! what the function's mark allows; its call sites must pass a function known there
//! that meets them. A dynamic call of a trait method whose declaration carries a
//! `fip::mark` costs that contract ([`Crates::contract_of`]); every implementation
//! is checked against it in its own crate (`crate::report`). A contract's
//! `param(g = K)` is inherited by every implementation (by position,
//! [`inherited_params`]), and every call through the contract (dynamic, or on a type
//! parameter) checks its argument for `g` like a call site of a function declaring
//! it. Anything else is `⊤`.
//!
//! **Bindings and std summaries.** A node is also keyed by what its parameters hold,
//! known at its call sites ([`Bind`]): the output behind a `&mut dyn fmt::Write` or a
//! `&mut fmt::Formatter`, the formatting functions of a value containing
//! `fmt::Arguments`, and what a callable argument holds ([`Callable`]: functions, a
//! trait object's concrete type, a declared parameter; up to [`MAX_CALLABLE_DEPTH`]
//! nested callees). They resolve the dynamic calls and formatting-function pointers of
//! `core::fmt`, and the open terms of a standard-library function without MIR taken
//! from the generated std summaries ([`crate::stdsum`], used only when its stamp
//! matches). Generating them (`--std-summaries`), the summarised function's own
//! parameters are bound symbolically and the calls through them become those terms;
//! a foreign call becomes the term `§ffi <symbol> <abi>`, resolved at the use site with
//! the analysed crate's FFI marks ([`Crates::ffi_verdict_std`]).

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use fip_lint_rules::mir as rules;
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_middle::mir::{self, AssertKind, Body, Operand, TerminatorKind};
use rustc_middle::ty::print::{with_no_trimmed_paths, with_no_visible_paths};
use rustc_middle::ty::{
    self, EarlyBinder, GenericArgs, GenericArgsRef, Instance, InstanceKind, ShimKind, Ty, TyCtxt,
    TypeFoldable, TypeVisitableExt, TypingEnv,
};
use rustc_span::Spanned;
use rustc_span::{DUMMY_SP, Span};

use crate::marks::{self, Mark, Source};
use crate::value::{Fact, SVar};

/// Explored instances per root before the rest is `⊤` ("analysis limit").
const MAX_NODES: usize = 20_000;
/// Witnesses kept per category and node.
const MAX_WITNESSES: usize = 16;
const MAX_UNKNOWN: usize = 64;

/// `0, 1, …` or `∞`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum B {
    Fin(u64),
    Inf,
}

impl Default for B {
    fn default() -> Self {
        B::Fin(0)
    }
}

impl B {
    fn add(self, o: B) -> B {
        match (self, o) {
            (B::Fin(a), B::Fin(b)) => B::Fin(a.saturating_add(b)),
            _ => B::Inf,
        }
    }
    fn max(self, o: B) -> B {
        match (self, o) {
            (B::Fin(a), B::Fin(b)) => B::Fin(a.max(b)),
            _ => B::Inf,
        }
    }
    pub fn is_zero(self) -> bool {
        self == B::Fin(0)
    }
    fn widen(self) -> B {
        if self.is_zero() { self } else { B::Inf }
    }
    /// `self · k` with `0 · x = 0`.
    pub fn mul(self, k: B) -> B {
        if self.is_zero() || k.is_zero() {
            return B::Fin(0);
        }
        match (self, k) {
            (B::Fin(a), B::Fin(b)) => B::Fin(a.saturating_mul(b)),
            _ => B::Inf,
        }
    }
    pub fn exceeds(self, n: u64) -> bool {
        match self {
            B::Fin(a) => a > n,
            B::Inf => true,
        }
    }
}

impl std::fmt::Display for B {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            B::Fin(n) => write!(f, "{n}"),
            B::Inf => write!(f, "∞"),
        }
    }
}

/// `c + Σ kᵢ·alloc(gᵢ)`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Cost {
    pub c: B,
    pub terms: BTreeMap<String, B>,
}

impl Cost {
    fn one() -> Cost {
        Cost {
            c: B::Fin(1),
            terms: BTreeMap::new(),
        }
    }
    fn term(k: &str) -> Cost {
        let mut terms = BTreeMap::new();
        terms.insert(k.to_string(), B::Fin(1));
        Cost {
            c: B::Fin(0),
            terms,
        }
    }
    fn add(&self, o: &Cost) -> Cost {
        let mut r = self.clone();
        r.c = r.c.add(o.c);
        for (k, v) in &o.terms {
            let e = r.terms.entry(k.clone()).or_default();
            *e = (*e).add(*v);
        }
        r
    }
    fn max(&self, o: &Cost) -> Cost {
        let mut r = self.clone();
        r.c = r.c.max(o.c);
        for (k, v) in &o.terms {
            let e = r.terms.entry(k.clone()).or_default();
            *e = (*e).max(*v);
        }
        r
    }
    fn widen(&self) -> Cost {
        Cost {
            c: self.c.widen(),
            terms: self
                .terms
                .iter()
                .map(|(k, v)| (k.clone(), v.widen()))
                .collect(),
        }
    }
    fn looped(&self, in_loop: bool) -> Cost {
        if in_loop { self.widen() } else { self.clone() }
    }
    /// Replaces the terms of the parameters in `declared` (`param(g = K)`) by their
    /// declared bound: a call `g(..)` by `K`, dropping a value of `g`'s type `F`
    /// (`drop(F)`, `param_types` maps `g` to `F`) by 0. The argument is checked where
    /// the function is instantiated, as in FP².
    pub fn instantiate(
        &self,
        declared: &[(String, u64)],
        param_types: &[(String, String)],
    ) -> Cost {
        let mut r = Cost {
            c: self.c,
            terms: BTreeMap::new(),
        };
        for (k, v) in &self.terms {
            let found = declared.iter().find_map(|(name, bound)| {
                let ty_name = param_types.iter().find(|(v, _)| v == name).map(|(_, t)| t);
                if name == k {
                    Some(*bound)
                } else if ty_name.is_some_and(|t| *k == format!("drop({t})")) {
                    Some(0)
                } else {
                    None
                }
            });
            match found {
                Some(bound) => r.c = r.c.add(v.mul(B::Fin(bound))),
                None => {
                    if !v.is_zero() {
                        r.terms.insert(k.clone(), *v);
                    }
                }
            }
        }
        r
    }
    pub fn display(&self) -> String {
        let mut parts = Vec::new();
        if !self.c.is_zero() || self.terms.is_empty() {
            parts.push(self.c.to_string());
        }
        for (k, v) in &self.terms {
            match v {
                B::Fin(0) => {}
                B::Fin(1) => parts.push(format!("alloc({k})")),
                v => parts.push(format!("{v}·alloc({k})")),
            }
        }
        parts.join(" + ")
    }
}

/// One call on a witness chain: the callee and the call site in the caller.
#[derive(Clone, Debug)]
pub struct Step {
    pub label: String,
    pub span: Span,
    pub in_loop: bool,
}

/// How an event is reached: calls from the node the summary belongs to, then the
/// event (`what`, at `span` in the last body; `DUMMY_SP` for a whole callee).
#[derive(Clone, Debug)]
pub struct Witness {
    pub steps: Vec<Step>,
    pub what: String,
    pub span: Span,
    pub in_loop: bool,
}

impl Witness {
    fn prefixed(&self, prefix: &[Step]) -> Witness {
        let mut w = self.clone();
        let mut steps = prefix.to_vec();
        steps.extend(w.steps);
        w.steps = steps;
        w
    }
    /// The span of the event in the innermost body that has one.
    pub fn spans(&self) -> Vec<Span> {
        let mut v: Vec<Span> = self.steps.iter().map(|s| s.span).collect();
        v.push(self.span);
        v
    }
}

#[derive(Clone, Debug, Default)]
pub struct Summary {
    pub alloc: Cost,
    pub alloc_w: Vec<Witness>,
    pub free: Vec<Witness>,
    pub panics: Vec<Witness>,
    pub unknown: Vec<Witness>,
    pub recursion: Option<Witness>,
    pub terms_w: BTreeMap<String, Witness>,
    /// The node's own body had panic sites discharged by Verus under the Verus
    /// `requires` of this function (top plan T13.4): a caller that Verus did not verify
    /// gets that precondition as a panic path. Not merged into callers.
    pub verus_pre: Option<String>,
}

fn push_w(list: &mut Vec<Witness>, w: Witness, cap: usize, key: impl Fn(&Witness) -> String) {
    if list.len() >= cap {
        return;
    }
    let k = key(&w);
    if list.iter().any(|x| key(x) == k) {
        return;
    }
    list.push(w);
}

fn key_what(w: &Witness) -> String {
    w.what.clone()
}

/// Same event through the same call site of the summarised body.
fn key_site(w: &Witness) -> String {
    let first = w.steps.first().map_or(w.span, |s| s.span);
    format!("{} @ {:?}", w.what, first)
}

impl Summary {
    /// Adds every event of `o` (reached through `prefix`) to `self`; not the cost.
    fn merge_events(&mut self, o: &Summary, prefix: &[Step]) {
        for w in &o.alloc_w {
            push_w(
                &mut self.alloc_w,
                w.prefixed(prefix),
                MAX_WITNESSES,
                key_site,
            );
        }
        for w in &o.free {
            push_w(&mut self.free, w.prefixed(prefix), MAX_WITNESSES, key_site);
        }
        for w in &o.panics {
            push_w(
                &mut self.panics,
                w.prefixed(prefix),
                MAX_WITNESSES,
                key_site,
            );
        }
        for w in &o.unknown {
            push_w(&mut self.unknown, w.prefixed(prefix), MAX_UNKNOWN, key_what);
        }
        if self.recursion.is_none()
            && let Some(r) = &o.recursion
        {
            self.recursion = Some(r.prefixed(prefix));
        }
        for (k, w) in &o.terms_w {
            self.terms_w
                .entry(k.clone())
                .or_insert_with(|| w.prefixed(prefix));
        }
    }
}

/// An event found in a body or standing for a whole callee.
#[derive(Clone, Debug)]
enum Ev {
    Alloc(String),
    Free(String),
    Panic(String),
    Unknown(String),
    /// A declared bound of `k` allocations: a call through a parameter declared
    /// `param(g = K)` (a function pointer or `&dyn Fn*`), or a dynamic call of a
    /// trait method whose declaration carries a contract (`fip::mark`).
    Bound(u64, String),
    /// Possible recursion declared by a contract (`fbip` allows it).
    Recurse(String),
    /// A panic site discharged by Verus under the `requires` of the named function
    /// (top plan T13.4): no event here, an obligation for its callers.
    VerusPre(String),
}

#[derive(Clone, Debug)]
enum Item {
    Call(usize),
    Term(String),
    Ev(Ev),
    /// Several events of one call: a call through a parameter declared
    /// `param(g = K)`, which may do what the function's own mark allows.
    Evs(Vec<Ev>),
    /// Several callees of one call site (the formatting functions a formatting may
    /// call); only returned by `call_item`, flattened into the block.
    Many(Vec<Item>),
    /// One of several callees: a call through a function pointer loaded from
    /// immutable data holding several candidates (a static table). Costs the maximum
    /// over the alternatives and has the events of every one.
    Alt(Vec<Item>),
}

impl Item {
    /// The nodes this item calls (through alternatives and sequences).
    fn calls(&self) -> Vec<usize> {
        match self {
            Item::Call(j) => vec![*j],
            Item::Many(items) | Item::Alt(items) => items.iter().flat_map(Item::calls).collect(),
            Item::Term(_) | Item::Ev(_) | Item::Evs(_) => Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
struct Site {
    item: Item,
    span: Span,
}

struct BodyInfo {
    blocks: Vec<Vec<Site>>,
    succ: Vec<Vec<usize>>,
    reachable: Vec<bool>,
    in_loop: Vec<bool>,
}

enum NodeKind {
    Pending,
    Leaf(Vec<Ev>),
    Body(BodyInfo),
}

struct Node<'tcx> {
    inst: Instance<'tcx>,
    /// Facts over the parameters that hold on entry: the context of the call sites
    /// that reach this node (the projection of their state), or a root's
    /// `fip::requires`. Empty: any call.
    ctx: Vec<Fact>,
    /// Non-empty contexts on the way from the root (at most [`MAX_CONTEXT_DEPTH`]).
    depth: u8,
    /// What parameters hold, known at the call sites that reach this node (outputs
    /// and formatting functions of a formatting, [`Bind`]). Empty: any call.
    binds: Binds<'tcx>,
    /// The node whose body first called this one (`None` for the root).
    parent: Option<usize>,
    label: String,
    kind: NodeKind,
}

/// Nested contexts (a callee analysed in the state of its call site, itself analysed
/// in a context, ..) before a callee is analysed for any call (empty context).
const MAX_CONTEXT_DEPTH: u8 = 3;

/// A declared precondition (`fip::requires(..)`): as written, and as facts over the
/// parameters.
#[derive(Clone, Debug)]
pub struct Requires {
    pub text: String,
    pub facts: Vec<Fact>,
}

/// The facts of the conjuncts of `fip::requires(..)` on `def_id`: `i` is an integer
/// parameter, `xs.len()` the length of a slice parameter, `w.n` / `xs[0]` the
/// integer and `w.b.len()` the slice length at an access path below a parameter of
/// type `&T` with `T: Freeze` (fields and elements of arrays or slices at a literal
/// index, not through a further reference; top plan T13.2).
pub fn requires_facts(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    cs: &[fip_lint_rules::requires::Conjunct],
) -> Result<Vec<Fact>, String> {
    use fip_lint_rules::requires::{Rel, Side, Step, Term};
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return Err("`fip::requires` applies to functions".to_string());
    }
    let env = TypingEnv::non_body_analysis(tcx, def_id);
    let idents = tcx.fn_arg_idents(def_id);
    // Late-bound regions erased: `Freeze` is asked of a type with no escaping vars.
    let sig = tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(def_id).skip_binder());
    let inputs = sig.inputs();
    let find = |name: &str| {
        idents
            .iter()
            .position(|i| i.is_some_and(|i| i.name.as_str() == name))
            .ok_or_else(|| format!("`{name}` is not a parameter"))
    };
    let side = |s: &Side| -> Result<(SVar, i128), String> {
        let at = |k: usize| u32::try_from(k).map_err(|_| "too many parameters".to_string());
        match &s.term {
            Term::Zero => Ok((SVar::Zero, s.offset)),
            Term::Param(p) => {
                let k = find(p)?;
                if !inputs[k].is_integral() {
                    return Err(format!("`{p}` is not an integer parameter"));
                }
                Ok((SVar::Arg(at(k)?), s.offset))
            }
            Term::Len(p) => {
                let k = find(p)?;
                let slice = inputs[k]
                    .builtin_deref(true)
                    .is_some_and(|t| matches!(t.kind(), ty::Slice(_) | ty::Str));
                if !slice {
                    return Err(format!("`{p}.len()`: `{p}` is not a slice reference"));
                }
                Ok((SVar::ArgLen(at(k)?), s.offset))
            }
            Term::Path(p, steps) | Term::PathLen(p, steps) => {
                let len = matches!(s.term, Term::PathLen(..));
                let shown = fip_lint_rules::requires::display_side(s);
                let k = find(p)?;
                let ty::Ref(_, mut t, ty::Mutability::Not) = *inputs[k].kind() else {
                    return Err(format!(
                        "`{shown}`: `{p}` is not a shared reference (an access path is read behind `&T`)"
                    ));
                };
                if !t.is_freeze(tcx, env) {
                    return Err(format!(
                        "`{shown}`: the type behind `{p}` has interior mutability (not `Freeze`): the value may change"
                    ));
                }
                let mut fs: Vec<u32> = Vec::new();
                for st in steps {
                    match st {
                        Step::Field(f) => {
                            let idx = match t.kind() {
                                ty::Adt(def, args) if def.is_struct() => def
                                    .non_enum_variant()
                                    .fields
                                    .iter()
                                    .enumerate()
                                    .find(|(_, fd)| fd.name.as_str() == f)
                                    .map(|(i, fd)| (i, fd.ty(tcx, args).skip_normalization())),
                                ty::Tuple(ts) => f
                                    .parse::<usize>()
                                    .ok()
                                    .and_then(|i| ts.get(i).map(|t| (i, *t))),
                                _ => None,
                            };
                            let Some((i, ft)) = idx else {
                                return Err(format!(
                                    "`{shown}`: no field `{f}` in `{t}` (structs and tuples only)"
                                ));
                            };
                            fs.push(u32::try_from(i).map_err(|_| "field index".to_string())?);
                            t = ft;
                        }
                        Step::Index(c) => {
                            let (ty::Array(e, _) | ty::Slice(e)) = *t.kind() else {
                                return Err(format!(
                                    "`{shown}`: `[{c}]` on `{t}`, which is not an array or slice (an access path does not go through a further reference)"
                                ));
                            };
                            let c = u32::try_from(*c)
                                .ok()
                                .filter(|c| *c < crate::value::VAR_INDEX)
                                .ok_or_else(|| format!("`{shown}`: index `{c}` out of range"))?;
                            fs.push(crate::value::ELEM | c);
                            t = e;
                        }
                    }
                }
                let fields = crate::value::Fields::new(&fs)
                    .ok_or_else(|| format!("`{shown}`: an access path has at most 4 steps"))?;
                if len {
                    if !crate::value::is_slice_ptr(t) {
                        return Err(format!(
                            "`{shown}`: the value at the path is not a slice reference"
                        ));
                    }
                    Ok((SVar::ArgPathLen(at(k)?, fields), s.offset))
                } else {
                    if !t.is_integral() {
                        return Err(format!(
                            "`{shown}`: the value at the path is not an integer"
                        ));
                    }
                    Ok((SVar::ArgPath(at(k)?, fields), s.offset))
                }
            }
        }
    };
    let mut facts = Vec::new();
    for c in cs {
        let ((a, ka), (b, kb)) = (side(&c.a)?, side(&c.b)?);
        // a + ka REL b + kb, i.e. a - b ≤ kb - ka (- 1 for `<`).
        let le = |a: SVar, b: SVar, c: i128| Fact { a, b, c };
        match c.rel {
            Rel::Lt => facts.push(le(a, b, kb - ka - 1)),
            Rel::Le => facts.push(le(a, b, kb - ka)),
            Rel::Eq => {
                facts.push(le(a, b, kb - ka));
                facts.push(le(b, a, ka - kb));
            }
        }
    }
    if !crate::value::satisfiable(&facts) {
        return Err("the precondition can never hold".to_string());
    }
    Ok(facts)
}

/// Crates whose MIR may be used: the local crate, `core`/`alloc`/`std` and their
/// dependencies ([`is_std_like`]), and crates whose root declares `fip::export`.
pub struct Crates {
    exported: HashMap<CrateNum, bool>,
    /// Crates that declare `fip::export` but contain a function with a body in source
    /// and no MIR in their metadata: built without `-Zalways-encode-mir`, i.e. not by
    /// the driver. Value: the first such function found.
    unencoded: HashMap<CrateNum, String>,
    /// `fip::mark` of functions in the local crate and in exported crates.
    marks: HashMap<DefId, Mark>,
    /// `fip::alloc_source`/`fip::free_source` of functions, trait method declarations
    /// and foreign functions in the local crate and in exported crates.
    sources: HashMap<DefId, Source>,
    /// `fip::requires(..)` of functions in the local crate and in exported crates.
    requires: HashMap<DefId, Requires>,
    /// Certificates (`fip::cert`) and exclusions (`fip::exclude`) of foreign functions
    /// declared in the local crate and in exported crates, keyed by **link symbol**: a
    /// mark applies to every foreign declaration of that symbol, wherever it is
    /// declared (`std`, `libc`, any dependency).
    ffi: HashMap<String, Vec<FfiDecl>>,
    /// Calls whose foreign callee was matched by symbol to a mark on another
    /// declaration: `(callee, marked declaration)`, reported in the crate summary.
    ffi_matches: std::cell::RefCell<Vec<(DefId, DefId)>>,
    /// Foreign calls inside std summaries (`§ffi` terms) matched to a mark by symbol:
    /// `(summarised std function, symbol, ABI, marked declaration)`, reported in the
    /// crate summary.
    ffi_std_matches: std::cell::RefCell<Vec<(String, String, String, DefId)>>,
    /// Generated summaries of standard-library functions without MIR, or why they
    /// are not used ([`crate::stdsum`]).
    pub std_summaries: Result<crate::stdsum::Sidecar, String>,
    /// Generating std summaries (`--std-summaries`): a foreign call is the term
    /// `§ffi <symbol> <abi>`, resolved where the summary is used.
    pub generating: bool,
    /// Verus sidecars of verified bodies (top plan T13.4).
    pub verus: crate::verustrust::VerusTrust,
}

/// The rustc version of this driver (`1.99.1 (<commit> <date>)`).
pub fn rustc_version() -> &'static str {
    rustc_interface::util::rustc_version_str().unwrap_or("unknown")
}

/// The std summaries file for this compiler and `target` (`FIP_PRELINT_STD_SUMMARIES`
/// overrides it).
pub fn std_summaries_path(target: &str) -> std::path::PathBuf {
    if let Some(p) = std::env::var_os("FIP_PRELINT_STD_SUMMARIES") {
        return std::path::PathBuf::from(p);
    }
    let release = rustc_version().split(' ').next().unwrap_or("unknown");
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("std-summaries")
        .join(format!("{release}-{target}.txt"))
}

/// Loads the std summaries for this compiler and the crate's target; any problem
/// (missing file, parse error, stamp mismatch) is the reason they are not used.
fn load_std_summaries(tcx: TyCtxt<'_>) -> Result<crate::stdsum::Sidecar, String> {
    let target = tcx.sess.opts.target_triple.tuple().to_string();
    let path = std_summaries_path(&target);
    // The file name only: diagnostics stay independent of the checkout's location.
    let name = path.file_name().map_or_else(
        || path.display().to_string(),
        |n| n.to_string_lossy().to_string(),
    );
    let text = std::fs::read_to_string(&path).map_err(|e| format!("cannot read `{name}`: {e}"))?;
    let sc = crate::stdsum::Sidecar::parse(&text).map_err(|e| format!("`{name}`: {e}"))?;
    sc.check_stamp(rustc_version(), &target)
        .map_err(|e| format!("`{name}`: {e}"))?;
    shipped_std(tcx).map_err(|e| format!("`{name}`: {e}"))?;
    Ok(sc)
}

/// `Err(reason)` unless the `core` this crate links is the sysroot's (the shipped
/// standard library): under a user `-Zbuild-std`, `std` is compiled with the
/// profile's settings, so the summaries (of the shipped release build) would leave
/// out its debug-assertion and overflow panic paths.
fn shipped_std(tcx: TyCtxt<'_>) -> Result<(), String> {
    let Some(&core) = tcx
        .crates(())
        .iter()
        .find(|&&c| tcx.crate_name(c).as_str() == "core")
    else {
        return Ok(());
    };
    let roots: Vec<std::path::PathBuf> = tcx
        .sess
        .opts
        .sysroot
        .all_paths()
        .filter_map(|p| p.canonicalize().ok())
        .collect();
    let src = tcx.used_crate_source(core);
    let mut paths = src.paths().peekable();
    if paths.peek().is_none() {
        return Err("the location of `core` is not known".to_string());
    }
    for p in paths {
        let inside = p
            .canonicalize()
            .is_ok_and(|c| roots.iter().any(|r| c.starts_with(r)));
        if !inside {
            let file = p
                .file_name()
                .map_or_else(String::new, |n| n.to_string_lossy().to_string());
            return Err(format!(
                "`core` (`{file}`) is not the sysroot's: summaries describe the shipped standard library only (a `-Zbuild-std` build has its own settings)"
            ));
        }
    }
    Ok(())
}

/// Why a function is an allocation or free source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceKind {
    /// `fip::alloc_source`/`fip::free_source` on the function.
    Declared,
    /// The same on the trait method it implements.
    TraitDeclared,
    /// A method of `GlobalAlloc` or `Allocator` (`fip_lint_rules::mir::ALLOCATOR_TRAIT_METHODS`).
    AllocatorTrait,
    /// A foreign C allocation function (`fip_lint_rules::mir::FOREIGN_ALLOC_SYMBOLS`).
    Foreign,
}

impl SourceKind {
    pub fn describe(self) -> &'static str {
        match self {
            SourceKind::Declared => "declared source",
            SourceKind::TraitDeclared => "source declared on the trait method",
            SourceKind::AllocatorTrait => "allocator trait method",
            SourceKind::Foreign => "foreign allocation function",
        }
    }
}

/// The trait method that `def_id` is or implements.
fn trait_method(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    if tcx.trait_of_assoc(def_id).is_some() {
        Some(def_id)
    } else if tcx.trait_impl_of_assoc(def_id).is_some() {
        tcx.trait_item_of(def_id)
    } else {
        None
    }
}

/// A contract's `param(..)` bounds (`params`, named as in the trait method
/// declaration `method`) renamed to the parameters of the implementation `item` at
/// the same positions; a position whose parameter has no name in `item` (`_`) is
/// dropped (the implementation cannot call it).
pub fn inherited_params(
    tcx: TyCtxt<'_>,
    params: &[(String, u64)],
    method: DefId,
    item: DefId,
) -> Vec<(String, u64)> {
    let decl = tcx.fn_arg_idents(method);
    let own = tcx.fn_arg_idents(item);
    params
        .iter()
        .filter_map(|(g, k)| {
            let pos = decl
                .iter()
                .position(|i| i.is_some_and(|i| i.name.as_str() == g))?;
            let name = (*own.get(pos)?)?.name;
            (name.as_str() != "_").then(|| (name.to_string(), *k))
        })
        .collect()
}

/// `true` if a parameter of type `t` can carry `param(g = K)` in a trait method
/// contract: a function pointer, or `&dyn Tr`, `&mut dyn Tr`, `Box<dyn Tr>` or a
/// reference to `Box<dyn Tr>` with a callable `Tr` (`Fn*`, `FipFn`). A generic
/// parameter makes the method not dyn-compatible (its calls resolve per instance).
pub fn contract_callable(tcx: TyCtxt<'_>, t: Ty<'_>) -> bool {
    if t.is_fn_ptr() {
        return true;
    }
    let inner = match *t.kind() {
        ty::Ref(_, inner, _) if inner.is_box() => inner.expect_boxed_ty(),
        ty::Ref(_, inner, _) => inner,
        _ if t.is_box() => t.expect_boxed_ty(),
        _ => return false,
    };
    let ty::Dynamic(preds, ..) = *inner.kind() else {
        return false;
    };
    preds.principal().is_some_and(|p| {
        tcx.fn_trait_kind_from_def_id(p.def_id()).is_some()
            || tcx.item_name(p.def_id()).as_str() == "FipFn"
    })
}

/// A certificate or an exclusion of one foreign declaration.
#[derive(Clone, Debug)]
pub enum FfiMark {
    Cert(marks::FfiCert),
    Exclude(marks::FfiExclude),
}

/// A foreign declaration carrying `fip::cert` or `fip::exclude`.
#[derive(Clone, Debug)]
pub struct FfiDecl {
    pub def_id: DefId,
    /// The declaration's ABI as rustc prints it (`"C"`, `"C-unwind"`, `"system"`, ..).
    pub abi: String,
    pub mark: FfiMark,
}

/// What the marks of a foreign function's link symbol say about a call of it.
#[derive(Clone, Debug)]
pub enum FfiVerdict<'a> {
    /// No declaration of the symbol is certified or excluded.
    Neither,
    /// The symbol is certified on one declaration and excluded on another (or the same).
    Both,
    /// Two certificates of the symbol state different properties.
    Conflict,
    /// A marked declaration of the symbol has another ABI than the callee's.
    Abi {
        marked: DefId,
        marked_abi: String,
    },
    Cert(&'a marks::FfiCert),
    Excluded,
}

/// The link symbol of a foreign function: its `#[link_name]`, else its name (foreign
/// items are not mangled).
pub fn ffi_symbol(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    tcx.symbol_name(Instance::mono(tcx, def_id))
        .name
        .to_string()
}

/// The name a foreign declaration is classified by in the allocation tables: its
/// link symbol (`#[link_name]` included), except for declarations in the standard
/// library, whose `extern "Rust"` runtime symbols (`__rust_alloc`, ..) are mangled
/// by `#[rustc_std_internal_symbol]` and are named by their item name in the tables.
pub fn foreign_table_name(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    if is_std_like(tcx, def_id.krate) {
        tcx.item_name(def_id).to_string()
    } else {
        ffi_symbol(tcx, def_id)
    }
}

/// The ABI of a foreign function as rustc prints it.
pub fn ffi_abi(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    tcx.fn_sig(def_id).skip_binder().abi().to_string()
}

/// The marked declaration of a symbol shown in reports: a local one first, then the
/// first in source order.
fn shown_decl(tcx: TyCtxt<'_>, decls: &[FfiDecl]) -> DefId {
    decls
        .iter()
        .min_by_key(|d| (!d.def_id.is_local(), tcx.def_span(d.def_id)))
        .map_or_else(|| decls[0].def_id, |d| d.def_id)
}

/// The certified properties a call counts (the evidence is not compared).
fn cert_key(c: &marks::FfiCert) -> (marks::Kind, u64, bool) {
    (c.kind, c.alloc, c.free)
}

impl Crates {
    pub fn new(tcx: TyCtxt<'_>) -> Crates {
        let mut exported = HashMap::new();
        for &cnum in tcx.crates(()) {
            exported.insert(
                cnum,
                !macros_only(tcx, cnum) && declares_export(tcx, cnum.as_def_id()),
            );
        }
        exported.insert(LOCAL_CRATE, true);
        let generate = std::env::var_os(crate::GENERATE_ENV).is_some();
        if generate {
            // The standard library of a `-Zbuild-std` build and its dependencies,
            // all compiled with their MIR encoded. Not proc-macro crates: their
            // metadata has no definitions to list (listing them was an ICE in
            // `rustc_metadata`, `def_key` on `None`) and nothing of them is called.
            for (cnum, v) in &mut exported {
                *v = *cnum == LOCAL_CRATE || !macros_only(tcx, *cnum);
            }
        }
        let std_summaries = if generate {
            Err("generating std summaries".to_string())
        } else {
            load_std_summaries(tcx)
        };
        let mut unencoded = HashMap::new();
        let mut marks = HashMap::new();
        let mut sources = HashMap::new();
        let mut requires = HashMap::new();
        let mut ffi: HashMap<String, Vec<FfiDecl>> = HashMap::new();
        for krate in rustc_public::external_crates() {
            let Some(&cnum) = tcx
                .crates(())
                .iter()
                .find(|&&c| tcx.crate_name(c).as_str() == krate.name.as_str())
            else {
                continue;
            };
            if !exported.get(&cnum).copied().unwrap_or(false) {
                continue;
            }
            for f in krate.fn_defs() {
                let def_id: DefId =
                    rustc_public::rustc_internal::internal(tcx, rustc_public::CrateDef::def_id(&f));
                if def_id.krate != cnum {
                    continue;
                }
                let attrs: Vec<String> = rustc_public::CrateDef::all_tool_attrs(&f)
                    .iter()
                    .map(|a| a.as_str().to_string())
                    .collect();
                // Sources may also be foreign functions and trait method declarations.
                // Malformed marks were reported where that crate was checked.
                if let Ok(Some(s)) = marks::source_of_printed(attrs.iter().map(String::as_str)) {
                    sources.insert(def_id, s);
                }
                if tcx.is_foreign_item(def_id) {
                    let decl = |mark| FfiDecl {
                        def_id,
                        abi: ffi_abi(tcx, def_id),
                        mark,
                    };
                    if let Ok(Some(cert)) = marks::cert_of_printed(attrs.iter().map(String::as_str))
                    {
                        ffi.entry(ffi_symbol(tcx, def_id))
                            .or_default()
                            .push(decl(FfiMark::Cert(cert)));
                    }
                    if let Ok(Some(excl)) =
                        marks::exclude_of_printed(attrs.iter().map(String::as_str))
                    {
                        ffi.entry(ffi_symbol(tcx, def_id))
                            .or_default()
                            .push(decl(FfiMark::Exclude(excl)));
                    }
                }
                if let Ok(Some(cs)) = marks::requires_of_printed(attrs.iter().map(String::as_str))
                    && let Ok(facts) = requires_facts(tcx, def_id, &cs)
                {
                    requires.insert(
                        def_id,
                        Requires {
                            text: fip_lint_rules::requires::display_all(&cs),
                            facts,
                        },
                    );
                }
                // A mark on a trait method declaration is a contract of every
                // implementation (dynamic calls use it); it may have no body.
                let contract = tcx.trait_of_assoc(def_id).is_some();
                let body = has_source_body(tcx, def_id);
                if body && !unencoded.contains_key(&cnum) && !tcx.is_mir_available(def_id) {
                    unencoded.insert(cnum, tcx.def_path_str(def_id));
                }
                if !body && !contract {
                    continue;
                }
                for attr in &attrs {
                    if let Some(args) = marks::mark_args_of_printed(attr)
                        && let Ok(m) = marks::parse_mark(args)
                    {
                        marks.insert(def_id, m);
                    }
                }
            }
        }
        Crates {
            exported,
            unencoded,
            marks,
            sources,
            requires,
            ffi,
            ffi_matches: std::cell::RefCell::new(Vec::new()),
            ffi_std_matches: std::cell::RefCell::new(Vec::new()),
            std_summaries,
            generating: generate,
            verus: crate::verustrust::VerusTrust::new(),
        }
    }
    /// Adds the marks of the local crate (the roots).
    pub fn add_local_marks(&mut self, roots: &[(DefId, Mark)]) {
        for (d, m) in roots {
            self.marks.insert(*d, m.clone());
        }
    }
    /// Adds the declared preconditions of the local crate.
    pub fn add_local_requires(&mut self, requires: &[(DefId, Requires)]) {
        for (d, r) in requires {
            self.requires.insert(*d, r.clone());
        }
    }
    /// The declared precondition of `def_id`.
    pub fn requires_of(&self, def_id: DefId) -> Option<&Requires> {
        self.requires.get(&def_id)
    }
    /// Adds the declared sources of the local crate.
    pub fn add_local_sources(&mut self, sources: &[(DefId, Source)]) {
        for (d, s) in sources {
            self.sources.insert(*d, *s);
        }
    }
    /// Adds the certified foreign functions and exclusions of the local crate (a
    /// declaration carrying both is passed in both lists: every call of its symbol is
    /// then an error).
    pub fn add_local_ffi(
        &mut self,
        tcx: TyCtxt<'_>,
        certs: &[(DefId, crate::marks::FfiCert)],
        excls: &[(DefId, crate::marks::FfiExclude)],
    ) {
        let marks = certs
            .iter()
            .map(|(d, c)| (*d, FfiMark::Cert(c.clone())))
            .chain(excls.iter().map(|(d, e)| (*d, FfiMark::Exclude(e.clone()))));
        for (def_id, mark) in marks {
            self.ffi
                .entry(ffi_symbol(tcx, def_id))
                .or_default()
                .push(FfiDecl {
                    def_id,
                    abi: ffi_abi(tcx, def_id),
                    mark,
                });
        }
    }
    /// Every marked declaration of `symbol` (local and exported crates).
    pub fn ffi_decls(&self, symbol: &str) -> &[FfiDecl] {
        self.ffi.get(symbol).map_or(&[], Vec::as_slice)
    }
    /// The verdict for a call of the foreign function `def_id`, from the marks on any
    /// declaration of its link symbol. A match through another declaration than
    /// `def_id` is recorded for the crate summary.
    pub fn ffi_verdict(&self, tcx: TyCtxt<'_>, def_id: DefId) -> FfiVerdict<'_> {
        let symbol = ffi_symbol(tcx, def_id);
        let abi = ffi_abi(tcx, def_id);
        let v = self.ffi_verdict_of(&symbol, &abi);
        if matches!(v, FfiVerdict::Cert(_) | FfiVerdict::Excluded) {
            let decls = self.ffi_decls(&symbol);
            if !decls.iter().any(|d| d.def_id == def_id) {
                // The declaration reported: a local one first, then the first in
                // source order.
                let shown = shown_decl(tcx, decls);
                let mut m = self.ffi_matches.borrow_mut();
                if !m.contains(&(def_id, shown)) {
                    m.push((def_id, shown));
                }
            }
        }
        v
    }
    /// The verdict for a foreign call inside the std summary of `path` (a `§ffi`
    /// term: the link symbol and ABI recorded when the summary was generated), from
    /// the marks of this crate and the exported crates; a match is recorded for the
    /// crate summary.
    pub fn ffi_verdict_std(
        &self,
        tcx: TyCtxt<'_>,
        path: &str,
        symbol: &str,
        abi: &str,
    ) -> FfiVerdict<'_> {
        let v = self.ffi_verdict_of(symbol, abi);
        if matches!(v, FfiVerdict::Cert(_) | FfiVerdict::Excluded) {
            let shown = shown_decl(tcx, self.ffi_decls(symbol));
            let entry = (path.to_string(), symbol.to_string(), abi.to_string(), shown);
            let mut m = self.ffi_std_matches.borrow_mut();
            if !m.contains(&entry) {
                m.push(entry);
            }
        }
        v
    }
    /// Foreign calls inside std summaries matched by symbol so far.
    pub fn ffi_std_matches(&self) -> Vec<(String, String, String, DefId)> {
        self.ffi_std_matches.borrow().clone()
    }
    /// The verdict for a call of a foreign function with link symbol `symbol` and ABI
    /// `abi`, from the marks on any declaration of that symbol.
    fn ffi_verdict_of(&self, symbol: &str, abi: &str) -> FfiVerdict<'_> {
        let decls = self.ffi_decls(symbol);
        if decls.is_empty() {
            return FfiVerdict::Neither;
        }
        let certs: Vec<&marks::FfiCert> = decls
            .iter()
            .filter_map(|d| match &d.mark {
                FfiMark::Cert(c) => Some(c),
                FfiMark::Exclude(_) => None,
            })
            .collect();
        if certs.len() < decls.len() && !certs.is_empty() {
            return FfiVerdict::Both;
        }
        if certs.iter().any(|c| cert_key(c) != cert_key(certs[0])) {
            return FfiVerdict::Conflict;
        }
        if let Some(d) = decls.iter().find(|d| d.abi != abi) {
            return FfiVerdict::Abi {
                marked: d.def_id,
                marked_abi: d.abi.clone(),
            };
        }
        match certs.first() {
            Some(c) => FfiVerdict::Cert(c),
            None => FfiVerdict::Excluded,
        }
    }
    /// Calls matched by symbol so far: `(callee, marked declaration)`.
    pub fn ffi_matches(&self) -> Vec<(DefId, DefId)> {
        self.ffi_matches.borrow().clone()
    }
    /// What a call of `def_id` does if it is an allocation or free source, and why:
    /// declared on the function or on the trait method it implements, a method of an
    /// allocator trait, or a foreign C allocation function. `None` for every other
    /// function, which is analysed through its MIR.
    pub fn source_of(&self, tcx: TyCtxt<'_>, def_id: DefId) -> Option<(Source, SourceKind)> {
        if let Some(s) = self.sources.get(&def_id) {
            return Some((*s, SourceKind::Declared));
        }
        if let Some(tm) = trait_method(tcx, def_id) {
            if let Some(s) = self.sources.get(&tm) {
                return Some((*s, SourceKind::TraitDeclared));
            }
            if let Some(trait_id) = tcx.trait_of_assoc(tm)
                && tcx.crate_name(trait_id.krate).as_str() == "core"
                && let Some((a, f)) = rules::allocator_trait_method(
                    &def_path(tcx, trait_id),
                    tcx.item_name(tm).as_str(),
                )
            {
                let s = Source {
                    alloc: u64::from(a),
                    free: f,
                };
                return Some((s, SourceKind::AllocatorTrait));
            }
        }
        if tcx.is_foreign_item(def_id)
            && let Some((a, f)) = rules::foreign_alloc_symbol(&foreign_table_name(tcx, def_id))
        {
            let s = Source {
                alloc: u64::from(a),
                free: f,
            };
            return Some((s, SourceKind::Foreign));
        }
        None
    }
    /// `true` if some known function declares `param(..)`: only then can a call site
    /// violate a declared parameter bound.
    pub fn has_param_marks(&self) -> bool {
        self.marks.values().any(|m| !m.params.is_empty())
    }
    /// The mark of `def_id` if it declares `param(..)`. An implementation of a trait
    /// method whose contract declares `param(..)`, and whose own mark (if any)
    /// declares none, inherits the contract's bounds, mapped by position to its own
    /// parameter names (top plan T5): its static call sites are checked against them,
    /// and its body counts them for its parameters.
    pub(crate) fn param_mark(
        &self,
        tcx: TyCtxt<'_>,
        def_id: DefId,
    ) -> Option<std::borrow::Cow<'_, Mark>> {
        if let Some(m) = self.marks.get(&def_id).filter(|m| !m.params.is_empty()) {
            return Some(std::borrow::Cow::Borrowed(m));
        }
        tcx.trait_impl_of_assoc(def_id)?;
        let method = tcx.trait_item_of(def_id)?;
        let c = self
            .contract_of(tcx, method)
            .filter(|m| !m.params.is_empty())?;
        let params = inherited_params(tcx, &c.params, method, def_id);
        if params.is_empty() {
            return None;
        }
        Some(std::borrow::Cow::Owned(Mark {
            params,
            ..c.clone()
        }))
    }
    /// The `fip::mark` of `def_id` itself (a local root, or a function of an exported
    /// crate).
    pub fn mark_of(&self, def_id: DefId) -> Option<&Mark> {
        self.marks.get(&def_id)
    }
    /// The contract of a trait method: the `fip::mark` on its declaration (local
    /// crate or an exported crate). A dynamic call of the method costs the contract;
    /// every implementation is checked against it, without its own or the
    /// declaration's `fip::requires(..)`. A contract's `param(g = K)` (a callable
    /// parameter, checked where the contract is declared) is assumed by every
    /// implementation and checked at every call through the contract (top plan T5);
    /// a contract with `fip::requires(..)` is rejected where it is declared.
    pub fn contract_of(&self, tcx: TyCtxt<'_>, def_id: DefId) -> Option<&Mark> {
        tcx.trait_of_assoc(def_id)?;
        self.marks.get(&def_id)
    }
    /// Every trait method with a contract, in a stable order.
    pub fn contracts(&self, tcx: TyCtxt<'_>) -> Vec<(DefId, Mark)> {
        let mut v: Vec<(DefId, Mark)> = self
            .marks
            .keys()
            .filter_map(|&d| self.contract_of(tcx, d).map(|m| (d, m.clone())))
            .collect();
        v.sort_by_key(|(d, _)| def_path(tcx, *d));
        v
    }
    pub(crate) fn exported(&self, c: CrateNum) -> bool {
        self.exported.get(&c).copied().unwrap_or(false)
    }
    /// Exported crates whose metadata lacks MIR, with one function as evidence.
    pub fn unencoded(&self, tcx: TyCtxt<'_>) -> Vec<(String, String)> {
        let mut v: Vec<(String, String)> = self
            .unencoded
            .iter()
            .map(|(c, f)| (tcx.crate_name(*c).to_string(), f.clone()))
            .collect();
        v.sort();
        v
    }
}

/// `true` if `def_id` is a function whose source has a body: not a foreign item and
/// not a required trait method without a default.
fn has_source_body(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if tcx.is_foreign_item(def_id) {
        return false;
    }
    match tcx.def_kind(def_id) {
        DefKind::Fn => true,
        DefKind::AssocFn => tcx.defaultness(def_id).has_value(),
        _ => false,
    }
}

/// `true` for a dependency loaded only for its macros (a proc-macro crate): its
/// metadata lists no functions that code of this crate can call, and listing its
/// definitions through `rustc_public` panics in `rustc_metadata`.
pub fn macros_only(tcx: TyCtxt<'_>, cnum: rustc_hir::def_id::CrateNum) -> bool {
    tcx.crate_dep_kind(cnum) == rustc_crate_store::CrateDepKind::MacrosOnly
}

/// The name of the check function a driver-mode `fip_fn!(prelint, N, ..)` expands
/// to (`fip-macros`, `docs/decisions/2026-11-03-fip-fn-driver-mode.md`).
pub const CHECKED_FN: &str = "__fip_prelint_checked";

/// `true` for the check function of a driver-mode `fip_fn!` (a local function named
/// [`CHECKED_FN`]).
pub fn is_checked_fn(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    def_id.is_local()
        && tcx
            .opt_item_name(def_id)
            .is_some_and(|n| n.as_str() == CHECKED_FN)
}

/// `true` if the crate root of `root` carries `fip::export`.
#[allow(
    deprecated,
    reason = "tool attributes are unparsed; `find_attr!` covers parsed ones only"
)]
pub fn declares_export(tcx: TyCtxt<'_>, root: DefId) -> bool {
    tcx.get_all_attrs(root).iter().any(|a| match a {
        rustc_hir::Attribute::Unparsed(item) => {
            let segs: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
            segs == ["fip", "export"]
        }
        _ => false,
    })
}

/// Local functions whose call sites are all in analysed code of this crate and pass
/// the function itself only as a callee (top plan T4.3): not exported by name, not a
/// trait method or trait implementation, without an external symbol (`#[no_mangle]`,
/// `#[export_name]`), never named outside the callee position of a call (so never
/// reified, coerced or passed as a callable), with a parameter of callable type. A
/// call site inside such a function that passes one of its unbound, undeclared
/// parameters is not reported on its own: each of the function's call sites checks
/// its body with what it passes (`Analysis::arguments_in`).
pub fn inferable_private(tcx: TyCtxt<'_>) -> HashSet<DefId> {
    use rustc_hir::intravisit::{self, Visitor};
    struct Values<'tcx> {
        tcx: TyCtxt<'tcx>,
        body: Option<rustc_hir::def_id::LocalDefId>,
        used: HashSet<DefId>,
    }
    impl<'tcx> Visitor<'tcx> for Values<'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::All;
        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }
        fn visit_nested_body(&mut self, id: rustc_hir::BodyId) {
            let prev = self.body.replace(self.tcx.hir_body_owner_def_id(id));
            let body = self.tcx.hir_body(id);
            self.visit_body(body);
            self.body = prev;
        }
        fn visit_expr(&mut self, e: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Call(callee, args) = e.kind
                && matches!(callee.kind, rustc_hir::ExprKind::Path(_))
            {
                for a in args {
                    self.visit_expr(a);
                }
                return;
            }
            if let rustc_hir::ExprKind::Path(ref qpath) = e.kind
                && let Some(owner) = self.body
            {
                let res = self.tcx.typeck(owner).qpath_res(qpath, e.hir_id);
                if let rustc_hir::def::Res::Def(_, d) = res {
                    self.used.insert(d);
                }
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut v = Values {
        tcx,
        body: None,
        used: HashSet::new(),
    };
    tcx.hir_walk_toplevel_module(&mut v);
    let visibilities = tcx.effective_visibilities(());
    let callable = |t: Ty<'_>| {
        let inner = match *t.kind() {
            ty::Ref(_, inner, _) => inner,
            _ => t,
        };
        let inner = if inner.is_box() {
            inner.expect_boxed_ty()
        } else {
            inner
        };
        inner.is_fn_ptr() || matches!(inner.kind(), ty::Dynamic(..))
    };
    tcx.mir_keys(())
        .iter()
        .filter(|&&d| {
            let def = d.to_def_id();
            matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
                && !visibilities.is_exported(d)
                && tcx.trait_of_assoc(def).is_none()
                && tcx.trait_impl_of_assoc(def).is_none()
                && !tcx.codegen_fn_attrs(def).contains_extern_indicator()
                && !v.used.contains(&def)
                && tcx
                    .fn_sig(def)
                    .skip_binder()
                    .skip_binder()
                    .inputs()
                    .iter()
                    .any(|t| callable(*t))
        })
        .map(|d| d.to_def_id())
        .collect()
}

pub(crate) fn is_std_crate(name: &str) -> bool {
    matches!(name, "core" | "alloc" | "std")
}

/// `true` for `core`, `alloc`, `std` and the crates the standard library depends on
/// (`hashbrown`, `std_detect`, `libc`, ..; top plan T7h): crates loaded only as
/// dependencies of a standard-library crate, by the chain `ExternCrate::dependency_of`
/// that rustc records (the shortest path through which a crate was loaded). They are
/// the shipped standard library's code: analysed where they have MIR, summarised
/// where not. Foreign functions in them still go through the FFI rule. A crate the
/// local crate depends on directly (even one of the same name) is not std-like.
pub(crate) fn is_std_like(tcx: TyCtxt<'_>, krate: CrateNum) -> bool {
    let mut k = krate;
    // Bounded walk: the chain ends at the local crate or a direct dependency.
    for _ in 0..32 {
        if is_std_crate(tcx.crate_name(k).as_str()) {
            return true;
        }
        if k == LOCAL_CRATE {
            return false;
        }
        match tcx.extern_crate(k) {
            Some(e) if !e.is_direct() && e.dependency_of != k => k = e.dependency_of,
            _ => return false,
        }
    }
    false
}

/// Strongly connected components (Tarjan, iterative), in reverse topological order
/// (every component after all components it reaches).
fn tarjan(n: usize, succ: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0; n];
    let mut on_stack = vec![false; n];
    let mut stack = Vec::new();
    let mut comps = Vec::new();
    let mut next = 0;
    for start in 0..n {
        if index[start] != usize::MAX {
            continue;
        }
        let mut call: Vec<(usize, usize)> = vec![(start, 0)];
        index[start] = next;
        low[start] = next;
        next += 1;
        stack.push(start);
        on_stack[start] = true;
        while let Some(&mut (v, ref mut i)) = call.last_mut() {
            if *i < succ[v].len() {
                let w = succ[v][*i];
                *i += 1;
                if index[w] == usize::MAX {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    call.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                call.pop();
                if let Some(&(u, _)) = call.last() {
                    low[u] = low[u].min(low[v]);
                }
                if low[v] == index[v] {
                    let mut comp = Vec::new();
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        comp.push(w);
                        if w == v {
                            break;
                        }
                    }
                    comp.sort_unstable();
                    comps.push(comp);
                }
            }
        }
    }
    comps
}

pub struct Analysis<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    crates: &'a Crates,
    nodes: Vec<Node<'tcx>>,
    index: HashMap<(Instance<'tcx>, Vec<Fact>, Binds<'tcx>), usize>,
    /// The node being classified.
    current: usize,
    queue: Vec<usize>,
    param_names: HashMap<u32, String>,
    param_types: Vec<(String, String)>,
    /// `param(..)` of the analysed function (the root's mark; empty for a body
    /// scanned by [`Analysis::arguments_in`]).
    owner_params: Vec<(String, u64)>,
    /// Call sites of callees with `param(..)` found in explored bodies.
    arg_sites: Vec<ArgSite>,
    /// Return summaries for the value analysis of the explored bodies.
    vsums: crate::value::Summaries<'a, 'tcx>,
    /// Direct calls (caller node, callee node, call span) in the bodies of
    /// Verus-verified functions: Verus checked the callee's `requires` there (top
    /// plan T13.4). Value: the caller's path and whether it has a `requires`.
    verus_direct: HashMap<(usize, usize, Span), (String, bool)>,
    /// Nodes of private functions entered from a call in the body that
    /// [`Analysis::arguments_in`] scans (top plan T4.3): that call.
    entries: HashMap<usize, Via>,
    /// Checking an implementation against its trait method's contract: a dynamic
    /// call of a contracted method may re-enter this implementation (or another one
    /// checked under the same assumption), so it also carries a possible recursion.
    contract_impl: bool,
}

/// A call, in a body scanned by [`Analysis::arguments_in`], of a private function
/// checked at its call sites (top plan T4.3): a call site inside that function (or
/// below it) is reported here, for this caller.
#[derive(Clone, Debug)]
pub struct Via {
    /// The call of the private function.
    pub span: Span,
    /// The private function called.
    pub private: String,
    /// For each of its callable parameters that this call passes an unbound,
    /// undeclared parameter of the caller: `(its parameter, the caller's)`.
    pub unknown: Vec<(String, String)>,
}

/// Result for one root.
pub struct RootResult {
    pub summary: Summary,
    pub label: String,
    /// Value parameter name → its generic type parameter (`g` → `F` for `g: F`).
    pub param_types: Vec<(String, String)>,
    /// Call sites in the explored bodies that violate a callee's `param(g = K)`.
    pub args: Vec<ArgViolation>,
}

/// A call site whose callee declares `param(g = K)`, with the argument's callable
/// entry points resolved.
struct ArgSite {
    caller: String,
    /// The function or closure containing the call.
    caller_def: DefId,
    /// `true` if the argument is a parameter of the caller that is neither bound at
    /// the caller's call sites nor declared `param(..)` (top plan T4.3).
    from_param: bool,
    span: Span,
    /// `true` if the call site lies in the local crate.
    local: bool,
    callee: String,
    param: String,
    declared: u64,
    /// The argument's type.
    arg: String,
    /// Label and item of each callable entry point of the argument
    /// (`<T as FipFn<A>>::call`, `<T as Fn<A>>::call`, ..).
    items: Vec<(String, Item)>,
    /// For a function pointer or callable trait object parameter: the callee's mark.
    /// Its body counts a call through the parameter by the declaration alone, so the
    /// argument must also respect what the mark forbids (a free or recursion under
    /// `fip`, a panic path under `strict = true, panic_macros = false`).
    indirect: Option<Mark>,
    /// The check function of a driver-mode `fip_fn!(prelint, N, ..)`
    /// (`__fip_prelint_checked`): its bound is a claim of the certificate for every
    /// instantiation of the enclosing function, so terms left are `⊤` here.
    certifying: bool,
    /// The node whose body contains the call (`usize::MAX`: the scanned body).
    node: usize,
}

/// The argument passed for a declared parameter: its type as shown, the callable
/// entry points (label, item), and whether the parameter is a function pointer or a
/// callable trait object (called by its declaration in the callee).
type ArgItems = (String, Vec<(String, Item)>, bool);

/// A call site passing, for a parameter declared `param(g = K)`, an argument whose
/// bound per call is `⊤` or, with no terms left, above `K`.
pub struct ArgViolation {
    /// The function or closure containing the call.
    pub caller: String,
    pub caller_def: DefId,
    /// The argument is an unbound, undeclared parameter of the caller.
    pub from_param: bool,
    /// The call site.
    pub span: Span,
    /// `true` if the call site lies in the local crate.
    pub local: bool,
    pub callee: String,
    pub param: String,
    pub declared: u64,
    /// The argument's type (a closure, `Certified<N, C>`, a function item, ..).
    pub arg: String,
    /// Allocations per call of the argument, after the analysed function's own
    /// `param(..)`.
    pub bound: Cost,
    /// The argument's events: allocation witnesses, unresolved calls (`⊤`), terms.
    pub summary: Summary,
    /// For a function pointer or callable trait object parameter: an event of the
    /// argument that the callee's mark forbids (`may free`, `recurses`, `may panic`)
    /// and its witness.
    pub forbidden: Option<(String, Witness)>,
    /// The call site lies in a private function checked at its call sites, entered
    /// through this call of the scanned body (top plan T4.3): reported there.
    pub via: Option<Via>,
}

impl ArgViolation {
    /// Identifies the same violation found from several roots or bodies.
    pub fn key(&self) -> String {
        format!(
            "{:?}|{:?}|{}|{}|{}",
            self.span,
            self.via.as_ref().map(|v| v.span),
            self.callee,
            self.param,
            self.arg
        )
    }
}

/// The definition path the std summaries are keyed by.
pub fn def_path_pub(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    def_path(tcx, def_id)
}

/// `(N, C)` for `fip_strict::Certified<N, C>` (`N` evaluated).
fn certified_parts<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(u64, Ty<'tcx>)> {
    let ty::Adt(def, args) = *ty.kind() else {
        return None;
    };
    if tcx.crate_name(def.did().krate).as_str() != "fip_strict"
        || tcx.item_name(def.did()).as_str() != "Certified"
    {
        return None;
    }
    let c = args.get(1)?.as_type()?;
    let n = args.first()?.as_const()?.try_to_leaf()?.to_u64();
    Some((n, c))
}

/// `(N, P)` for `fip_strict::Certified<N, P>` with `P` a function pointer type.
fn certified_fn_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(u64, Ty<'tcx>)> {
    certified_parts(tcx, ty).filter(|(_, p)| p.is_fn_ptr())
}

fn def_path(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    with_no_visible_paths!(with_no_trimmed_paths!(tcx.def_path_str(def_id)))
}

/// `def_id`'s path if it is defined in a standard-library crate, else the empty
/// string: every path-table test goes through it, because the paths of local items
/// print without a crate prefix (a local `mod core { .. }` would otherwise match a
/// `core::..` entry).
fn std_path(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    if is_std_like(tcx, def_id.krate) {
        def_path(tcx, def_id)
    } else {
        String::new()
    }
}

fn def_path_args<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, args: GenericArgsRef<'tcx>) -> String {
    with_no_visible_paths!(with_no_trimmed_paths!(
        tcx.def_path_str_with_args(def_id, args)
    ))
}

/// Checks inserted for undefined behaviour (`-Zub-checks`, on with debug
/// assertions): they fire only when an `unsafe` contract is already broken.
fn is_ub_check_assert(msg: &AssertKind<Operand<'_>>) -> bool {
    matches!(
        msg,
        AssertKind::MisalignedPointerDereference { .. }
            | AssertKind::NullPointerDereference
            | AssertKind::NullReferenceConstructed
            | AssertKind::InvalidEnumConstruction(_)
    )
}

fn describe_assert(msg: &AssertKind<Operand<'_>>) -> String {
    match msg {
        AssertKind::BoundsCheck { .. } => "index out of bounds (bounds check)".to_string(),
        AssertKind::Overflow(op, ..) => format!("arithmetic overflow check ({op:?})"),
        AssertKind::OverflowNeg(_) => "negation overflow check".to_string(),
        AssertKind::DivisionByZero(_) => "division by zero check".to_string(),
        AssertKind::RemainderByZero(_) => "remainder by zero check".to_string(),
        AssertKind::MisalignedPointerDereference { .. } => "misaligned pointer check".to_string(),
        AssertKind::NullPointerDereference => "null pointer check".to_string(),
        _ => "assertion".to_string(),
    }
}

impl<'a, 'tcx> Analysis<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, crates: &'a Crates, owner: DefId) -> Analysis<'a, 'tcx> {
        Analysis::new_in(tcx, crates, owner, owner)
    }

    /// Analysis of `owner`'s body in the typing environment of `env_owner` (the
    /// implementation, for a trait method's default body checked for one impl).
    fn new_in(
        tcx: TyCtxt<'tcx>,
        crates: &'a Crates,
        env_owner: DefId,
        owner: DefId,
    ) -> Analysis<'a, 'tcx> {
        let env = TypingEnv::post_analysis(tcx, tcx.typeck_root_def_id(env_owner));
        let mut a = Analysis {
            tcx,
            env,
            crates,
            nodes: Vec::new(),
            index: HashMap::new(),
            current: 0,
            queue: Vec::new(),
            param_names: HashMap::new(),
            param_types: Vec::new(),
            owner_params: Vec::new(),
            arg_sites: Vec::new(),
            entries: HashMap::new(),
            vsums: crate::value::Summaries::new(crates),
            verus_direct: HashMap::new(),
            contract_impl: false,
        };
        a.collect_param_names(owner);
        a
    }

    fn identity(&self, owner: DefId) -> Instance<'tcx> {
        let tcx = self.tcx;
        let args = tcx.erase_and_anonymize_regions(GenericArgs::identity_for_item(tcx, owner));
        Instance::new_raw(owner, args)
    }

    pub fn run(tcx: TyCtxt<'tcx>, crates: &'a Crates, root: DefId, mark: &Mark) -> RootResult {
        let a = Analysis::new(tcx, crates, root);
        let inst = a.identity(root);
        a.run_root(root, inst, mark, true)
    }

    /// An implementation of a trait method checked against the method's contract:
    /// as [`Analysis::run`], but without assuming the implementation's own
    /// `fip::requires(..)`. A dynamic call, which relies on the contract, does not
    /// check that precondition, so assuming it would accept a panic path that a
    /// dynamic call reaches.
    pub fn run_contract(
        tcx: TyCtxt<'tcx>,
        crates: &'a Crates,
        root: DefId,
        mark: &Mark,
    ) -> RootResult {
        let a = Analysis::new(tcx, crates, root);
        let inst = a.identity(root);
        a.run_root(root, inst, mark, false)
    }

    /// Generating std summaries: the standard-library functions without MIR in the
    /// shipped `std` that the analysis of the seed `root` reaches.
    pub fn reached_std(
        tcx: TyCtxt<'tcx>,
        crates: &'a Crates,
        root: DefId,
        mark: &Mark,
    ) -> Vec<DefId> {
        let mut a = Analysis::new(tcx, crates, root);
        a.owner_params = mark.params.clone();
        let inst = a.identity(root);
        a.node_in(inst, Vec::new(), 0);
        while let Some(i) = a.queue.pop() {
            a.classify(i);
        }
        a.std_defs()
    }

    /// Generating std summaries: the summary of the standard-library function `def`,
    /// analysed as a root whose `&mut dyn fmt::Write`, `&mut fmt::Formatter` and
    /// `fmt::Arguments` parameters are left open (terms over them), and the functions
    /// without shipped MIR it reaches.
    pub fn summarize(
        tcx: TyCtxt<'tcx>,
        crates: &'a Crates,
        def: DefId,
    ) -> (crate::stdsum::FnSummary, Vec<DefId>) {
        let mut a = Analysis::new(tcx, crates, def);
        let inst = a.identity(def);
        let mut binds: Binds<'tcx> = Vec::new();
        if matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn) {
            let inputs = tcx.fn_sig(def).skip_binder().skip_binder().inputs();
            for (i, t) in inputs.iter().enumerate() {
                let (Ok(local), Ok(i)) = (u32::try_from(i + 1), u32::try_from(i)) else {
                    break;
                };
                let b = if is_dyn_write_ref(tcx, *t) {
                    Some(Bind::Dyn(Out::Param(i)))
                } else if is_formatter_ref(tcx, *t) {
                    Some(Bind::Formatter(Out::Param(i)))
                } else if mentions_fmt_args(tcx, *t, 2) {
                    Some(Bind::Fmt(Vec::new(), vec![i]))
                } else if is_obj_ref(tcx, *t) {
                    Some(Bind::Obj(Obj::Param(i)))
                } else {
                    None
                };
                if let Some(b) = b {
                    binds.push((local, b));
                }
                // The formatter, output or `dyn Debug` held below the parameter (a
                // builder's formatter, a `PadAdapter`'s buffer; top plan T7a/b).
                for (path, leaf) in bindable_paths(tcx, *t) {
                    let Some(key) = place_path(&path) else {
                        continue;
                    };
                    let b = match leaf {
                        Leaf::Formatter => Bind::Formatter(Out::Param(i)),
                        Leaf::Dyn => Bind::Dyn(Out::Param(i)),
                        Leaf::Obj => Bind::Obj(Obj::Param(i)),
                    };
                    binds.push((local, Bind::At(key, Box::new(b))));
                }
            }
        }
        let r = a.node_bound(inst, Vec::new(), 0, binds);
        while let Some(i) = a.queue.pop() {
            a.classify(i);
        }
        let sums = a.evaluate();
        let reached = a.std_defs();
        (to_fn_summary(&sums[r]), reached)
    }

    /// The explored standard-library functions that the shipped `std` has no MIR
    /// for: not generic and not cross-crate inlinable (closures inside them too).
    fn std_defs(&self) -> Vec<DefId> {
        let tcx = self.tcx;
        let mut v: Vec<DefId> = self
            .nodes
            .iter()
            .filter_map(|n| match n.inst.def {
                InstanceKind::Item(d) => Some(d),
                _ => None,
            })
            .filter(|&d| {
                is_std_like(tcx, d.krate)
                    && matches!(
                        tcx.def_kind(d),
                        DefKind::Fn | DefKind::AssocFn | DefKind::Closure
                    )
                    && !tcx.is_foreign_item(d)
                    && !tcx.generics_of(d).requires_monomorphization(tcx)
                    && !tcx.cross_crate_inlinable(d)
            })
            .collect();
        v.sort_by_key(|d| def_path(tcx, *d));
        v.dedup();
        v
    }

    /// The default body of the trait method `method` as `impl_def` uses it (the impl
    /// does not override it), analysed as a root in the impl's typing environment,
    /// against the method's contract: without the declaration's `fip::requires(..)`,
    /// as [`Analysis::run_contract`]; `None` if it does not resolve to that body.
    pub fn run_default(
        tcx: TyCtxt<'tcx>,
        crates: &'a Crates,
        impl_def: DefId,
        method: DefId,
        mark: &Mark,
    ) -> Option<RootResult> {
        let a = Analysis::new_in(tcx, crates, impl_def, method);
        let trait_ref = tcx
            .impl_trait_ref(impl_def)
            .instantiate_identity()
            .skip_norm_wip();
        let args = tcx.erase_and_anonymize_regions(trait_ref.args);
        let inst = Instance::try_resolve(tcx, a.env, method, args).ok()??;
        if inst.def != InstanceKind::Item(method) {
            return None;
        }
        Some(a.run_root(method, inst, mark, false))
    }

    /// `assume_requires`: analyse under the root's declared precondition (a root:
    /// its callers check it), or under none (an implementation checked against a
    /// contract: dynamic calls check no precondition).
    fn run_root(
        self,
        root: DefId,
        inst: Instance<'tcx>,
        mark: &Mark,
        assume_requires: bool,
    ) -> RootResult {
        let crates = self.crates;
        let mut a = self;
        a.owner_params = mark.params.clone();
        a.contract_impl = !assume_requires;
        // A root is analysed under its own precondition (checked at its callers).
        let ctx = crates
            .requires_of(root)
            .filter(|_| assume_requires)
            .map(|r| r.facts.clone())
            .unwrap_or_default();
        let r = a.node_in(inst, ctx, 0);
        while let Some(i) = a.queue.pop() {
            a.classify(i);
        }
        if std::env::var_os("FIP_PRELINT_DUMP").is_some() {
            a.dump();
        }
        let sums = a.evaluate();
        a.dump_args(&sums);
        RootResult {
            summary: sums[r].clone(),
            label: a.nodes[r].label.clone(),
            param_types: a.param_types.clone(),
            args: a.arg_violations(&sums),
        }
    }

    /// Declared parameter bounds at the call sites of one local function or closure
    /// body (identity arguments, its own typing environment). Only the arguments'
    /// entry points are explored, not the body's other callees, except the bodies of
    /// the `inferable` private functions it calls, bound to what it passes (top plan
    /// T4.3). Used for every local body that is not a root, so that callers which are
    /// not roots are checked.
    pub fn arguments_in(
        tcx: TyCtxt<'tcx>,
        crates: &'a Crates,
        owner: DefId,
        inferable: &HashSet<DefId>,
    ) -> Vec<ArgViolation> {
        let mut a = Analysis::new(tcx, crates, owner);
        // No node is being classified while the owner's body is read: its parameters
        // have no bindings.
        a.current = usize::MAX;
        let inst = a.identity(owner);
        let body = tcx.instance_mir(inst.def);
        for data in body.basic_blocks.iter() {
            if data.is_cleanup {
                continue;
            }
            let term = data.terminator();
            let (TerminatorKind::Call {
                func,
                args: call_args,
                ..
            }
            | TerminatorKind::TailCall {
                func,
                args: call_args,
                ..
            }) = &term.kind
            else {
                continue;
            };
            let Some(fty) = a.subst(inst, func.ty(&body.local_decls, tcx)) else {
                continue;
            };
            let ty::FnDef(def_id, args) = *fty.kind() else {
                continue;
            };
            let Some(args) = args.no_bound_vars() else {
                continue;
            };
            if let Ok(Some(callee)) = Instance::try_resolve(tcx, a.env, def_id, args) {
                a.note_arg_site(inst, body, term.source_info.span, callee, call_args);
                // A private function whose own call-site reports for its unbound
                // parameters are replaced by this call site (top plan T4.3): its body
                // is checked with what this call passes.
                // An inferable owner passing its own unbound parameter on is checked the
                // same way from its own call sites (the binding then reaches the callee).
                let passes_own = inferable.contains(&owner)
                    && call_args
                        .iter()
                        .any(|c| a.unbound_param(inst, body, &c.node));
                if !passes_own
                    && matches!(callee.def, InstanceKind::Item(d) if inferable.contains(&d))
                {
                    let binds = a.call_binds(inst, body, callee, call_args);
                    let i = a.node_bound(callee, Vec::new(), 0, binds);
                    let unknown = a.unknown_params(inst, body, callee, call_args);
                    a.entries.entry(i).or_insert_with(|| Via {
                        span: term.source_info.span,
                        private: def_path(tcx, callee.def_id()),
                        unknown,
                    });
                }
            } else if tcx.trait_of_assoc(def_id).is_some()
                && a.crates.contract_of(tcx, def_id).is_some()
            {
                // A call on `Self` or a type parameter that does not resolve here
                // costs the contract: its arguments are checked against the
                // contract's `param(..)` (top plan T5).
                let callee = Instance::new_raw(def_id, args);
                a.note_arg_site(inst, body, term.source_info.span, callee, call_args);
            }
        }
        if a.arg_sites.is_empty() && a.queue.is_empty() {
            return Vec::new();
        }
        while let Some(i) = a.queue.pop() {
            a.classify(i);
        }
        let sums = a.evaluate();
        a.dump_args(&sums);
        a.arg_violations(&sums)
    }

    /// The parameters of `callee` for which a call in `inst`'s body passes an
    /// unbound, undeclared parameter of the caller: `(callee's name, caller's name)`.
    fn unknown_params(
        &self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        callee: Instance<'tcx>,
        call_args: &[Spanned<Operand<'tcx>>],
    ) -> Vec<(String, String)> {
        let tcx = self.tcx;
        let name = |d: DefId, k: usize| {
            tcx.fn_arg_idents(d)
                .get(k)
                .copied()
                .flatten()
                .map_or_else(|| format!("#{k}"), |i| i.name.to_string())
        };
        let mut out = Vec::new();
        for (k, a) in call_args.iter().enumerate() {
            let callable = self
                .subst(inst, a.node.ty(&body.local_decls, tcx))
                .is_some_and(|t| self.is_callable_value(t));
            if !callable || !self.unbound_param(inst, body, &a.node) {
                continue;
            }
            let mut origin = origin_of(tcx, body, &a.node);
            if let Some(Origin::Ref(l)) = origin {
                origin = origin_of(tcx, body, &Operand::Copy(mir::Place::from(l)));
            }
            if let Some(Origin::Arg(l)) = origin {
                out.push((
                    name(callee.def_id(), k),
                    name(inst.def_id(), l.as_usize() - 1),
                ));
            }
        }
        out
    }

    /// Value-parameter names of the root's parameters whose type is a generic
    /// parameter (`g: F`, `g: &F`, `g: impl Fn(..)`), keyed by the type parameter.
    fn collect_param_names(&mut self, root: DefId) {
        let tcx = self.tcx;
        if !matches!(tcx.def_kind(root), DefKind::Fn | DefKind::AssocFn) {
            return;
        }
        let sig = tcx.fn_sig(root).skip_binder().skip_binder();
        let idents = tcx.fn_arg_idents(root);
        for (i, input) in sig.inputs().iter().enumerate() {
            if let ty::Param(p) = input.peel_refs().kind()
                && let Some(Some(ident)) = idents.get(i)
            {
                self.param_names.insert(p.index, ident.name.to_string());
                self.param_types
                    .push((ident.name.to_string(), p.name.to_string()));
            }
        }
    }

    fn label(&self, inst: Instance<'tcx>) -> String {
        match inst.def {
            InstanceKind::Item(def_id) => def_path_args(self.tcx, def_id, inst.args),
            InstanceKind::Shim(ShimKind::DropGlue(_, Some(ty))) => {
                with_no_visible_paths!(with_no_trimmed_paths!(format!("drop glue of {ty}")))
            }
            InstanceKind::Intrinsic(def_id) | InstanceKind::LlvmIntrinsic(def_id) => {
                format!("{} (intrinsic)", def_path_args(self.tcx, def_id, inst.args))
            }
            InstanceKind::Virtual(def_id, _) => {
                format!("{} (virtual)", def_path_args(self.tcx, def_id, inst.args))
            }
            InstanceKind::Shim(_) => format!(
                "{} (shim)",
                def_path_args(self.tcx, inst.def_id(), inst.args)
            ),
        }
    }

    fn node_for(&mut self, inst: Instance<'tcx>) -> usize {
        self.node_in(inst, Vec::new(), 0)
    }

    /// The node of `inst` entered in context `ctx` (facts over its parameters).
    fn node_in(&mut self, inst: Instance<'tcx>, ctx: Vec<Fact>, depth: u8) -> usize {
        self.node_bound(inst, ctx, depth, Vec::new())
    }

    /// The node of `inst` entered in context `ctx` with its parameters bound to
    /// `binds`.
    fn node_bound(
        &mut self,
        inst: Instance<'tcx>,
        ctx: Vec<Fact>,
        depth: u8,
        binds: Binds<'tcx>,
    ) -> usize {
        let key = (inst, ctx, binds);
        if let Some(&i) = self.index.get(&key) {
            return i;
        }
        let i = self.nodes.len();
        let label = self.label(inst);
        let parent = (i > 0 && self.current < i).then_some(self.current);
        self.nodes.push(Node {
            inst,
            ctx: key.1.clone(),
            depth,
            binds: key.2.clone(),
            parent,
            label,
            kind: NodeKind::Pending,
        });
        self.index.insert(key, i);
        self.queue.push(i);
        i
    }
    fn node_contract(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>, m: &Mark) -> usize {
        let inst = Instance::new_raw(def_id, args);
        let key = (inst, Vec::new(), Vec::new());
        if let Some(&i) = self.index.get(&key) {
            return i;
        }
        let i = self.nodes.len();
        let label = self.label(inst);
        let parent = (i > 0 && self.current < i).then_some(self.current);
        let evs = contract_call_events(&format!("call of `{}`", def_path(self.tcx, def_id)), m);
        self.nodes.push(Node {
            inst,
            ctx: Vec::new(),
            depth: 0,
            binds: Vec::new(),
            parent,
            label,
            kind: NodeKind::Leaf(evs),
        });
        self.index.insert(key, i);
        i
    }

    fn subst<T: TypeFoldable<TyCtxt<'tcx>>>(&self, inst: Instance<'tcx>, v: T) -> Option<T> {
        inst.try_instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            self.env,
            EarlyBinder::bind(self.tcx, v),
        )
        .ok()
    }

    fn classify(&mut self, i: usize) {
        if self.nodes.len() > MAX_NODES {
            self.nodes[i].kind = NodeKind::Leaf(vec![Ev::Unknown(format!(
                "analysis limit ({MAX_NODES} instances) reached at `{}`",
                self.nodes[i].label
            ))]);
            return;
        }
        let inst = self.nodes[i].inst;
        self.current = i;
        let tcx = self.tcx;
        let kind = match inst.def {
            InstanceKind::Item(def_id) => self.classify_item(inst, def_id),
            InstanceKind::Intrinsic(def_id) => self.classify_intrinsic(inst, def_id),
            InstanceKind::LlvmIntrinsic(def_id) => NodeKind::Leaf(vec![Ev::Unknown(format!(
                "LLVM intrinsic `{}`",
                def_path(tcx, def_id)
            ))]),
            // A dynamic call of a source's trait method is that source in every
            // implementation (declared on the trait, or an allocator trait). A
            // dynamic call of a method whose declaration carries a contract costs the
            // contract (every implementation is checked against it); any other
            // dynamic call is `⊤`.
            InstanceKind::Virtual(def_id, _) => match self.source_leaf(def_id) {
                Some(leaf) => leaf,
                None => match self.crates.contract_of(tcx, def_id) {
                    Some(m) => {
                        let path = def_path(tcx, def_id);
                        let mut evs = contract_events(&path, m);
                        // The contract is assumed for the implementation being
                        // checked as well: without this, a cycle through dynamic
                        // calls would be assumed away on both sides.
                        if self.contract_impl && m.kind != marks::Kind::Fbip {
                            evs.push(Ev::Recurse(format!(
                                "dynamic call of `{path}` inside an implementation checked against a contract: it may call this implementation again"
                            )));
                        }
                        NodeKind::Leaf(evs)
                    }
                    None => NodeKind::Leaf(vec![Ev::Unknown(format!(
                        "dynamic call to `{}` (trait object)",
                        def_path_args(tcx, def_id, inst.args)
                    ))]),
                },
            },
            InstanceKind::Shim(ShimKind::DropGlue(_, None)) => NodeKind::Leaf(Vec::new()),
            InstanceKind::Shim(ShimKind::DropGlue(_, Some(ty)))
                if matches!(ty.kind(), ty::Param(_)) =>
            {
                NodeKind::Leaf(vec![Ev::Unknown(format!(
                    "drop glue of the type parameter `{ty}`"
                ))])
            }
            InstanceKind::Shim(
                ShimKind::ThreadLocal(_)
                | ShimKind::FutureDropPoll(..)
                | ShimKind::AsyncDropGlue(..)
                | ShimKind::AsyncDropGlueCtor(..)
                | ShimKind::ConstructCoroutineInClosure { .. },
            ) => NodeKind::Leaf(vec![Ev::Unknown(format!(
                "unsupported shim `{}`",
                self.nodes[i].label
            ))]),
            // rustc builds a polymorphic drop shim in the typing environment of
            // `drop_in_place`, which lacks the root's bounds and the types of its
            // const parameters; it may fail with an internal compiler error there
            // (measured: a field `[Vec<T>; N]`). Such a drop is `⊤`, never an abort.
            InstanceKind::Shim(ShimKind::DropGlue(_, Some(ty))) if ty.has_param() => {
                match self.polymorphic_shim(inst) {
                    Some(body) => NodeKind::Body(self.scan_body(inst, body)),
                    None => NodeKind::Leaf(vec![Ev::Unknown(format!(
                        "drop glue of `{ty}`: rustc cannot build its drop shim for the generic type (internal compiler error caught)"
                    ))]),
                }
            }
            InstanceKind::Shim(_) => {
                let body = tcx.instance_mir(inst.def);
                NodeKind::Body(self.scan_body(inst, body))
            }
        };
        self.nodes[i].kind = kind;
    }

    /// The MIR of a drop shim whose type mentions a generic parameter, or `None` if
    /// rustc panics while building it (an internal compiler error). The panic is
    /// caught with rustc's panic hook (backtrace, ICE file) suspended; a failed query
    /// stays poisoned, and asking for it again panics again, which is caught the same
    /// way.
    fn polymorphic_shim(&self, inst: Instance<'tcx>) -> Option<&'tcx Body<'tcx>> {
        let tcx = self.tcx;
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let body =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tcx.instance_mir(inst.def)));
        std::panic::set_hook(hook);
        body.ok()
    }

    fn classify_intrinsic(&mut self, inst: Instance<'tcx>, def_id: DefId) -> NodeKind {
        let tcx = self.tcx;
        let name = tcx.item_name(def_id);
        let name = name.as_str();
        if name == "const_eval_select" {
            // `const_eval_select(args, const_fn, rt_fn)`: at run time `rt_fn` runs.
            if let Some(rt) = inst.args.types().nth(2)
                && let ty::FnDef(d, a) = *rt.kind()
                && let Some(a) = a.no_bound_vars()
            {
                let item = self.resolve(d, a);
                return NodeKind::Body(BodyInfo {
                    blocks: vec![vec![Site {
                        item,
                        span: DUMMY_SP,
                    }]],
                    succ: vec![Vec::new()],
                    reachable: vec![true],
                    in_loop: vec![false],
                });
            }
        }
        if rules::is_alloc_free_intrinsic(name) {
            return NodeKind::Leaf(Vec::new());
        }
        if rules::is_panic_intrinsic(name) {
            return NodeKind::Leaf(vec![Ev::Panic(format!("intrinsic `{name}`"))]);
        }
        NodeKind::Leaf(vec![Ev::Unknown(format!(
            "intrinsic `{name}` (not in `fip_lint_rules::mir::ALLOC_FREE_INTRINSICS`)"
        ))])
    }

    /// A source (see [`Crates::source_of`]) is an opaque boundary: a leaf with exactly
    /// the declared events, `n` allocations and/or a possible free. Its body is never
    /// analysed, so nothing inside it (bookkeeping, a backing allocator, loops,
    /// recursion, panics, `⊤`) is reported.
    fn source_leaf(&self, def_id: DefId) -> Option<NodeKind> {
        let tcx = self.tcx;
        let (s, kind) = self.crates.source_of(tcx, def_id)?;
        let path = def_path(tcx, def_id);
        let why = kind.describe();
        let mut evs = Vec::new();
        let count = if s.alloc > 1 {
            format!(" (n = {})", s.alloc)
        } else {
            String::new()
        };
        for _ in 0..s.alloc {
            evs.push(Ev::Alloc(format!("allocation: {why} `{path}`{count}")));
        }
        if s.free {
            evs.push(Ev::Free(format!("free: {why} `{path}`")));
        }
        Some(NodeKind::Leaf(evs))
    }

    fn classify_item(&mut self, inst: Instance<'tcx>, def_id: DefId) -> NodeKind {
        let tcx = self.tcx;
        if let Some(leaf) = self.source_leaf(def_id) {
            return leaf;
        }
        let path = def_path(tcx, def_id);
        // Path tables name standard-library items only (see `std_path`).
        let std = std_path(tcx, def_id);
        if rules::is_realloc_entry(&std) {
            return NodeKind::Leaf(vec![
                Ev::Alloc(format!("reallocation `{path}`")),
                Ev::Free(format!("reallocation `{path}`")),
            ]);
        }
        if rules::is_alloc_entry(&std) {
            return NodeKind::Leaf(vec![Ev::Alloc(format!("allocation `{path}`"))]);
        }
        if rules::is_dealloc_entry(&std) {
            return NodeKind::Leaf(vec![Ev::Free(format!("deallocation `{path}`"))]);
        }
        if rules::is_panic_entry(&std) {
            return NodeKind::Leaf(vec![Ev::Panic(format!("`{path}`"))]);
        }
        if rules::is_ub_check(&std) {
            return NodeKind::Leaf(Vec::new());
        }
        if matches!(tcx.def_kind(def_id), DefKind::Ctor(..)) {
            return NodeKind::Leaf(Vec::new());
        }
        if tcx.is_foreign_item(def_id) {
            // By link symbol (`#[link_name]`), like the marks: the Rust name of a
            // foreign declaration outside `std` says nothing about what it binds.
            let name = foreign_table_name(tcx, def_id);
            let name = name.as_str();
            if rules::is_realloc_entry(name) {
                return NodeKind::Leaf(vec![
                    Ev::Alloc(format!("reallocation `{name}`")),
                    Ev::Free(format!("reallocation `{name}`")),
                ]);
            }
            if rules::is_alloc_entry(name) {
                return NodeKind::Leaf(vec![Ev::Alloc(format!("allocation `{name}`"))]);
            }
            if rules::is_dealloc_entry(name) {
                return NodeKind::Leaf(vec![Ev::Free(format!("deallocation `{name}`"))]);
            }
            if rules::is_alloc_free_symbol(name) {
                return NodeKind::Leaf(Vec::new());
            }
            // Generating std summaries: the seed has no marks; the call is the term
            // `§ffi <symbol> <abi>`, resolved with the marks of the crate that uses
            // the summary ([`Analysis::resolve_term`]).
            if self.crates.generating {
                let key = format!("§ffi {} {}", ffi_symbol(tcx, def_id), ffi_abi(tcx, def_id));
                return NodeKind::Body(BodyInfo {
                    blocks: vec![vec![Site {
                        item: Item::Term(key),
                        span: DUMMY_SP,
                    }]],
                    succ: vec![Vec::new()],
                    reachable: vec![true],
                    in_loop: vec![false],
                });
            }
            // Marks apply by link symbol, so a declaration in `std`, `libc` or any
            // dependency is covered by a mark on a declaration in the user's crate.
            let symbol = ffi_symbol(tcx, def_id);
            let sym_note = if def_id.is_local() {
                String::new()
            } else {
                format!(" (symbol `{symbol}`)")
            };
            let msg = match self.crates.ffi_verdict(tcx, def_id) {
                FfiVerdict::Cert(c) => {
                    let mut evs = Vec::new();
                    let count = if c.alloc > 1 {
                        format!(" (n = {})", c.alloc)
                    } else {
                        String::new()
                    };
                    for _ in 0..c.alloc {
                        evs.push(Ev::Alloc(format!(
                            "allocation: certified foreign function `{path}`{count}"
                        )));
                    }
                    if c.free {
                        evs.push(Ev::Free(format!(
                            "free: certified foreign function `{path}`"
                        )));
                    }
                    return NodeKind::Leaf(evs);
                }
                FfiVerdict::Excluded => return NodeKind::Leaf(Vec::new()),
                FfiVerdict::Neither => {
                    format!("foreign function `{path}`{sym_note} is neither certified nor excluded")
                }
                FfiVerdict::Both => {
                    format!("foreign function `{path}`{sym_note} is both certified and excluded")
                }
                FfiVerdict::Conflict => format!(
                    "foreign function `{path}`: its symbol `{symbol}` has certificates with different properties"
                ),
                FfiVerdict::Abi { marked, marked_abi } => format!(
                    "foreign function `{path}` is declared `extern {}`, but its symbol `{symbol}` is marked on `{}`, declared `extern {marked_abi}`: marks do not apply across ABIs",
                    ffi_abi(tcx, def_id),
                    tcx.def_path_str(marked)
                ),
            };
            return NodeKind::Leaf(vec![Ev::Unknown(format!("ffi:{msg}"))]);
        }
        let crate_name = tcx.crate_name(def_id.krate);
        let crate_name = crate_name.as_str();
        let std_like = is_std_like(tcx, def_id.krate);
        if !std_like && !self.crates.exported(def_id.krate) {
            return NodeKind::Leaf(vec![Ev::Unknown(format!(
                "`{path}` (crate `{crate_name}` does not declare `fip::export`)"
            ))]);
        }
        if std_like && self.diverges(def_id) {
            return NodeKind::Leaf(vec![Ev::Panic(format!("`{path}` (diverges)"))]);
        }
        if !tcx.is_mir_available(def_id) {
            let why = if std_like {
                match &self.crates.std_summaries {
                    Ok(sc) => match sc.fns.get(&path) {
                        Some(s) => return self.summary_node(&path, s),
                        None => "no MIR: not generic and not #[inline]; not in the std summaries"
                            .to_string(),
                    },
                    Err(e) => format!(
                        "no MIR: not generic and not #[inline]; std summaries not used: {e}"
                    ),
                }
            } else {
                "no MIR although the crate declares `fip::export`: it was built without `-Zalways-encode-mir`".to_string()
            };
            return NodeKind::Leaf(vec![Ev::Unknown(format!("`{path}` ({why})"))]);
        }
        let body = tcx.instance_mir(inst.def);
        NodeKind::Body(self.scan_body(inst, body))
    }

    /// A standard-library function without MIR, from its generated summary
    /// ([`crate::stdsum`]): its events, and its open calls through parameters
    /// resolved with this node's bindings (`⊤` where they are not known). Calls with
    /// multiplicity `∞` sit in a loop block.
    fn summary_node(&mut self, path: &str, s: &crate::stdsum::FnSummary) -> NodeKind {
        use crate::stdsum::Count;
        let mut once: Vec<Site> = Vec::new();
        let mut looped: Vec<Site> = Vec::new();
        let site = |item| Site {
            item,
            span: DUMMY_SP,
        };
        let w = |what: &str| format!("std summary of `{path}`: {what}");
        match s.alloc {
            Count::Fin(0) => {}
            Count::Fin(n) => once.push(site(Item::Ev(Ev::Bound(n, w("allocation"))))),
            Count::Inf => looped.push(site(Item::Ev(Ev::Alloc(w("allocation"))))),
        }
        for f in &s.free {
            once.push(site(Item::Ev(Ev::Free(w(f)))));
        }
        for f in &s.panic {
            once.push(site(Item::Ev(Ev::Panic(w(f)))));
        }
        for f in &s.top {
            once.push(site(Item::Ev(Ev::Unknown(w(f)))));
        }
        if let Some(r) = &s.recursion {
            once.push(site(Item::Ev(Ev::Recurse(w(r)))));
        }
        for (mult, key) in &s.terms {
            let items = self.resolve_term(path, key);
            match mult {
                Count::Fin(k) if *k <= 16 => {
                    for _ in 0..*k {
                        once.extend(items.iter().cloned().map(site));
                    }
                }
                _ => looped.extend(items.into_iter().map(site)),
            }
        }
        NodeKind::Body(BodyInfo {
            blocks: vec![once, looped],
            succ: vec![vec![1], vec![1]],
            reachable: vec![true, true],
            in_loop: vec![false, true],
        })
    }

    /// The calls a summary term stands for, from this node's bindings.
    fn resolve_term(&mut self, path: &str, key: &str) -> Vec<Item> {
        let unknown = |why: String| {
            vec![Item::Ev(Ev::Unknown(format!(
                "std summary of `{path}`: {why} (`{key}`)"
            )))]
        };
        let parts: Vec<&str> = key.split(' ').collect();
        let param_local = |i: &str| {
            i.parse::<u32>()
                .ok()
                .and_then(|i| i.checked_add(1))
                .map(mir::Local::from_u32)
        };
        match parts.as_slice() {
            ["§out", i, method] => {
                let Some(l) = param_local(i) else {
                    return unknown("malformed term".to_string());
                };
                let Some(out) = self.out_param(l) else {
                    return unknown("the output it writes to is not known here".to_string());
                };
                let Some(m) = self.trait_method_by_path(method) else {
                    return unknown(format!("trait method `{method}` not found"));
                };
                match self.out_method(m, &out) {
                    Some(item) => vec![item],
                    None => unknown(format!(
                        "`{method}` for `{}` does not resolve",
                        out_desc(&out)
                    )),
                }
            }
            ["§fmt", i, "out", what @ ..] => {
                let Some(l) = param_local(i) else {
                    return unknown("malformed term".to_string());
                };
                let (fns, params) = match self.bind_of(l) {
                    Some(Bind::Fmt(f, p)) => (f, p),
                    _ => {
                        return unknown(
                            "the formatting functions it calls are not known here".to_string(),
                        );
                    }
                };
                if !params.is_empty() {
                    return unknown(
                        "the formatting functions it calls are not known here".to_string(),
                    );
                }
                let out = match self.parse_out(what) {
                    Ok(o) => o,
                    Err(why) => return unknown(why),
                };
                fns.into_iter()
                    .map(|f| self.formatter_item(f, &out))
                    .collect()
            }
            // A dynamic call on the `&dyn Debug`/`&dyn Display` parameter `i` with a
            // `Formatter` writing to `out` (top plan T7a): the method of the concrete
            // type the parameter is bound to here.
            ["§dyn", i, method, "fmt", what @ ..] => {
                let Some(l) = param_local(i) else {
                    return unknown("malformed term".to_string());
                };
                let t = match self.bind_of(l) {
                    Some(Bind::Obj(Obj::Ty(t))) => t,
                    _ => {
                        return unknown(
                            "the value it formats is not known here (a `dyn` value of unknown origin)"
                                .to_string(),
                        );
                    }
                };
                let out = match self.parse_out(what) {
                    Ok(o) => o,
                    Err(why) => return unknown(why),
                };
                let Some(m) = self.trait_method_by_path(method) else {
                    return unknown(format!("trait method `{method}` not found"));
                };
                let args = self.tcx.mk_args(&[t.into()]);
                match Instance::try_resolve(self.tcx, self.env, m, args) {
                    Ok(Some(c)) if !matches!(c.def, InstanceKind::Virtual(..)) => {
                        // `fn fmt(&self, f: &mut Formatter)`: the formatter is local 2.
                        let binds = vec![(2, Bind::Formatter(out))];
                        vec![Item::Call(self.node_bound(c, Vec::new(), 0, binds))]
                    }
                    _ => unknown(format!("`{method}` for `{t}` does not resolve")),
                }
            }
            // A foreign call inside the summarised function: the verdict of this
            // crate's FFI marks for its link symbol and ABI, as for a direct call.
            ["§ffi", symbol, abi] => self.ffi_term(path, symbol, abi),
            _ => unknown("unknown term".to_string()),
        }
    }

    /// The events of the foreign call `§ffi <symbol> <abi>` inside the std summary of
    /// `path`: a certificate's events, nothing for an exclusion (both listed in the
    /// crate summary), else the FFI error (neither certified nor excluded, both,
    /// conflicting certificates, another ABI) naming the summarised function.
    fn ffi_term(&mut self, path: &str, symbol: &str, abi: &str) -> Vec<Item> {
        let tcx = self.tcx;
        let inside = format!("called inside `{path}` (std summary)");
        let msg = match self.crates.ffi_verdict_std(tcx, path, symbol, abi) {
            FfiVerdict::Cert(c) => {
                let count = if c.alloc > 1 {
                    format!(" (n = {})", c.alloc)
                } else {
                    String::new()
                };
                let mut items = Vec::new();
                for _ in 0..c.alloc {
                    items.push(Item::Ev(Ev::Alloc(format!(
                        "allocation: certified foreign function `{symbol}`{count}, {inside}"
                    ))));
                }
                if c.free {
                    items.push(Item::Ev(Ev::Free(format!(
                        "free: certified foreign function `{symbol}`, {inside}"
                    ))));
                }
                return items;
            }
            FfiVerdict::Excluded => return Vec::new(),
            FfiVerdict::Neither => format!(
                "foreign function `{symbol}` (`extern {abi}`), {inside}, is neither certified nor excluded"
            ),
            FfiVerdict::Both => format!(
                "foreign function `{symbol}` (`extern {abi}`), {inside}, is both certified and excluded"
            ),
            FfiVerdict::Conflict => format!(
                "foreign function `{symbol}`, {inside}: its symbol has certificates with different properties"
            ),
            FfiVerdict::Abi { marked, marked_abi } => format!(
                "foreign function `{symbol}`, {inside}, is declared `extern {abi}`, but its symbol is marked on `{}`, declared `extern {marked_abi}`: marks do not apply across ABIs",
                tcx.def_path_str(marked)
            ),
        };
        vec![Item::Ev(Ev::Unknown(format!("ffi:{msg}")))]
    }

    /// The output a summary term names ([`out_desc`]): `param <j>` (what this node's
    /// parameter `j` writes to), `pad <out>` (a `PadAdapter` over `out`), or `ty
    /// alloc::string::String`.
    fn parse_out(&self, what: &[&str]) -> Result<Out<'tcx>, String> {
        let not_known = || "the output it writes to is not known here".to_string();
        match what {
            ["param", j] => {
                let l = j
                    .parse::<u32>()
                    .ok()
                    .and_then(|j| j.checked_add(1))
                    .map(mir::Local::from_u32)
                    .ok_or_else(|| "malformed term".to_string())?;
                self.out_param(l).ok_or_else(not_known)
            }
            ["pad", rest @ ..] => Ok(Out::Pad(Box::new(self.parse_out(rest)?))),
            ["ty", rest @ ..] if rest.join(" ") == "alloc::string::String" => {
                match self.tcx.lang_items().string() {
                    Some(d) => Ok(Out::Ty(
                        self.tcx.type_of(d).instantiate_identity().skip_norm_wip(),
                    )),
                    None => Err("`String` not found".to_string()),
                }
            }
            _ => Err("the output type is not supported".to_string()),
        }
    }

    /// The `fmt::Write` method `m` (without generic parameters of its own) of the
    /// output `out`: of its type, or of the `PadAdapter` over an output. `None` for a
    /// parameter's output or a method that does not resolve.
    fn out_method(&mut self, m: DefId, out: &Out<'tcx>) -> Option<Item> {
        match out {
            Out::Ty(t) => {
                let args = self.tcx.mk_args(&[(*t).into()]);
                match Instance::try_resolve(self.tcx, self.env, m, args) {
                    Ok(Some(c)) if !matches!(c.def, InstanceKind::Virtual(..)) => {
                        Some(Item::Call(self.node_for(c)))
                    }
                    _ => None,
                }
            }
            Out::Pad(inner) => self.pad_call(m, std::iter::empty(), inner),
            Out::Param(_) => None,
        }
    }

    /// The trait method with the definition path `path` (e.g.
    /// `core::fmt::Write::write_str`).
    fn trait_method_by_path(&self, path: &str) -> Option<DefId> {
        let (tr, name) = path.rsplit_once("::")?;
        let tcx = self.tcx;
        tcx.all_traits_including_private()
            .find(|d| def_path(tcx, *d) == tr)
            .and_then(|t| {
                tcx.associated_items(t)
                    .in_definition_order()
                    .find(|m| m.is_fn() && tcx.item_name(m.def_id).as_str() == name)
                    .map(|m| m.def_id)
            })
    }

    fn diverges(&self, def_id: DefId) -> bool {
        matches!(self.tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
            && self
                .tcx
                .fn_sig(def_id)
                .skip_binder()
                .skip_binder()
                .output()
                .is_never()
    }

    fn scan_body(&mut self, inst: Instance<'tcx>, body: &'tcx Body<'tcx>) -> BodyInfo {
        let tcx = self.tcx;
        let env = self.env;
        let n = body.basic_blocks.len();
        let mut blocks: Vec<Vec<Site>> = (0..n).map(|_| Vec::new()).collect();
        let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
        // Asserts proved unable to fire and blocks no feasible path reaches, by the
        // value analysis (run only on bodies with an `Assert` or a `SwitchInt` on a
        // comparison).
        let (ctx, depth) = {
            let node = &self.nodes[self.current];
            (node.ctx.clone(), node.depth)
        };
        let proved = crate::value::analyse(tcx, env, inst, body, &self.vsums, &ctx);
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            let b = bb.as_usize();
            // No execution reaches the terminator of a dead block, nor its successors
            // through it: its sites are not counted and its edges are not followed.
            if proved.dead(b) {
                continue;
            }
            let term = data.terminator();
            succ[b] = term
                .successors()
                .filter(|s| !body.basic_blocks[*s].is_cleanup)
                .map(|s| s.as_usize())
                .collect();
            // A function with `fip::requires(..)` taken as a value: the calls through
            // it cannot be checked.
            for st in &data.statements {
                if let mir::StatementKind::Assign(assign) = &st.kind {
                    for op in rvalue_operands(&assign.1) {
                        self.reified(inst, body, op, st.source_info.span, &mut blocks[b]);
                    }
                }
            }
            let span = term.source_info.span;
            match &term.kind {
                TerminatorKind::Call { func, args, .. }
                | TerminatorKind::TailCall { func, args, .. } => {
                    let here = proved.contexts.get(&b);
                    let item = self.call_item(inst, body, func, args, here, depth);
                    // The callees of this call: one, or the candidates of a pointer
                    // loaded from a static table (each checked as if called here).
                    let callees = match &item {
                        Item::Call(_) | Item::Alt(_) => item.calls(),
                        _ => Vec::new(),
                    };
                    // A direct call of a function item from a Verus-verified body.
                    if let Item::Call(j) = &item
                        && let Some((fd, _)) = func.const_fn_def()
                        && self.nodes[*j].inst.def == InstanceKind::Item(fd)
                        && let InstanceKind::Item(caller) = inst.def
                        && let Some(listed) = self.crates.verus.is_listed(tcx, caller, body.span)
                    {
                        self.verus_direct.insert((self.current, *j, span), listed);
                    }
                    for j in callees {
                        // Call sites in analysed crates (local, `fip::export`) are
                        // checked against the callee's declared parameter bounds.
                        let callee = self.nodes[j].inst;
                        if matches!(inst.def, InstanceKind::Item(_))
                            && self.crates.exported(inst.def_id().krate)
                        {
                            self.note_arg_site(inst, body, span, callee, args);
                        }
                        // And against its declared precondition: the state here must
                        // entail it, else the call is a panic path (a broken contract).
                        if let InstanceKind::Item(d) = callee.def
                            && let Some(req) = self.crates.requires_of(d)
                            && !here.is_some_and(|c| crate::value::entails(c, &req.facts))
                        {
                            blocks[b].push(Site {
                                item: Item::Ev(Ev::Panic(format!(
                                    "precondition `{}` of `{}` not established at this call",
                                    req.text,
                                    def_path(tcx, d)
                                ))),
                                span,
                            });
                        }
                    }
                    for a in args.iter() {
                        self.reified(inst, body, &a.node, span, &mut blocks[b]);
                    }
                    match item {
                        Item::Many(items) => {
                            blocks[b].extend(items.into_iter().map(|item| Site { item, span }));
                        }
                        item => blocks[b].push(Site { item, span }),
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    let ty = place.ty(&body.local_decls, tcx).ty;
                    match self.subst(inst, ty) {
                        Some(ty) if ty.needs_drop(tcx, self.env) => {
                            // A drop runs its drop glue, analysed like a callee: it
                            // frees exactly when the glue reaches a deallocation, a
                            // free source or `⊤`. Glue of a type that mentions a
                            // generic parameter is analysed field by field in the
                            // root's typing environment; only the drop of a bare
                            // parameter frees for some instantiations only: the
                            // term `drop(T)`.
                            let item = self.drop_item(ty);
                            blocks[b].push(Site { item, span });
                        }
                        Some(_) => {}
                        None => blocks[b].push(Site {
                            item: Item::Ev(Ev::Unknown(format!(
                                "drop of `{ty}` (type not normalizable)"
                            ))),
                            span,
                        }),
                    }
                }
                TerminatorKind::Assert {
                    cond,
                    expected,
                    msg,
                    ..
                } => {
                    let cannot_fire = self
                        .eval_in_block(data, cond)
                        .is_some_and(|v| (v != 0) == *expected)
                        || proved.assert_cannot_fire(b)
                        || (matches!(**msg, AssertKind::Overflow(mir::BinOp::Add, ..))
                            && crate::value::enumerate_count_cannot_overflow(tcx, inst));
                    if !cannot_fire && !is_ub_check_assert(msg) {
                        // A body-local site of a Verus-verified function (top plan
                        // T13.4): discharged under its `requires`, which becomes its
                        // callers' obligation; else kept, with the reason if its
                        // package declares a Verus sidecar.
                        let verdict = match inst.def {
                            InstanceKind::Item(d) => {
                                self.crates.verus.site(tcx, d, body.span, span)
                            }
                            _ => crate::verustrust::SiteVerdict::Kept(None),
                        };
                        match verdict {
                            crate::verustrust::SiteVerdict::Discharged(Some(f)) => {
                                blocks[b].push(Site {
                                    item: Item::Ev(Ev::VerusPre(f)),
                                    span,
                                });
                            }
                            crate::verustrust::SiteVerdict::Discharged(None) => {}
                            crate::verustrust::SiteVerdict::Kept(why) => {
                                let what = match why {
                                    Some(why) => format!(
                                        "{} (not discharged by Verus: {why})",
                                        describe_assert(msg)
                                    ),
                                    None => describe_assert(msg),
                                };
                                blocks[b].push(Site {
                                    item: Item::Ev(Ev::Panic(what)),
                                    span,
                                });
                            }
                        }
                    }
                }
                TerminatorKind::InlineAsm { .. } => blocks[b].push(Site {
                    item: Item::Ev(Ev::Unknown("inline assembly".to_string())),
                    span,
                }),
                _ => {}
            }
        }
        // Reachability from the entry over non-cleanup edges.
        let mut reachable = vec![false; n];
        let mut work = vec![0usize];
        while let Some(b) = work.pop() {
            if b >= n || reachable[b] {
                continue;
            }
            reachable[b] = true;
            work.extend(succ[b].iter().copied());
        }
        for b in 0..n {
            if !reachable[b] {
                succ[b].clear();
                blocks[b].clear();
            }
        }
        let mut in_loop = vec![false; n];
        for comp in tarjan(n, &succ) {
            let cyclic = comp.len() > 1 || succ[comp[0]].contains(&comp[0]);
            if cyclic {
                for b in comp {
                    in_loop[b] = true;
                }
            }
        }
        BodyInfo {
            blocks,
            succ,
            reachable,
            in_loop,
        }
    }

    /// Value of `op` if it is a constant, or a local assigned in `data` (before the
    /// terminator) from constants by `IntToInt` casts and unsigned comparisons. Used
    /// to drop `Assert`s that cannot fire at opt-level 0 (`x >> 1` checks `1 < 32`).
    fn eval_in_block(&self, data: &mir::BasicBlockData<'tcx>, op: &Operand<'tcx>) -> Option<u128> {
        let mut known: HashMap<mir::Local, u128> = HashMap::new();
        let tcx = self.tcx;
        let eval_op = |known: &HashMap<mir::Local, u128>, o: &Operand<'tcx>| -> Option<u128> {
            match o {
                Operand::Constant(c) => c.const_.try_eval_bits(tcx, self.env),
                Operand::Copy(p) | Operand::Move(p) => {
                    p.as_local().and_then(|l| known.get(&l).copied())
                }
                _ => None,
            }
        };
        for st in &data.statements {
            let mir::StatementKind::Assign(assign) = &st.kind else {
                continue;
            };
            let (place, rv) = &**assign;
            let Some(local) = place.as_local() else {
                continue;
            };
            known.remove(&local);
            let v = match rv {
                mir::Rvalue::Use(o, ..) => match o {
                    Operand::Constant(c) if c.const_.ty().is_signed() => None,
                    _ => eval_op(&known, o),
                },
                // Only casts of constants to unsigned types: no sign extension.
                mir::Rvalue::Cast(mir::CastKind::IntToInt, Operand::Constant(c), to)
                    if to.is_integral() && !to.is_signed() =>
                {
                    let size_of = |t: Ty<'tcx>| {
                        tcx.layout_of(self.env.as_query_input(t))
                            .ok()
                            .map(|l| l.size)
                    };
                    let from = c.const_.ty();
                    match (
                        c.const_.try_eval_bits(tcx, self.env),
                        size_of(from),
                        size_of(*to),
                    ) {
                        (Some(v), Some(fs), Some(ts)) if !from.is_signed() || ts <= fs => {
                            Some(ts.truncate(v))
                        }
                        _ => None,
                    }
                }
                mir::Rvalue::BinaryOp(op, ops) => {
                    let (a, b) = &**ops;
                    let unsigned = |o: &Operand<'tcx>| match o {
                        Operand::Constant(c) => !c.const_.ty().is_signed(),
                        _ => true,
                    };
                    match (eval_op(&known, a), eval_op(&known, b)) {
                        (Some(x), Some(y)) if unsigned(a) && unsigned(b) => match op {
                            mir::BinOp::Lt => Some(u128::from(x < y)),
                            mir::BinOp::Le => Some(u128::from(x <= y)),
                            mir::BinOp::Gt => Some(u128::from(x > y)),
                            mir::BinOp::Ge => Some(u128::from(x >= y)),
                            mir::BinOp::Eq => Some(u128::from(x == y)),
                            mir::BinOp::Ne => Some(u128::from(x != y)),
                            _ => None,
                        },
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(v) = v {
                known.insert(local, v);
            }
        }
        eval_op(&known, op)
    }

    /// The callee of a call in `inst`'s body. A callee whose body may use it
    /// (`Summaries::wants_context`) is entered in the context `here` (the caller's
    /// state projected onto the arguments), unless contexts are nested
    /// [`MAX_CONTEXT_DEPTH`] deep or the call is direct recursion. A call through a
    /// function pointer, and a dynamic call, is resolved when the pointer comes from
    /// one function (or one concrete type) on every path in this body
    /// ([`origin_of`]), or is a parameter declared `param(g = K)`.
    fn call_item(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        here: Option<&Vec<Fact>>,
        depth: u8,
    ) -> Item {
        let fty = func.ty(&body.local_decls, self.tcx);
        let Some(fty) = self.subst(inst, fty) else {
            return Item::Ev(Ev::Unknown(format!(
                "callee of type `{fty}` (not normalizable)"
            )));
        };
        // Inside `<Certified<N, fn(..)> as FipFn<A>>::call`: the call of the held
        // pointer (`Fn::call` of the pointer type, or a direct pointer call) costs
        // the certificate (top plan T1.4).
        let pointer_call = match *fty.kind() {
            ty::FnPtr(..) => true,
            ty::FnDef(d, a) => {
                self.tcx
                    .trait_of_assoc(d)
                    .is_some_and(|t| self.tcx.fn_trait_kind_from_def_id(t).is_some())
                    && a.no_bound_vars()
                        .and_then(|a| a.first())
                        .and_then(|g| g.as_type())
                        .is_some_and(|t| t.is_fn_ptr())
            }
            _ => false,
        };
        if pointer_call && let Some(item) = self.certified_call(inst) {
            return item;
        }
        match *fty.kind() {
            ty::FnDef(def_id, fargs) => match fargs.no_bound_vars() {
                Some(fargs) => match Instance::try_resolve(self.tcx, self.env, def_id, fargs) {
                    Ok(Some(callee))
                        if depth < MAX_CONTEXT_DEPTH
                            && !self.on_path(callee)
                            && matches!(callee.def, InstanceKind::Item(_))
                            && here.is_some()
                            && self.vsums.wants_context(self.tcx, callee) =>
                    {
                        let ctx = here.cloned().unwrap_or_default();
                        let binds = self.call_binds(inst, body, callee, args);
                        Item::Call(self.node_bound(callee, ctx, depth + 1, binds))
                    }
                    // Bindings make a separate node even for a callee already on the
                    // path (nested formatting: `core::fmt::write` reached again from
                    // a `Display` impl); they range over finitely many types, and equal
                    // bindings reuse the node (recursion stays a cycle).
                    Ok(Some(callee)) if !matches!(callee.def, InstanceKind::Virtual(..)) => {
                        let binds = self.call_binds(inst, body, callee, args);
                        if binds.is_empty() {
                            self.resolve(def_id, fargs)
                        } else {
                            Item::Call(self.node_bound(callee, Vec::new(), 0, binds))
                        }
                    }
                    Ok(Some(callee)) if matches!(callee.def, InstanceKind::Virtual(..)) => self
                        .devirtualize(inst, body, callee, args)
                        .unwrap_or_else(|| Item::Call(self.node_for(callee))),
                    _ => self.resolve(def_id, fargs),
                },
                None => Item::Ev(Ev::Unknown(format!("callee `{fty}` with bound variables"))),
            },
            ty::FnPtr(..) => self
                .pointer_target(inst, body, func)
                .or_else(|| self.formatter_call(inst, body, fty, args))
                .unwrap_or_else(|| {
                    Item::Ev(Ev::Unknown(format!(
                        "call through a function pointer `{fty}`"
                    )))
                }),
            _ => Item::Ev(Ev::Unknown(format!("call of `{fty}`"))),
        }
    }

    /// The function a function pointer `op` in `inst`'s body calls: the function item
    /// or closure it is reified from on every path, the function a constant or a
    /// load from immutable data holds (several candidates: their maximum,
    /// [`Analysis::data_targets`]), or the declared bound of a parameter
    /// `param(g = K)`. `None`: not known here (`⊤`).
    fn pointer_target(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<Item> {
        match origin_of(self.tcx, body, op)? {
            Origin::Fn(t) => self.function_item(inst, t),
            Origin::Arg(l) => match self.bind_of(l) {
                Some(Bind::Callable(c)) => self.callable_item(&c, None),
                _ => self.declared_param_call(inst, body, l),
            },
            Origin::Const(c) => self.data_item(inst, c, None),
            Origin::Load(c, proj) => self.data_item(inst, c, Some(proj)),
            // `*self` in the `Fn`/`FnMut` shim of a function pointer: what the
            // reference is bound to (top plan T3).
            Origin::DerefArg(l) => match self.bind_of(l) {
                Some(Bind::Callable(c)) => self.callable_item(&c, None),
                _ => None,
            },
            // A load below a parameter bound to a reference constant (`(self.inner)`
            // in `LocalKey::try_with` with `self = &KEY`): the load below the
            // constant (top plan T7g).
            Origin::ArgAt(l, proj) => match (self.bind_of(l), proj.first()) {
                (Some(Bind::Data(c)), Some(mir::ProjectionElem::Deref)) => {
                    let rest = self.tcx.mk_place_elems(&proj[1..]);
                    self.data_item(inst, c, Some(rest))
                }
                _ => None,
            },
            // An element of a local array: every candidate element (their maximum).
            Origin::Elems(l, idx) => {
                let mut items = Vec::new();
                for e in array_elems(body, l, idx) {
                    // No arrays of arrays: an element is resolved by its own origin.
                    if matches!(origin_of(self.tcx, body, e), Some(Origin::Elems(..)) | None) {
                        return None;
                    }
                    match self.pointer_target(inst, body, e)? {
                        Item::Alt(v) => items.extend(v),
                        i => items.push(i),
                    }
                }
                match items.len() {
                    0 => None,
                    1 => items.pop(),
                    _ => Some(Item::Alt(items)),
                }
            }
            Origin::Pointee(_) | Origin::BufOf(_) | Origin::Ref(_) | Origin::BoxPtr(_) => None,
        }
    }

    /// The call through the function pointer of a `fip_strict::Certified<N, fn(..)>`
    /// (top plan T1.4): inside its `FipFn::call` (`(self.f)(..)`, the only call
    /// through a pointer in a `Certified` method), the certificate's bound `N`: at
    /// most `N` allocations, no free, no recursion. The certificate says nothing
    /// about panics, so a panic path is assumed. Every analysed construction
    /// (`Certified::assume`) is checked against `N` at its call site
    /// ([`Analysis::note_arg_site`]); constructions in unanalysed crates are trusted
    /// (`assume` is `unsafe`).
    fn certified_call(&self, inst: Instance<'tcx>) -> Option<Item> {
        let tcx = self.tcx;
        let InstanceKind::Item(d) = inst.def else {
            return None;
        };
        let imp = tcx.impl_of_assoc(d)?;
        let self_ty = tcx.type_of(imp).instantiate(tcx, inst.args).skip_norm_wip();
        let (n, p) = certified_fn_ptr(tcx, self_ty)?;
        let shown = with_no_visible_paths!(with_no_trimmed_paths!(p.to_string()));
        let what = format!("call of a certified function pointer `Certified<{n}, {shown}>`");
        let mut evs = vec![Ev::Bound(
            n,
            format!("{what}: {n} allocation(s) certified by its construction"),
        )];
        evs.push(Ev::Panic(format!(
            "{what}: its certificate bounds allocations, not panics, so it may panic"
        )));
        Some(Item::Evs(evs))
    }

    /// The call through a function pointer held in immutable data
    /// ([`Analysis::data_targets`]): the one candidate, or the alternatives.
    fn data_item(
        &mut self,
        inst: Instance<'tcx>,
        c: mir::Const<'tcx>,
        proj: Option<&'tcx ty::List<mir::PlaceElem<'tcx>>>,
    ) -> Option<Item> {
        let mut items: Vec<Item> = self
            .data_targets(inst, c, proj)?
            .into_iter()
            .map(|t| Item::Call(self.node_for(t)))
            .collect();
        if items.len() == 1 {
            items.pop()
        } else {
            Some(Item::Alt(items))
        }
    }

    /// The functions a function pointer read from immutable data may be. With `proj`
    /// `None`, `c` is a constant of function pointer type: the function it evaluates
    /// to. Else `c` is a constant reference (to a `static` or to constant memory) and
    /// the pointer is read at `proj` (fields of structs and tuples, array or slice
    /// elements) below it: every function pointer an index may select is a candidate
    /// (top plan T1.1, T1.2), also through a shared reference stored in the data
    /// (`static S: &[fn()]`, `S.ops.f` with `ops: &'static Ops`) when the memory it
    /// points to is immutable and of a `Freeze` type. `None` (so `⊤`) if the memory
    /// may change after initialisation (a `static mut`, a thread local, a foreign
    /// static, a static whose type is not `Freeze`, a mutable allocation, memory
    /// behind a reference to a type that is not `Freeze`), for any other projection
    /// (an enum variant), or if a value read is not a pointer to a function.
    fn data_targets(
        &self,
        inst: Instance<'tcx>,
        c: mir::Const<'tcx>,
        proj: Option<&'tcx ty::List<mir::PlaceElem<'tcx>>>,
    ) -> Option<Vec<Instance<'tcx>>> {
        use rustc_abi::Size;
        use rustc_middle::mir::interpret::{GlobalAlloc, Scalar, alloc_range};
        /// Above this many elements a table is not enumerated (`⊤`).
        const MAX_CANDIDATES: u64 = 256;
        let tcx = self.tcx;
        let c = self.subst(inst, c)?;
        let val = c.eval(tcx, self.env, DUMMY_SP).ok()?;
        let function = |s: Scalar| -> Option<Instance<'tcx>> {
            let Scalar::Ptr(ptr, _) = s else {
                return None;
            };
            match tcx.global_alloc(ptr.provenance.alloc_id()) {
                GlobalAlloc::Function { instance } => Some(instance),
                _ => None,
            }
        };
        let Some(proj) = proj else {
            if !c.ty().is_fn_ptr() {
                return None;
            }
            let mir::ConstValue::Scalar(s) = val else {
                return None;
            };
            return function(s).map(|f| vec![f]);
        };
        let pointee = c.ty().builtin_deref(true)?;
        let ptr_size = tcx.data_layout.pointer_size();
        // The allocation a pointer stored in data points to, if it never changes after
        // initialisation.
        let immutable = |alloc_id| {
            let alloc = match tcx.global_alloc(alloc_id) {
                GlobalAlloc::Static(def) => {
                    if tcx.is_mutable_static(def)
                        || tcx.is_thread_local_static(def)
                        || tcx.is_foreign_item(def)
                        || !tcx
                            .type_of(def)
                            .instantiate_identity()
                            .skip_norm_wip()
                            .is_freeze(tcx, self.env)
                    {
                        return None;
                    }
                    tcx.eval_static_initializer(def).ok()?
                }
                GlobalAlloc::Memory(a) => a,
                _ => return None,
            };
            (alloc.inner().mutability == rustc_ast::Mutability::Not).then_some(alloc)
        };
        let (alloc_id, start, slice_len) = match val {
            mir::ConstValue::Scalar(Scalar::Ptr(ptr, _)) => {
                let (prov, off) = ptr.into_raw_parts();
                (prov.alloc_id(), off, None)
            }
            mir::ConstValue::Slice { alloc_id, meta } => (alloc_id, Size::ZERO, Some(meta)),
            // A wide reference stored in constant memory (`const CT: &[fn()] = &[..]`):
            // its data pointer and length.
            mir::ConstValue::Indirect { alloc_id, offset } => {
                let GlobalAlloc::Memory(holder) = tcx.global_alloc(alloc_id) else {
                    return None;
                };
                let holder = holder.inner();
                let Scalar::Ptr(ptr, _) = holder
                    .read_scalar(&tcx, alloc_range(offset, ptr_size), true)
                    .ok()?
                else {
                    return None;
                };
                let len = if pointee.is_sized(tcx, self.env) {
                    None
                } else {
                    let len = holder
                        .read_scalar(&tcx, alloc_range(offset + ptr_size, ptr_size), false)
                        .ok()?;
                    Some(len.to_target_usize(&tcx).discard_err()?)
                };
                let (prov, off) = ptr.into_raw_parts();
                (prov.alloc_id(), off, len)
            }
            _ => return None,
        };
        let layout = |t: Ty<'tcx>| tcx.layout_of(self.env.as_query_input(t)).ok();
        // Each place: its type, the allocation holding it, its offset there, and the
        // length of a slice reached through a wide reference.
        let mut places = vec![(pointee, immutable(alloc_id)?, start, slice_len)];
        for elem in proj.iter() {
            let mut next = Vec::new();
            for (t, alloc, off, len) in places {
                match elem {
                    mir::ProjectionElem::Field(f, fty) => {
                        let is_struct = match t.kind() {
                            ty::Adt(def, _) => def.is_struct(),
                            ty::Tuple(_) => true,
                            _ => false,
                        };
                        if !is_struct {
                            return None;
                        }
                        let fty = self.subst(inst, fty)?;
                        next.push((
                            fty,
                            alloc,
                            off + layout(t)?.fields.offset(f.as_usize()),
                            None,
                        ));
                    }
                    mir::ProjectionElem::Index(_) | mir::ProjectionElem::ConstantIndex { .. } => {
                        let (et, n) = match *t.kind() {
                            ty::Array(et, n) => (et, n.try_to_target_usize(tcx)?),
                            ty::Slice(et) => (et, len?),
                            _ => return None,
                        };
                        if n > MAX_CANDIDATES {
                            return None;
                        }
                        let range = match elem {
                            mir::ProjectionElem::ConstantIndex {
                                offset,
                                from_end: false,
                                ..
                            } => offset..offset + 1,
                            mir::ProjectionElem::ConstantIndex {
                                offset,
                                from_end: true,
                                ..
                            } => {
                                let i = n.checked_sub(offset)?;
                                i..i + 1
                            }
                            _ => 0..n,
                        };
                        let stride = layout(et)?.size;
                        for i in range.filter(|i| *i < n) {
                            next.push((et, alloc, off + stride * i, None));
                        }
                    }
                    // A shared reference stored in the data (top plan T1 residue): the
                    // memory it points to, if that is immutable too and its type is
                    // `Freeze` (else a `Cell` behind it could change it).
                    mir::ProjectionElem::Deref => {
                        let ty::Ref(_, inner, rustc_ast::Mutability::Not) = *t.kind() else {
                            return None;
                        };
                        if !inner.is_freeze(tcx, self.env) {
                            return None;
                        }
                        let a = alloc.inner();
                        let Scalar::Ptr(ptr, _) =
                            a.read_scalar(&tcx, alloc_range(off, ptr_size), true).ok()?
                        else {
                            return None;
                        };
                        let len = if inner.is_sized(tcx, self.env) {
                            None
                        } else {
                            let len = a
                                .read_scalar(&tcx, alloc_range(off + ptr_size, ptr_size), false)
                                .ok()?;
                            Some(len.to_target_usize(&tcx).discard_err()?)
                        };
                        let (prov, to) = ptr.into_raw_parts();
                        next.push((inner, immutable(prov.alloc_id())?, to, len));
                    }
                    _ => return None,
                }
            }
            places = next;
        }
        let mut out = Vec::new();
        for (t, alloc, off, _) in places {
            if !t.is_fn_ptr() {
                return None;
            }
            let s = alloc
                .inner()
                .read_scalar(&tcx, alloc_range(off, ptr_size), true)
                .ok()?;
            let f = function(s)?;
            if !out.contains(&f) {
                out.push(f);
            }
        }
        (!out.is_empty()).then_some(out)
    }

    /// The callee for a value of the function item or closure type `t` (of `inst`'s
    /// MIR) called through a function pointer.
    fn function_item(&mut self, inst: Instance<'tcx>, t: Ty<'tcx>) -> Option<Item> {
        let t = self.subst(inst, t)?;
        match *t.kind() {
            ty::FnDef(d, a) => Some(self.resolve(d, a.no_bound_vars()?)),
            ty::Closure(d, a) => {
                let callee = Instance::resolve_closure(self.tcx, d, a, ty::ClosureKind::FnOnce);
                Some(Item::Call(self.node_for(callee)))
            }
            _ => None,
        }
    }

    /// A dynamic call (`callee` is `Virtual`, `args[0]` its receiver) whose receiver
    /// is, on every path in `inst`'s body, a pointer unsized from one concrete type:
    /// the method of that type, with the other arguments' bindings. A receiver that
    /// is a parameter (or a place below one) bound at the node's call sites: the
    /// output's method, the callable, or the `dyn Debug`/`dyn Display` value's
    /// method (top plan T7a). A receiver that is a parameter declared `param(g = K)`
    /// of a callable trait object (`&dyn Fn*`, `&dyn FipFn`): the declared bound.
    fn devirtualize(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        callee: Instance<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
    ) -> Option<Item> {
        let tcx = self.tcx;
        let InstanceKind::Virtual(def_id, _) = callee.def else {
            return None;
        };
        let recv = &args.first()?.node;
        match origin_of(tcx, body, recv)? {
            Origin::Pointee(t) => {
                let t = self.subst(inst, t)?;
                if !t.is_sized(tcx, self.env) {
                    return None;
                }
                self.obj_call(inst, body, callee, &Obj::Ty(t), args)
            }
            Origin::Arg(l) => {
                match self.bind_of(l) {
                    Some(Bind::Dyn(out) | Bind::Formatter(out)) => {
                        return self.output_call(def_id, callee, &out);
                    }
                    Some(Bind::Callable(c)) => {
                        if let Some(item) = self.callable_item(&c, Some(callee)) {
                            return Some(item);
                        }
                    }
                    Some(Bind::Obj(o)) => return self.obj_call(inst, body, callee, &o, args),
                    _ => {}
                }
                let trait_id = tcx.trait_of_assoc(def_id)?;
                if !self.is_callable_trait(trait_id) {
                    return None;
                }
                self.declared_param_call(inst, body, l)
            }
            Origin::ArgAt(l, p) => match self.bind_at(l, &place_path(p)?)? {
                Bind::Dyn(out) | Bind::Formatter(out) => self.output_call(def_id, callee, &out),
                Bind::Obj(o) => self.obj_call(inst, body, callee, &o, args),
                _ => None,
            },
            Origin::BufOf(l) => match self.bind_of(l) {
                Some(Bind::Formatter(out)) => self.output_call(def_id, callee, &out),
                _ => None,
            },
            // The receiver `&**self` of `<Box<dyn Fn*> as Fn*>::call*`: what the
            // `&Box` parameter is bound to (top plan T2).
            // Also the receiver `&**g` of `g: &Rc<dyn Fn*>` (`Deref::deref` of
            // `Rc`/`Arc`): unbound, the parameter's declared bound.
            Origin::BoxPtr(l) => match self.bind_of(l) {
                Some(Bind::Callable(c)) => self.callable_item(&c, Some(callee)),
                _ if tcx
                    .trait_of_assoc(def_id)
                    .is_some_and(|t| self.is_callable_trait(t)) =>
                {
                    self.declared_param_call(inst, body, l)
                }
                _ => None,
            },
            Origin::Fn(_)
            | Origin::Const(_)
            | Origin::Load(..)
            | Origin::Ref(_)
            | Origin::DerefArg(_)
            | Origin::Elems(..) => None,
        }
    }

    /// A dynamic call (`callee`, `args` with the receiver first) on a trait object
    /// known to hold `obj`: the method of its concrete type, called with the other
    /// arguments' bindings; or (generating std summaries, `obj` a parameter) the term
    /// `§dyn <i> <method> fmt <out>` when the method's only other argument is a
    /// `&mut Formatter` whose output is known (top plan T7a).
    fn obj_call(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        callee: Instance<'tcx>,
        obj: &Obj<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
    ) -> Option<Item> {
        let tcx = self.tcx;
        let InstanceKind::Virtual(def_id, _) = callee.def else {
            return None;
        };
        match obj {
            Obj::Ty(t) => {
                let margs = tcx.mk_args_from_iter(
                    std::iter::once((*t).into()).chain(callee.args.iter().skip(1)),
                );
                match Instance::try_resolve(tcx, self.env, def_id, margs) {
                    Ok(Some(c)) if !matches!(c.def, InstanceKind::Virtual(..)) => {
                        // The receiver is now `&T`: its trait-object binding is dropped.
                        let binds: Binds<'tcx> = self
                            .call_binds(inst, body, c, args)
                            .into_iter()
                            .filter(|(k, _)| *k != 1)
                            .collect();
                        Some(Item::Call(if binds.is_empty() {
                            self.node_for(c)
                        } else {
                            self.node_bound(c, Vec::new(), 0, binds)
                        }))
                    }
                    _ => None,
                }
            }
            Obj::Param(i) => {
                let [_, f] = args else {
                    return None;
                };
                let fty = self.subst(inst, f.node.ty(&body.local_decls, tcx))?;
                if !is_formatter_ref(tcx, fty) {
                    return None;
                }
                let out = self.formatter_out(inst, body, &f.node)?;
                Some(Item::Term(format!(
                    "§dyn {i} {} fmt {}",
                    def_path(tcx, def_id),
                    out_desc(&out)
                )))
            }
        }
    }

    /// The binding of parameter local `l` of the node being classified (as a whole;
    /// [`Analysis::bind_at`] for places below it).
    fn bind_of(&self, l: mir::Local) -> Option<Bind<'tcx>> {
        let l = u32::try_from(l.as_usize()).ok()?;
        // No node: a body checked on its own (`arguments_in`), without bindings.
        self.nodes
            .get(self.current)?
            .binds
            .iter()
            .find(|(k, b)| *k == l && !matches!(b, Bind::At(..)))
            .map(|(_, b)| b.clone())
    }

    /// The binding of the place at `path` below parameter local `l` of the node
    /// being classified ([`Bind::At`]). The output `buf` of a formatter bound at a
    /// path is that formatter's output.
    fn bind_at(&self, l: mir::Local, path: &[u32]) -> Option<Bind<'tcx>> {
        let k = u32::try_from(l.as_usize()).ok()?;
        let binds = &self.nodes.get(self.current)?.binds;
        let find = |p: &[u32]| {
            binds.iter().find_map(|(j, b)| match b {
                Bind::At(q, inner) if *j == k && q.as_slice() == p => Some((**inner).clone()),
                _ => None,
            })
        };
        if let Some(b) = find(path) {
            return Some(b);
        }
        // `(*f).buf` of a formatter `f` at a path: its output.
        if let [prefix @ .., PATH_DEREF, _] = path
            && let Some(Bind::Formatter(o)) = find(prefix)
        {
            return Some(Bind::Dyn(o));
        }
        None
    }

    /// The output reached through parameter local `l` of the node being classified:
    /// its own binding as an output or formatter, or the only such binding at a path
    /// below it (a builder's formatter, a `PadAdapter`'s buffer).
    fn out_param(&self, l: mir::Local) -> Option<Out<'tcx>> {
        if let Some(Bind::Dyn(o) | Bind::Formatter(o)) = self.bind_of(l) {
            return Some(o);
        }
        let k = u32::try_from(l.as_usize()).ok()?;
        let mut outs = self
            .nodes
            .get(self.current)?
            .binds
            .iter()
            .filter_map(|(j, b)| match b {
                Bind::At(_, inner) if *j == k => match &**inner {
                    Bind::Dyn(o) | Bind::Formatter(o) => Some(o.clone()),
                    _ => None,
                },
                _ => None,
            });
        let first = outs.next()?;
        outs.all(|o| o == first).then_some(first)
    }

    /// A dynamic call of `def_id` (`callee` is `Virtual`) on the output `out` of a
    /// formatting: the method of its type, of the `PadAdapter` over an output, or
    /// (generating std summaries) the term `§out <i> <method>` over the summarised
    /// function's parameter `i`.
    fn output_call(
        &mut self,
        def_id: DefId,
        callee: Instance<'tcx>,
        out: &Out<'tcx>,
    ) -> Option<Item> {
        let tcx = self.tcx;
        match out {
            Out::Ty(t) => {
                let args = tcx.mk_args_from_iter(
                    std::iter::once((*t).into()).chain(callee.args.iter().skip(1)),
                );
                match Instance::try_resolve(tcx, self.env, def_id, args) {
                    Ok(Some(c)) if !matches!(c.def, InstanceKind::Virtual(..)) => {
                        Some(Item::Call(self.node_for(c)))
                    }
                    _ => None,
                }
            }
            Out::Param(i) => Some(Item::Term(format!("§out {i} {}", def_path(tcx, def_id)))),
            Out::Pad(inner) => self.pad_call(def_id, callee.args.iter().skip(1), inner),
        }
    }

    /// The method `def_id` of `fmt::Write` for `core::fmt::builders::PadAdapter`, its
    /// `buf` bound to the output `inner` (top plan T7b).
    fn pad_call(
        &mut self,
        def_id: DefId,
        rest: impl Iterator<Item = ty::GenericArg<'tcx>>,
        inner: &Out<'tcx>,
    ) -> Option<Item> {
        let tcx = self.tcx;
        let (pad, buf) = self.pad_adapter(def_id)?;
        let args = tcx.mk_args_from_iter(std::iter::once(pad.into()).chain(rest));
        match Instance::try_resolve(tcx, self.env, def_id, args) {
            Ok(Some(c)) if !matches!(c.def, InstanceKind::Virtual(..)) => {
                let binds = vec![(
                    1,
                    Bind::At(vec![PATH_DEREF, buf], Box::new(Bind::Dyn(inner.clone()))),
                )];
                Some(Item::Call(self.node_bound(c, Vec::new(), 0, binds)))
            }
            _ => None,
        }
    }

    /// The type `core::fmt::builders::PadAdapter<'_, '_>` (from the implementations
    /// of the trait of the `fmt::Write` method `method`) and the index of its `buf`
    /// field.
    fn pad_adapter(&self, method: DefId) -> Option<(Ty<'tcx>, u32)> {
        let tcx = self.tcx;
        let write = tcx.trait_of_assoc(method)?;
        tcx.all_impls(write).find_map(|i| {
            let ty = tcx.type_of(i).instantiate_identity().skip_norm_wip();
            let ty::Adt(def, _) = ty.kind() else {
                return None;
            };
            if std_path(tcx, def.did()) != "core::fmt::builders::PadAdapter" {
                return None;
            }
            let buf = def
                .non_enum_variant()
                .fields
                .iter_enumerated()
                .find(|(_, f)| f.name.as_str() == "buf")
                .map(|(i, _)| i.as_usize())?;
            let erased = tcx.lifetimes.re_erased;
            let args = tcx.mk_args_from_iter(
                tcx.generics_of(def.did())
                    .own_params
                    .iter()
                    .map(|_| ty::GenericArg::from(erased)),
            );
            Some((ty::Ty::new_adt(tcx, *def, args), u32::try_from(buf).ok()?))
        })
    }

    /// The parameter bindings of a call of `callee` in `inst`'s body: for each
    /// argument that is a `&mut dyn fmt::Write`, a `&mut fmt::Formatter`, a value
    /// containing `fmt::Arguments`, a callable or a `&dyn Debug`/`&dyn Display`, what
    /// it is known to hold here (its output, its formatting functions, its function
    /// or concrete type); and for the places below an argument that hold such values
    /// (closure captures, `core::fmt` builders: [`bindable_paths`]), what they hold.
    /// Arguments that are not known are not bound.
    fn call_binds(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        callee: Instance<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
    ) -> Binds<'tcx> {
        let tcx = self.tcx;
        let mut binds = Vec::new();
        // Closures and other "rust-call" bodies take their arguments untupled: only
        // the first parameter (the closure) lines up with the call's arguments.
        let untupled = matches!(callee.def, InstanceKind::Item(d) if tcx.is_closure_like(d))
            || matches!(callee.def, InstanceKind::Shim(_));
        for (k, a) in args.iter().enumerate() {
            if untupled && k > 0 {
                break;
            }
            let Some(ty) = self.subst(inst, a.node.ty(&body.local_decls, tcx)) else {
                continue;
            };
            let Ok(local) = u32::try_from(k + 1) else {
                break;
            };
            let bind = if is_dyn_write_ref(tcx, ty) {
                self.out_of(inst, body, &a.node).map(Bind::Dyn)
            } else if is_formatter_ref(tcx, ty) {
                self.formatter_out(inst, body, &a.node).map(Bind::Formatter)
            } else if mentions_fmt_args(tcx, ty, 2) {
                self.fmt_set(inst, body, &a.node)
                    .map(|(fns, params)| Bind::Fmt(fns, params))
            } else if self.is_callable_value(ty) && self.callable_depth() < MAX_CALLABLE_DEPTH {
                self.callable_of(inst, body, &a.node, ty)
                    .map(Bind::Callable)
            } else if is_obj_ref(tcx, ty) {
                self.obj_of(inst, body, &a.node).map(Bind::Obj)
            } else if holds_fn_ptr(tcx, ty) {
                self.data_of(inst, body, &a.node).map(Bind::Data)
            } else {
                None
            };
            if let Some(b) = bind {
                binds.push((local, b));
            }
            let (Operand::Copy(q) | Operand::Move(q)) = &a.node else {
                continue;
            };
            for (path, leaf) in bindable_paths(tcx, ty) {
                let Some(key) = place_path(&path) else {
                    continue;
                };
                let mut proj = q.projection.to_vec();
                proj.extend(path);
                let op = Operand::Copy(mir::Place {
                    local: q.local,
                    projection: tcx.mk_place_elems(&proj),
                });
                let b = match leaf {
                    Leaf::Formatter => self.formatter_out(inst, body, &op).map(Bind::Formatter),
                    Leaf::Dyn => self.out_of(inst, body, &op).map(Bind::Dyn),
                    Leaf::Obj => self.obj_of(inst, body, &op).map(Bind::Obj),
                };
                if let Some(b) = b {
                    binds.push((local, Bind::At(key, Box::new(b))));
                }
            }
        }
        binds
    }

    /// The reference constant a shared-reference operand of `inst`'s body is on
    /// every path ([`Origin::Const`], instantiated), or the [`Bind::Data`] of the
    /// parameter it passes on (top plan T7g). Whether the memory is immutable is
    /// decided where a load is resolved ([`Analysis::data_targets`]).
    fn data_of(
        &self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<mir::Const<'tcx>> {
        match origin_of(self.tcx, body, op)? {
            Origin::Const(c) => {
                let c = self.subst(inst, c)?;
                (!c.has_param()).then_some(c)
            }
            Origin::Arg(l) => match self.bind_of(l)? {
                Bind::Data(c) => Some(c),
                _ => None,
            },
            _ => None,
        }
    }

    /// What a `&dyn Debug`/`&dyn Display` operand of `inst`'s body holds: the
    /// concrete type it is unsized from, or the binding of the parameter (or place
    /// below one) it comes from.
    fn obj_of(
        &self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<Obj<'tcx>> {
        match origin_of(self.tcx, body, op)? {
            Origin::Pointee(t) => {
                let t = self.subst(inst, t)?;
                t.is_sized(self.tcx, self.env).then_some(Obj::Ty(t))
            }
            Origin::Arg(l) => match self.bind_of(l)? {
                Bind::Obj(o) => Some(o),
                _ => None,
            },
            Origin::ArgAt(l, p) => match self.bind_at(l, &place_path(p)?)? {
                Bind::Obj(o) => Some(o),
                _ => None,
            },
            _ => None,
        }
    }

    /// Nodes with a callable binding from the node being classified up its first
    /// callers (bounded by [`MAX_CALLABLE_DEPTH`]).
    fn callable_depth(&self) -> usize {
        let mut n = 0;
        let mut at = (self.current < self.nodes.len()).then_some(self.current);
        while let Some(i) = at {
            if self.nodes[i]
                .binds
                .iter()
                .any(|(_, b)| matches!(b, Bind::Callable(_)))
            {
                n += 1;
            }
            at = self.nodes[i].parent;
        }
        n
    }

    /// `true` for the types a callable binding describes: a function pointer, a
    /// reference to one, and a callable trait object behind a reference or a `Box`
    /// ([`Analysis::callable_dyn`]).
    fn is_callable_value(&self, ty: Ty<'tcx>) -> bool {
        ty.is_fn_ptr()
            || matches!(*ty.kind(), ty::Ref(_, inner, _) if inner.is_fn_ptr())
            || self.callable_dyn(ty).is_some()
    }

    /// What the callable operand `op` (of type `ty`, [`Analysis::is_callable_value`])
    /// of `inst`'s body holds on every path: the function(s) a function pointer is
    /// reified from or read from immutable data, the concrete type a trait object is
    /// unsized from, the binding of a parameter it passes on, or a parameter declared
    /// `param(h = K)`. For a reference `&l` to a function pointer or to a `Box<dyn
    /// Fn*>`: what `l` holds. `None`: not known (the callee is analysed without it).
    fn callable_of(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<Callable<'tcx>> {
        let tcx = self.tcx;
        // `ty` is the operand's type in this instance: a function pointer there is
        // read with `&mut` receivers of its `FnMut` shim allowed.
        let fn_ptr =
            ty.is_fn_ptr() || matches!(*ty.kind(), ty::Ref(_, inner, _) if inner.is_fn_ptr());
        let origin = if fn_ptr {
            origin_of_fn_ptr(tcx, body, op)
        } else {
            origin_of(tcx, body, op)
        };
        match origin? {
            Origin::Fn(t) if ty.is_fn_ptr() => {
                let t = self.subst(inst, t)?;
                let f = match *t.kind() {
                    ty::FnDef(d, a) => {
                        Instance::try_resolve(tcx, self.env, d, a.no_bound_vars()?).ok()??
                    }
                    ty::Closure(d, a) => {
                        Instance::resolve_closure(tcx, d, a, ty::ClosureKind::FnOnce)
                    }
                    _ => return None,
                };
                Some(Callable::Fns(vec![f]))
            }
            Origin::Const(c) if ty.is_fn_ptr() => {
                Some(Callable::Fns(self.data_targets(inst, c, None)?))
            }
            Origin::Load(c, proj) if ty.is_fn_ptr() => {
                Some(Callable::Fns(self.data_targets(inst, c, Some(proj))?))
            }
            // An element of a local array: the functions every candidate holds.
            Origin::Elems(l, idx) if ty.is_fn_ptr() => {
                let mut fns = Vec::new();
                for e in array_elems(body, l, idx) {
                    if matches!(origin_of(tcx, body, e), Some(Origin::Elems(..)) | None) {
                        return None;
                    }
                    let Callable::Fns(fs) = self.callable_of(inst, body, e, ty)? else {
                        return None;
                    };
                    for f in fs {
                        if !fns.contains(&f) {
                            fns.push(f);
                        }
                    }
                }
                (!fns.is_empty()).then_some(Callable::Fns(fns))
            }
            Origin::Pointee(t) if !ty.is_fn_ptr() => {
                let t = self.subst(inst, t)?;
                t.is_sized(tcx, self.env).then_some(Callable::Pointee(t))
            }
            Origin::Ref(l) => {
                let ty::Ref(_, inner, _) = *ty.kind() else {
                    return None;
                };
                if !self.is_callable_value(inner) {
                    return None;
                }
                self.callable_of(inst, body, &Operand::Copy(mir::Place::from(l)), inner)
            }
            Origin::Arg(l) => {
                if let Some(Bind::Callable(c)) = self.bind_of(l) {
                    return Some(c);
                }
                let InstanceKind::Item(d) = inst.def else {
                    return None;
                };
                let (g, _) = self.declared_param(d, body, l)?;
                Some(Callable::Declared(d, g))
            }
            _ => None,
        }
    }

    /// The call through a callable parameter bound to `c` (`recv` the dynamic
    /// callee of a trait object call, `None` for a function pointer).
    fn callable_item(&mut self, c: &Callable<'tcx>, recv: Option<Instance<'tcx>>) -> Option<Item> {
        let tcx = self.tcx;
        match c {
            Callable::Fns(fs) => {
                if recv.is_some() {
                    return None;
                }
                let mut items: Vec<Item> =
                    fs.iter().map(|f| Item::Call(self.node_for(*f))).collect();
                if items.len() == 1 {
                    items.pop()
                } else {
                    Some(Item::Alt(items))
                }
            }
            Callable::Pointee(t) => {
                let callee = recv?;
                let InstanceKind::Virtual(def_id, _) = callee.def else {
                    return None;
                };
                let args = tcx.mk_args_from_iter(
                    std::iter::once((*t).into()).chain(callee.args.iter().skip(1)),
                );
                match Instance::try_resolve(tcx, self.env, def_id, args) {
                    Ok(Some(f)) if !matches!(f.def, InstanceKind::Virtual(..)) => {
                        Some(Item::Call(self.node_for(f)))
                    }
                    _ => None,
                }
            }
            Callable::Declared(d, g) => {
                let mark = self.crates.param_mark(self.tcx, *d)?;
                let k = mark.params.iter().find(|(n, _)| n == g)?.1;
                Some(Item::Evs(param_events(g, k, &mark)))
            }
        }
    }

    /// The output a `&mut dyn fmt::Write` operand of `inst`'s body writes to.
    fn out_of(
        &self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<Out<'tcx>> {
        match origin_of(self.tcx, body, op)? {
            Origin::Pointee(t) => Some(Out::Ty(self.subst(inst, t)?)),
            Origin::Arg(l) => match self.bind_of(l)? {
                Bind::Dyn(o) | Bind::Formatter(o) => Some(o),
                Bind::Fmt(..) | Bind::Callable(_) | Bind::Obj(_) | Bind::At(..) | Bind::Data(_) => {
                    None
                }
            },
            Origin::ArgAt(l, p) => match self.bind_at(l, &place_path(p)?)? {
                Bind::Dyn(o) | Bind::Formatter(o) => Some(o),
                _ => None,
            },
            Origin::BufOf(l) => match self.bind_of(l)? {
                Bind::Formatter(o) => Some(o),
                _ => None,
            },
            Origin::Fn(_)
            | Origin::Const(_)
            | Origin::Load(..)
            | Origin::Ref(_)
            | Origin::DerefArg(_)
            | Origin::BoxPtr(_)
            | Origin::Elems(..) => None,
        }
    }

    /// The output of a `&mut fmt::Formatter` operand of `inst`'s body: a parameter
    /// (or a place below one) bound to a formatter, a `Formatter::new(out, ..)` made
    /// in the body, or a `PadAdapter::wrap(f, ..)` over the formatter `f` (top plan
    /// T7b).
    fn formatter_out(
        &self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<Out<'tcx>> {
        let cx = OriginCx::new(self.tcx, body);
        match cx.formatter_src(op, 0)? {
            FmtrSrc::Param(l) => match self.bind_of(l)? {
                Bind::Formatter(o) => Some(o),
                _ => None,
            },
            FmtrSrc::At(l, p) => match self.bind_at(l, &place_path(p)?)? {
                Bind::Formatter(o) => Some(o),
                _ => None,
            },
            FmtrSrc::New(out) => self.out_of(inst, body, out),
            FmtrSrc::Pad(f) => self
                .formatter_out(inst, body, f)
                .map(|o| Out::Pad(Box::new(o))),
        }
    }

    /// The formatting functions an operand containing `fmt::Arguments` (or
    /// `fmt::rt::Argument`) of `inst`'s body may carry: those reified by the
    /// `rt::Argument` constructors that built it in the body, and those of the
    /// parameters it comes from (and, generating std summaries, the summarised
    /// function's parameters). `None` if any part of it has another origin.
    fn fmt_set(
        &self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<(Vec<Ty<'tcx>>, Vec<u32>)> {
        let tcx = self.tcx;
        let cx = OriginCx::new(tcx, body);
        let mut fns: Vec<Ty<'tcx>> = Vec::new();
        let mut params: Vec<u32> = Vec::new();
        for src in cx.fmt_sources(op, 0)? {
            match src {
                FmtSrc::Param(l) => match self.bind_of(l)? {
                    Bind::Fmt(f, p) => {
                        fns.extend(f);
                        params.extend(p);
                    }
                    _ => return None,
                },
                FmtSrc::Ctor(t) => {
                    let ty::FnDef(d, a) = *self.subst(inst, t)?.kind() else {
                        return None;
                    };
                    let ctor =
                        Instance::try_resolve(tcx, self.env, d, a.no_bound_vars()?).ok()??;
                    fns.extend(self.reified_in(ctor)?);
                }
            }
        }
        fns.sort_by_key(|t| t.to_string());
        fns.dedup();
        params.sort_unstable();
        params.dedup();
        Some((fns, params))
    }

    /// The function items and closures reified to function pointers in the body of
    /// the `rt::Argument` constructor `ctor` (the formatting function it stores).
    fn reified_in(&self, ctor: Instance<'tcx>) -> Option<Vec<Ty<'tcx>>> {
        use rustc_middle::ty::adjustment::PointerCoercion;
        let tcx = self.tcx;
        if !tcx.is_mir_available(ctor.def_id()) {
            return None;
        }
        let body = tcx.instance_mir(ctor.def);
        let mut v = Vec::new();
        for data in body.basic_blocks.iter() {
            for st in &data.statements {
                if let mir::StatementKind::Assign(assign) = &st.kind
                    && let mir::Rvalue::Cast(
                        mir::CastKind::PointerCoercion(
                            PointerCoercion::ReifyFnPointer(_)
                            | PointerCoercion::ClosureFnPointer(_),
                            _,
                        ),
                        op,
                        _,
                    ) = &assign.1
                {
                    v.push(self.subst(ctor, op.ty(&body.local_decls, tcx))?);
                }
            }
        }
        Some(v)
    }

    /// A call through a formatting function pointer (`unsafe fn(NonNull<()>,
    /// &mut Formatter) -> Result`, stored in `rt::Argument`) in a body bound to
    /// formatting functions: each of them, with a `Formatter` writing to the output
    /// of the call's formatter argument. Generating std summaries, the term
    /// `§fmt <i> out ..` over the summarised function's parameter `i`.
    fn formatter_call(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        fty: Ty<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
    ) -> Option<Item> {
        let tcx = self.tcx;
        let ty::FnPtr(sig_tys, _) = fty.kind() else {
            return None;
        };
        let inputs = sig_tys.skip_binder().inputs();
        if inputs.len() != 2 || !is_formatter_ref(tcx, inputs[1]) || args.len() != 2 {
            return None;
        }
        // The function pointers come from `rt::Argument` values of the node's
        // bound parameters; a body that builds its own may call others.
        if body_builds_arguments(tcx, body) {
            return None;
        }
        let mut fns: Vec<Ty<'tcx>> = Vec::new();
        let mut params: Vec<u32> = Vec::new();
        let mut bound = false;
        for (_, b) in self.nodes[self.current].binds.clone() {
            if let Bind::Fmt(f, p) = b {
                fns.extend(f);
                params.extend(p);
                bound = true;
            }
        }
        if !bound {
            return None;
        }
        let out = self.formatter_out(inst, body, &args[1].node)?;
        let mut items = Vec::new();
        for i in params {
            items.push(Item::Term(format!("§fmt {i} out {}", out_desc(&out))));
        }
        for f in fns {
            items.push(self.formatter_item(f, &out));
        }
        Some(Item::Many(items))
    }

    /// The call of the formatting function `f` (a function item or closure type)
    /// with a `Formatter` writing to `out`.
    fn formatter_item(&mut self, f: Ty<'tcx>, out: &Out<'tcx>) -> Item {
        match *f.kind() {
            ty::FnDef(d, a) => match a
                .no_bound_vars()
                .map(|a| (a, Instance::try_resolve(self.tcx, self.env, d, a)))
            {
                None => Item::Ev(Ev::Unknown(format!(
                    "formatting function `{f}` with bound variables"
                ))),
                Some((a, r)) => match r {
                    Ok(Some(c)) => {
                        // `fn fmt(&self, f: &mut Formatter)`: the formatter is local 2.
                        let binds = vec![(2, Bind::Formatter(out.clone()))];
                        Item::Call(self.node_bound(c, Vec::new(), 0, binds))
                    }
                    _ => self.resolve(d, a),
                },
            },
            ty::Closure(d, a) => {
                let c = Instance::resolve_closure(self.tcx, d, a, ty::ClosureKind::FnOnce);
                Item::Call(self.node_for(c))
            }
            _ => Item::Ev(Ev::Unknown(format!(
                "formatting function of type `{f}` (not a function item or closure)"
            ))),
        }
    }

    /// A call through the parameter in local `l` of `inst` (a function pointer or a
    /// callable trait object) whose function declares `param(g = K)` for it: `K`
    /// allocations, checked at every call site of the function.
    fn declared_param_call(
        &self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        l: mir::Local,
    ) -> Option<Item> {
        let InstanceKind::Item(d) = inst.def else {
            return None;
        };
        let (g, k) = self.declared_param(d, body, l)?;
        let mark = self.crates.param_mark(self.tcx, d)?;
        Some(Item::Evs(param_events(&g, k, &mark)))
    }

    /// The name and declared bound of the parameter in local `l` of `d`'s body, if
    /// `d` declares `param(g = K)` for it.
    fn declared_param(&self, d: DefId, body: &Body<'tcx>, l: mir::Local) -> Option<(String, u64)> {
        let tcx = self.tcx;
        if !matches!(tcx.def_kind(d), DefKind::Fn | DefKind::AssocFn) {
            return None;
        }
        let pos = l.as_usize().checked_sub(1)?;
        if pos >= body.arg_count {
            return None;
        }
        let ident = (*tcx.fn_arg_idents(d).get(pos)?)?;
        let g = ident.name.to_string();
        let mark = self.crates.param_mark(self.tcx, d)?;
        let k = mark.params.iter().find(|(n, _)| *n == g)?.1;
        Some((g, k))
    }

    /// `true` if `inst` is the node being classified or one of the nodes through
    /// which it was first reached: a call of it is recursion, which gets the empty
    /// context (so a recursive component is the same nodes as without contexts).
    fn on_path(&self, inst: Instance<'tcx>) -> bool {
        let mut at = Some(self.current);
        while let Some(i) = at {
            if self.nodes[i].inst == inst {
                return true;
            }
            at = self.nodes[i].parent;
        }
        false
    }

    /// Reports a function with `fip::requires(..)` used as a value (`op`, outside the
    /// callee position of a call): reified to a function pointer or passed as a
    /// callable, its precondition cannot be checked where it is called.
    fn reified(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
        span: Span,
        sites: &mut Vec<Site>,
    ) {
        let Some(ty) = self.subst(inst, op.ty(&body.local_decls, self.tcx)) else {
            return;
        };
        if let ty::FnDef(d, _) = *ty.kind()
            && let Some(req) = self.crates.requires_of(d)
        {
            sites.push(Site {
                item: Item::Ev(Ev::Panic(format!(
                    "`{}` declares `fip::requires({})` but is used as a function value: its precondition is not checked where it is called",
                    def_path(self.tcx, d),
                    req.text
                ))),
                span,
            });
        }
    }

    fn resolve(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>) -> Item {
        match Instance::try_resolve(self.tcx, self.env, def_id, args) {
            Ok(Some(callee)) => Item::Call(self.node_for(callee)),
            Ok(None) => self.unresolved(def_id, args),
            Err(_) => Item::Ev(Ev::Unknown(format!(
                "`{}` (resolution failed)",
                def_path_args(self.tcx, def_id, args)
            ))),
        }
    }

    /// The root's value parameter of type `p` (`g` for `g: F`), else the type
    /// parameter's own name.
    fn param_name(&self, p: ty::ParamTy) -> String {
        self.param_names
            .get(&p.index)
            .cloned()
            .unwrap_or_else(|| p.name.to_string())
    }

    fn is_callable_trait(&self, trait_id: DefId) -> bool {
        let tcx = self.tcx;
        tcx.fn_trait_kind_from_def_id(trait_id).is_some()
            || tcx.item_name(trait_id).as_str() == "FipFn"
    }

    /// The drop of a value of type `ty` (which needs dropping): its drop glue, or the
    /// term `drop(T)` for a bare type parameter `T`.
    fn drop_item(&mut self, ty: Ty<'tcx>) -> Item {
        if let ty::Param(p) = ty.kind() {
            return Item::Term(format!("drop({})", p.name));
        }
        let tcx = self.tcx;
        let glue = tcx.require_lang_item(LangItem::DropGlue, DUMMY_SP);
        self.resolve(glue, tcx.mk_args(&[ty.into()]))
    }

    fn unresolved(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>) -> Item {
        let tcx = self.tcx;
        // `drop_in_place::<T>` reaches the drop glue of a bare type parameter, which
        // is not resolvable: the term `drop(T)`, like a `Drop` of a `T`.
        if tcx.is_lang_item(def_id, LangItem::DropGlue)
            && let Some(ty) = args.types().next()
            && let ty::Param(p) = ty.kind()
        {
            return Item::Term(format!("drop({})", p.name));
        }
        // A source's trait method is that source for every implementation: the call
        // is the declared event, not a term.
        if self.crates.source_of(tcx, def_id).is_some() {
            return Item::Call(self.node_for(Instance::new_raw(def_id, args)));
        }
        // A trait method declaration with a contract: an unresolved call on `Self`
        // or a type parameter costs the contract (every implementation is checked).
        if let Some(m) = self.crates.contract_of(tcx, def_id) {
            return Item::Call(self.node_contract(def_id, args, m));
        }
        if let Some(trait_id) = tcx.trait_of_assoc(def_id)
            && let Some(self_ty) = args.types().next()
            && let ty::Param(p) = self_ty.peel_refs().kind()
        {
            if self.is_callable_trait(trait_id) {
                return Item::Term(self.param_name(*p));
            }
            return Item::Term(format!(
                "<{} as {}>::{}",
                p.name,
                tcx.item_name(trait_id),
                tcx.item_name(def_id)
            ));
        }
        Item::Ev(Ev::Unknown(format!(
            "`{}` (not resolvable to one function)",
            def_path_args(tcx, def_id, args)
        )))
    }

    /// Records the call of `callee` at `span` in `caller` (whose MIR is `body`, the
    /// call's arguments `call_args`) if the callee declares `param(g = K)`: for each
    /// such `g`, the argument's callable entry points are resolved and become nodes
    /// of the graph. A dynamic call (and an unresolved one on a type parameter,
    /// whose callee is the trait method itself) is checked against the contract's
    /// `param(..)` (top plan T5).
    fn note_arg_site(
        &mut self,
        caller: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        span: Span,
        callee: Instance<'tcx>,
        call_args: &[Spanned<Operand<'tcx>>],
    ) {
        let (InstanceKind::Item(def_id) | InstanceKind::Virtual(def_id, _)) = callee.def else {
            return;
        };
        if self.certified_construction(caller, body, span, callee, call_args) {
            return;
        }
        let crates = self.crates;
        let Some(mark) = crates.param_mark(self.tcx, def_id) else {
            return;
        };
        let caller_label = self.label(caller);
        let callee_label = def_path(self.tcx, def_id);
        for (g, declared) in &mark.params {
            let Some((arg, items, indirect)) =
                self.argument_items(caller, body, call_args, def_id, callee.args, g)
            else {
                continue;
            };
            // The driver-mode check function (`fip_fn!(prelint, N, ..)`) takes the
            // closure by its type (`g: &G`) and never calls it: the argument must not
            // do what its mark forbids (free, recursion), as for a parameter called by
            // its declaration.
            let indirect =
                (indirect || is_checked_fn(self.tcx, def_id)).then(|| mark.clone().into_owned());
            let from_param = self
                .tcx
                .fn_arg_idents(def_id)
                .iter()
                .position(|i| i.is_some_and(|i| i.name.as_str() == g))
                .and_then(|pos| call_args.get(pos))
                .is_some_and(|a| self.unbound_param(caller, body, &a.node));
            self.arg_sites.push(ArgSite {
                caller: caller_label.clone(),
                caller_def: caller.def_id(),
                from_param,
                span,
                local: caller.def_id().is_local(),
                callee: callee_label.clone(),
                param: g.clone(),
                declared: *declared,
                arg,
                items,
                indirect,
                certifying: is_checked_fn(self.tcx, def_id),
                node: self.current,
            });
        }
    }

    /// A construction `Certified::<N, fn(..)>::assume(f)` (or `assume_no_panic_macros`,
    /// top plan T1.4): checked
    /// like an argument for a declared `param(f = N)` of a `#[fip(N)]` callee that
    /// calls `f` by its declaration (so a free or recursion of `f` is forbidden, a
    /// panic allowed): the function `f` holds must allocate at most `N` times per call;
    /// a pointer of unknown origin is `⊤` here. `false` for any other callee.
    fn certified_construction(
        &mut self,
        caller: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        span: Span,
        callee: Instance<'tcx>,
        call_args: &[Spanned<Operand<'tcx>>],
    ) -> bool {
        let tcx = self.tcx;
        let InstanceKind::Item(def_id) = callee.def else {
            return false;
        };
        if tcx
            .opt_item_name(def_id)
            .is_none_or(|n| !matches!(n.as_str(), "assume" | "assume_no_panic_macros"))
        {
            return false;
        }
        let Some(imp) = tcx.impl_of_assoc(def_id) else {
            return false;
        };
        if tcx.trait_impl_of_assoc(def_id).is_some() {
            return false;
        }
        let self_ty = tcx
            .type_of(imp)
            .instantiate(tcx, callee.args)
            .skip_norm_wip();
        let Some((n, p)) = certified_parts(tcx, self_ty) else {
            return false;
        };
        let op = call_args.first().map(|a| &a.node);
        let (arg, items) = if p.is_fn_ptr() {
            self.indirect_argument(caller, body, op, "f", p)
        } else if p.has_param() && !matches!(p.kind(), ty::Closure(..) | ty::FnDef(..)) {
            // A generic callable type: instantiated with a function pointer, calls
            // would trust a bound no analysed site checked.
            let shown = with_no_visible_paths!(with_no_trimmed_paths!(p.to_string()));
            let what = format!(
                "`Certified::assume` with the generic callable type `{shown}`: if it is instantiated with a function pointer, calls trust a bound that is not checked here"
            );
            (shown, vec![(what.clone(), Item::Ev(Ev::Unknown(what)))])
        } else {
            // A closure or function item, also one generic only through the
            // enclosing function's parameters (no instantiation makes it a function
            // pointer): its calls are analysed through its body.
            return false;
        };
        let from_param = op.is_some_and(|o| self.unbound_param(caller, body, o));
        let shown = with_no_visible_paths!(with_no_trimmed_paths!(p.to_string()));
        self.arg_sites.push(ArgSite {
            caller: self.label(caller),
            caller_def: caller.def_id(),
            from_param,
            span,
            local: caller.def_id().is_local(),
            callee: format!("fip_strict::Certified::<{n}, {shown}>::assume"),
            param: "f".to_string(),
            declared: n,
            arg,
            items,
            indirect: Some(Mark {
                kind: crate::marks::Kind::Fip,
                n,
                strict: false,
                panic_macros: true,
                params: vec![("f".to_string(), n)],
            }),
            certifying: false,
            node: self.current,
        });
        true
    }

    /// `true` if `op` (in `caller`'s body) is, directly or as `&l`, a parameter of
    /// `caller` that has no callable binding and no `param(..)` declaration.
    fn unbound_param(
        &self,
        caller: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> bool {
        let mut origin = origin_of(self.tcx, body, op);
        if let Some(Origin::Ref(l)) = origin {
            origin = origin_of(self.tcx, body, &Operand::Copy(mir::Place::from(l)));
        }
        let Some(Origin::Arg(l)) = origin else {
            return false;
        };
        if self.bind_of(l).is_some() {
            return false;
        }
        match caller.def {
            InstanceKind::Item(d) => self.declared_param(d, body, l).is_none(),
            _ => true,
        }
    }

    /// The type passed for `g` to `callee` (instantiated with `args`) and the
    /// callable methods (`call`, `call_mut`, `call_once`) of every callable bound
    /// (`Fn*`, `FipFn`) of `g`'s generic type parameter, resolved for that type.
    /// For `g` a function pointer or a callable trait object (`&dyn Fn*`,
    /// `&dyn FipFn`): the function the argument holds, found in the caller's body
    /// ([`Analysis::indirect_argument`]). `None` if the parameter has no callable
    /// bound: then `param(g = K)` bounds no call.
    fn argument_items(
        &mut self,
        caller: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        call_args: &[Spanned<Operand<'tcx>>],
        callee: DefId,
        args: GenericArgsRef<'tcx>,
        g: &str,
    ) -> Option<ArgItems> {
        let tcx = self.tcx;
        let pos = tcx
            .fn_arg_idents(callee)
            .iter()
            .position(|i| i.is_some_and(|i| i.name.as_str() == g));
        let Some(pos) = pos else {
            let what = format!(
                "`{}` declares `param({g} = ..)` but has no parameter `{g}`",
                def_path(tcx, callee)
            );
            return Some((
                "?".to_string(),
                vec![(what.clone(), Item::Ev(Ev::Unknown(what)))],
                false,
            ));
        };
        let input = tcx.fn_sig(callee).skip_binder().skip_binder().inputs()[pos];
        if input.is_fn_ptr() || self.callable_dyn(input).is_some() {
            let op = call_args.get(pos).map(|a| &a.node);
            let (arg, items) = self.indirect_argument(caller, body, op, g, input);
            return Some((arg, items, true));
        }
        let ty::Param(p) = *input.peel_refs().kind() else {
            let shown = with_no_visible_paths!(with_no_trimmed_paths!(input.to_string()));
            let what = format!(
                "parameter `{g}: {shown}` is neither of a generic type, a function pointer nor a reference to a callable trait object: the function it holds is not determined at the call site"
            );
            return Some((
                shown,
                vec![(what.clone(), Item::Ev(Ev::Unknown(what)))],
                false,
            ));
        };
        let arg_ty = args.type_at(p.index as usize);
        let arg = with_no_visible_paths!(with_no_trimmed_paths!(arg_ty.to_string()));
        // `G` instantiated with a function pointer: its `Fn*` methods are shims that
        // call through `self`, bound to what the argument holds here (top plan T3).
        let bound = if arg_ty.is_fn_ptr() {
            call_args.get(pos).and_then(|a| {
                let aty = self.subst(caller, a.node.ty(&body.local_decls, tcx))?;
                self.callable_of(caller, body, &a.node, aty)
            })
        } else {
            None
        };
        let mut items: Vec<(String, Item)> = Vec::new();
        for clause in tcx.param_env(callee).caller_bounds() {
            let Some(pred) = clause.as_trait_clause() else {
                continue;
            };
            let pred = tcx.instantiate_bound_regions_with_erased(pred);
            let on_p = matches!(pred.self_ty().kind(), ty::Param(q) if q.index == p.index);
            if !on_p || !self.is_callable_trait(pred.def_id()) {
                continue;
            }
            for m in tcx.associated_items(pred.def_id()).in_definition_order() {
                if !m.is_fn() || !tcx.generics_of(m.def_id).own_params.is_empty() {
                    continue;
                }
                let margs = EarlyBinder::bind(tcx, pred.trait_ref.args).instantiate(tcx, args);
                let (label, item) = match tcx.try_normalize_erasing_regions(self.env, margs) {
                    Ok(margs) => {
                        let item = match (
                            &bound,
                            Instance::try_resolve(tcx, self.env, m.def_id, margs),
                        ) {
                            (Some(c), Ok(Some(shim)))
                                if matches!(shim.def, InstanceKind::Shim(_)) =>
                            {
                                Item::Call(self.node_bound(
                                    shim,
                                    Vec::new(),
                                    0,
                                    vec![(1, Bind::Callable(c.clone()))],
                                ))
                            }
                            _ => self.resolve(m.def_id, margs),
                        };
                        (def_path_args(tcx, m.def_id, margs), item)
                    }
                    Err(_) => {
                        let label = def_path(tcx, m.def_id);
                        let what = format!("`{label}` for `{arg}` (not normalizable)");
                        (label, Item::Ev(Ev::Unknown(what)))
                    }
                };
                if items.iter().all(|(l, _)| *l != label) {
                    items.push((label, item));
                }
            }
        }
        if items.is_empty() {
            None
        } else {
            Some((arg, items, false))
        }
    }

    /// The principal trait of `t = &dyn Tr`, `&mut dyn Tr`, `Box<dyn Tr>` or a
    /// reference to `Box<dyn Tr>` if `Tr` is callable (`Fn*`, `FipFn`).
    fn callable_dyn(&self, t: Ty<'tcx>) -> Option<ty::Binder<'tcx, ty::ExistentialTraitRef<'tcx>>> {
        let inner = match *t.kind() {
            ty::Ref(_, inner, _) if inner.is_box() => inner.expect_boxed_ty(),
            ty::Ref(_, inner, _) => shared_ptr_pointee(self.tcx, inner).unwrap_or(inner),
            _ if t.is_box() => t.expect_boxed_ty(),
            _ => shared_ptr_pointee(self.tcx, t)?,
        };
        let ty::Dynamic(preds, ..) = *inner.kind() else {
            return None;
        };
        let principal = preds.principal()?;
        self.is_callable_trait(principal.def_id())
            .then_some(principal)
    }

    /// The argument passed at a call site in `caller`'s `body` (`op`) for a
    /// parameter `g` declared `param(g = K)` whose type `input` is a function pointer
    /// or a reference to a callable trait object: the function it holds when its
    /// origin in the body is one function item or closure (function pointer) or one
    /// concrete type (trait object), [`origin_of`]; the caller's own declared bound
    /// when it passes on a parameter declared `param(h = K')`; else `⊤` at the call
    /// site (a pointer loaded from data, a call result, two origins).
    fn indirect_argument(
        &mut self,
        caller: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: Option<&Operand<'tcx>>,
        g: &str,
        input: Ty<'tcx>,
    ) -> (String, Vec<(String, Item)>) {
        let tcx = self.tcx;
        let shown = |t: Ty<'tcx>| with_no_visible_paths!(with_no_trimmed_paths!(t.to_string()));
        let unknown = |what: String| vec![(what.clone(), Item::Ev(Ev::Unknown(what)))];
        let not_known = format!(
            "the function passed for `{g}` is not known at this call site: it is not reified or unsized from one function or type on every path (a pointer loaded from data, a call result, or two origins)"
        );
        let Some(op) = op else {
            return (shown(input), unknown(not_known));
        };
        let mut origin = origin_of(tcx, body, op);
        // A parameter of the caller bound at the caller's call sites (top plan B):
        // what it holds there.
        if let Some(Origin::Arg(l)) = origin
            && let Some(Bind::Callable(c)) = self.bind_of(l)
        {
            match c {
                Callable::Pointee(t) => origin = Some(Origin::Pointee(t)),
                Callable::Fns(fs) if input.is_fn_ptr() => {
                    let items: Vec<(String, Item)> = fs
                        .into_iter()
                        .map(|f| (self.label(f), Item::Call(self.node_for(f))))
                        .collect();
                    let names: Vec<&str> = items.iter().map(|(l, _)| l.as_str()).collect();
                    let label = match names.as_slice() {
                        [one] => (*one).to_string(),
                        many => format!("one of {}", many.join(", ")),
                    };
                    return (label, items);
                }
                Callable::Declared(d, h) => {
                    if let Some(mark) = self.crates.param_mark(self.tcx, d)
                        && let Some(&(_, k)) = mark.params.iter().find(|(n, _)| *n == h)
                    {
                        let what = format!(
                            "call of parameter `{h}` of `{}`, declared `param({h} = {k})`",
                            def_path(tcx, d)
                        );
                        return (
                            shown(input),
                            vec![(what, Item::Evs(param_events(&h, k, &mark)))],
                        );
                    }
                }
                Callable::Fns(_) => {}
            }
        }
        // `&l` for a `&Box<dyn Fn*>` parameter: the box `l` (top plan T2).
        if let Some(Origin::Ref(l)) = origin {
            origin = origin_of(tcx, body, &Operand::Copy(mir::Place::from(l)));
        }
        match origin {
            Some(Origin::Fn(t)) if input.is_fn_ptr() => {
                let label = self.subst(caller, t).map_or_else(|| shown(t), shown);
                match self.function_item(caller, t) {
                    Some(item) => (label.clone(), vec![(label, item)]),
                    None => (label, unknown(not_known)),
                }
            }
            Some(o @ (Origin::Const(_) | Origin::Load(..))) if input.is_fn_ptr() => {
                let (c, proj) = match o {
                    Origin::Load(c, proj) => (c, Some(proj)),
                    Origin::Const(c) => (c, None),
                    _ => return (shown(input), unknown(not_known)),
                };
                let Some(targets) = self.data_targets(caller, c, proj) else {
                    return (shown(input), unknown(not_known));
                };
                let items: Vec<(String, Item)> = targets
                    .into_iter()
                    .map(|t| (self.label(t), Item::Call(self.node_for(t))))
                    .collect();
                let names: Vec<&str> = items.iter().map(|(l, _)| l.as_str()).collect();
                let label = match names.as_slice() {
                    [one] => (*one).to_string(),
                    many => format!("one of {}", many.join(", ")),
                };
                (label, items)
            }
            Some(Origin::Pointee(t)) => {
                let Some(principal) = self.callable_dyn(input) else {
                    return (shown(input), unknown(not_known));
                };
                let Some(t) = self.subst(caller, t) else {
                    return (shown(t), unknown(not_known));
                };
                let label = shown(t);
                let trait_ref = tcx
                    .instantiate_bound_regions_with_erased(principal)
                    .with_self_ty(tcx, t);
                let mut items = Vec::new();
                for m in tcx.associated_items(trait_ref.def_id).in_definition_order() {
                    if !m.is_fn() || !tcx.generics_of(m.def_id).own_params.is_empty() {
                        continue;
                    }
                    let item = match tcx.try_normalize_erasing_regions(
                        self.env,
                        ty::Unnormalized::new(trait_ref.args),
                    ) {
                        Ok(margs) => self.resolve(m.def_id, margs),
                        Err(_) => Item::Ev(Ev::Unknown(format!(
                            "`{}` for `{label}` (not normalizable)",
                            def_path(tcx, m.def_id)
                        ))),
                    };
                    items.push((def_path(tcx, m.def_id), item));
                }
                if items.is_empty() {
                    return (label, unknown(not_known));
                }
                (label, items)
            }
            Some(Origin::Arg(l)) => {
                let declared = match caller.def {
                    InstanceKind::Item(d) => self.declared_param(d, body, l),
                    _ => None,
                };
                let label = shown(input);
                match declared {
                    Some((h, k)) => {
                        let what = format!("call of parameter `{h}`, declared `param({h} = {k})`");
                        let evs = match caller.def {
                            InstanceKind::Item(d) => self
                                .crates
                                .param_mark(self.tcx, d)
                                .map(|m| param_events(&h, k, &m))
                                .unwrap_or_default(),
                            _ => Vec::new(),
                        };
                        (label, vec![(what, Item::Evs(evs))])
                    }
                    None => {
                        let name = l
                            .as_usize()
                            .checked_sub(1)
                            .and_then(|i| match caller.def {
                                InstanceKind::Item(d)
                                    if matches!(
                                        tcx.def_kind(d),
                                        DefKind::Fn | DefKind::AssocFn
                                    ) =>
                                {
                                    tcx.fn_arg_idents(d).get(i).copied().flatten()
                                }
                                _ => None,
                            })
                            .map_or_else(|| "?".to_string(), |i| i.name.to_string());
                        (
                            label,
                            unknown(format!(
                                "the function passed for `{g}` is the parameter `{name}` of `{}`, which declares no `param({name} = ..)`",
                                def_path(tcx, caller.def_id())
                            )),
                        )
                    }
                }
            }
            _ => (shown(input), unknown(not_known)),
        }
    }

    /// The recorded call sites whose argument violates the declared bound: `⊤`, or
    /// above `K` once the analysed function's own `param(..)` are instantiated (an
    /// argument still relative to generic parameters is checked where those are
    /// instantiated).
    fn arg_violations(&self, sums: &[Summary]) -> Vec<ArgViolation> {
        let mut out = Vec::new();
        for site in &self.arg_sites {
            let mut s = Summary::default();
            let mut cost = Cost::default();
            // The entry points are alternatives (`call`, `call_mut`, `call_once` of
            // one value): allocation witnesses come from one with the largest bound.
            let mut best: Option<(usize, B)> = None;
            for (_, item) in &site.items {
                if let Item::Call(j) = item
                    && best.is_none_or(|(_, c)| sums[*j].alloc.c > c)
                {
                    best = Some((*j, sums[*j].alloc.c));
                }
            }
            for (label, item) in &site.items {
                let unknown = |what: &String| Witness {
                    steps: Vec::new(),
                    what: what.clone(),
                    span: DUMMY_SP,
                    in_loop: false,
                };
                match item {
                    Item::Call(j) => {
                        let mut cs = sums[*j].clone();
                        cost = cost.max(&cs.alloc);
                        if best.is_some_and(|(b, _)| b != *j) {
                            cs.alloc_w.clear();
                        }
                        let step = Step {
                            label: self.nodes[*j].label.clone(),
                            span: DUMMY_SP,
                            in_loop: false,
                        };
                        s.merge_events(&cs, std::slice::from_ref(&step));
                        // Called through the parameter: Verus checked no
                        // precondition there (top plan T13.4).
                        if let Some(f) = &cs.verus_pre {
                            push_w(
                                &mut s.panics,
                                Witness {
                                    steps: vec![step],
                                    what: verus_pre_text(f),
                                    span: DUMMY_SP,
                                    in_loop: false,
                                },
                                MAX_WITNESSES,
                                key_site,
                            );
                        }
                    }
                    Item::Term(k) => {
                        cost = cost.max(&Cost::term(k));
                        let what = match self.owner_params.iter().find(|(g, _)| g == k) {
                            Some((g, n)) => {
                                format!(
                                    "call of parameter `{g}` (`{label}`), declared `param({g} = {n})`"
                                )
                            }
                            None => format!("call of `{k}` (`{label}`)"),
                        };
                        s.terms_w.entry(k.clone()).or_insert_with(|| unknown(&what));
                    }
                    Item::Ev(Ev::Unknown(w)) => {
                        push_w(&mut s.unknown, unknown(w), MAX_UNKNOWN, key_what);
                    }
                    // A parameter of the caller passed on: what the caller declares for
                    // it (`param(h = K')` and the caller's mark).
                    Item::Ev(ev) => cost = cost.max(&local_event(&mut s, ev, unknown)),
                    Item::Evs(evs) => {
                        let mut c = Cost::default();
                        for ev in evs {
                            c = c.add(&local_event(&mut s, ev, unknown));
                        }
                        cost = cost.max(&c);
                    }
                    Item::Many(_) | Item::Alt(_) => {
                        let what = "several callees (internal)".to_string();
                        push_w(&mut s.unknown, unknown(&what), MAX_UNKNOWN, key_what);
                    }
                }
            }
            s.alloc = cost.clone();
            let bound = cost.instantiate(&self.owner_params, &self.param_types);
            // A driver-mode `fip_fn!` in a generic function: the certificate claims
            // its bound for every instantiation, which a term left does not show.
            if site.certifying {
                for k in bound.terms.keys() {
                    let what = format!(
                        "`{k}` depends on the type parameters of the enclosing function: `fip_fn!(prelint, {}, ..)` claims its bound for every instantiation, which is not checked here",
                        site.declared
                    );
                    let w = Witness {
                        steps: Vec::new(),
                        what,
                        span: DUMMY_SP,
                        in_loop: false,
                    };
                    push_w(&mut s.unknown, w, MAX_UNKNOWN, key_what);
                }
            }
            // A call through a function pointer or trait object parameter is counted
            // by the declaration in the callee's body: the argument must not do what
            // the callee's mark forbids either.
            let forbidden = site.indirect.as_ref().and_then(|m| {
                if m.kind == crate::marks::Kind::Fip {
                    if let Some(w) = s.free.first() {
                        return Some(("may free".to_string(), w.clone()));
                    }
                    if let Some(w) = &s.recursion {
                        return Some(("recurses".to_string(), w.clone()));
                    }
                }
                if m.strict
                    && !m.panic_macros
                    && let Some(w) = s.panics.first()
                {
                    return Some(("may panic".to_string(), w.clone()));
                }
                None
            });
            let violated = !s.unknown.is_empty()
                || (bound.terms.is_empty() && bound.c.exceeds(site.declared))
                || forbidden.is_some();
            // The entry of the scanned body's call this site was reached through.
            let mut at = site.node;
            let mut via = None;
            while let Some(n) = self.nodes.get(at) {
                if let Some(v) = self.entries.get(&at) {
                    via = Some(v.clone());
                    break;
                }
                let Some(p) = n.parent else {
                    break;
                };
                at = p;
            }
            if violated {
                out.push(ArgViolation {
                    caller: site.caller.clone(),
                    caller_def: site.caller_def,
                    from_param: site.from_param,
                    span: site.span,
                    local: site.local,
                    callee: site.callee.clone(),
                    param: site.param.clone(),
                    declared: site.declared,
                    arg: site.arg.clone(),
                    bound,
                    summary: s,
                    forbidden,
                    via,
                });
            }
        }
        out
    }

    fn call_edges(&self, i: usize) -> Vec<usize> {
        match &self.nodes[i].kind {
            NodeKind::Body(info) => {
                let mut v: Vec<usize> = info
                    .blocks
                    .iter()
                    .flatten()
                    .flat_map(|s| s.item.calls())
                    .collect();
                v.sort_unstable();
                v.dedup();
                v
            }
            _ => Vec::new(),
        }
    }

    /// Steps from `from` to every node of `set` reachable inside `set` (BFS), and the
    /// shortest cycle back to `from`.
    fn paths_within(
        &self,
        from: usize,
        set: &HashSet<usize>,
    ) -> (HashMap<usize, Vec<Step>>, Vec<Step>) {
        let mut paths: HashMap<usize, Vec<Step>> = HashMap::new();
        paths.insert(from, Vec::new());
        let mut cycle = Vec::new();
        let mut q = VecDeque::from([from]);
        while let Some(u) = q.pop_front() {
            let NodeKind::Body(info) = &self.nodes[u].kind else {
                continue;
            };
            for (b, sites) in info.blocks.iter().enumerate() {
                for (s, j) in sites
                    .iter()
                    .flat_map(|s| s.item.calls().into_iter().map(move |j| (s, j)))
                {
                    if !set.contains(&j) {
                        continue;
                    }
                    let step = Step {
                        label: self.nodes[j].label.clone(),
                        span: s.span,
                        in_loop: info.in_loop[b],
                    };
                    if j == from && cycle.is_empty() {
                        let mut c = paths[&u].clone();
                        c.push(step.clone());
                        cycle = c;
                    }
                    if !paths.contains_key(&j) {
                        let mut p = paths[&u].clone();
                        p.push(step);
                        paths.insert(j, p);
                        q.push_back(j);
                    }
                }
            }
        }
        (paths, cycle)
    }

    /// Summary of one node; calls into `skip` (the node's own recursive component)
    /// contribute nothing here.
    fn node_summary(
        &self,
        i: usize,
        sums: &[Option<Summary>],
        skip: Option<&HashSet<usize>>,
    ) -> Summary {
        let mut s = Summary::default();
        match &self.nodes[i].kind {
            NodeKind::Pending => {
                s.unknown.push(Witness {
                    steps: Vec::new(),
                    what: format!("`{}` (not explored)", self.nodes[i].label),
                    span: DUMMY_SP,
                    in_loop: false,
                });
            }
            NodeKind::Leaf(evs) => {
                for ev in evs {
                    let w = |what: &String| Witness {
                        steps: Vec::new(),
                        what: what.clone(),
                        span: DUMMY_SP,
                        in_loop: false,
                    };
                    match ev {
                        Ev::Alloc(what) => {
                            s.alloc = s.alloc.add(&Cost::one());
                            // A source with `n = N` is N events and one witness.
                            if s.alloc_w.iter().all(|x| x.what != *what) {
                                s.alloc_w.push(w(what));
                            }
                        }
                        Ev::Free(what) => s.free.push(w(what)),
                        Ev::Panic(what) => s.panics.push(w(what)),
                        Ev::Unknown(what) => s.unknown.push(w(what)),
                        Ev::Bound(k, what) => {
                            s.alloc = s.alloc.add(&Cost {
                                c: B::Fin(*k),
                                terms: BTreeMap::new(),
                            });
                            if *k > 0 && s.alloc_w.iter().all(|x| x.what != *what) {
                                s.alloc_w.push(w(what));
                            }
                        }
                        Ev::Recurse(what) => {
                            if s.recursion.is_none() {
                                s.recursion = Some(w(what));
                            }
                        }
                        Ev::VerusPre(f) => {
                            if s.verus_pre.is_none() {
                                s.verus_pre = Some(f.clone());
                            }
                        }
                    }
                }
            }
            NodeKind::Body(info) => {
                let n = info.blocks.len();
                let mut bcost = vec![Cost::default(); n];
                for (b, cost) in bcost.iter_mut().enumerate() {
                    if !info.reachable[b] {
                        continue;
                    }
                    let in_loop = info.in_loop[b];
                    for site in &info.blocks[b] {
                        let c =
                            self.site_cost(i, &site.item, site.span, in_loop, sums, skip, &mut s);
                        *cost = cost.add(&c);
                    }
                }
                s.alloc = longest_path(info, &bcost);
            }
        }
        s
    }

    /// The cost of one site of a body (looped if `in_loop`), its events merged into
    /// `s`; calls into `skip` contribute nothing. Alternatives cost their maximum.
    #[allow(clippy::too_many_arguments)]
    fn site_cost(
        &self,
        caller: usize,
        item: &Item,
        span: Span,
        in_loop: bool,
        sums: &[Option<Summary>],
        skip: Option<&HashSet<usize>>,
        s: &mut Summary,
    ) -> Cost {
        let local = |what: &String| Witness {
            steps: Vec::new(),
            what: what.clone(),
            span,
            in_loop,
        };
        match item {
            Item::Call(j) => {
                if skip.is_some_and(|k| k.contains(j)) {
                    return Cost::default();
                }
                let Some(cs) = sums[*j].as_ref() else {
                    return Cost::default();
                };
                let step = Step {
                    label: self.nodes[*j].label.clone(),
                    span,
                    in_loop,
                };
                s.merge_events(cs, std::slice::from_ref(&step));
                if let Some(f) = &cs.verus_pre {
                    self.verus_obligation(caller, *j, f, span, in_loop, s);
                }
                cs.alloc.looped(in_loop)
            }
            Item::Term(k) => {
                s.terms_w
                    .entry(k.clone())
                    .or_insert_with(|| local(&format!("call of `{k}`")));
                Cost::term(k).looped(in_loop)
            }
            Item::Ev(ev) => local_event(s, ev, local).looped(in_loop),
            Item::Evs(evs) => {
                let mut c = Cost::default();
                for ev in evs {
                    c = c.add(&local_event(s, ev, local).looped(in_loop));
                }
                c
            }
            Item::Alt(items) => {
                let mut c = Cost::default();
                for item in items {
                    c = c.max(&self.site_cost(caller, item, span, in_loop, sums, skip, s));
                }
                c
            }
            // Flattened by `scan_body`; never stored.
            Item::Many(_) => {
                let what = "several callees (internal)".to_string();
                push_w(&mut s.unknown, local(&what), MAX_UNKNOWN, key_what);
                Cost::default()
            }
        }
    }

    /// The callee `j` had panic sites discharged by Verus under the `requires` of `f`
    /// (top plan T13.4). A direct call from a Verus-verified caller: Verus checked the
    /// precondition here, under the caller's own `requires`, which becomes the
    /// caller's obligation in turn (none if it has none). Any other call: the
    /// precondition is a panic path at this call site.
    fn verus_obligation(
        &self,
        caller: usize,
        j: usize,
        f: &str,
        span: Span,
        in_loop: bool,
        s: &mut Summary,
    ) {
        match self.verus_direct.get(&(caller, j, span)) {
            Some((g, true)) => {
                if s.verus_pre.is_none() {
                    s.verus_pre = Some(g.clone());
                }
            }
            Some((_, false)) => {}
            None => push_w(
                &mut s.panics,
                Witness {
                    steps: Vec::new(),
                    what: verus_pre_text(f),
                    span,
                    in_loop,
                },
                MAX_WITNESSES,
                key_site,
            ),
        }
    }

    fn evaluate(&self) -> Vec<Summary> {
        let n = self.nodes.len();
        let succ: Vec<Vec<usize>> = (0..n).map(|i| self.call_edges(i)).collect();
        let mut sums: Vec<Option<Summary>> = vec![None; n];
        for comp in tarjan(n, &succ) {
            let cyclic = comp.len() > 1 || succ[comp[0]].contains(&comp[0]);
            if !cyclic {
                let s = self.node_summary(comp[0], &sums, None);
                sums[comp[0]] = Some(s);
                continue;
            }
            let set: HashSet<usize> = comp.iter().copied().collect();
            let locals: Vec<Summary> = comp
                .iter()
                .map(|&m| self.node_summary(m, &sums, Some(&set)))
                .collect();
            let total = locals
                .iter()
                .fold(Cost::default(), |acc, l| acc.add(&l.alloc))
                .widen();
            for &m in &comp {
                let (paths, cycle) = self.paths_within(m, &set);
                let mut s = Summary {
                    alloc: total.clone(),
                    ..Summary::default()
                };
                for (k, &other) in comp.iter().enumerate() {
                    let prefix = paths.get(&other).cloned().unwrap_or_default();
                    s.merge_events(&locals[k], &prefix);
                    // Calls inside the cycle were skipped by `site_cost`: a Verus
                    // precondition of a member is a panic path for every member
                    // (conservative; Verus rejects recursion without `decreases`).
                    if let Some(f) = &locals[k].verus_pre {
                        push_w(
                            &mut s.panics,
                            Witness {
                                steps: prefix.clone(),
                                what: verus_pre_text(f),
                                span: DUMMY_SP,
                                in_loop: false,
                            },
                            MAX_WITNESSES,
                            key_site,
                        );
                    }
                }
                s.recursion = Some(Witness {
                    steps: cycle,
                    what: "recursion".to_string(),
                    span: DUMMY_SP,
                    in_loop: false,
                });
                sums[m] = Some(s);
            }
        }
        sums.into_iter().map(Option::unwrap_or_default).collect()
    }

    fn dump(&self) {
        eprintln!("fip-prelint dump: {} nodes", self.nodes.len());
        for (i, node) in self.nodes.iter().enumerate() {
            match &node.kind {
                NodeKind::Pending => eprintln!("  [{i}] {} : pending", node.label),
                NodeKind::Leaf(evs) => eprintln!("  [{i}] {} : leaf {evs:?}", node.label),
                NodeKind::Body(info) => {
                    let mut items = Vec::new();
                    for (b, sites) in info.blocks.iter().enumerate() {
                        for s in sites {
                            let l = if info.in_loop[b] { " (loop)" } else { "" };
                            match &s.item {
                                Item::Call(j) => items.push(format!("call [{j}]{l}")),
                                Item::Term(k) => items.push(format!("term {k}{l}")),
                                Item::Ev(e) => items.push(format!("{e:?}{l}")),
                                Item::Evs(es) => items.push(format!("{es:?}{l}")),
                                Item::Many(is) => items.push(format!("{is:?}{l}")),
                                Item::Alt(is) => items.push(format!("one of {is:?}{l}")),
                            }
                        }
                    }
                    eprintln!("  [{i}] {} : body {}", node.label, items.join(", "));
                }
            }
        }
        // Every source the root uses, with the location of its declaration: source
        // marks are trusted, so they are listed.
        for node in &self.nodes {
            let def_id = match node.inst.def {
                InstanceKind::Item(d) | InstanceKind::Virtual(d, _) => d,
                _ => continue,
            };
            if let NodeKind::Leaf(_) = node.kind
                && let Some((s, kind)) = self.crates.source_of(self.tcx, def_id)
            {
                let at = self
                    .tcx
                    .sess
                    .source_map()
                    .span_to_diagnostic_string(self.tcx.def_span(def_id));
                eprintln!(
                    "fip-prelint dump: source: `{}` ({}, {} allocation(s), free: {}) at {at}",
                    node.label,
                    kind.describe(),
                    s.alloc,
                    s.free
                );
            }
            if let NodeKind::Leaf(_) = node.kind
                && self.tcx.is_foreign_item(def_id)
            {
                let symbol = ffi_symbol(self.tcx, def_id);
                for d in self.crates.ffi_decls(&symbol) {
                    let at = self
                        .tcx
                        .sess
                        .source_map()
                        .span_to_diagnostic_string(self.tcx.def_span(d.def_id));
                    match &d.mark {
                        FfiMark::Cert(cert) => eprintln!(
                            "fip-prelint dump: certified foreign function: `{}` (symbol `{symbol}`, {} allocation(s), free: {}, evidence: {:?}) at {at}",
                            node.label, cert.alloc, cert.free, cert.evidence
                        ),
                        FfiMark::Exclude(excl) => {
                            let reason = excl
                                .reason
                                .as_deref()
                                .map(|r| format!(": {r}"))
                                .unwrap_or_default();
                            eprintln!(
                                "fip-prelint dump: excluded foreign function: `{}` (symbol `{symbol}`, user assumption{reason}) at {at}",
                                node.label
                            );
                        }
                    }
                }
            }
        }
    }

    /// With `FIP_PRELINT_DUMP=1`: every checked call site of a callee with
    /// `param(..)`, the argument and its bound before the analysed function's own
    /// `param(..)`.
    fn dump_args(&self, sums: &[Summary]) {
        if std::env::var_os("FIP_PRELINT_DUMP").is_none() {
            return;
        }
        let wit = |what: &String| Witness {
            steps: Vec::new(),
            what: what.clone(),
            span: DUMMY_SP,
            in_loop: false,
        };
        for site in &self.arg_sites {
            let mut cost = Cost::default();
            let mut unknown = false;
            for (_, item) in &site.items {
                match item {
                    Item::Call(j) => {
                        cost = cost.max(&sums[*j].alloc);
                        unknown |= !sums[*j].unknown.is_empty();
                    }
                    Item::Term(k) => cost = cost.max(&Cost::term(k)),
                    Item::Ev(Ev::Unknown(_)) => unknown = true,
                    Item::Ev(ev) => cost = cost.max(&local_event(&mut Summary::default(), ev, wit)),
                    Item::Evs(evs) => {
                        let mut c = Cost::default();
                        for ev in evs {
                            c = c.add(&local_event(&mut Summary::default(), ev, wit));
                        }
                        cost = cost.max(&c);
                    }
                    Item::Many(_) | Item::Alt(_) => unknown = true,
                }
            }
            let bound = if unknown {
                "⊤".to_string()
            } else {
                cost.display()
            };
            eprintln!(
                "fip-prelint dump: argument: `{}` -> `{}` for `{}` (param {} = {}): `{}`, bound {bound}",
                site.caller, site.callee, site.param, site.param, site.declared, site.arg
            );
        }
    }
}

/// The events of a call through the parameter `g` declared `param(g = k)` by a
/// function marked `m`: `k` allocations and what `m` allows (a free and recursion for
/// `fbip`, panics unless strict). Every call site checks its argument against them.
fn param_events(g: &str, k: u64, m: &Mark) -> Vec<Ev> {
    let mut evs = declared_events(
        &format!("call of parameter `{g}`"),
        &format!("`param({g} = {k})` of `{}`", m.tag()),
        m,
        k,
    );
    if k == 0 {
        // Keeps the call visible in dumps; costs nothing.
        evs.insert(
            0,
            Ev::Bound(
                0,
                format!("call of parameter `{g}`, declared `param({g} = 0)`"),
            ),
        );
    }
    evs
}

/// A witness as one line: `a` -> `b`: what.
fn plain_witness(w: &Witness) -> String {
    if w.steps.is_empty() {
        return w.what.clone();
    }
    let chain: Vec<String> = w.steps.iter().map(|s| format!("`{}`", s.label)).collect();
    format!("{}: {}", chain.join(" -> "), w.what)
}

/// A root summary as a std summary entry: terms over parameters stay open; any other
/// term (none is expected for a non-generic function) is `⊤`.
fn to_fn_summary(s: &Summary) -> crate::stdsum::FnSummary {
    use crate::stdsum::Count;
    let count = |b: B| match b {
        B::Fin(n) => Count::Fin(n),
        B::Inf => Count::Inf,
    };
    let mut f = crate::stdsum::FnSummary {
        alloc: count(s.alloc.c),
        ..Default::default()
    };
    for (k, m) in &s.alloc.terms {
        if m.is_zero() {
            continue;
        }
        if k.starts_with('§') {
            f.terms.push((count(*m), k.clone()));
        } else {
            f.top.push(format!("open term `{k}`"));
        }
    }
    f.free = s.free.iter().map(plain_witness).collect();
    f.panic = s.panics.iter().map(plain_witness).collect();
    f.top.extend(s.unknown.iter().map(plain_witness));
    f.recursion = s.recursion.as_ref().map(plain_witness);
    f
}

/// Adds one event found in a body (witness `w`) to `s`; returns its allocation cost.
/// The panic path of a call that Verus did not check against the callee's `requires`
/// (top plan T13.4).
fn verus_pre_text(f: &str) -> String {
    format!(
        "precondition of `{f}` verified by Verus only for Verus callers (its body's panic sites are discharged by Verus under its `requires`)"
    )
}

fn local_event(s: &mut Summary, ev: &Ev, w: impl Fn(&String) -> Witness) -> Cost {
    match ev {
        Ev::Alloc(what) => {
            push_w(&mut s.alloc_w, w(what), MAX_WITNESSES, key_site);
            return Cost::one();
        }
        Ev::Free(what) => push_w(&mut s.free, w(what), MAX_WITNESSES, key_site),
        Ev::Panic(what) => push_w(&mut s.panics, w(what), MAX_WITNESSES, key_site),
        Ev::Unknown(what) => push_w(&mut s.unknown, w(what), MAX_UNKNOWN, key_what),
        Ev::Bound(k, what) => {
            if *k > 0 {
                push_w(&mut s.alloc_w, w(what), MAX_WITNESSES, key_site);
            }
            return Cost {
                c: B::Fin(*k),
                terms: BTreeMap::new(),
            };
        }
        Ev::Recurse(what) => {
            if s.recursion.is_none() {
                s.recursion = Some(w(what));
            }
        }
        Ev::VerusPre(f) => {
            if s.verus_pre.is_none() {
                s.verus_pre = Some(f.clone());
            }
        }
    }
    Cost::default()
}

/// The events of a call whose behaviour is declared rather than analysed (`what`
/// describes the call, `by` the declaration): `n` allocations; for `fbip`, a possible
/// free and recursion; panic paths unless `strict = true, panic_macros = false`. Used
/// for a dynamic call of a trait method with a contract (`m` is the contract) and for
/// a call through a parameter declared `param(g = K)` (`m` is the function's mark,
/// `n = K`); in both cases what is declared is checked elsewhere (every
/// implementation, every call site).
fn declared_events(what: &str, by: &str, m: &Mark, n: u64) -> Vec<Ev> {
    let mut evs = Vec::new();
    if n > 0 {
        evs.push(Ev::Bound(
            n,
            format!("{what}: {n} allocation(s) declared by {by}"),
        ));
    }
    if m.kind == marks::Kind::Fbip {
        evs.push(Ev::Free(format!("{what}: {by} allows frees (`fbip`)")));
        evs.push(Ev::Recurse(format!(
            "{what}: {by} allows recursion (`fbip`)"
        )));
    }
    if !m.strict {
        evs.push(Ev::Panic(format!(
            "{what}: {by} is not strict, it may panic"
        )));
    } else if m.panic_macros {
        evs.push(Ev::Panic(format!(
            "{what}: {by} allows panic paths (`panic_macros = true`)"
        )));
    }
    evs
}

/// The events of a dynamic call of the trait method `path` whose declaration carries
/// the contract `m`.
fn contract_events(path: &str, m: &Mark) -> Vec<Ev> {
    contract_call_events(&format!("dynamic call of `{path}`"), m)
}

fn contract_call_events(what: &str, m: &Mark) -> Vec<Ev> {
    let n = if m.kind == marks::Kind::Fip { m.n } else { 0 };
    declared_events(what, &format!("its contract `{}`", m.tag()), m, n)
}

/// Where a function pointer or a pointer to a trait object in one body comes from,
/// when it is the same on every path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Origin<'tcx> {
    /// Reified from a function item or a closure (its type, in the body's MIR).
    Fn(Ty<'tcx>),
    /// Unsized from a pointer to this concrete type (in the body's MIR).
    Pointee(Ty<'tcx>),
    /// The value of a parameter of the body, never reassigned.
    Arg(mir::Local),
    /// The output (`buf`) of the `fmt::Formatter` that the parameter in this local
    /// points to.
    BufOf(mir::Local),
    /// A constant (of function pointer type, or a reference to immutable data).
    Const(mir::Const<'tcx>),
    /// A load at these projections below the reference constant: a `static` or
    /// constant memory ([`Analysis::data_targets`] decides whether it is immutable).
    Load(mir::Const<'tcx>, &'tcx ty::List<mir::PlaceElem<'tcx>>),
    /// A shared reference to this local of the body (`&l`).
    Ref(mir::Local),
    /// The value behind the reference parameter in this local, never reassigned
    /// (`*_1` in the `Fn` shim of a function pointer).
    DerefArg(mir::Local),
    /// The pointer owned by the `Box` behind the reference parameter in this local
    /// (`(*_1).0`, cast to `*const F`, reborrowed: the receiver in `<Box<F, A> as
    /// Fn<Args>>::call`).
    BoxPtr(mir::Local),
    /// The value at these projections (fields, and dereferences of references)
    /// below the parameter in this local, never reassigned, where every read of the
    /// place yields the value it held on entry ([`OriginCx::stable_below`]): fields of
    /// the parameter's own value, of memory behind a shared reference to a `Freeze`
    /// type, or audited fields of `core::fmt` that are never reassigned
    /// ([`AUDITED_FIELDS`]); top plan T7a/b.
    ArgAt(mir::Local, &'tcx ty::List<mir::PlaceElem<'tcx>>),
    /// An element of the local array in this local ([`OriginCx::elems`]): the one at
    /// the constant index, or any ([`array_elems`] lists the candidates).
    Elems(mir::Local, Option<u64>),
}

/// `Rc<T, A>` or `Arc<T, A>`: its pointee type `T`.
fn shared_ptr_pointee<'tcx>(tcx: TyCtxt<'tcx>, t: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let ty::Adt(def, args) = *t.kind() else {
        return None;
    };
    let d = def.did();
    let shared = tcx.is_diagnostic_item(rustc_span::sym::Rc, d)
        || tcx.is_diagnostic_item(rustc_span::sym::Arc, d);
    shared.then(|| args.type_at(0))
}

/// The operands a read of the local array `l` at `idx` (any element for `None`) may
/// yield: the elements of every array aggregate or repeat assigned to `l`
/// ([`OriginCx::elems`] checked that these are its only assignments).
fn array_elems<'b, 'tcx>(
    body: &'b Body<'tcx>,
    l: mir::Local,
    idx: Option<u64>,
) -> Vec<&'b Operand<'tcx>> {
    let mut out = Vec::new();
    for data in body.basic_blocks.iter() {
        for st in &data.statements {
            let mir::StatementKind::Assign(assign) = &st.kind else {
                continue;
            };
            if assign.0.local != l || !assign.0.projection.is_empty() {
                continue;
            }
            match &assign.1 {
                mir::Rvalue::Repeat(op, _) => out.push(op),
                mir::Rvalue::Aggregate(_, ops) => match idx {
                    Some(i) => out.extend(usize::try_from(i).ok().and_then(|i| ops.raw.get(i))),
                    None => out.extend(ops.iter()),
                },
                _ => {}
            }
        }
    }
    out
}

/// The output of a formatting: a concrete type implementing `fmt::Write`, or
/// (generating std summaries) a parameter of the summarised function, or a
/// `core::fmt::builders::PadAdapter` writing to an output (the `{:#?}` path, top plan
/// T7b).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Out<'tcx> {
    Ty(Ty<'tcx>),
    Param(u32),
    Pad(Box<Out<'tcx>>),
}

/// What a `&dyn fmt::Debug`/`&dyn fmt::Display` parameter holds (top plan T7a): a
/// trait object unsized from a pointer to this concrete type, or (generating std
/// summaries) the summarised function's parameter.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Obj<'tcx> {
    Ty(Ty<'tcx>),
    Param(u32),
}

/// A path below a parameter in a [`Bind::At`]: field indices, and
/// [`PATH_DEREF`] for a dereference.
type Path = Vec<u32>;

/// A dereference in a [`Path`].
const PATH_DEREF: u32 = u32::MAX;

/// What a parameter of an analysed body holds, known at the call sites of its node.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Bind<'tcx> {
    /// A `&mut dyn fmt::Write` writing to this output.
    Dyn(Out<'tcx>),
    /// A `&mut fmt::Formatter` writing to this output.
    Formatter(Out<'tcx>),
    /// A value containing `fmt::Arguments`/`fmt::rt::Argument`: the formatting
    /// functions it may carry (function item or closure types) and, generating std
    /// summaries, the summarised function's parameters whose functions it carries.
    Fmt(Vec<Ty<'tcx>>, Vec<u32>),
    /// A callable value (a function pointer, a `&dyn Fn*`) known at the call sites
    /// (top plan B).
    Callable(Callable<'tcx>),
    /// A `&dyn fmt::Debug`/`&dyn fmt::Display` known at the call sites (top plan
    /// T7a).
    Obj(Obj<'tcx>),
    /// What the place at this path below the parameter holds (a formatter, an
    /// output or a `dyn Debug` inside a closure's captures or a `core::fmt` builder;
    /// top plan T7a/b). A parameter may have several.
    At(Path, Box<Bind<'tcx>>),
    /// A shared reference to immutable data holding function pointers: this
    /// reference constant (a `static` or constant memory, as [`Origin::Const`]), so
    /// loads below the parameter read the evaluated initializer (top plan T7g with
    /// T1.2: `&'static LocalKey`).
    Data(mir::Const<'tcx>),
}

/// What a callable parameter holds, known at the call sites of a node: a must-fact
/// of every call site that reaches it (top plan B).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Callable<'tcx> {
    /// A function pointer to one of these functions (a reified function or
    /// closure, a constant, the candidates of immutable data).
    Fns(Vec<Instance<'tcx>>),
    /// A callable trait object unsized from a pointer to this concrete type.
    Pointee(Ty<'tcx>),
    /// A parameter `g` of the function `d` that declares `param(g = K)`: calls cost
    /// what that declaration allows (checked at every call site of `d`).
    Declared(DefId, String),
}

/// Nodes with callable bindings on the way from the root before an argument is no
/// longer bound (the node falls back to no binding, as without top plan B).
const MAX_CALLABLE_DEPTH: usize = 3;

/// Bindings of a node's parameters, by local (`1..=arg_count`).
type Binds<'tcx> = Vec<(u32, Bind<'tcx>)>;

fn adt_is(tcx: TyCtxt<'_>, ty: Ty<'_>, path: &str) -> bool {
    matches!(ty.kind(), ty::Adt(def, _) if std_path(tcx, def.did()) == path)
}

/// `&mut fmt::Formatter` (or a shared reference to one).
fn is_formatter_ref(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Ref(..)) && adt_is(tcx, ty.peel_refs(), "core::fmt::Formatter")
}

/// `&mut dyn fmt::Write` (or a shared reference to one).
fn is_dyn_write_ref(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    let ty::Ref(_, inner, _) = *ty.kind() else {
        return false;
    };
    matches!(inner.kind(), ty::Dynamic(preds, ..)
        if preds.principal_def_id().is_some_and(|d| std_path(tcx, d) == "core::fmt::Write"))
}

/// `&dyn fmt::Debug` or `&dyn fmt::Display` (a value formatted through `core`'s debug
/// builders, top plan T7a).
fn is_obj_ref(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    let ty::Ref(_, inner, _) = *ty.kind() else {
        return false;
    };
    matches!(inner.kind(), ty::Dynamic(preds, ..)
    if preds.principal_def_id().is_some_and(|d| {
        matches!(std_path(tcx, d).as_str(), "core::fmt::Debug" | "core::fmt::Display")
    }))
}

/// What a place found by [`bindable_paths`] holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Leaf {
    /// `&(mut) fmt::Formatter`.
    Formatter,
    /// `&(mut) dyn fmt::Write`.
    Dyn,
    /// `&dyn fmt::Debug`/`&dyn fmt::Display`.
    Obj,
}

fn leaf_of(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Option<Leaf> {
    let ty::Ref(_, inner, _) = *ty.kind() else {
        return None;
    };
    if adt_is(tcx, inner, "core::fmt::Formatter") {
        Some(Leaf::Formatter)
    } else if is_dyn_write_ref(tcx, ty) {
        Some(Leaf::Dyn)
    } else if is_obj_ref(tcx, ty) {
        Some(Leaf::Obj)
    } else {
        None
    }
}

/// The places below a value of type `ty` (fields of closures' captures, of tuples and
/// of `core::fmt::builders` types, through references) that hold a formatter, an
/// output or a `dyn Debug`/`dyn Display` (top plan T7a/b), as projections from the
/// value. Bounded in depth and number.
fn bindable_paths<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Vec<(Vec<mir::PlaceElem<'tcx>>, Leaf)> {
    const MAX_DEPTH: usize = 6;
    const MAX_PATHS: usize = 8;
    fn walk<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
        prefix: &mut Vec<mir::PlaceElem<'tcx>>,
        out: &mut Vec<(Vec<mir::PlaceElem<'tcx>>, Leaf)>,
    ) {
        if prefix.len() >= MAX_DEPTH || out.len() >= MAX_PATHS {
            return;
        }
        let fields: Vec<Ty<'tcx>> = match *ty.kind() {
            ty::Ref(_, inner, _) => {
                if container(tcx, inner) {
                    prefix.push(mir::ProjectionElem::Deref);
                    walk(tcx, inner, prefix, out);
                    prefix.pop();
                }
                return;
            }
            ty::Closure(_, args) => args.as_closure().upvar_tys().iter().collect(),
            ty::Tuple(ts) => ts.iter().collect(),
            ty::Adt(def, args) if container(tcx, ty) => def
                .non_enum_variant()
                .fields
                .iter()
                .map(|f| f.ty(tcx, args).skip_norm_wip())
                .collect(),
            _ => return,
        };
        for (i, ft) in fields.into_iter().enumerate() {
            prefix.push(mir::ProjectionElem::Field(
                rustc_abi::FieldIdx::from_usize(i),
                ft,
            ));
            match leaf_of(tcx, ft) {
                Some(leaf) => {
                    if out.len() < MAX_PATHS {
                        out.push((prefix.clone(), leaf));
                    }
                }
                None => walk(tcx, ft, prefix, out),
            }
            prefix.pop();
        }
    }
    /// Types whose fields are looked into: closures, tuples, and the structs of
    /// `core::fmt::builders`.
    fn container<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            ty::Closure(..) | ty::Tuple(..) => true,
            ty::Adt(def, _) => {
                def.is_struct() && std_path(tcx, def.did()).starts_with("core::fmt::builders::")
            }
            _ => false,
        }
    }
    let mut out = Vec::new();
    if container(tcx, ty.peel_refs()) {
        walk(tcx, ty, &mut Vec::new(), &mut out);
    }
    out
}

/// `&T` (shared) where `T` holds a function pointer in a field (structs and tuples,
/// two levels): a reference whose target, if it is immutable data, is resolved
/// through [`Bind::Data`] (top plan T7g).
fn holds_fn_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    fn has<'tcx>(tcx: TyCtxt<'tcx>, t: Ty<'tcx>, depth: u8) -> bool {
        match *t.kind() {
            ty::FnPtr(..) => true,
            ty::Tuple(ts) if depth > 0 => ts.iter().any(|t| has(tcx, t, depth - 1)),
            ty::Adt(def, args) if depth > 0 && def.is_struct() => def
                .non_enum_variant()
                .fields
                .iter()
                .any(|f| has(tcx, f.ty(tcx, args).skip_norm_wip(), depth - 1)),
            _ => false,
        }
    }
    matches!(*ty.kind(), ty::Ref(_, inner, ty::Mutability::Not) if has(tcx, inner, 2))
}

/// The [`Path`] of a projection of fields and dereferences.
fn place_path(proj: &[mir::PlaceElem<'_>]) -> Option<Path> {
    proj.iter()
        .map(|e| match e {
            mir::ProjectionElem::Deref => Some(PATH_DEREF),
            mir::ProjectionElem::Field(f, _) => u32::try_from(f.as_usize()).ok(),
            _ => None,
        })
        .collect()
}

/// Fields of `core::fmt` that are private to `core` and assigned only where their
/// struct is built, never afterwards (audited in the sources of rustc 1.99.1, which
/// the std summaries' stamp pins; reopen on a repin): reading one through a `&mut`
/// always yields the value it was built with (top plan T7a/b).
const AUDITED_FIELDS: &[(&str, &str)] = &[
    ("core::fmt::Formatter", "buf"),
    ("core::fmt::builders::PadAdapter", "buf"),
    ("core::fmt::builders::DebugStruct", "fmt"),
    ("core::fmt::builders::DebugTuple", "fmt"),
    ("core::fmt::builders::DebugInner", "fmt"),
    ("core::fmt::builders::DebugList", "inner"),
    ("core::fmt::builders::DebugSet", "inner"),
    ("core::fmt::builders::DebugMap", "fmt"),
];

/// `true` if field `f` of the struct type `ty` is in [`AUDITED_FIELDS`].
fn audited_field(tcx: TyCtxt<'_>, ty: Ty<'_>, f: rustc_abi::FieldIdx) -> bool {
    let ty::Adt(def, _) = ty.kind() else {
        return false;
    };
    if !def.is_struct() {
        return false;
    }
    let path = std_path(tcx, def.did());
    let Some(field) = def.non_enum_variant().fields.get(f) else {
        return false;
    };
    AUDITED_FIELDS
        .iter()
        .any(|(p, n)| *p == path && field.name.as_str() == *n)
}

/// The field names, from the result, at which the builder that the `core::fmt`
/// function `d` returns holds its first argument (the formatter): `debug_struct_new`
/// and `Formatter::debug_struct` build `DebugStruct { fmt, .. }`, `debug_list_new`
/// `DebugList { inner: DebugInner { fmt, .. } }`, and so on (audited in the sources of
/// rustc 1.99.1; top plan T7a).
fn builder_ctor_fields(tcx: TyCtxt<'_>, d: DefId) -> Option<&'static [&'static str]> {
    let name = tcx.item_name(d);
    let formatter_method = tcx.impl_of_assoc(d).is_some_and(|i| {
        matches!(tcx.def_kind(i), DefKind::Impl { of_trait: false })
            && adt_is(
                tcx,
                tcx.type_of(i).instantiate_identity().skip_norm_wip(),
                "core::fmt::Formatter",
            )
    });
    let builders = std_path(tcx, d).starts_with("core::fmt::builders::");
    match name.as_str() {
        "debug_struct" | "debug_tuple" | "debug_map" if formatter_method => Some(&["fmt"]),
        "debug_list" | "debug_set" if formatter_method => Some(&["inner", "fmt"]),
        "debug_struct_new" | "debug_tuple_new" | "debug_map_new" if builders => Some(&["fmt"]),
        "debug_list_new" | "debug_set_new" if builders => Some(&["inner", "fmt"]),
        _ => None,
    }
}

/// `true` for a method of a `core::fmt::builders` struct returning `&mut Self`
/// (`DebugStruct::field`, `DebugList::entries`, `DebugMap::key`, ..): every one
/// returns its receiver `self` (audited in the sources of rustc 1.99.1; top plan T7a).
fn returns_receiver(tcx: TyCtxt<'_>, d: DefId) -> bool {
    let Some(i) = tcx.impl_of_assoc(d) else {
        return false;
    };
    if !matches!(tcx.def_kind(i), DefKind::Impl { of_trait: false }) {
        return false;
    }
    let self_ty = tcx.type_of(i).instantiate_identity().skip_norm_wip();
    let ty::Adt(def, _) = self_ty.kind() else {
        return false;
    };
    if !std_path(tcx, def.did()).starts_with("core::fmt::builders::") {
        return false;
    }
    let sig = tcx.fn_sig(d).skip_binder().skip_binder();
    let recv_is_mut_self = sig.inputs().first().is_some_and(|t| {
        matches!(*t.kind(), ty::Ref(_, inner, m) if m.is_mut() && matches!(inner.kind(), ty::Adt(a, _) if a.did() == def.did()))
    });
    let out_is_mut_self = matches!(*sig.output().kind(),
        ty::Ref(_, inner, m) if m.is_mut() && matches!(inner.kind(), ty::Adt(a, _) if a.did() == def.did()));
    recv_is_mut_self && out_is_mut_self
}

/// `true` for `core::fmt::builders::PadAdapter::wrap(fmt, slot, state)`: it returns a
/// `Formatter` writing to a `PadAdapter` (in `slot`) over `fmt`'s output (audited in
/// the sources of rustc 1.99.1: `fmt.wrap_buf(move |buf| slot.insert(PadAdapter {
/// buf, state }))`; top plan T7b).
fn is_pad_wrap(tcx: TyCtxt<'_>, d: DefId) -> bool {
    tcx.item_name(d).as_str() == "wrap"
        && tcx.impl_of_assoc(d).is_some_and(|i| {
            adt_is(
                tcx,
                tcx.type_of(i).instantiate_identity().skip_norm_wip(),
                "core::fmt::builders::PadAdapter",
            )
        })
}

/// The text of an output in a summary term (`param <j>`, `pad <out>`, `ty <type>`).
fn out_desc(out: &Out<'_>) -> String {
    match out {
        Out::Param(j) => format!("param {j}"),
        Out::Pad(inner) => format!("pad {}", out_desc(inner)),
        Out::Ty(t) => format!(
            "ty {}",
            with_no_visible_paths!(with_no_trimmed_paths!(t.to_string()))
        ),
    }
}

/// `true` if a value of `ty` may contain `fmt::Arguments` or `fmt::rt::Argument`
/// (through generic arguments, closure captures, references, and ADT fields up to
/// `depth` levels).
fn mentions_fmt_args<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: u8) -> bool {
    for t in ty.walk() {
        let Some(t) = t.as_type() else {
            continue;
        };
        if adt_is(tcx, t, "core::fmt::Arguments") || adt_is(tcx, t, "core::fmt::rt::Argument") {
            return true;
        }
        if depth > 0
            && let ty::Adt(def, args) = *t.kind()
        {
            for f in def.all_fields() {
                if mentions_fmt_args(tcx, f.ty(tcx, args).skip_norm_wip(), depth - 1) {
                    return true;
                }
            }
        }
    }
    false
}

/// `true` if `body` calls a `fmt::Arguments` or `fmt::rt::Argument` constructor
/// (`new*`, `from*`).
fn body_builds_arguments<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    body.basic_blocks.iter().any(|data| {
        matches!(&data.terminator().kind, TerminatorKind::Call { func, .. }
            if matches!(*func.ty(&body.local_decls, tcx).kind(), ty::FnDef(d, _) if {
                let p = std_path(tcx, d);
                let name = tcx.item_name(d);
                let ctor = name.as_str().starts_with("new") || name.as_str().starts_with("from");
                ctor && (p.starts_with("core::fmt::rt::Argument::") || p.starts_with("core::fmt::Arguments::"))
            }))
    })
}

/// Where a part of a value containing `fmt::Arguments` comes from.
enum FmtSrc<'tcx> {
    /// A parameter (never reassigned) of the body.
    Param(mir::Local),
    /// A call of an `rt::Argument` constructor (its function item type).
    Ctor(Ty<'tcx>),
}

/// Where a `&mut fmt::Formatter` comes from.
enum FmtrSrc<'b, 'tcx> {
    /// A parameter (never reassigned) of the body.
    Param(mir::Local),
    /// `Formatter::new(out, ..)` in the body: `out`.
    New(&'b Operand<'tcx>),
    /// A formatter at this path below a parameter ([`Origin::ArgAt`]).
    At(mir::Local, &'tcx ty::List<mir::PlaceElem<'tcx>>),
    /// `PadAdapter::wrap(fmt, ..)` in the body ([`is_pad_wrap`]): a `PadAdapter` over
    /// the output of the formatter `fmt`.
    Pad(&'b Operand<'tcx>),
}

/// One assignment of a whole local.
enum Def<'b, 'tcx> {
    Rv(&'b mir::Rvalue<'tcx>),
    /// The destination of a call: its callee and arguments.
    Call(&'b Operand<'tcx>, &'b [Spanned<Operand<'tcx>>]),
}

/// Locals whose value may change other than by an assignment of the whole local:
/// a mutable borrow, a write to a field, a call or `asm!` destination. Writes through
/// a dereference (`*p = ..`, `&mut *p`) change the pointee, not the pointer.
struct Unstable(Vec<bool>);

impl<'tcx> mir::visit::Visitor<'tcx> for Unstable {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        ctx: mir::visit::PlaceContext,
        _: mir::Location,
    ) {
        use mir::visit::{MutatingUseContext, PlaceContext};
        let PlaceContext::MutatingUse(m) = ctx else {
            return;
        };
        let through_deref = place.projection.first() == Some(&mir::ProjectionElem::Deref);
        let whole = place.projection.is_empty()
            && matches!(
                m,
                MutatingUseContext::Store | MutatingUseContext::Drop | MutatingUseContext::Call
            );
        if !through_deref && !whole {
            self.0[place.local.as_usize()] = true;
        }
    }
}

/// A must-analysis over one body: the origin of `op` if every assignment that can
/// produce its value (through copies, moves and reborrows `&*p`) is the same
/// reification of one function or closure, the same unsizing of one concrete type,
/// the unchanged parameter, the same constant, the same load below a constant
/// reference, or the same field of a local aggregate. Anything else (two origins, a
/// value loaded through a parameter, a call result, a local changed in place) is
/// `None`.
fn origin_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    op: &Operand<'tcx>,
) -> Option<Origin<'tcx>> {
    OriginCx::new(tcx, body).operand(op, 0)
}

/// [`origin_of`] for an operand whose type in the instance being analysed is a
/// function pointer (or a reference to one): a mutable borrow `&mut l` used only as
/// the receiver of `FnMut::call_mut` does not change `l` ([`OriginCx::new_fn_ptr`]).
fn origin_of_fn_ptr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    op: &Operand<'tcx>,
) -> Option<Origin<'tcx>> {
    OriginCx::new_fn_ptr(tcx, body).operand(op, 0)
}

struct OriginCx<'b, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'b Body<'tcx>,
    unstable: Vec<bool>,
    writes: Vec<Vec<Def<'b, 'tcx>>>,
    /// `&mut l` used only as the receiver of `FnMut::call_mut` is `Origin::Ref(l)`
    /// and does not make `l` unstable ([`OriginCx::new_fn_ptr`]).
    fn_ptr: bool,
}

impl<'b, 'tcx> OriginCx<'b, 'tcx> {
    const MAX_DEPTH: usize = 32;

    /// The assignments of every whole local of `body` (statements and call
    /// destinations) and the locals changed in any other way.
    fn new(tcx: TyCtxt<'tcx>, body: &'b Body<'tcx>) -> OriginCx<'b, 'tcx> {
        use mir::visit::Visitor;
        let n = body.local_decls.len();
        let mut unstable = Unstable(vec![false; n]);
        unstable.visit_body(body);
        let mut writes: Vec<Vec<Def<'b, 'tcx>>> = (0..n).map(|_| Vec::new()).collect();
        for data in body.basic_blocks.iter() {
            for st in &data.statements {
                if let mir::StatementKind::Assign(assign) = &st.kind
                    && assign.0.projection.is_empty()
                {
                    writes[assign.0.local.as_usize()].push(Def::Rv(&assign.1));
                }
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &data.terminator().kind
                && destination.projection.is_empty()
            {
                writes[destination.local.as_usize()].push(Def::Call(func, args));
            }
        }
        OriginCx {
            tcx,
            body,
            unstable: unstable.0,
            writes,
            fn_ptr: false,
        }
    }

    /// [`OriginCx::new`] for reading a function pointer (top plan T1 residue): a
    /// mutable borrow `_t = &mut l` of a whole local `l` declared as a function
    /// pointer or a type parameter, where `_t` is used only once, moved as the
    /// receiver of `<_ as FnMut<_>>::call_mut`, does not make `l` unstable. Sound only
    /// where `l` holds a function pointer in the instance (the caller checks the
    /// operand's type): then that call is the function pointer's `FnMut` shim, which
    /// reads `*self` and never writes it.
    fn new_fn_ptr(tcx: TyCtxt<'tcx>, body: &'b Body<'tcx>) -> OriginCx<'b, 'tcx> {
        use mir::visit::Visitor;
        let mut cx = OriginCx::new(tcx, body);
        cx.fn_ptr = true;
        let Some(fn_mut) = tcx.lang_items().fn_mut_trait() else {
            return cx;
        };
        // Receivers moved into `FnMut::call_mut`.
        let mut receivers = Vec::new();
        for data in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, args, .. } = &data.terminator().kind
                && let ty::FnDef(d, _) = *func.ty(&body.local_decls, tcx).kind()
                && tcx.trait_of_assoc(d) == Some(fn_mut)
                && let Some(Operand::Move(r)) = args.first().map(|a| &a.node)
                && r.projection.is_empty()
            {
                receivers.push(r.local);
            }
        }
        // Uses of every local (a receiver must have exactly its assignment and the move).
        struct Uses(Vec<u32>);
        impl<'tcx> Visitor<'tcx> for Uses {
            fn visit_local(
                &mut self,
                l: mir::Local,
                _: mir::visit::PlaceContext,
                _: mir::Location,
            ) {
                self.0[l.as_usize()] += 1;
            }
        }
        let mut uses = Uses(vec![0; body.local_decls.len()]);
        uses.visit_body(body);
        let mut exempt = Vec::new();
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for (i, st) in data.statements.iter().enumerate() {
                if let mir::StatementKind::Assign(assign) = &st.kind
                    && assign.0.projection.is_empty()
                    && let mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, q) = &assign.1
                    && q.projection.is_empty()
                    && receivers.iter().filter(|r| **r == assign.0.local).count() == 1
                    && uses.0[assign.0.local.as_usize()] == 2
                    && matches!(
                        body.local_decls[q.local].ty.kind(),
                        ty::FnPtr(..) | ty::Param(_)
                    )
                {
                    exempt.push(mir::Location {
                        block: bb,
                        statement_index: i,
                    });
                }
            }
        }
        if exempt.is_empty() {
            return cx;
        }
        // Instability again, without the exempt borrows.
        struct Except<'e> {
            inner: Unstable,
            exempt: &'e [mir::Location],
        }
        impl<'tcx> Visitor<'tcx> for Except<'_> {
            fn visit_place(
                &mut self,
                place: &mir::Place<'tcx>,
                ctx: mir::visit::PlaceContext,
                loc: mir::Location,
            ) {
                if !self.exempt.contains(&loc) {
                    self.inner.visit_place(place, ctx, loc);
                }
            }
        }
        let mut v = Except {
            inner: Unstable(vec![false; body.local_decls.len()]),
            exempt: &exempt,
        };
        v.visit_body(body);
        cx.unstable = v.inner.0;
        cx
    }

    /// `true` for a parameter local (`1..=arg_count`).
    fn is_arg(&self, l: mir::Local) -> bool {
        (1..=self.body.arg_count).contains(&l.as_usize())
    }

    /// `(*f).buf` with `f: &mut fmt::Formatter` a parameter: `f`.
    fn buf_of(&self, p: mir::Place<'tcx>, depth: usize) -> Option<Origin<'tcx>> {
        let [
            mir::ProjectionElem::Deref,
            mir::ProjectionElem::Field(_, fty),
        ] = p.projection.as_slice()
        else {
            return None;
        };
        let base = self.body.local_decls[p.local].ty;
        if !is_formatter_ref(self.tcx, base) || !is_dyn_write_ref(self.tcx, *fty) {
            return None;
        }
        match self.local(p.local, depth)? {
            Origin::Arg(l) => Some(Origin::BufOf(l)),
            _ => None,
        }
    }

    /// The sources of the formatting functions in a value containing
    /// `fmt::Arguments` (see [`Analysis::fmt_set`]).
    fn fmt_sources(&self, op: &Operand<'tcx>, depth: usize) -> Option<Vec<FmtSrc<'tcx>>> {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.fmt_place(*p, depth),
            Operand::Constant(c) => (!mentions_fmt_args(self.tcx, c.ty(), 2)).then(Vec::new),
            _ => None,
        }
    }

    /// A part of a value (fields, elements, the pointee) carries no formatting
    /// function the value does not.
    fn fmt_place(&self, p: mir::Place<'tcx>, depth: usize) -> Option<Vec<FmtSrc<'tcx>>> {
        let parts = p.projection.iter().all(|e| {
            matches!(
                e,
                mir::ProjectionElem::Deref
                    | mir::ProjectionElem::Field(..)
                    | mir::ProjectionElem::Index(_)
                    | mir::ProjectionElem::ConstantIndex { .. }
                    | mir::ProjectionElem::Subslice { .. }
                    | mir::ProjectionElem::Downcast(..)
            )
        });
        if !parts {
            return None;
        }
        self.fmt_local(p.local, depth)
    }

    fn fmt_local(&self, l: mir::Local, depth: usize) -> Option<Vec<FmtSrc<'tcx>>> {
        if depth > Self::MAX_DEPTH || self.unstable[l.as_usize()] {
            return None;
        }
        let writes = &self.writes[l.as_usize()];
        if self.is_arg(l) {
            return writes.is_empty().then(|| vec![FmtSrc::Param(l)]);
        }
        if writes.is_empty() {
            return None;
        }
        let mut v = Vec::new();
        for w in writes {
            let part = match w {
                Def::Rv(rv) => self.fmt_rvalue(rv, depth + 1)?,
                Def::Call(func, args) => self.fmt_call(func, args, depth + 1)?,
            };
            v.extend(part);
        }
        Some(v)
    }

    fn fmt_rvalue(&self, rv: &mir::Rvalue<'tcx>, depth: usize) -> Option<Vec<FmtSrc<'tcx>>> {
        match rv {
            mir::Rvalue::Use(op, ..) | mir::Rvalue::Cast(_, op, _) | mir::Rvalue::Repeat(op, _) => {
                self.fmt_sources(op, depth)
            }
            mir::Rvalue::CopyForDeref(p)
            | mir::Rvalue::Ref(_, _, p)
            | mir::Rvalue::RawPtr(_, p) => self.fmt_place(*p, depth),
            mir::Rvalue::Aggregate(_, ops) => {
                let mut v = Vec::new();
                for op in ops {
                    let t = op.ty(&self.body.local_decls, self.tcx);
                    if mentions_fmt_args(self.tcx, t, 2) {
                        v.extend(self.fmt_sources(op, depth)?);
                    }
                }
                Some(v)
            }
            _ => None,
        }
    }

    /// The result of a call: an `rt::Argument` constructor; an `Arguments`
    /// constructor or a `core::ptr` method (pointer arithmetic) carries what its
    /// arguments carry; anything else is not known.
    fn fmt_call(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        depth: usize,
    ) -> Option<Vec<FmtSrc<'tcx>>> {
        let ft = func.ty(&self.body.local_decls, self.tcx);
        let ty::FnDef(d, _) = *ft.kind() else {
            return None;
        };
        let path = std_path(self.tcx, d);
        if path.starts_with("core::fmt::rt::Argument::") {
            return Some(vec![FmtSrc::Ctor(ft)]);
        }
        if path.starts_with("core::fmt::Arguments::") || path.starts_with("core::ptr::") {
            let mut v = Vec::new();
            for a in args {
                let t = a.node.ty(&self.body.local_decls, self.tcx);
                if mentions_fmt_args(self.tcx, t, 2) {
                    v.extend(self.fmt_sources(&a.node, depth)?);
                }
            }
            return Some(v);
        }
        None
    }

    /// Where a `&mut fmt::Formatter` operand comes from.
    fn formatter_src(&self, op: &Operand<'tcx>, depth: usize) -> Option<FmtrSrc<'b, 'tcx>> {
        let (Operand::Copy(p) | Operand::Move(p)) = op else {
            return None;
        };
        if !p.projection.is_empty() {
            return self.formatter_at(p.local, p.projection, depth);
        }
        self.formatter_local(p.local, depth)
    }

    /// A formatter read at a place with projections: a parameter's, or one at a path
    /// below a parameter ([`OriginCx::at`]).
    fn formatter_at(
        &self,
        l: mir::Local,
        proj: &[mir::PlaceElem<'tcx>],
        depth: usize,
    ) -> Option<FmtrSrc<'b, 'tcx>> {
        match self.at(l, proj, depth)? {
            Origin::Arg(l) => Some(FmtrSrc::Param(l)),
            Origin::ArgAt(l, p) => Some(FmtrSrc::At(l, p)),
            _ => None,
        }
    }

    fn formatter_local(&self, l: mir::Local, depth: usize) -> Option<FmtrSrc<'b, 'tcx>> {
        if depth > Self::MAX_DEPTH || self.unstable[l.as_usize()] {
            return None;
        }
        let writes = &self.writes[l.as_usize()];
        if self.is_arg(l) {
            return writes.is_empty().then_some(FmtrSrc::Param(l));
        }
        let [w] = writes.as_slice() else {
            return None;
        };
        match w {
            Def::Rv(mir::Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..))
                if p.projection.is_empty() =>
            {
                self.formatter_local(p.local, depth + 1)
            }
            Def::Rv(mir::Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..))
            | Def::Rv(mir::Rvalue::CopyForDeref(p)) => {
                self.formatter_at(p.local, p.projection, depth + 1)
            }
            // `&mut f` of a `Formatter` value, or `&mut *f` of a reference to one.
            Def::Rv(mir::Rvalue::Ref(_, _, p)) if p.projection.is_empty() => {
                self.formatter_value(p.local, depth + 1)
            }
            Def::Rv(mir::Rvalue::Ref(_, _, p))
                if p.projection.as_slice() == [mir::ProjectionElem::Deref] =>
            {
                self.formatter_local(p.local, depth + 1)
            }
            // `&mut *x` of a reference at a path: the same formatter as `x`.
            Def::Rv(mir::Rvalue::Ref(_, _, p))
                if p.projection.last() == Some(&mir::ProjectionElem::Deref) =>
            {
                let n = p.projection.len() - 1;
                self.formatter_at(p.local, &p.projection[..n], depth + 1)
            }
            _ => None,
        }
    }

    /// A local holding a `Formatter` value: `Formatter::new(out, ..)`, or the
    /// aggregate `Formatter { buf: out, .. }` it is inlined to. The value is passed
    /// on as `&mut Formatter`, so it is "unstable"; its `buf` is still `out`: the field
    /// is private to `core`, and `core` never assigns it (audited in the sources of
    /// rustc 1.99.1, which the std summaries' stamp pins: `buf` is set only where a
    /// `Formatter` is built).
    fn formatter_value(&self, l: mir::Local, depth: usize) -> Option<FmtrSrc<'b, 'tcx>> {
        if depth > Self::MAX_DEPTH || self.is_arg(l) {
            return None;
        }
        if let [Def::Rv(mir::Rvalue::Aggregate(kind, ops))] = self.writes[l.as_usize()].as_slice()
            && let mir::AggregateKind::Adt(did, variant, ..) = **kind
            && std_path(self.tcx, did) == "core::fmt::Formatter"
        {
            let fields = &self.tcx.adt_def(did).variant(variant).fields;
            let buf = fields
                .iter_enumerated()
                .find(|(_, f)| f.name.as_str() == "buf")
                .map(|(i, _)| i)?;
            return ops.get(buf).map(FmtrSrc::New);
        }
        let [Def::Call(func, args)] = self.writes[l.as_usize()].as_slice() else {
            return None;
        };
        let ty::FnDef(d, _) = *func.ty(&self.body.local_decls, self.tcx).kind() else {
            return None;
        };
        let tcx = self.tcx;
        let is_new = tcx.item_name(d).as_str() == "new"
            && tcx.impl_of_assoc(d).is_some_and(|i| {
                adt_is(
                    tcx,
                    tcx.type_of(i).instantiate_identity().skip_norm_wip(),
                    "core::fmt::Formatter",
                )
            });
        if is_pad_wrap(tcx, d) {
            return args.first().map(|a| FmtrSrc::Pad(&a.node));
        }
        if !is_new {
            return None;
        }
        args.first().map(|a| FmtrSrc::New(&a.node))
    }

    fn operand(&self, op: &Operand<'tcx>, depth: usize) -> Option<Origin<'tcx>> {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                self.local(p.local, depth)
            }
            Operand::Copy(p) | Operand::Move(p) => self.place(*p, depth),
            Operand::Constant(c) => Some(Origin::Const(c.const_)),
            _ => None,
        }
    }

    /// The value at a place with projections: the output of a formatter parameter
    /// ([`OriginCx::buf_of`]), a load below a reference constant (`(*_3)[_4]` with
    /// `_3 = const {TABLE: &[fn(u8) -> u8; 2]}`), a field of a local aggregate
    /// ([`OriginCx::field`]), or else a path below a parameter ([`OriginCx::at`]).
    fn place(&self, p: mir::Place<'tcx>, depth: usize) -> Option<Origin<'tcx>> {
        self.place_known(p, depth)
            .or_else(|| self.at(p.local, p.projection, depth))
    }

    /// The value at `l.proj` (fields and dereferences) on every read of that place
    /// (top plan T7a/b): below a parameter, [`Origin::ArgAt`] if
    /// [`OriginCx::stable_below`] holds; through a local assigned once from a copy,
    /// a reborrow (`&mut q` read through `*`), a struct, tuple or closure aggregate (a
    /// field: its operand), or a `core::fmt` builder constructor
    /// ([`builder_ctor_fields`]: the formatter it was given). A local that may change
    /// otherwise is followed only through [`AUDITED_FIELDS`].
    fn at(
        &self,
        l: mir::Local,
        proj: &[mir::PlaceElem<'tcx>],
        depth: usize,
    ) -> Option<Origin<'tcx>> {
        if depth > Self::MAX_DEPTH {
            return None;
        }
        if proj.is_empty() {
            return self.local(l, depth);
        }
        let tcx = self.tcx;
        let li = l.as_usize();
        if self.is_arg(l) {
            if self.unstable[li] || !self.writes[li].is_empty() {
                return None;
            }
            return self
                .stable_below(self.body.local_decls[l].ty, proj)
                .then(|| Origin::ArgAt(l, tcx.mk_place_elems(proj)));
        }
        let [w] = self.writes[li].as_slice() else {
            return None;
        };
        let ty = self.body.local_decls[l].ty;
        let concat = |q: &mir::Place<'tcx>, rest: &[mir::PlaceElem<'tcx>]| {
            let mut v: Vec<mir::PlaceElem<'tcx>> = q.projection.to_vec();
            v.extend_from_slice(rest);
            v
        };
        match w {
            Def::Rv(mir::Rvalue::Aggregate(kind, ops)) => {
                let mir::ProjectionElem::Field(f, _) = proj[0] else {
                    return None;
                };
                let is_struct = match **kind {
                    mir::AggregateKind::Tuple | mir::AggregateKind::Closure(..) => true,
                    mir::AggregateKind::Adt(d, _, _, _, None) => tcx.adt_def(d).is_struct(),
                    _ => false,
                };
                if !is_struct {
                    return None;
                }
                let env = TypingEnv::post_analysis(tcx, self.body.source.def_id());
                let stable = !self.unstable[li] && ty.is_freeze(tcx, env);
                if !stable && !audited_field(tcx, ty, f) {
                    return None;
                }
                match ops.get(f)? {
                    Operand::Copy(q) | Operand::Move(q) => {
                        self.at(q.local, &concat(q, &proj[1..]), depth + 1)
                    }
                    Operand::Constant(c) if proj.len() == 1 => Some(Origin::Const(c.const_)),
                    _ => None,
                }
            }
            Def::Rv(
                mir::Rvalue::Use(Operand::Copy(q) | Operand::Move(q), ..)
                | mir::Rvalue::CopyForDeref(q),
            ) if !self.unstable[li] => self.at(q.local, &concat(q, proj), depth + 1),
            // `l = &q` (or `&mut q`) read through `*l`: `q`.
            Def::Rv(mir::Rvalue::Ref(_, _, q))
                if !self.unstable[li] && proj[0] == mir::ProjectionElem::Deref =>
            {
                self.at(q.local, &concat(q, &proj[1..]), depth + 1)
            }
            Def::Call(func, args) => {
                let ty::FnDef(d, _) = *func.ty(&self.body.local_decls, tcx).kind() else {
                    return None;
                };
                // A builder method returning its receiver (`&mut Self`): the place
                // below the result is the place below the receiver.
                if returns_receiver(tcx, d) && proj[0] == mir::ProjectionElem::Deref {
                    return match &args.first()?.node {
                        Operand::Copy(q) | Operand::Move(q) => {
                            self.at(q.local, &concat(q, proj), depth + 1)
                        }
                        _ => None,
                    };
                }
                let names = builder_ctor_fields(tcx, d)?;
                // Follow the named (audited) fields of the builder value.
                let mut cur = ty;
                for (i, name) in names.iter().enumerate() {
                    let mir::ProjectionElem::Field(f, fty) = *proj.get(i)? else {
                        return None;
                    };
                    let ty::Adt(def, _) = cur.kind() else {
                        return None;
                    };
                    if def.non_enum_variant().fields.get(f)?.name.as_str() != *name
                        || !audited_field(tcx, cur, f)
                    {
                        return None;
                    }
                    cur = fty;
                }
                match &args.first()?.node {
                    Operand::Copy(q) | Operand::Move(q) => {
                        self.at(q.local, &concat(q, &proj[names.len()..]), depth + 1)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `true` if every read of the place `proj` below a parameter of type `ty` (never
    /// reassigned) yields its value on entry: each field is of the parameter's own
    /// value, or of memory behind a shared reference to a `Freeze` type, or in
    /// [`AUDITED_FIELDS`] (behind a `&mut`, or below a field that may change); a
    /// dereference is of a reference whose value is itself stable. Anything else
    /// (a dereference of a `Box` or raw pointer, an index, a downcast) is not.
    fn stable_below(&self, ty: Ty<'tcx>, proj: &[mir::PlaceElem<'tcx>]) -> bool {
        let tcx = self.tcx;
        let env = TypingEnv::post_analysis(tcx, self.body.source.def_id());
        let mut cur = ty;
        let mut mutable = false;
        for e in proj {
            match *e {
                mir::ProjectionElem::Deref => {
                    if mutable {
                        return false;
                    }
                    let ty::Ref(_, inner, m) = *cur.kind() else {
                        return false;
                    };
                    mutable = m.is_mut() || !inner.is_freeze(tcx, env);
                    cur = inner;
                }
                mir::ProjectionElem::Field(f, fty) => {
                    if mutable {
                        if !audited_field(tcx, cur, f) {
                            return false;
                        }
                        // A never-reassigned reference is a stable value; a struct
                        // field may still change in its other fields.
                        mutable = !fty.is_ref();
                    }
                    cur = fty;
                }
                _ => return false,
            }
        }
        !mutable
    }

    fn place_known(&self, p: mir::Place<'tcx>, depth: usize) -> Option<Origin<'tcx>> {
        if let Some(o) = self.buf_of(p, depth) {
            return Some(o);
        }
        match p.projection.first()? {
            mir::ProjectionElem::Deref => match self.local(p.local, depth)? {
                Origin::Arg(l) if p.projection.len() == 1 => Some(Origin::DerefArg(l)),
                Origin::Arg(l)
                    if p.projection.len() == 2
                        && matches!(p.projection[1], mir::ProjectionElem::Field(f, _) if f.as_usize() == 0)
                        && self.body.local_decls[p.local]
                            .ty
                            .builtin_deref(true)
                            .is_some_and(|t| t.is_box()) =>
                {
                    Some(Origin::BoxPtr(l))
                }
                Origin::Const(c) => {
                    let elems = self.const_elems(&p.projection[1..], depth);
                    Some(Origin::Load(c, self.tcx.mk_place_elems(&elems)))
                }
                // A load through a reference read from immutable data (`(*_13)[_2]`
                // with `_13 = copy (*_7)`, `_7 = const {S: &&[fn()]}`): the
                // dereference inside the data ([`Analysis::data_targets`] decides).
                Origin::Load(c, pre) if pre.len() + p.projection.len() <= 8 => {
                    let mut elems: Vec<mir::PlaceElem<'tcx>> = pre.to_vec();
                    elems.push(mir::ProjectionElem::Deref);
                    elems.extend(self.const_elems(&p.projection[1..], depth));
                    Some(Origin::Load(c, self.tcx.mk_place_elems(&elems)))
                }
                _ => None,
            },
            mir::ProjectionElem::Field(..) => self.field(p.local, p.projection, depth),
            mir::ProjectionElem::Index(i) if p.projection.len() == 1 => {
                self.elems(p.local, self.constant_index(*i, depth), depth)
            }
            mir::ProjectionElem::ConstantIndex {
                offset,
                from_end: false,
                ..
            } if p.projection.len() == 1 => self.elems(p.local, Some(*offset), depth),
            _ => None,
        }
    }

    /// `proj` with every index local holding one constant replaced by that
    /// constant index (that element only).
    fn const_elems(
        &self,
        proj: &[mir::PlaceElem<'tcx>],
        depth: usize,
    ) -> Vec<mir::PlaceElem<'tcx>> {
        proj.iter()
            .map(|e| match *e {
                mir::ProjectionElem::Index(i) => match self.constant_index(i, depth) {
                    Some(offset) => mir::ProjectionElem::ConstantIndex {
                        offset,
                        min_length: offset.saturating_add(1),
                        from_end: false,
                    },
                    None => *e,
                },
                e => e,
            })
            .collect()
    }

    /// An element of the local array `l` (top plan T1 residue): `l` is a local of
    /// the body (not a parameter) only ever assigned as a whole, each time by an
    /// array aggregate or a repeat, and never borrowed mutably or written in part
    /// ([`Unstable`]). [`Origin::Elems`]: every element of every assignment is a
    /// candidate, or the one at the constant index `idx`.
    fn elems(&self, l: mir::Local, idx: Option<u64>, depth: usize) -> Option<Origin<'tcx>> {
        let li = l.as_usize();
        if depth > Self::MAX_DEPTH || self.unstable[li] || self.is_arg(l) {
            return None;
        }
        let writes = &self.writes[li];
        let arrays = writes.iter().all(|w| match w {
            Def::Rv(mir::Rvalue::Repeat(..)) => true,
            Def::Rv(mir::Rvalue::Aggregate(k, _)) => matches!(**k, mir::AggregateKind::Array(_)),
            _ => false,
        });
        (!writes.is_empty() && arrays).then_some(Origin::Elems(l, idx))
    }

    /// The value of an index local assigned exactly once, from an integer constant,
    /// and never changed otherwise.
    fn constant_index(&self, l: mir::Local, depth: usize) -> Option<u64> {
        if depth > Self::MAX_DEPTH || self.unstable[l.as_usize()] || self.is_arg(l) {
            return None;
        }
        let [Def::Rv(mir::Rvalue::Use(Operand::Constant(c), ..))] =
            self.writes[l.as_usize()].as_slice()
        else {
            return None;
        };
        let env = TypingEnv::post_analysis(self.tcx, self.body.source.def_id());
        c.const_.try_eval_target_usize(self.tcx, env)
    }

    /// `l.f` (`proj` a chain of fields): `l` is a local of the body (not a
    /// parameter) that is only ever assigned as a whole, every time by a struct or
    /// tuple aggregate, and never borrowed mutably or written in part
    /// ([`Unstable`]); the origin of the field's operand in each aggregate, if they
    /// agree (top plan T1.3).
    fn field(
        &self,
        l: mir::Local,
        proj: &[mir::PlaceElem<'tcx>],
        depth: usize,
    ) -> Option<Origin<'tcx>> {
        if depth > Self::MAX_DEPTH || self.unstable[l.as_usize()] || self.is_arg(l) {
            return None;
        }
        // A shared borrow could change a value with interior mutability in place.
        let env = TypingEnv::post_analysis(self.tcx, self.body.source.def_id());
        if !self.body.local_decls[l].ty.is_freeze(self.tcx, env) {
            return None;
        }
        let (mir::ProjectionElem::Field(f, _), rest) = proj.split_first()? else {
            return None;
        };
        let mut found = None;
        for w in &self.writes[l.as_usize()] {
            let Def::Rv(mir::Rvalue::Aggregate(kind, ops)) = w else {
                return None;
            };
            let is_struct = match **kind {
                mir::AggregateKind::Tuple => true,
                mir::AggregateKind::Adt(d, _, _, _, None) => self.tcx.adt_def(d).is_struct(),
                _ => false,
            };
            if !is_struct {
                return None;
            }
            let op = ops.get(*f)?;
            let o = if rest.is_empty() {
                self.operand(op, depth + 1)?
            } else {
                match op {
                    Operand::Copy(q) | Operand::Move(q) if q.projection.is_empty() => {
                        self.field(q.local, rest, depth + 1)?
                    }
                    _ => return None,
                }
            };
            if found.is_some_and(|x| x != o) {
                return None;
            }
            found = Some(o);
        }
        found
    }

    fn local(&self, l: mir::Local, depth: usize) -> Option<Origin<'tcx>> {
        if depth > Self::MAX_DEPTH || self.unstable[l.as_usize()] {
            return None;
        }
        let writes = &self.writes[l.as_usize()];
        if (1..=self.body.arg_count).contains(&l.as_usize()) {
            return writes.is_empty().then_some(Origin::Arg(l));
        }
        let mut found = None;
        for w in writes {
            let o = match w {
                Def::Rv(rv) => self.rvalue(rv, depth + 1)?,
                Def::Call(func, args) => self.shared_deref(func, args, depth)?,
            };
            if found.is_some_and(|f| f != o) {
                return None;
            }
            found = Some(o);
        }
        found
    }

    /// `<Rc<T, A> as Deref>::deref(p)` or `Arc`'s, with `p` a parameter `&Rc<..>`
    /// never reassigned: [`Origin::BoxPtr`] of `p` (the pointee of the `Rc` behind the
    /// parameter; through a shared reference the `Rc` cannot be replaced, and the
    /// type of its pointee never changes).
    fn shared_deref(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        depth: usize,
    ) -> Option<Origin<'tcx>> {
        let tcx = self.tcx;
        let ty::FnDef(d, fargs) = *func.ty(&self.body.local_decls, tcx).kind() else {
            return None;
        };
        let deref = tcx.lang_items().deref_trait()?;
        if tcx.trait_of_assoc(d) != Some(deref) {
            return None;
        }
        shared_ptr_pointee(tcx, fargs.no_bound_vars()?.type_at(0))?;
        let [a] = args else {
            return None;
        };
        match self.operand(&a.node, depth + 1)? {
            Origin::Arg(l) => Some(Origin::BoxPtr(l)),
            _ => None,
        }
    }

    fn rvalue(&self, rv: &mir::Rvalue<'tcx>, depth: usize) -> Option<Origin<'tcx>> {
        use rustc_middle::ty::adjustment::PointerCoercion;
        let ty_of = |op: &Operand<'tcx>| op.ty(&self.body.local_decls, self.tcx);
        match rv {
            mir::Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
            | mir::Rvalue::CopyForDeref(p)
                if !p.projection.is_empty() =>
            {
                self.place(*p, depth)
            }
            mir::Rvalue::Use(op, ..) => self.operand(op, depth),
            mir::Rvalue::CopyForDeref(p) => self.local(p.local, depth),
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(
                    PointerCoercion::ReifyFnPointer(_) | PointerCoercion::ClosureFnPointer(_),
                    _,
                ),
                op,
                _,
            ) => {
                let t = ty_of(op);
                matches!(t.kind(), ty::FnDef(..) | ty::Closure(..)).then_some(Origin::Fn(t))
            }
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _),
                op,
                _,
            ) => {
                let from = ty_of(op);
                // `Rc<F>` / `Arc<F>` unsized to `Rc<dyn ..>`: the pointee `F`.
                let pointee = from
                    .builtin_deref(true)
                    .or_else(|| shared_ptr_pointee(self.tcx, from))?;
                if matches!(pointee.kind(), ty::Dynamic(..)) {
                    // An upcast keeps the concrete type of the original pointer.
                    self.operand(op, depth)
                } else {
                    Some(Origin::Pointee(pointee))
                }
            }
            // `&*p`: the same pointee (and metadata) as `p`.
            mir::Rvalue::Ref(_, _, p) | mir::Rvalue::RawPtr(_, p)
                if p.projection.as_slice() == [mir::ProjectionElem::Deref] =>
            {
                self.local(p.local, depth)
            }
            // `&*x` of a reference at a path: the same pointee as `x` (top plan T7a/b).
            mir::Rvalue::Ref(_, _, p) | mir::Rvalue::RawPtr(_, p)
                if p.projection.last() == Some(&mir::ProjectionElem::Deref) =>
            {
                let n = p.projection.len() - 1;
                self.at(p.local, &p.projection[..n], depth)
            }
            // `&l`: a shared borrow keeps `l` unchanged while it lives.
            mir::Rvalue::Ref(_, mir::BorrowKind::Shared, p) if p.projection.is_empty() => {
                Some(Origin::Ref(p.local))
            }
            // `&mut l` reading a function pointer: only a `call_mut` receiver keeps
            // `l` stable ([`OriginCx::new_fn_ptr`]), which `local` checks.
            mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, p)
                if self.fn_ptr && p.projection.is_empty() =>
            {
                Some(Origin::Ref(p.local))
            }
            // A `Box`'s pointer keeps its origin through the casts of its deref.
            mir::Rvalue::Cast(_, op, _) => match self.operand(op, depth)? {
                o @ Origin::BoxPtr(_) => Some(o),
                _ => None,
            },
            _ => None,
        }
    }
}

/// The operands an rvalue reads.
fn rvalue_operands<'b, 'tcx>(rv: &'b mir::Rvalue<'tcx>) -> Vec<&'b Operand<'tcx>> {
    match rv {
        mir::Rvalue::Use(op, ..)
        | mir::Rvalue::Repeat(op, _)
        | mir::Rvalue::Cast(_, op, _)
        | mir::Rvalue::UnaryOp(_, op)
        | mir::Rvalue::WrapUnsafeBinder(op, _) => vec![op],
        mir::Rvalue::BinaryOp(_, ops) => vec![&ops.0, &ops.1],
        mir::Rvalue::Aggregate(_, ops) => ops.iter().collect(),
        _ => Vec::new(),
    }
}

/// Maximum over entry-to-exit paths of the summed block costs (blocks of one
/// control-flow cycle are one unit; their costs are already widened).
fn longest_path(info: &BodyInfo, bcost: &[Cost]) -> Cost {
    let n = info.blocks.len();
    if n == 0 {
        return Cost::default();
    }
    let comps = tarjan(n, &info.succ);
    let mut comp_of = vec![0usize; n];
    for (c, members) in comps.iter().enumerate() {
        for &b in members {
            comp_of[b] = c;
        }
    }
    let mut best: Vec<Cost> = vec![Cost::default(); comps.len()];
    for (c, members) in comps.iter().enumerate() {
        let mut own = Cost::default();
        let mut tail = Cost::default();
        for &b in members {
            own = own.add(&bcost[b]);
            for &t in &info.succ[b] {
                let tc = comp_of[t];
                if tc != c {
                    tail = tail.max(&best[tc]);
                }
            }
        }
        best[c] = own.add(&tail);
    }
    best[comp_of[0]].clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bound_arithmetic() {
        assert_eq!(B::Fin(2).add(B::Fin(3)), B::Fin(5));
        assert_eq!(B::Fin(2).add(B::Inf), B::Inf);
        assert_eq!(B::Fin(0).mul(B::Inf), B::Fin(0));
        assert_eq!(B::Inf.mul(B::Fin(0)), B::Fin(0));
        assert_eq!(B::Fin(2).mul(B::Inf), B::Inf);
        assert_eq!(B::Fin(0).widen(), B::Fin(0));
        assert_eq!(B::Fin(1).widen(), B::Inf);
        assert!(B::Inf.exceeds(u64::MAX));
        assert!(!B::Fin(1).exceeds(1));
    }

    #[test]
    fn terms_are_instantiated_by_declared_bounds() {
        let c = Cost::one()
            .add(&Cost::term("g").looped(true))
            .add(&Cost::term("drop(F)"))
            .add(&Cost::term("h"));
        assert_eq!(c.display(), "1 + alloc(drop(F)) + ∞·alloc(g) + alloc(h)");
        let types = vec![("g".to_string(), "F".to_string())];
        let zero = c.instantiate(&[("g".to_string(), 0)], &types);
        assert_eq!(zero.c, B::Fin(1));
        assert_eq!(zero.display(), "1 + alloc(h)");
        let one = c.instantiate(&[("g".to_string(), 1), ("h".to_string(), 2)], &types);
        assert_eq!(one.c, B::Inf);
        assert!(one.terms.is_empty());
    }

    #[test]
    fn path_maximum_not_sum() {
        // bb0 -> bb1 | bb2 -> bb3; one allocation on each branch.
        let info = BodyInfo {
            blocks: vec![Vec::new(), Vec::new(), Vec::new(), Vec::new()],
            succ: vec![vec![1, 2], vec![3], vec![3], Vec::new()],
            reachable: vec![true; 4],
            in_loop: vec![false; 4],
        };
        let costs = vec![Cost::default(), Cost::one(), Cost::one(), Cost::one()];
        assert_eq!(longest_path(&info, &costs).c, B::Fin(2));
    }

    #[test]
    fn contract_events_follow_the_mark() {
        let kinds = |m: &str| -> Vec<String> {
            let mark = marks::parse_mark(m).expect("mark");
            contract_events("T::m", &mark)
                .iter()
                .map(|e| match e {
                    Ev::Alloc(_) => "alloc".to_string(),
                    Ev::Free(_) => "free".to_string(),
                    Ev::Panic(_) => "panic".to_string(),
                    Ev::Unknown(_) => "top".to_string(),
                    Ev::Bound(k, _) => format!("bound {k}"),
                    Ev::Recurse(_) => "recurse".to_string(),
                    Ev::VerusPre(_) => "verus".to_string(),
                })
                .collect()
        };
        assert_eq!(kinds(r#"kind = "fip""#), vec!["panic"]);
        assert_eq!(
            kinds(r#"kind = "fip", n = 2, strict = true, panic_macros = false"#),
            vec!["bound 2"]
        );
        assert_eq!(kinds(r#"kind = "fip", strict = true"#), vec!["panic"]);
        assert_eq!(
            kinds(r#"kind = "fbip", strict = true, panic_macros = false"#),
            vec!["free", "recurse"]
        );
    }

    #[test]
    fn tarjan_orders_components_callees_first() {
        // 0 -> 1 -> 2 -> 1, 0 -> 3
        let comps = tarjan(4, &[vec![1, 3], vec![2], vec![1], Vec::new()]);
        let pos = |n: usize| comps.iter().position(|c| c.contains(&n)).unwrap();
        assert!(pos(1) < pos(0) && pos(3) < pos(0));
        assert_eq!(comps[pos(1)], vec![1, 2]);
    }
}
