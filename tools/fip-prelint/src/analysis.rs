// SPDX-License-Identifier: Apache-2.0
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
//! or one unsized concrete type, on every path ([`origin_of`]). A parameter declared
//! `param(g = K)` of function-pointer or `&dyn Fn*`/`&dyn FipFn` type counts `K` and
//! what the function's mark allows; its call sites must pass a function known there
//! that meets them. A dynamic call of a trait method whose declaration carries a
//! `fip::mark` costs that contract ([`Crates::contract_of`]); every implementation
//! is checked against it in its own crate (`crate::report`). Anything else is `⊤`.

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
}

#[derive(Clone, Debug)]
enum Item {
    Call(usize),
    Term(String),
    Ev(Ev),
    /// Several events of one call: a call through a parameter declared
    /// `param(g = K)`, which may do what the function's own mark allows.
    Evs(Vec<Ev>),
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
/// parameter, `xs.len()` the length of a slice parameter.
pub fn requires_facts(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    cs: &[fip_lint_rules::requires::Conjunct],
) -> Result<Vec<Fact>, String> {
    use fip_lint_rules::requires::{Rel, Side, Term};
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return Err("`fip::requires` applies to functions".to_string());
    }
    let idents = tcx.fn_arg_idents(def_id);
    let inputs = tcx.fn_sig(def_id).skip_binder().skip_binder().inputs();
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

/// Crates whose MIR may be used: the local crate, `core`/`alloc`/`std`, and crates
/// whose root declares `fip::export`.
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

impl Crates {
    pub fn new(tcx: TyCtxt<'_>) -> Crates {
        let mut exported = HashMap::new();
        for &cnum in tcx.crates(()) {
            exported.insert(cnum, declares_export(tcx, cnum.as_def_id()));
        }
        exported.insert(LOCAL_CRATE, true);
        let mut unencoded = HashMap::new();
        let mut marks = HashMap::new();
        let mut sources = HashMap::new();
        let mut requires = HashMap::new();
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
            && let Some((a, f)) = rules::foreign_alloc_symbol(tcx.item_name(def_id).as_str())
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
    /// The mark of `def_id` if it declares `param(..)`.
    fn param_mark(&self, def_id: DefId) -> Option<&Mark> {
        self.marks.get(&def_id).filter(|m| !m.params.is_empty())
    }
    /// The contract of a trait method: the `fip::mark` on its declaration (local
    /// crate or an exported crate). A dynamic call of the method costs the contract;
    /// every implementation is checked against it. A contract with `param(..)` is
    /// rejected where it is declared and not used.
    pub fn contract_of(&self, tcx: TyCtxt<'_>, def_id: DefId) -> Option<&Mark> {
        tcx.trait_of_assoc(def_id)?;
        self.marks.get(&def_id).filter(|m| m.params.is_empty())
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

pub(crate) fn is_std_crate(name: &str) -> bool {
    matches!(name, "core" | "alloc" | "std")
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
    index: HashMap<(Instance<'tcx>, Vec<Fact>), usize>,
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
}

/// A call site passing, for a parameter declared `param(g = K)`, an argument whose
/// bound per call is `⊤` or, with no terms left, above `K`.
pub struct ArgViolation {
    /// The function or closure containing the call.
    pub caller: String,
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
}

impl ArgViolation {
    /// Identifies the same violation found from several roots or bodies.
    pub fn key(&self) -> String {
        format!(
            "{:?}|{}|{}|{}",
            self.span, self.callee, self.param, self.arg
        )
    }
}

fn def_path(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    with_no_visible_paths!(with_no_trimmed_paths!(tcx.def_path_str(def_id)))
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
            vsums: crate::value::Summaries::new(crates),
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
        a.run_root(root, inst, mark)
    }

    /// The default body of the trait method `method` as `impl_def` uses it (the impl
    /// does not override it), analysed as a root in the impl's typing environment;
    /// `None` if it does not resolve to that body.
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
        Some(a.run_root(method, inst, mark))
    }

    fn run_root(self, root: DefId, inst: Instance<'tcx>, mark: &Mark) -> RootResult {
        let crates = self.crates;
        let mut a = self;
        a.owner_params = mark.params.clone();
        // A root is analysed under its own precondition (checked at its callers).
        let ctx = crates
            .requires_of(root)
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
    /// entry points are explored, not the body's other callees. Used for every local
    /// body that is not a root, so that callers which are not roots are checked.
    pub fn arguments_in(tcx: TyCtxt<'tcx>, crates: &'a Crates, owner: DefId) -> Vec<ArgViolation> {
        let mut a = Analysis::new(tcx, crates, owner);
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
            }
        }
        if a.arg_sites.is_empty() {
            return Vec::new();
        }
        while let Some(i) = a.queue.pop() {
            a.classify(i);
        }
        let sums = a.evaluate();
        a.dump_args(&sums);
        a.arg_violations(&sums)
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
        let key = (inst, ctx);
        if let Some(&i) = self.index.get(&key) {
            return i;
        }
        let i = self.nodes.len();
        let label = self.label(inst);
        let parent = (i > 0).then_some(self.current);
        self.nodes.push(Node {
            inst,
            ctx: key.1.clone(),
            depth,
            parent,
            label,
            kind: NodeKind::Pending,
        });
        self.index.insert(key, i);
        self.queue.push(i);
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
                    Some(m) => NodeKind::Leaf(contract_events(&def_path(tcx, def_id), m)),
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
        if rules::is_realloc_entry(&path) {
            return NodeKind::Leaf(vec![
                Ev::Alloc(format!("reallocation `{path}`")),
                Ev::Free(format!("reallocation `{path}`")),
            ]);
        }
        if rules::is_alloc_entry(&path) {
            return NodeKind::Leaf(vec![Ev::Alloc(format!("allocation `{path}`"))]);
        }
        if rules::is_dealloc_entry(&path) {
            return NodeKind::Leaf(vec![Ev::Free(format!("deallocation `{path}`"))]);
        }
        if rules::is_panic_entry(&path) {
            return NodeKind::Leaf(vec![Ev::Panic(format!("`{path}`"))]);
        }
        if rules::is_ub_check(&path) {
            return NodeKind::Leaf(Vec::new());
        }
        if matches!(tcx.def_kind(def_id), DefKind::Ctor(..)) {
            return NodeKind::Leaf(Vec::new());
        }
        if tcx.is_foreign_item(def_id) {
            let name = tcx.item_name(def_id);
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
            return NodeKind::Leaf(vec![Ev::Unknown(format!("foreign function `{path}`"))]);
        }
        let crate_name = tcx.crate_name(def_id.krate);
        let crate_name = crate_name.as_str();
        let std_like = is_std_crate(crate_name);
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
                "no MIR: not generic and not #[inline]"
            } else {
                "no MIR although the crate declares `fip::export`: it was built without `-Zalways-encode-mir`"
            };
            return NodeKind::Leaf(vec![Ev::Unknown(format!("`{path}` ({why})"))]);
        }
        let body = tcx.instance_mir(inst.def);
        NodeKind::Body(self.scan_body(inst, body))
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
                    if let Item::Call(j) = item {
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
                    blocks[b].push(Site { item, span });
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
                        blocks[b].push(Site {
                            item: Item::Ev(Ev::Panic(describe_assert(msg))),
                            span,
                        });
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
                        Item::Call(self.node_in(callee, ctx, depth + 1))
                    }
                    Ok(Some(callee)) if matches!(callee.def, InstanceKind::Virtual(..)) => {
                        match args.first() {
                            Some(recv) => self
                                .devirtualize(inst, body, callee, &recv.node)
                                .unwrap_or_else(|| Item::Call(self.node_for(callee))),
                            None => Item::Call(self.node_for(callee)),
                        }
                    }
                    _ => self.resolve(def_id, fargs),
                },
                None => Item::Ev(Ev::Unknown(format!("callee `{fty}` with bound variables"))),
            },
            ty::FnPtr(..) => self.pointer_target(inst, body, func).unwrap_or_else(|| {
                Item::Ev(Ev::Unknown(format!(
                    "call through a function pointer `{fty}`"
                )))
            }),
            _ => Item::Ev(Ev::Unknown(format!("call of `{fty}`"))),
        }
    }

    /// The function a function pointer `op` in `inst`'s body calls: the function item
    /// or closure it is reified from on every path, or the declared bound of a
    /// parameter `param(g = K)`. `None`: not known here (`⊤`).
    fn pointer_target(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<Item> {
        match origin_of(self.tcx, body, op)? {
            Origin::Fn(t) => self.function_item(inst, t),
            Origin::Arg(l) => self.declared_param_call(inst, body, l),
            Origin::Pointee(_) => None,
        }
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

    /// A dynamic call (`callee` is `Virtual`) whose receiver `recv` is, on every path
    /// in `inst`'s body, a pointer unsized from one concrete type: the method of that
    /// type. A receiver that is a parameter declared `param(g = K)` of a callable
    /// trait object (`&dyn Fn*`, `&dyn FipFn`): the declared bound.
    fn devirtualize(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        callee: Instance<'tcx>,
        recv: &Operand<'tcx>,
    ) -> Option<Item> {
        let tcx = self.tcx;
        let InstanceKind::Virtual(def_id, _) = callee.def else {
            return None;
        };
        match origin_of(tcx, body, recv)? {
            Origin::Pointee(t) => {
                let t = self.subst(inst, t)?;
                if !t.is_sized(tcx, self.env) {
                    return None;
                }
                let args = tcx
                    .mk_args_from_iter(std::iter::once(t.into()).chain(callee.args.iter().skip(1)));
                match Instance::try_resolve(tcx, self.env, def_id, args) {
                    Ok(Some(c)) if !matches!(c.def, InstanceKind::Virtual(..)) => {
                        Some(Item::Call(self.node_for(c)))
                    }
                    _ => None,
                }
            }
            Origin::Arg(l) => {
                let trait_id = tcx.trait_of_assoc(def_id)?;
                if !self.is_callable_trait(trait_id) {
                    return None;
                }
                self.declared_param_call(inst, body, l)
            }
            Origin::Fn(_) => None,
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
        let mark = self.crates.param_mark(d)?;
        Some(Item::Evs(param_events(&g, k, mark)))
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
        let mark = self.crates.param_mark(d)?;
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
    /// of the graph.
    fn note_arg_site(
        &mut self,
        caller: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        span: Span,
        callee: Instance<'tcx>,
        call_args: &[Spanned<Operand<'tcx>>],
    ) {
        let InstanceKind::Item(def_id) = callee.def else {
            return;
        };
        let crates = self.crates;
        let Some(mark) = crates.param_mark(def_id) else {
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
            let indirect = indirect.then(|| mark.clone());
            self.arg_sites.push(ArgSite {
                caller: caller_label.clone(),
                span,
                local: caller.def_id().is_local(),
                callee: callee_label.clone(),
                param: g.clone(),
                declared: *declared,
                arg,
                items,
                indirect,
            });
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
    ) -> Option<(String, Vec<(String, Item)>, bool)> {
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
                    Ok(margs) => (
                        def_path_args(tcx, m.def_id, margs),
                        self.resolve(m.def_id, margs),
                    ),
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

    /// The principal trait of `t = &dyn Tr` or `&mut dyn Tr` if `Tr` is callable
    /// (`Fn*`, `FipFn`).
    fn callable_dyn(&self, t: Ty<'tcx>) -> Option<ty::Binder<'tcx, ty::ExistentialTraitRef<'tcx>>> {
        let ty::Ref(_, inner, _) = *t.kind() else {
            return None;
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
        match origin_of(tcx, body, op) {
            Some(Origin::Fn(t)) if input.is_fn_ptr() => {
                let label = self.subst(caller, t).map_or_else(|| shown(t), shown);
                match self.function_item(caller, t) {
                    Some(item) => (label.clone(), vec![(label, item)]),
                    None => (label, unknown(not_known)),
                }
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
                                .param_mark(d)
                                .map(|m| param_events(&h, k, m))
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
                                "the function passed for `{g}` is the parameter `{name}` of the caller, which declares no `param({name} = ..)`"
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
                }
            }
            s.alloc = cost.clone();
            let bound = cost.instantiate(&self.owner_params, &self.param_types);
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
            if violated {
                out.push(ArgViolation {
                    caller: site.caller.clone(),
                    span: site.span,
                    local: site.local,
                    callee: site.callee.clone(),
                    param: site.param.clone(),
                    declared: site.declared,
                    arg: site.arg.clone(),
                    bound,
                    summary: s,
                    forbidden,
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
                    .filter_map(|s| match s.item {
                        Item::Call(j) => Some(j),
                        _ => None,
                    })
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
                for s in sites {
                    let Item::Call(j) = s.item else { continue };
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
                    }
                }
            }
            NodeKind::Body(info) => {
                let n = info.blocks.len();
                let mut bcost = vec![Cost::default(); n];
                for b in 0..n {
                    if !info.reachable[b] {
                        continue;
                    }
                    let in_loop = info.in_loop[b];
                    for site in &info.blocks[b] {
                        let local = |what: &String| Witness {
                            steps: Vec::new(),
                            what: what.clone(),
                            span: site.span,
                            in_loop,
                        };
                        match &site.item {
                            Item::Call(j) => {
                                if skip.is_some_and(|k| k.contains(j)) {
                                    continue;
                                }
                                let Some(cs) = sums[*j].as_ref() else {
                                    continue;
                                };
                                let step = Step {
                                    label: self.nodes[*j].label.clone(),
                                    span: site.span,
                                    in_loop,
                                };
                                bcost[b] = bcost[b].add(&cs.alloc.looped(in_loop));
                                s.merge_events(cs, std::slice::from_ref(&step));
                            }
                            Item::Term(k) => {
                                bcost[b] = bcost[b].add(&Cost::term(k).looped(in_loop));
                                s.terms_w
                                    .entry(k.clone())
                                    .or_insert_with(|| local(&format!("call of `{k}`")));
                            }
                            Item::Ev(ev) => {
                                bcost[b] =
                                    bcost[b].add(&local_event(&mut s, ev, local).looped(in_loop));
                            }
                            Item::Evs(evs) => {
                                for ev in evs {
                                    bcost[b] = bcost[b]
                                        .add(&local_event(&mut s, ev, local).looped(in_loop));
                                }
                            }
                        }
                    }
                }
                s.alloc = longest_path(info, &bcost);
            }
        }
        s
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

/// Adds one event found in a body (witness `w`) to `s`; returns its allocation cost.
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
    let n = if m.kind == marks::Kind::Fip { m.n } else { 0 };
    declared_events(
        &format!("dynamic call of `{path}`"),
        &format!("its contract `{}`", m.tag()),
        m,
        n,
    )
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
            && matches!(m, MutatingUseContext::Store | MutatingUseContext::Drop);
        if !through_deref && !whole {
            self.0[place.local.as_usize()] = true;
        }
    }
}

/// A must-analysis over one body: the origin of `op` if every assignment that can
/// produce its value (through copies, moves and reborrows `&*p`) is the same
/// reification of one function or closure, the same unsizing of one concrete type,
/// or the unchanged parameter. Anything else (two origins, a value loaded from
/// memory, a call result, a local changed in place) is `None`.
fn origin_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    op: &Operand<'tcx>,
) -> Option<Origin<'tcx>> {
    use mir::visit::Visitor;
    let n = body.local_decls.len();
    let mut unstable = Unstable(vec![false; n]);
    unstable.visit_body(body);
    let mut writes: Vec<Vec<&mir::Rvalue<'tcx>>> = vec![Vec::new(); n];
    for data in body.basic_blocks.iter() {
        for st in &data.statements {
            if let mir::StatementKind::Assign(assign) = &st.kind
                && assign.0.projection.is_empty()
            {
                writes[assign.0.local.as_usize()].push(&assign.1);
            }
        }
    }
    let cx = OriginCx {
        tcx,
        body,
        unstable: unstable.0,
        writes,
    };
    cx.operand(op, 0)
}

struct OriginCx<'b, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'b Body<'tcx>,
    unstable: Vec<bool>,
    writes: Vec<Vec<&'b mir::Rvalue<'tcx>>>,
}

impl<'tcx> OriginCx<'_, 'tcx> {
    const MAX_DEPTH: usize = 32;

    fn operand(&self, op: &Operand<'tcx>, depth: usize) -> Option<Origin<'tcx>> {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                self.local(p.local, depth)
            }
            _ => None,
        }
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
        for rv in writes {
            let o = self.rvalue(rv, depth + 1)?;
            if found.is_some_and(|f| f != o) {
                return None;
            }
            found = Some(o);
        }
        found
    }

    fn rvalue(&self, rv: &mir::Rvalue<'tcx>, depth: usize) -> Option<Origin<'tcx>> {
        use rustc_middle::ty::adjustment::PointerCoercion;
        let ty_of = |op: &Operand<'tcx>| op.ty(&self.body.local_decls, self.tcx);
        match rv {
            mir::Rvalue::Use(op, ..) => self.operand(op, depth),
            mir::Rvalue::CopyForDeref(p) if p.projection.is_empty() => self.local(p.local, depth),
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
                let pointee = ty_of(op).builtin_deref(true)?;
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
