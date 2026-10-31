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
//! **Events.** Allocation and deallocation entry points, `Drop` terminators on types
//! with drop glue (possible frees), `Assert` terminators and panic entry points
//! (panic paths), and everything that cannot be resolved or has no usable MIR
//! (`⊤`, with the reason). Tables: `fip_lint_rules::mir`.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use fip_lint_rules::mir as rules;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_middle::mir::{self, AssertKind, Body, Operand, TerminatorKind};
use rustc_middle::ty::print::{with_no_trimmed_paths, with_no_visible_paths};
use rustc_middle::ty::{
    self, EarlyBinder, GenericArgs, GenericArgsRef, Instance, InstanceKind, ShimKind, Ty, TyCtxt,
    TypeFoldable, TypeVisitableExt, TypingEnv,
};
use rustc_span::{DUMMY_SP, Span};

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
}

#[derive(Clone, Debug)]
enum Item {
    Call(usize),
    Term(String),
    Ev(Ev),
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
    label: String,
    kind: NodeKind,
}

/// Crates whose MIR may be used: the local crate, `core`/`alloc`/`std`, and crates
/// whose root declares `fip::export`.
pub struct Crates {
    exported: HashMap<CrateNum, bool>,
    /// Crates that declare `fip::export` but contain a function with a body in source
    /// and no MIR in their metadata: built without `-Zalways-encode-mir`, i.e. not by
    /// the driver. Value: the first such function found.
    unencoded: HashMap<CrateNum, String>,
}

impl Crates {
    pub fn new(tcx: TyCtxt<'_>) -> Crates {
        let mut exported = HashMap::new();
        for &cnum in tcx.crates(()) {
            exported.insert(cnum, declares_export(tcx, cnum.as_def_id()));
        }
        exported.insert(LOCAL_CRATE, true);
        let mut unencoded = HashMap::new();
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
                if def_id.krate != cnum || !has_source_body(tcx, def_id) {
                    continue;
                }
                if !tcx.is_mir_available(def_id) {
                    unencoded.insert(cnum, tcx.def_path_str(def_id));
                    break;
                }
            }
        }
        Crates {
            exported,
            unencoded,
        }
    }
    fn exported(&self, c: CrateNum) -> bool {
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

fn is_std_crate(name: &str) -> bool {
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
    index: HashMap<Instance<'tcx>, usize>,
    queue: Vec<usize>,
    param_names: HashMap<u32, String>,
    param_types: Vec<(String, String)>,
}

/// Result for one root.
pub struct RootResult {
    pub summary: Summary,
    pub label: String,
    /// Value parameter name → its generic type parameter (`g` → `F` for `g: F`).
    pub param_types: Vec<(String, String)>,
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
    pub fn run(tcx: TyCtxt<'tcx>, crates: &'a Crates, root: DefId) -> RootResult {
        let env = TypingEnv::post_analysis(tcx, root);
        let mut a = Analysis {
            tcx,
            env,
            crates,
            nodes: Vec::new(),
            index: HashMap::new(),
            queue: Vec::new(),
            param_names: HashMap::new(),
            param_types: Vec::new(),
        };
        a.collect_param_names(root);
        let args = tcx.erase_and_anonymize_regions(GenericArgs::identity_for_item(tcx, root));
        let inst = Instance::new_raw(root, args);
        let r = a.node_for(inst);
        while let Some(i) = a.queue.pop() {
            a.classify(i);
        }
        if std::env::var_os("FIP_PRELINT_DUMP").is_some() {
            a.dump();
        }
        let sums = a.evaluate();
        RootResult {
            summary: sums[r].clone(),
            label: a.nodes[r].label.clone(),
            param_types: a.param_types.clone(),
        }
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
                with_no_visible_paths!(with_no_trimmed_paths!(format!("drop glue of `{ty}`")))
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
        if let Some(&i) = self.index.get(&inst) {
            return i;
        }
        let i = self.nodes.len();
        let label = self.label(inst);
        self.nodes.push(Node {
            inst,
            label,
            kind: NodeKind::Pending,
        });
        self.index.insert(inst, i);
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
        let tcx = self.tcx;
        let kind = match inst.def {
            InstanceKind::Item(def_id) => self.classify_item(inst, def_id),
            InstanceKind::Intrinsic(def_id) => self.classify_intrinsic(inst, def_id),
            InstanceKind::LlvmIntrinsic(def_id) => NodeKind::Leaf(vec![Ev::Unknown(format!(
                "LLVM intrinsic `{}`",
                def_path(tcx, def_id)
            ))]),
            InstanceKind::Virtual(def_id, _) => NodeKind::Leaf(vec![Ev::Unknown(format!(
                "dynamic call to `{}` (trait object)",
                def_path_args(tcx, def_id, inst.args)
            ))]),
            InstanceKind::Shim(ShimKind::DropGlue(_, None)) => NodeKind::Leaf(Vec::new()),
            InstanceKind::Shim(ShimKind::DropGlue(_, Some(ty))) if ty.has_param() => {
                NodeKind::Leaf(vec![Ev::Unknown(format!(
                    "drop glue of generic `{ty}` (called directly)"
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
            InstanceKind::Shim(_) => {
                let body = tcx.instance_mir(inst.def);
                NodeKind::Body(self.scan_body(inst, body))
            }
        };
        self.nodes[i].kind = kind;
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

    fn classify_item(&mut self, inst: Instance<'tcx>, def_id: DefId) -> NodeKind {
        let tcx = self.tcx;
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
        let n = body.basic_blocks.len();
        let mut blocks: Vec<Vec<Site>> = (0..n).map(|_| Vec::new()).collect();
        let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            let b = bb.as_usize();
            let term = data.terminator();
            succ[b] = term
                .successors()
                .filter(|s| !body.basic_blocks[*s].is_cleanup)
                .map(|s| s.as_usize())
                .collect();
            let span = term.source_info.span;
            match &term.kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                    let item = self.call_item(inst, body, func);
                    blocks[b].push(Site { item, span });
                }
                TerminatorKind::Drop { place, .. } => {
                    let ty = place.ty(&body.local_decls, tcx).ty;
                    match self.subst(inst, ty) {
                        Some(ty) if ty.needs_drop(tcx, self.env) => {
                            // Dropping a value whose type mentions a generic
                            // parameter frees only for some instantiations: a term,
                            // like a call (`drop(T)`, `drop(Option<T>)`).
                            if ty.has_param() {
                                let name = match ty.kind() {
                                    ty::Param(p) => format!("drop({})", p.name),
                                    _ => format!("drop({ty})"),
                                };
                                blocks[b].push(Site {
                                    item: Item::Term(name),
                                    span,
                                });
                                continue;
                            }
                            blocks[b].push(Site {
                                item: Item::Ev(Ev::Free(format!("drop of `{ty}`"))),
                                span,
                            });
                            let glue = Instance::resolve_drop_glue(tcx, ty);
                            blocks[b].push(Site {
                                item: Item::Call(self.node_for(glue)),
                                span,
                            });
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
                        .is_some_and(|v| (v != 0) == *expected);
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

    fn call_item(
        &mut self,
        inst: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        func: &Operand<'tcx>,
    ) -> Item {
        let fty = func.ty(&body.local_decls, self.tcx);
        let Some(fty) = self.subst(inst, fty) else {
            return Item::Ev(Ev::Unknown(format!(
                "callee of type `{fty}` (not normalizable)"
            )));
        };
        match *fty.kind() {
            ty::FnDef(def_id, args) => match args.no_bound_vars() {
                Some(args) => self.resolve(def_id, args),
                None => Item::Ev(Ev::Unknown(format!("callee `{fty}` with bound variables"))),
            },
            ty::FnPtr(..) => Item::Ev(Ev::Unknown(format!(
                "call through a function pointer `{fty}`"
            ))),
            _ => Item::Ev(Ev::Unknown(format!("call of `{fty}`"))),
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

    fn unresolved(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>) -> Item {
        let tcx = self.tcx;
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
                            s.alloc_w.push(w(what));
                        }
                        Ev::Free(what) => s.free.push(w(what)),
                        Ev::Panic(what) => s.panics.push(w(what)),
                        Ev::Unknown(what) => s.unknown.push(w(what)),
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
                            Item::Ev(Ev::Alloc(what)) => {
                                bcost[b] = bcost[b].add(&Cost::one().looped(in_loop));
                                push_w(&mut s.alloc_w, local(what), MAX_WITNESSES, key_site);
                            }
                            Item::Ev(Ev::Free(what)) => {
                                push_w(&mut s.free, local(what), MAX_WITNESSES, key_site);
                            }
                            Item::Ev(Ev::Panic(what)) => {
                                push_w(&mut s.panics, local(what), MAX_WITNESSES, key_site);
                            }
                            Item::Ev(Ev::Unknown(what)) => {
                                push_w(&mut s.unknown, local(what), MAX_UNKNOWN, key_what);
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
                            }
                        }
                    }
                    eprintln!("  [{i}] {} : body {}", node.label, items.join(", "));
                }
            }
        }
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
    fn tarjan_orders_components_callees_first() {
        // 0 -> 1 -> 2 -> 1, 0 -> 3
        let comps = tarjan(4, &[vec![1, 3], vec![2], vec![1], Vec::new()]);
        let pos = |n: usize| comps.iter().position(|c| c.contains(&n)).unwrap();
        assert!(pos(1) < pos(0) && pos(3) < pos(0));
        assert_eq!(comps[pos(1)], vec![1, 2]);
    }
}
