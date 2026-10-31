// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Interprocedural allocation bounds for `#[fip]`, `#[fip(N)]` and `#[fbip]`.
//!
//! `#[fip]` sees allocation sites only in its own body. [`fip_violations`] computes,
//! for every function of the scanned crates, an upper bound on the heap allocations
//! one call performs, counting everything it calls, and checks every marked function
//! against its attribute:
//!
//! | attribute | requires |
//! |---|---|
//! | `#[fip]` | bound 0, no recursion (see [`crate::callgraph`]) |
//! | `#[fip(N)]` | bound ≤ `N`, no recursion |
//! | `#[fbip]` | bound 0 (recursion allowed) |
//!
//! ## Lattice and summaries
//!
//! A bound is one of `0, 1, …, ∞, ⊤` ([`Bound`]); `⊤` means *unknown* and absorbs
//! every sum. A summary is `c + Σ kᵢ·alloc(gᵢ)`: a constant plus symbolic terms for
//! the function's callable parameters `gᵢ` (closures, `fn` pointers, `Fn*`/`FipFn`
//! values). Per function, `alloc(f) = Σ` over its body of
//!
//! - allocation sites (the `fip-lint-rules` tables: `Box::new`, `vec!`, `.clone()`, …):
//!   1 each;
//! - calls to functions of the scanned sources: the callee's summary, its parameter
//!   terms instantiated with the arguments (a closure literal's or `fip_fn!`'s body
//!   summary, a named function's summary, the caller's own parameter as a term,
//!   anything else `⊤`);
//! - method calls: the maximum over every scanned method of that name taking
//!   `self`; with none, 0 for `ALLOC_FREE_METHODS`, else `⊤`; `<T>::m(..)` likewise;
//!   a `for` loop over anything but a range literal calls `.into_iter()` and, in the
//!   loop, `.next()` this way;
//! - calls of closures bound to a local: the closure body's summary;
//! - `core`/`std` functions of the audited `CORE_TABLE` and explicit drops: 0;
//!   capitalised names that are not defined functions (tuple structs, enum
//!   variants): 0; any other external path, a name that matches scanned functions
//!   only by name, a call through an expression or a non-closure local, `?`, or a
//!   macro not defined in the scanned sources (except the compile-time and panic
//!   macros of `fip-lint-rules`): `⊤`, never 0;
//!
//! and everything inside a loop body or a `while` condition is multiplied by `∞`
//! (`∞·0 = 0`). Summaries are computed per strongly connected component in reverse
//! topological order; recursive components iterate to a fixpoint, widening a growing
//! bound to `∞`.
//!
//! A root whose bound still has parameter terms is reported as conditional ("fip
//! relative to its parameters", with the symbolic summary), never as a pass;
//! `param(g = K)` in its `#[fip(..)]` attribute instantiates `g` with `K` for the
//! verdict, and every call site of such a function is checked to pass an argument
//! whose bound is at most `K`.
//!
//! **A check, not a proof.** Implicit calls (drop glue, operators, `Deref`, `Index`
//! on user types), panic paths, functions and macros outside the scanned sources and
//! anything only types could tell apart are not seen; method calls and `T::f()` with
//! one local candidate are resolved by name, so an implementation outside the
//! scanned sources is not seen. Gaps and measurements:
//! `TODOs/callgraph-fip-summaries.md`, `TODOs/callgraph-limitations.md`.

use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

use fip_lint_rules::ALLOC_FREE_METHODS;

use crate::srcmodel::{self, Arg, Ev, MarkKind, Program, Res};

/// An allocation bound: finite, `∞`, or unknown (`⊤`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bound {
    /// At most this many allocations.
    Finite(u64),
    /// Unbounded (an allocating call or site inside a loop, or widened recursion).
    Infinite,
    /// Cannot be determined from the scanned sources.
    Unknown,
}

impl Bound {
    const ZERO: Self = Self::Finite(0);

    fn add(self, o: Self) -> Self {
        match (self, o) {
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Infinite, _) | (_, Self::Infinite) => Self::Infinite,
            (Self::Finite(a), Self::Finite(b)) => Self::Finite(a.saturating_add(b)),
        }
    }

    fn mul(self, o: Self) -> Self {
        match (self, o) {
            (Self::Finite(0), _) | (_, Self::Finite(0)) => Self::ZERO,
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Infinite, _) | (_, Self::Infinite) => Self::Infinite,
            (Self::Finite(a), Self::Finite(b)) => Self::Finite(a.saturating_mul(b)),
        }
    }
}

impl fmt::Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Finite(n) => write!(f, "{n}"),
            Self::Infinite => f.write_str("∞"),
            Self::Unknown => f.write_str("⊤"),
        }
    }
}

/// `c + Σ k·alloc(param)`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Sum {
    c: Bound,
    terms: BTreeMap<String, Bound>,
}

impl Sum {
    fn konst(c: Bound) -> Self {
        Self {
            c,
            terms: BTreeMap::new(),
        }
    }

    fn zero() -> Self {
        Self::konst(Bound::ZERO)
    }

    fn unknown() -> Self {
        Self::konst(Bound::Unknown)
    }

    fn term(p: &str) -> Self {
        let mut s = Self::zero();
        s.terms.insert(p.to_string(), Bound::Finite(1));
        s
    }

    fn norm(mut self) -> Self {
        if self.c == Bound::Unknown {
            self.terms.clear();
        }
        self.terms.retain(|_, k| *k != Bound::ZERO);
        self
    }

    fn add(&self, o: &Self) -> Self {
        let mut s = self.clone();
        s.c = s.c.add(o.c);
        for (p, k) in &o.terms {
            let e = s.terms.entry(p.clone()).or_insert(Bound::ZERO);
            *e = e.add(*k);
        }
        s.norm()
    }

    fn scale(&self, k: Bound) -> Self {
        Self {
            c: k.mul(self.c),
            terms: self
                .terms
                .iter()
                .map(|(p, c)| (p.clone(), k.mul(*c)))
                .collect(),
        }
        .norm()
    }

    fn max(&self, o: &Self) -> Self {
        let mut s = self.clone();
        s.c = s.c.max(o.c);
        for (p, k) in &o.terms {
            let e = s.terms.entry(p.clone()).or_insert(Bound::ZERO);
            *e = (*e).max(*k);
        }
        s.norm()
    }

    fn subst(&self, p: &str, v: &Self) -> Self {
        let mut s = self.clone();
        match s.terms.remove(p) {
            Some(k) => s.add(&v.scale(k)),
            None => s,
        }
    }

    /// Widening for recursive components: components that grew become `∞`.
    fn widen(old: &Self, new: &Self) -> Self {
        let up = |o: Bound, n: Bound| {
            if n > o && n != Bound::Unknown {
                Bound::Infinite
            } else {
                n
            }
        };
        Self {
            c: up(old.c, new.c),
            terms: new
                .terms
                .iter()
                .map(|(p, k)| {
                    let o = old.terms.get(p).copied().unwrap_or(Bound::ZERO);
                    (p.clone(), up(o, *k))
                })
                .collect(),
        }
        .norm()
    }
}

impl fmt::Display for Sum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = Vec::new();
        if self.c != Bound::ZERO || self.terms.is_empty() {
            parts.push(self.c.to_string());
        }
        for (p, k) in &self.terms {
            if *k == Bound::Finite(1) {
                parts.push(format!("alloc({p})"));
            } else {
                parts.push(format!("{k}·alloc({p})"));
            }
        }
        f.write_str(&parts.join(" + "))
    }
}

/// What a violation is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViolationKind {
    /// The root takes part in, or reaches, a call cycle (not allowed for `#[fip]` /
    /// `#[fip(N)]`).
    Recursion {
        /// The cycle, first name repeated at the end.
        cycle: Vec<String>,
    },
    /// The computed bound exceeds what the attribute allows.
    BoundExceeded {
        /// Computed bound (`∞` for an allocation reached inside a loop).
        bound: Bound,
        /// `0` for `#[fip]`/`#[fbip]`, `N` for `#[fip(N)]`.
        allowed: u64,
    },
    /// The bound is unknown (`⊤`) because of something the checker cannot see into.
    Unresolved {
        /// What could not be resolved.
        what: String,
        /// `file:line`.
        at: String,
    },
    /// A call passes, for a parameter declared `param(g = K)`, an argument whose
    /// bound is not at most `K`.
    ArgumentExceedsDeclared {
        /// Calling function.
        caller: String,
        /// Parameter name.
        param: String,
        /// Declared bound `K`.
        declared: u64,
        /// Bound of the argument.
        bound: Bound,
        /// `file:line` of the call.
        at: String,
    },
}

/// A violation of a marked function, with a witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Violation {
    /// The marked function (display name: module path, owner, name).
    pub root: String,
    /// Its attribute (`#[fip]`, `#[fip(2)]`, `#[fbip]`).
    pub attribute: String,
    /// What is violated.
    pub kind: ViolationKind,
    /// Call chain from the root to an allocation site or unresolved call, with
    /// `(in loop)` markers and `file:line`, e.g.
    /// ``a -> b (in loop) -> c: allocation site `Box::new` at x.rs:3``.
    pub witness: String,
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = match &self.kind {
            ViolationKind::Recursion { .. } => "recursion".to_string(),
            ViolationKind::BoundExceeded { bound, allowed } => {
                format!("may allocate {bound} times, at most {allowed} allowed")
            }
            ViolationKind::Unresolved { what, at } => {
                format!("cannot check: {what} at {at}")
            }
            ViolationKind::ArgumentExceedsDeclared {
                param,
                declared,
                bound,
                ..
            } => format!("argument for `{param}` may allocate {bound} times, declared {declared}"),
        };
        write!(
            f,
            "{} {}: {what}; {}",
            self.attribute, self.root, self.witness
        )
    }
}

/// A higher-order root whose bound depends on its (undeclared) parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conditional {
    /// The marked function.
    pub root: String,
    /// Its attribute.
    pub attribute: String,
    /// Symbolic bound, e.g. `∞·alloc(g)`: fip relative to its parameters.
    pub summary: String,
}

/// Bound of one marked function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootSummary {
    /// The marked function.
    pub root: String,
    /// Its attribute.
    pub attribute: String,
    /// Bound after `param(..)` instantiation (`⊤` unknown, `∞` unbounded).
    pub summary: String,
    /// An explicit `drop` / `mem::drop` is reachable (implicit drops are not seen).
    pub may_free: bool,
    /// `file:line` of the function.
    pub at: String,
}

/// Result of [`fip_violations`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Report {
    /// Violations, each with a witness.
    pub violations: Vec<Violation>,
    /// Roots that pass only relative to their parameters.
    pub conditional: Vec<Conditional>,
    /// Every marked function with its bound.
    pub roots: Vec<RootSummary>,
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for v in &self.violations {
            writeln!(f, "violation: {v}")?;
        }
        for c in &self.conditional {
            writeln!(
                f,
                "conditional: {} {}: fip relative to its parameters, bound {}",
                c.attribute, c.root, c.summary
            )?;
        }
        Ok(())
    }
}

/// [`fip_violations`] over `sources` (path, text) as one crate.
#[must_use]
pub fn fip_violations_in(sources: &[(PathBuf, String)]) -> Report {
    Analysis::new(&srcmodel::build(
        &[(String::new(), sources.to_vec())],
        false,
    ))
    .report()
}

/// [`fip_violations`] over in-memory crates (crate name, sources).
#[must_use]
pub fn fip_violations_in_crates(crates: &[(&str, &[(PathBuf, String)])]) -> Report {
    let groups: Vec<srcmodel::Group> = crates
        .iter()
        .map(|(n, s)| ((*n).to_string(), s.to_vec()))
        .collect();
    Analysis::new(&srcmodel::build(&groups, true)).report()
}

/// [`fip_violations_in`] over every `.rs` file under `dir`.
///
/// # Panics
///
/// Panics if `dir` or a file in it cannot be read.
#[must_use]
pub fn fip_violations_dir(dir: &Path) -> Report {
    fip_violations_in(&srcmodel::read_dir_sources(dir))
}

/// Checks every `#[fip]` / `#[fip(N)]` / `#[fbip]` function of the given crates
/// (crate name, source directory) against its attribute, counting allocations
/// through callees. Paths `crate_name::..` resolve into the scanned crate of that
/// name.
///
/// # Panics
///
/// Panics if a directory or a file in it cannot be read.
#[must_use]
pub fn fip_violations(crates: &[(&str, &Path)]) -> Report {
    let groups: Vec<srcmodel::Group> = crates
        .iter()
        .map(|(n, d)| ((*n).to_string(), srcmodel::read_dir_sources(d)))
        .collect();
    Analysis::new(&srcmodel::build(&groups, true)).report()
}

/// Binding of a callable parameter while explaining a bound.
#[derive(Clone, Debug)]
struct Bind {
    sum: Sum,
    src: Src,
}

#[derive(Clone, Debug)]
enum Src {
    None,
    Closure(usize, Env),
    Fns(Vec<usize>),
}

type Env = BTreeMap<String, Bind>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Want {
    Unknown,
    Positive,
    Infinite,
}

impl Want {
    fn matches(self, c: Bound) -> bool {
        match self {
            Self::Unknown => c == Bound::Unknown,
            Self::Positive => c != Bound::Unknown && c > Bound::ZERO,
            Self::Infinite => c == Bound::Infinite,
        }
    }
}

/// End of a witness chain.
#[derive(Clone, Debug)]
struct Leaf {
    steps: Vec<String>,
    what: String,
    at: String,
}

/// Where an event is explained: the function, its parameter bindings, what is
/// sought, the loop marker and `file:line`.
struct Place<'e> {
    func: usize,
    env: &'e Env,
    want: Want,
    tag: &'e str,
    at: String,
}

/// State while explaining one root.
struct Explain {
    path: Vec<usize>,
    steps: Vec<String>,
    leaves: Vec<Leaf>,
    all: bool,
}

struct Analysis<'p> {
    p: &'p Program,
    sums: Vec<Sum>,
    frees: Vec<bool>,
}

fn attribute(m: &srcmodel::Mark) -> String {
    match m.kind {
        MarkKind::Fbip => "#[fbip]".to_string(),
        _ if m.n > 0 => format!("#[fip({})]", m.n),
        _ => "#[fip]".to_string(),
    }
}

fn path_text(segs: &[String], name: &str) -> String {
    let mut p = segs.to_vec();
    p.push(name.to_string());
    p.join("::")
}

impl<'p> Analysis<'p> {
    fn new(p: &'p Program) -> Self {
        let mut a = Self {
            p,
            sums: vec![Sum::zero(); p.fns.len()],
            frees: vec![false; p.fns.len()],
        };
        for scc in a.sccs() {
            a.solve(&scc);
        }
        a
    }

    fn deps(&self, f: usize) -> Vec<usize> {
        let mut out = Vec::new();
        for e in &self.p.fns[f].events {
            match &e.ev {
                Ev::Call { args, res, .. } | Ev::Method { args, res, .. } => {
                    if let Res::Fns(v) = res {
                        out.extend(v.iter().copied());
                    }
                    for a in args {
                        match a {
                            Arg::Closure(c) => out.push(*c),
                            Arg::Named {
                                res: Res::Fns(v), ..
                            } => out.extend(v.iter().copied()),
                            _ => {}
                        }
                    }
                }
                Ev::ClosureCall(c) => out.push(*c),
                _ => {}
            }
        }
        out
    }

    /// Strongly connected components in reverse topological order (Tarjan).
    fn sccs(&self) -> Vec<Vec<usize>> {
        let n = self.p.fns.len();
        let deps: Vec<Vec<usize>> = (0..n).map(|f| self.deps(f)).collect();
        let mut st = Tarjan {
            index: vec![usize::MAX; n],
            low: vec![0; n],
            on: vec![false; n],
            stack: Vec::new(),
            next: 0,
            out: Vec::new(),
        };
        for v in 0..n {
            if st.index[v] == usize::MAX {
                st.visit(&deps, v);
            }
        }
        st.out
    }

    fn solve(&mut self, scc: &[usize]) {
        let mut round = 0;
        loop {
            let mut changed = false;
            for &f in scc {
                let mut new = self.eval_fn(f);
                if round >= 2 {
                    new = Sum::widen(&self.sums[f], &new);
                }
                let fr = self.eval_frees(f);
                if new != self.sums[f] || fr != self.frees[f] {
                    changed = true;
                    self.sums[f] = new;
                    self.frees[f] = fr;
                }
            }
            round += 1;
            if !changed {
                break;
            }
            if round > 64 {
                for &f in scc {
                    self.sums[f] = Sum::unknown();
                }
                break;
            }
        }
    }

    fn eval_frees(&self, f: usize) -> bool {
        self.p.fns[f].events.iter().any(|e| match &e.ev {
            Ev::Call {
                res: Res::External { frees: true, .. },
                ..
            } => true,
            Ev::Call {
                res: Res::Fns(v), ..
            }
            | Ev::Method {
                res: Res::Fns(v), ..
            } => v.iter().any(|&t| self.frees[t]),
            Ev::ClosureCall(c) => self.frees[*c],
            _ => false,
        })
    }

    fn eval_fn(&self, f: usize) -> Sum {
        let mut total = Sum::zero();
        for e in &self.p.fns[f].events {
            let mut c = self.ev_cost(f, &e.ev);
            if e.in_loop {
                c = c.scale(Bound::Infinite);
            }
            total = total.add(&c);
        }
        total
    }

    fn is_callable(&self, f: usize, p: &str) -> bool {
        self.p.fns[self.p.outer(f)]
            .params
            .iter()
            .any(|q| q.callable && q.name == p)
    }

    /// Argument offset for a call to `t`: path calls and qualified calls pass the
    /// receiver as the first argument.
    fn offset(&self, t: usize, ev: &Ev) -> usize {
        let has_self = self.p.fns[t].has_self;
        match ev {
            Ev::Call { .. }
            | Ev::Method {
                qualified: true, ..
            } => usize::from(has_self),
            _ => 0,
        }
    }

    fn ev_cost(&self, f: usize, ev: &Ev) -> Sum {
        match ev {
            Ev::Site(_) => Sum::konst(Bound::Finite(1)),
            Ev::Call { args, res, .. } => match res {
                Res::Fns(v) if !v.is_empty() => self.max_inst(f, v, args, ev),
                Res::External { cost: Some(k), .. } => Sum::konst(Bound::Finite(*k)),
                Res::Constructor => Sum::zero(),
                _ => Sum::unknown(),
            },
            Ev::Method {
                name,
                args,
                site,
                res,
                ..
            } => {
                let v = match res {
                    Res::Fns(v) => v.as_slice(),
                    _ => &[],
                };
                if !v.is_empty() {
                    let s = self.max_inst(f, v, args, ev);
                    if *site {
                        s.max(&Sum::konst(Bound::Finite(1)))
                    } else {
                        s
                    }
                } else if *site {
                    Sum::konst(Bound::Finite(1))
                } else if ALLOC_FREE_METHODS.contains(&name.as_str()) {
                    Sum::zero()
                } else {
                    Sum::unknown()
                }
            }
            Ev::ParamCall(p) if self.is_callable(f, p) => Sum::term(p),
            Ev::ClosureCall(c) => self.sums[*c].clone(),
            Ev::Escape(_) | Ev::Value { .. } => Sum::zero(),
            Ev::ParamCall(_) | Ev::Indirect | Ev::Unknown(_) => Sum::unknown(),
        }
    }

    fn max_inst(&self, f: usize, v: &[usize], args: &[Arg], ev: &Ev) -> Sum {
        let mut out: Option<Sum> = None;
        for &t in v {
            let s = self.inst(f, t, args, self.offset(t, ev));
            out = Some(match out {
                Some(o) => o.max(&s),
                None => s,
            });
        }
        out.unwrap_or_else(Sum::unknown)
    }

    /// Callee `t`'s summary with its parameter terms replaced by `args` (in `f`'s
    /// terms).
    fn inst(&self, f: usize, t: usize, args: &[Arg], offset: usize) -> Sum {
        let s = &self.sums[t];
        let mut out = Sum::konst(s.c);
        for (p, k) in &s.terms {
            let v = self.p.fns[t]
                .params
                .iter()
                .position(|q| &q.name == p)
                .and_then(|i| args.get(i + offset))
                .map_or_else(Sum::unknown, |a| self.arg_sum(f, a));
            out = out.add(&v.scale(*k));
        }
        out
    }

    fn arg_sum(&self, f: usize, a: &Arg) -> Sum {
        match a {
            Arg::Closure(c) => self.sums[*c].clone(),
            Arg::Param(p) if self.is_callable(f, p) => Sum::term(p),
            Arg::Named {
                res: Res::Fns(v), ..
            } if !v.is_empty() => {
                let mut out = Sum::zero();
                for &t in v {
                    if !self.sums[t].terms.is_empty() {
                        return Sum::unknown();
                    }
                    out = out.max(&self.sums[t]);
                }
                out
            }
            _ => Sum::unknown(),
        }
    }

    // ---- verdicts ----

    fn report(&self) -> Report {
        let g = self.p.graph();
        let mut rep = Report::default();
        for r in self.p.roots() {
            self.check_root(r, &g, &mut rep);
        }
        self.check_declared_arguments(&mut rep);
        rep
    }

    fn root_env(&self, r: usize) -> (Sum, Env) {
        let f = &self.p.fns[r];
        let mut s = self.sums[r].clone();
        let mut env = Env::new();
        for (g, k) in &f.mark.params {
            let v = Sum::konst(Bound::Finite(*k));
            s = s.subst(g, &v);
            env.insert(
                g.clone(),
                Bind {
                    sum: v,
                    src: Src::None,
                },
            );
        }
        (s, env)
    }

    fn check_root(&self, r: usize, g: &[std::collections::BTreeSet<usize>], rep: &mut Report) {
        let f = &self.p.fns[r];
        let attr = attribute(&f.mark);
        let (s, env) = self.root_env(r);
        rep.roots.push(RootSummary {
            root: f.display.clone(),
            attribute: attr.clone(),
            summary: s.to_string(),
            may_free: self.frees[r],
            at: self.p.loc(f.file, f.line),
        });
        let mut bad = false;
        if f.mark.kind == MarkKind::Fip {
            for cycle in self.p.cycles_from(g, r) {
                bad = true;
                let mut chain = self.p.chain_to(g, r, &cycle[0]);
                chain.pop();
                chain.extend(cycle.iter().cloned());
                rep.violations.push(Violation {
                    root: f.display.clone(),
                    attribute: attr.clone(),
                    witness: chain.join(" -> "),
                    kind: ViolationKind::Recursion { cycle },
                });
            }
        }
        let allowed = if f.mark.kind == MarkKind::Fip {
            f.mark.n
        } else {
            0
        };
        if s.c == Bound::Unknown {
            for leaf in self.explain_root(r, &env, Want::Unknown, true) {
                rep.violations.push(Violation {
                    root: f.display.clone(),
                    attribute: attr.clone(),
                    witness: self.witness(r, &leaf),
                    kind: ViolationKind::Unresolved {
                        what: leaf.what.clone(),
                        at: leaf.at.clone(),
                    },
                });
            }
        } else if s.c > Bound::Finite(allowed) {
            let want = if s.c == Bound::Infinite {
                Want::Infinite
            } else {
                Want::Positive
            };
            let leaf = self.explain_root(r, &env, want, false).into_iter().next();
            rep.violations.push(Violation {
                root: f.display.clone(),
                attribute: attr.clone(),
                witness: leaf.map_or_else(String::new, |l| self.witness(r, &l)),
                kind: ViolationKind::BoundExceeded {
                    bound: s.c,
                    allowed,
                },
            });
        } else if !s.terms.is_empty() && !bad {
            rep.conditional.push(Conditional {
                root: f.display.clone(),
                attribute: attr,
                summary: s.to_string(),
            });
        }
    }

    fn check_declared_arguments(&self, rep: &mut Report) {
        for (k, f) in self.p.fns.iter().enumerate() {
            for e in &f.events {
                let (Ev::Call {
                    args,
                    res: Res::Fns(v),
                    ..
                }
                | Ev::Method {
                    args,
                    res: Res::Fns(v),
                    ..
                }) = &e.ev
                else {
                    continue;
                };
                for &t in v {
                    let callee = &self.p.fns[t];
                    for (g, decl) in &callee.mark.params {
                        let Some(i) = callee.params.iter().position(|q| &q.name == g) else {
                            continue;
                        };
                        let a = args.get(i + self.offset(t, &e.ev)).unwrap_or(&Arg::Other);
                        let s = self.arg_sum(k, a);
                        if s.terms.is_empty() && s.c > Bound::Finite(*decl) {
                            let at = self.p.loc(e.file, e.line);
                            rep.violations.push(Violation {
                                root: callee.display.clone(),
                                attribute: attribute(&callee.mark),
                                witness: format!(
                                    "{} -> {} at {at}: argument for `{g}` may allocate {} times",
                                    self.p.fns[self.p.outer(k)].display,
                                    callee.display,
                                    s.c
                                ),
                                kind: ViolationKind::ArgumentExceedsDeclared {
                                    caller: self.p.fns[self.p.outer(k)].display.clone(),
                                    param: g.clone(),
                                    declared: *decl,
                                    bound: s.c,
                                    at,
                                },
                            });
                        }
                    }
                }
            }
        }
    }

    fn witness(&self, r: usize, leaf: &Leaf) -> String {
        let mut chain = vec![self.p.fns[r].display.clone()];
        chain.extend(leaf.steps.iter().cloned());
        format!("{}: {} at {}", chain.join(" -> "), leaf.what, leaf.at)
    }

    // ---- witnesses ----

    fn conc(s: &Sum, env: &Env) -> Sum {
        let mut out = Sum::konst(s.c);
        for (p, k) in &s.terms {
            let v = env.get(p).map_or_else(|| Sum::term(p), |b| b.sum.clone());
            out = out.add(&v.scale(*k));
        }
        out
    }

    fn explain_root(&self, r: usize, env: &Env, want: Want, all: bool) -> Vec<Leaf> {
        let mut st = Explain {
            path: Vec::new(),
            steps: Vec::new(),
            leaves: Vec::new(),
            all,
        };
        self.explain(r, env, want, &mut st);
        let mut seen = std::collections::BTreeSet::new();
        st.leaves
            .into_iter()
            .filter(|l| seen.insert((l.what.clone(), l.at.clone())))
            .collect()
    }

    /// Finds events of `f` (under `env`) whose contribution matches `want` and
    /// follows them to allocation sites or unresolved calls.
    fn explain(&self, f: usize, env: &Env, want: Want, st: &mut Explain) -> bool {
        st.path.push(f);
        let mut found = false;
        for e in &self.p.fns[f].events {
            let raw = Self::conc(&self.ev_cost(f, &e.ev), env);
            let c = if e.in_loop {
                raw.scale(Bound::Infinite)
            } else {
                raw.clone()
            };
            if !want.matches(c.c) {
                continue;
            }
            let inner = if want == Want::Infinite && raw.c != Bound::Infinite {
                Want::Positive
            } else {
                want
            };
            let place = Place {
                func: f,
                env,
                want: inner,
                tag: if e.in_loop { " (in loop)" } else { "" },
                at: self.p.loc(e.file, e.line),
            };
            if self.explain_event(&place, &e.ev, st) {
                found = true;
                if !st.all {
                    break;
                }
            }
        }
        st.path.pop();
        found
    }

    fn explain_event(&self, pl: &Place<'_>, ev: &Ev, st: &mut Explain) -> bool {
        let tag = pl.tag;
        let leaf = |st: &mut Explain, what: String| {
            st.leaves.push(Leaf {
                steps: st.steps.clone(),
                what,
                at: pl.at.clone(),
            });
            true
        };
        match ev {
            Ev::Site(w) => leaf(st, format!("allocation site {w}{tag}")),
            Ev::Call {
                segs,
                name,
                args,
                res,
            } => match res {
                Res::Fns(v) if !v.is_empty() => self.descend(pl, v, args, ev, st),
                Res::Guess(v) => {
                    let names: Vec<&str> =
                        v.iter().map(|&t| self.p.fns[t].display.as_str()).collect();
                    let path = path_text(segs, name);
                    let names = names.join(", ");
                    leaf(
                        st,
                        format!("unresolved call `{path}` (only name matches: {names}){tag}"),
                    )
                }
                _ => leaf(
                    st,
                    format!("unresolved call `{}`{tag}", path_text(segs, name)),
                ),
            },
            Ev::Method {
                name,
                args,
                site,
                res,
                ..
            } => {
                let targets = match res {
                    Res::Fns(v) => v.as_slice(),
                    _ => &[],
                };
                if !targets.is_empty() && self.descend(pl, targets, args, ev, st) {
                    return true;
                }
                if *site {
                    leaf(st, format!("allocation site `.{name}()`{tag}"))
                } else if targets.is_empty() {
                    leaf(st, format!("unresolved method `.{name}()`{tag}"))
                } else {
                    false
                }
            }
            Ev::ParamCall(param) => match pl.env.get(param).map(|bind| &bind.src) {
                Some(Src::Closure(closure, cenv)) => {
                    let shown = &self.p.fns[*closure].display;
                    st.steps
                        .push(format!("{shown} (argument for `{param}`){tag}"));
                    let found = self.explain(*closure, cenv, pl.want, st);
                    st.steps.pop();
                    found
                }
                Some(Src::Fns(targets)) => {
                    let empty = Env::new();
                    let inner = Place {
                        env: &empty,
                        at: pl.at.clone(),
                        ..*pl
                    };
                    self.descend(&inner, targets, &[], ev, st)
                }
                _ => {
                    let bound = pl
                        .env
                        .get(param)
                        .map_or_else(|| "unknown".to_string(), |bind| bind.sum.to_string());
                    leaf(
                        st,
                        format!("call to parameter `{param}` (bound {bound}){tag}"),
                    )
                }
            },
            Ev::ClosureCall(closure) => {
                st.steps
                    .push(format!("{}{tag}", self.p.fns[*closure].display));
                let found =
                    !st.path.contains(closure) && self.explain(*closure, pl.env, pl.want, st);
                st.steps.pop();
                found
            }
            Ev::Indirect => leaf(st, format!("call through an expression{tag}")),
            Ev::Unknown(what) => leaf(st, format!("{what}{tag}")),
            Ev::Escape(_) | Ev::Value { .. } => false,
        }
    }

    fn descend(
        &self,
        pl: &Place<'_>,
        targets: &[usize],
        args: &[Arg],
        ev: &Ev,
        st: &mut Explain,
    ) -> bool {
        let mut found = false;
        for &t in targets {
            if st.path.contains(&t) {
                continue;
            }
            let child = self.bind_args(pl.func, t, args, self.offset(t, ev), pl.env);
            if !pl.want.matches(Self::conc(&self.sums[t], &child).c) {
                continue;
            }
            st.steps
                .push(format!("{}{}", self.p.fns[t].display, pl.tag));
            let r = self.explain(t, &child, pl.want, st);
            st.steps.pop();
            if r {
                found = true;
                if !st.all {
                    break;
                }
            }
        }
        found
    }

    fn bind_args(&self, f: usize, t: usize, args: &[Arg], offset: usize, env: &Env) -> Env {
        let mut out = Env::new();
        for (i, prm) in self.p.fns[t].params.iter().enumerate() {
            if !prm.callable {
                continue;
            }
            let b = match args.get(i + offset) {
                Some(Arg::Closure(c)) => Bind {
                    sum: Self::conc(&self.sums[*c], env),
                    src: Src::Closure(*c, env.clone()),
                },
                Some(Arg::Param(q)) => env.get(q).cloned().unwrap_or_else(|| Bind {
                    sum: Sum::term(q),
                    src: Src::None,
                }),
                Some(
                    a @ Arg::Named {
                        res: Res::Fns(v), ..
                    },
                ) => Bind {
                    sum: self.arg_sum(f, a),
                    src: Src::Fns(v.clone()),
                },
                _ => Bind {
                    sum: Sum::unknown(),
                    src: Src::None,
                },
            };
            out.insert(prm.name.clone(), b);
        }
        out
    }
}

struct Tarjan {
    index: Vec<usize>,
    low: Vec<usize>,
    on: Vec<bool>,
    stack: Vec<usize>,
    next: usize,
    out: Vec<Vec<usize>>,
}

impl Tarjan {
    fn visit(&mut self, deps: &[Vec<usize>], v: usize) {
        self.index[v] = self.next;
        self.low[v] = self.next;
        self.next += 1;
        self.stack.push(v);
        self.on[v] = true;
        for &w in &deps[v] {
            if self.index[w] == usize::MAX {
                self.visit(deps, w);
                self.low[v] = self.low[v].min(self.low[w]);
            } else if self.on[w] {
                self.low[v] = self.low[v].min(self.index[w]);
            }
        }
        if self.low[v] == self.index[v] {
            let mut scc = Vec::new();
            while let Some(w) = self.stack.pop() {
                self.on[w] = false;
                scc.push(w);
                if w == v {
                    break;
                }
            }
            self.out.push(scc);
        }
    }
}

#[cfg(test)]
mod tests;
