// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Roots, attribute validation and verdicts as compiler diagnostics.
//!
//! | verdict | diagnostic |
//! |---|---|
//! | allocation bound above the declared one (`fip`: 0, `fip(N)`: N, `fbip`: 0) | error |
//! | possible free, recursion (`fip`, `fip(N)`) | error |
//! | `⊤`: unresolved call, no usable MIR ("cannot check") | error, one per distinct leaf |
//! | panic path, `strict = true` with `panic_macros = false` | error |
//! | panic path, `strict = true` otherwise | note |
//! | terms left: callable parameters without `param(..)`, trait methods on generic parameters, drops of a bare type parameter (`drop(T)`, also inside the glue of `Option<T>`, `Vec<T>`, ..) | warning |
//! | a call site passing, for a callee's `param(g = K)`, an argument that may allocate more than `K` times per call, or `⊤` (in any analysed body: roots, what they reach in analysed crates, every local function and closure) | error, at the call site |
//! | unknown name under `fip::`, misplaced or malformed attribute | error |
//! | a FIP mark (`fip::mark`) on an allocation/free source, including `GlobalAlloc`/`Allocator` methods | error |
//! | a call site that does not establish the callee's `fip::requires(..)`, a function with `fip::requires(..)` used as a function value | panic path (above) |
//! | a malformed or unsatisfiable `fip::requires(..)` | error |
//! | an implementation (in this crate) of a trait method whose declaration carries `fip::mark` (a contract) that breaks it | error, as for a root (also when the driver compiles a dependency that declares `fip::export`) |
//! | an implementation of a contracted trait method in a crate without `fip::export` | error (`⊤`), at the implementation |
//! | `param(..)` in a trait method contract | error |
//! | a standard-library function without MIR not covered by the std summaries, or summaries not used (missing file, stamp of another rustc or target) | `⊤` (error), with the reason |
//!
//! `FIP_PRELINT_WARN_ONLY=1` turns the errors into warnings tagged `[error]`.
//! The per-crate summary note ends with the number of declared sources when the crate
//! declares any (`fip::alloc_source`/`fip::free_source` are trusted declarations).

use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::{Attribute, CRATE_OWNER_ID, ItemLocalId};
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_span::Span;

use crate::analysis::{
    Analysis, ArgViolation, Crates, Requires, RootResult, Witness, requires_facts,
};
use crate::marks::{self, Kind, Mark, Source};

struct Out<'tcx> {
    tcx: TyCtxt<'tcx>,
    warn_only: bool,
    errors: usize,
    warnings: usize,
    notes: usize,
}

impl<'tcx> Out<'tcx> {
    fn error(&mut self, span: Span, msg: &str) {
        self.errors += 1;
        if self.warn_only {
            self.tcx
                .dcx()
                .struct_span_warn(span, format!("fip-prelint [error]: {msg}"))
                .emit();
        } else {
            self.tcx
                .dcx()
                .struct_span_err(span, format!("fip-prelint: {msg}"))
                .emit();
        }
    }
    fn warning(&mut self, span: Span, msg: &str) {
        self.warnings += 1;
        self.tcx
            .dcx()
            .struct_span_warn(span, format!("fip-prelint: {msg}"))
            .emit();
    }
    fn note(&mut self, span: Span, msg: &str) {
        self.notes += 1;
        self.tcx
            .dcx()
            .struct_span_note(span, format!("fip-prelint: {msg}"))
            .emit();
    }
}

/// Where a span lies.
enum Loc {
    /// The standard library, the cargo registry, or no source: elided in chains.
    Std,
    /// A source outside the analysed workspace, given by absolute path (a path or
    /// git dependency such as `fip-strict` used by another project): shown in chains
    /// without its machine-dependent path.
    External,
    /// `file:line` in the analysed workspace (relative path).
    User(String),
}

fn locate(tcx: TyCtxt<'_>, span: Span) -> Loc {
    if span.is_dummy() {
        return Loc::Std;
    }
    let sp = span.source_callsite();
    let s = tcx.sess.source_map().span_to_diagnostic_string(sp);
    let file_line = s.split(": ").next().unwrap_or(&s);
    let mut parts = file_line.rsplitn(3, ':');
    let _col = parts.next();
    let (Some(line), Some(file)) = (parts.next(), parts.next()) else {
        return Loc::Std;
    };
    if file.starts_with("/rustc/")
        || file.contains("/.rustup/")
        || file.contains("/.cargo/registry/")
        || file.starts_with('<')
    {
        return Loc::Std;
    }
    if std::path::Path::new(file).is_absolute() {
        return Loc::External;
    }
    Loc::User(format!("{file}:{line}"))
}

/// `file:line` of a span in the analysed sources; `None` for the standard library
/// and the cargo registry, whose paths and lines depend on the toolchain, and for
/// sources outside the workspace (absolute paths).
fn user_location(tcx: TyCtxt<'_>, span: Span) -> Option<String> {
    match locate(tcx, span) {
        Loc::User(l) => Some(l),
        Loc::Std | Loc::External => None,
    }
}

/// `root -> a (file:line) -> b (in loop) (file:line): what (file:line)`: each call
/// with its call site when that lies in the analysed sources. Calls made inside the
/// standard library are elided as `…`, except the last one; calls made in sources
/// outside the workspace are shown without a location.
fn render(tcx: TyCtxt<'_>, root: &str, w: &Witness) -> String {
    let mut parts = vec![format!("`{root}`")];
    let n = w.steps.len();
    let mut elided = false;
    let mut elided_loop = false;
    for (k, s) in w.steps.iter().enumerate() {
        let place = locate(tcx, s.span);
        let shown = !matches!(place, Loc::Std);
        let loc = match place {
            Loc::User(l) => Some(l),
            Loc::Std | Loc::External => None,
        };
        if k == 0 || shown || k + 1 == n {
            if elided {
                parts.push(if elided_loop {
                    "… (in loop)".to_string()
                } else {
                    "…".to_string()
                });
                elided = false;
                elided_loop = false;
            }
            let mut p = format!("`{}`", s.label);
            if s.in_loop {
                p.push_str(" (in loop)");
            }
            if let Some(l) = loc {
                p.push_str(&format!(" ({l})"));
            }
            parts.push(p);
        } else {
            elided = true;
            elided_loop |= s.in_loop;
        }
    }
    let chain = parts.join(" -> ");
    let in_loop = if w.in_loop { " (in loop)" } else { "" };
    match user_location(tcx, w.span) {
        Some(l) => format!("{chain}: {}{in_loop} ({l})", w.what),
        None => format!("{chain}: {}{in_loop}", w.what),
    }
}

/// Primary span of a witness: the call site (or event) in the root's body.
fn primary(w: &Witness, fallback: Span) -> Span {
    let sp = w.steps.first().map_or(w.span, |s| s.span);
    if sp.is_dummy() {
        fallback
    } else {
        sp.source_callsite()
    }
}

/// Checks every `fip::` attribute of the crate: known name, right place.
fn validate_tool_attrs(out: &mut Out<'_>) {
    let tcx = out.tcx;
    let mut bad: Vec<(Span, String)> = Vec::new();
    for owner in tcx.hir_crate_items(()).owners() {
        let map = tcx.hir_attr_map(owner);
        for (local_id, attrs) in map.map.iter() {
            for attr in attrs.iter() {
                let Attribute::Unparsed(item) = attr else {
                    continue;
                };
                let segs: Vec<String> = item.path.segments.iter().map(|s| s.to_string()).collect();
                if segs.first().map(String::as_str) != Some("fip") {
                    continue;
                }
                let name = segs[1..].join("::");
                let on_owner = *local_id == ItemLocalId::ZERO;
                let on_root = owner == CRATE_OWNER_ID && on_owner;
                let on_fn = on_owner
                    && matches!(tcx.def_kind(owner.def_id), DefKind::Fn | DefKind::AssocFn);
                let msg = match name.as_str() {
                    "export" if on_root => None,
                    "export" => Some("`fip::export` belongs at the crate root: `#![cfg_attr(fip_prelint, fip::export)]`".to_string()),
                    "mark" if on_fn => None,
                    "mark" => Some("`fip::mark` applies to functions with a body".to_string()),
                    "alloc_source" | "free_source" if on_fn => None,
                    "requires" if on_fn => None,
                    "requires" => Some("`fip::requires` applies to functions".to_string()),
                    "alloc_source" | "free_source" => Some(format!(
                        "`fip::{name}` applies to functions, methods, trait method declarations and foreign functions"
                    )),
                    other => {
                        let names: Vec<String> =
                            marks::KNOWN.iter().map(|k| format!("`fip::{k}`")).collect();
                        let (last, rest) = names.split_last().expect("KNOWN is not empty");
                        Some(format!(
                            "unknown attribute `fip::{other}`; the tool `fip` has only {} and {last}",
                            rest.join(", ")
                        ))
                    }
                };
                if let Some(m) = msg {
                    bad.push((item.span, m));
                }
            }
        }
    }
    bad.sort_by_key(|(sp, _)| *sp);
    // The attribute of a unit or tuple struct is also recorded for its constructor:
    // one error per attribute.
    bad.dedup();
    for (sp, m) in bad {
        out.error(sp, &m);
    }
}

/// Local functions carrying `fip::mark`, through `rustc_public`.
fn roots(tcx: TyCtxt<'_>, out: &mut Out<'_>) -> Vec<(DefId, Mark)> {
    let mut roots = Vec::new();
    for f in rustc_public::local_crate().fn_defs() {
        for attr in f.all_tool_attrs() {
            let printed = attr.as_str();
            let Some(args) = marks::mark_args_of_printed(printed) else {
                continue;
            };
            let def_id: DefId = rustc_public::rustc_internal::internal(tcx, f.def_id());
            match marks::parse_mark(args) {
                Ok(m) => roots.push((def_id, m)),
                Err(e) => out.error(tcx.def_span(def_id), &format!("malformed `fip::mark`: {e}")),
            }
        }
    }
    roots.sort_by_key(|(d, _)| tcx.def_span(*d));
    roots
}

/// Local functions, trait method declarations and foreign functions carrying
/// `fip::alloc_source` or `fip::free_source`, through `rustc_public`.
fn local_sources(tcx: TyCtxt<'_>, out: &mut Out<'_>) -> Vec<(DefId, Source)> {
    let mut sources = Vec::new();
    for f in rustc_public::local_crate().fn_defs() {
        let attrs: Vec<String> = f
            .all_tool_attrs()
            .iter()
            .map(|a| a.as_str().to_string())
            .collect();
        let def_id: DefId = rustc_public::rustc_internal::internal(tcx, f.def_id());
        match marks::source_of_printed(attrs.iter().map(String::as_str)) {
            Ok(Some(s)) => sources.push((def_id, s)),
            Ok(None) => {}
            Err(e) => out.error(
                tcx.def_span(def_id),
                &format!("malformed allocation/free source: {e}"),
            ),
        }
    }
    sources.sort_by_key(|(d, _)| tcx.def_span(*d));
    sources
}

/// Local functions carrying `fip::requires(..)`, through `rustc_public`; a malformed
/// one is an error (and is not used).
fn local_requires(tcx: TyCtxt<'_>, out: &mut Out<'_>) -> Vec<(DefId, Requires)> {
    let mut found = Vec::new();
    for f in rustc_public::local_crate().fn_defs() {
        let attrs: Vec<String> = f
            .all_tool_attrs()
            .iter()
            .map(|a| a.as_str().to_string())
            .collect();
        let def_id: DefId = rustc_public::rustc_internal::internal(tcx, f.def_id());
        let parsed =
            marks::requires_of_printed(attrs.iter().map(String::as_str)).and_then(|cs| match cs {
                None => Ok(None),
                Some(cs) => requires_facts(tcx, def_id, &cs).map(|facts| {
                    Some(Requires {
                        text: fip_lint_rules::requires::display_all(&cs),
                        facts,
                    })
                }),
            });
        match parsed {
            Ok(Some(r)) => found.push((def_id, r)),
            Ok(None) => {}
            Err(e) => out.error(
                tcx.def_span(def_id),
                &format!("malformed `fip::requires`: {e}"),
            ),
        }
    }
    found.sort_by_key(|(d, _)| tcx.def_span(*d));
    found
}

/// Verdicts of one root (`requires`: its declared precondition, under which it is
/// analysed; `contract`: the trait method whose contract an implementation is
/// checked against).
fn verdict(
    out: &mut Out<'_>,
    def_id: DefId,
    mark: &Mark,
    requires: Option<&Requires>,
    contract: Option<&str>,
    r: &RootResult,
) {
    let label = r.label.as_str();
    let s = &r.summary;
    let tcx = out.tcx;
    let fspan = tcx.def_span(def_id);
    let mut tag = match requires {
        Some(req) => format!("{} under `fip::requires({})`", mark.tag(), req.text),
        None => mark.tag(),
    };
    if let Some(c) = contract {
        tag = format!("{tag} (contract of `{c}`)");
    }
    let bound = s.alloc.instantiate(&mark.params, &r.param_types);
    let allowed = match mark.kind {
        Kind::Fip => mark.n,
        Kind::Fbip => 0,
    };
    if bound.c.exceeds(allowed) {
        // One chain per call site in the root's body.
        let mut seen: Vec<Span> = Vec::new();
        let mut chains: Vec<String> = Vec::new();
        for w in &s.alloc_w {
            let sp = primary(w, fspan);
            if seen.contains(&sp) || chains.len() >= 3 {
                continue;
            }
            seen.push(sp);
            chains.push(render(tcx, label, w));
        }
        let sp = s.alloc_w.first().map_or(fspan, |w| primary(w, fspan));
        out.error(
            sp,
            &format!(
                "`{label}` is {tag} but may allocate {} time(s), at most {allowed} allowed: {}",
                bound.c,
                chains.join("; ")
            ),
        );
    }
    if mark.kind == Kind::Fip {
        if let Some(w) = s.free.first() {
            out.error(
                primary(w, fspan),
                &format!("`{label}` is {tag} but may free: {}", render(tcx, label, w)),
            );
        }
        if let Some(w) = &s.recursion {
            out.error(
                primary(w, fspan),
                &format!("`{label}` is {tag} but recurses: {}", render(tcx, label, w)),
            );
        }
    }
    for w in &s.unknown {
        out.error(
            primary(w, fspan),
            &format!(
                "cannot check `{label}` ({tag}): unresolved: {}",
                render(tcx, label, w)
            ),
        );
    }
    if mark.strict {
        for w in &s.panics {
            let msg = format!(
                "`{label}` is {tag}: reachable panic path: {}",
                render(tcx, label, w)
            );
            if mark.panic_macros {
                out.note(primary(w, fspan), &msg);
            } else {
                out.error(
                    primary(w, fspan),
                    &format!("{msg} (`panic_macros = false`)"),
                );
            }
        }
    }
    if !bound.terms.is_empty() {
        let mut obligations = Vec::new();
        for k in bound.terms.keys() {
            let what = match k.strip_prefix("drop(").and_then(|t| t.strip_suffix(')')) {
                Some(t) => format!("drop of a `{t}`"),
                None if k.starts_with('<') => format!("call of `{k}`"),
                None => format!("call of parameter `{k}`"),
            };
            let at = s
                .terms_w
                .get(k)
                .and_then(|w| {
                    w.spans()
                        .into_iter()
                        .rev()
                        .find_map(|sp| user_location(tcx, sp))
                })
                .map(|l| format!(" ({l})"))
                .unwrap_or_default();
            obligations.push(format!("{what}{at}"));
        }
        out.warning(
            fspan,
            &format!(
                "`{label}` is {tag} only relative to its generic parameters: allocation bound {}; open: {} (each instantiation is checked where it is analysed; `param(g = K)` fixes the bound of a callable parameter)",
                bound.display(),
                obligations.join("; ")
            ),
        );
    }
}

/// A call site whose argument violates the callee's `param(g = K)`.
fn report_argument(out: &mut Out<'_>, fallback: Span, v: &ArgViolation) {
    let tcx = out.tcx;
    let sp = if v.local && !v.span.is_dummy() {
        v.span.source_callsite()
    } else {
        fallback
    };
    let declared = format!("`param({} = {})`", v.param, v.declared);
    let mut chains: Vec<String> = Vec::new();
    if !v.summary.unknown.is_empty() {
        for w in &v.summary.unknown {
            let c = render(tcx, &v.arg, w);
            if chains.len() < 3 && !chains.contains(&c) {
                chains.push(c);
            }
        }
        out.error(
            sp,
            &format!(
                "cannot check the argument for `{}` that `{}` passes to `{}` (declared {declared}): unresolved: {}",
                v.param,
                v.caller,
                v.callee,
                chains.join("; ")
            ),
        );
        return;
    }
    // An event the callee's mark forbids, for a function pointer or trait object
    // parameter whose calls the callee counts by its declaration.
    if !v.bound.c.exceeds(v.declared)
        && let Some((what, w)) = &v.forbidden
    {
        out.error(
            sp,
            &format!(
                "`{}` passes to `{}` an argument for `{}` that {what}, but `{}` counts calls of `{}` by its declaration {declared} and its mark forbids that: {}",
                v.caller,
                v.callee,
                v.param,
                v.callee,
                v.param,
                render(tcx, &v.arg, w)
            ),
        );
        return;
    }
    // One chain per place in the analysed sources where the argument's allocations
    // start (the paths below `Box::new` differ only inside the standard library).
    let mut places: Vec<String> = Vec::new();
    for w in v.summary.alloc_w.iter().chain(v.summary.terms_w.values()) {
        let c = render(tcx, &v.arg, w);
        let place = w
            .spans()
            .into_iter()
            .find_map(|sp| user_location(tcx, sp))
            .unwrap_or_else(|| c.clone());
        if chains.len() < 3 && !places.contains(&place) {
            places.push(place);
            chains.push(c);
        }
    }
    out.error(
        sp,
        &format!(
            "`{}` passes to `{}` an argument for `{}` that may allocate {} time(s) per call, but `{}` declares {declared}: {}",
            v.caller,
            v.callee,
            v.param,
            v.bound.c,
            v.callee,
            chains.join("; ")
        ),
    );
}

/// Local functions, methods and closures with MIR, in definition order.
fn local_bodies(tcx: TyCtxt<'_>) -> Vec<DefId> {
    tcx.mir_keys(())
        .iter()
        .map(|d| d.to_def_id())
        .filter(|&d| {
            matches!(
                tcx.def_kind(d),
                DefKind::Fn | DefKind::AssocFn | DefKind::Closure
            ) && tcx.is_mir_available(d)
        })
        .collect()
}

/// Entry point after analysis: validate attributes, analyse every root, check the
/// declared parameter bounds at every call site, report.
pub fn check_crate(tcx: TyCtxt<'_>) {
    let mut out = Out {
        tcx,
        warn_only: std::env::var("FIP_PRELINT_WARN_ONLY").is_ok_and(|v| v == "1"),
        errors: 0,
        warnings: 0,
        notes: 0,
    };
    validate_tool_attrs(&mut out);
    let mut crates = Crates::new(tcx);
    // A dependency that declares `fip::export` but carries no MIR would otherwise look
    // opted in while giving no bodies: a hard error, whether or not a root calls it.
    for (krate, func) in crates.unencoded(tcx) {
        out.errors += 1;
        tcx.dcx().err(format!(
            "fip-prelint: crate `{krate}` declares `fip::export` but `{func}` has no MIR: \
             it was built without `-Zalways-encode-mir`. Declare `fip::export` in the crate's \
             source (`#![cfg_attr(fip_prelint, fip::export)]`) so that `cargo fip-prelint` \
             compiles it with the driver, or remove `fip::export`"
        ));
    }
    let marked = roots(tcx, &mut out);
    crates.add_local_marks(&marked);
    let sources = local_sources(tcx, &mut out);
    crates.add_local_sources(&sources);
    let requires = local_requires(tcx, &mut out);
    crates.add_local_requires(&requires);
    // A mark on a trait method declaration is a contract of every implementation, not
    // a root; a declaration with a default body is also checked as a root (the
    // default body, for any `Self`).
    let mut roots: Vec<(DefId, Mark)> = Vec::new();
    for (def_id, mark) in &marked {
        let decl = tcx.trait_of_assoc(*def_id).is_some();
        if decl && !mark.params.is_empty() {
            out.error(
                tcx.def_span(*def_id),
                "`param(..)` is not supported in the contract of a trait method: its dynamic calls are `⊤`",
            );
        }
        if !decl || tcx.defaultness(*def_id).has_value() {
            roots.push((*def_id, mark.clone()));
        }
    }
    // A violation reached from several roots (or also found in the body scan below) is
    // reported once, for the first root in source order.
    let mut seen: HashSet<String> = HashSet::new();
    let mut passed = 0usize;
    let mut checked = 0usize;
    for (def_id, mark) in &roots {
        checked += 1;
        // The body of an allocation or free source is outside FIP and never analysed:
        // a verdict on it would be vacuous, and would contradict its callers, which
        // count it as an allocation or a free.
        if let Some((s, kind)) = crates.source_of(tcx, *def_id) {
            let what = match (s.alloc, s.free) {
                (0, _) => "a possible free".to_string(),
                (n, false) => format!("{n} allocation(s)"),
                (n, true) => format!("{n} allocation(s) and a possible free"),
            };
            out.error(
                tcx.def_span(*def_id),
                &format!(
                    "`{}` is {} but is an allocation/free source ({}): its body is outside FIP and is not analysed, and its callers count each call as {what}; remove the FIP attribute",
                    tcx.def_path_str(*def_id),
                    mark.tag(),
                    kind.describe()
                ),
            );
            continue;
        }
        let before = (out.errors, out.warnings);
        let r = Analysis::run(tcx, &crates, *def_id, mark);
        verdict(
            &mut out,
            *def_id,
            mark,
            crates.requires_of(*def_id),
            None,
            &r,
        );
        for v in &r.args {
            if seen.insert(v.key()) {
                report_argument(&mut out, tcx.def_span(*def_id), v);
            }
        }
        if (out.errors, out.warnings) == before {
            passed += 1;
        }
    }
    let (c, p) = check_local_implementations(&mut out, &crates, &mut seen);
    checked += c;
    passed += p;
    // Implementations in other crates: one in a crate compiled by the driver (the
    // local crate's dependencies that declare `fip::export`) was checked against the
    // contract where it was compiled; one in any other crate cannot be checked (`⊤`),
    // whether or not this crate calls the method dynamically (a value of that type
    // may reach a dynamic call through a function of this crate).
    for (method, mark) in crates.contracts(tcx) {
        for impl_def in implementations(tcx, method) {
            let krate = impl_def.krate;
            if impl_def.is_local()
                || crates.exported(krate)
                || crate::analysis::is_std_crate(tcx.crate_name(krate).as_str())
            {
                continue;
            }
            out.error(
                tcx.def_span(impl_def),
                &format!(
                    "cannot check the contract `{}` of `{}`: its implementation for `{}` is in crate `{}`, which does not declare `fip::export`, so dynamic calls of the method are not covered by the contract (⊤)",
                    mark.tag(),
                    tcx.def_path_str(method),
                    tcx.type_of(impl_def).skip_binder(),
                    tcx.crate_name(krate)
                ),
            );
        }
    }
    // Callers that are not roots: every other local body, with identity arguments.
    let mut outside_roots = 0usize;
    if crates.has_param_marks() {
        for owner in local_bodies(tcx) {
            if roots.iter().any(|(d, _)| *d == owner) {
                continue;
            }
            for v in Analysis::arguments_in(tcx, &crates, owner) {
                if seen.insert(v.key()) {
                    report_argument(&mut out, tcx.def_span(owner), &v);
                    outside_roots += 1;
                }
            }
        }
    }
    if marked.is_empty() && checked == 0 && outside_roots == 0 && sources.is_empty() {
        return;
    }
    // Source marks are trusted declarations (they hide a body): their number is part
    // of the summary whenever the crate declares any.
    let declared = if sources.is_empty() {
        String::new()
    } else {
        format!(", {} declared sources", sources.len())
    };
    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
    tcx.dcx().note(format!(
        "fip-prelint: crate `{crate_name}`: {} roots, {passed} passed, {} errors, {} warnings, {} notes{declared}",
        checked,
        out.errors,
        out.warnings,
        out.notes
    ));
}

/// Every implementation in the local crate of a trait method with a contract
/// (declared here or in an exported crate) is checked against it, as a root.
/// Returns the number of implementations checked and of those that passed.
fn check_local_implementations(
    out: &mut Out<'_>,
    crates: &Crates,
    seen: &mut HashSet<String>,
) -> (usize, usize) {
    let tcx = out.tcx;
    let (mut checked, mut passed) = (0, 0);
    for (method, mark) in crates.contracts(tcx) {
        for impl_def in implementations(tcx, method) {
            if !impl_def.is_local() {
                continue;
            }
            checked += 1;
            let before = (out.errors, out.warnings);
            if let Some(r) = check_implementation(out, crates, impl_def, method, &mark) {
                for v in &r.args {
                    if seen.insert(v.key()) {
                        report_argument(out, tcx.def_span(impl_def), v);
                    }
                }
            }
            if (out.errors, out.warnings) == before {
                passed += 1;
            }
        }
    }
    (checked, passed)
}

/// A dependency that declares `fip::export`, compiled by the driver without roots
/// and verdicts: only its implementations of trait methods with a contract are
/// checked (dynamic calls in other crates rely on them). Silent unless one fails.
pub fn check_dependency(tcx: TyCtxt<'_>) {
    let mut out = Out {
        tcx,
        warn_only: std::env::var("FIP_PRELINT_WARN_ONLY").is_ok_and(|v| v == "1"),
        errors: 0,
        warnings: 0,
        notes: 0,
    };
    let mut crates = Crates::new(tcx);
    // Malformed attributes are not reported here (the crate is not checked); only
    // well-formed marks and sources are used.
    let marked: Vec<(DefId, Mark)> = rustc_public::local_crate()
        .fn_defs()
        .iter()
        .filter_map(|f| {
            let def_id: DefId = rustc_public::rustc_internal::internal(tcx, f.def_id());
            f.all_tool_attrs().iter().find_map(|a| {
                let args = marks::mark_args_of_printed(a.as_str())?;
                marks::parse_mark(args).ok().map(|m| (def_id, m))
            })
        })
        .collect();
    crates.add_local_marks(&marked);
    let sources: Vec<(DefId, Source)> = rustc_public::local_crate()
        .fn_defs()
        .iter()
        .filter_map(|f| {
            let def_id: DefId = rustc_public::rustc_internal::internal(tcx, f.def_id());
            let attrs: Vec<String> = f
                .all_tool_attrs()
                .iter()
                .map(|a| a.as_str().to_string())
                .collect();
            marks::source_of_printed(attrs.iter().map(String::as_str))
                .ok()
                .flatten()
                .map(|s| (def_id, s))
        })
        .collect();
    crates.add_local_sources(&sources);
    let mut seen = HashSet::new();
    let (checked, passed) = check_local_implementations(&mut out, &crates, &mut seen);
    if checked > 0 && out.errors + out.warnings > 0 {
        let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
        tcx.dcx().note(format!(
            "fip-prelint: dependency `{crate_name}`: {checked} implementations of trait methods with a contract, {passed} passed, {} errors, {} warnings",
            out.errors, out.warnings
        ));
    }
}

/// The implementations of the trait that declares `method`, over the whole crate
/// graph of the crate being checked, in a stable order.
fn implementations(tcx: TyCtxt<'_>, method: DefId) -> Vec<DefId> {
    let Some(trait_id) = tcx.trait_of_assoc(method) else {
        return Vec::new();
    };
    let mut impls: Vec<DefId> = tcx.all_impls(trait_id).collect();
    impls.sort_by_key(|d| (d.krate, tcx.def_path_str(*d)));
    impls
}

/// Checks the implementation of `method` in `impl_def` against the method's contract
/// `mark`, as a root: the impl's own method, or the trait's default body for that
/// impl. `None` if neither has MIR here (an error).
fn check_implementation(
    out: &mut Out<'_>,
    crates: &Crates,
    impl_def: DefId,
    method: DefId,
    mark: &Mark,
) -> Option<RootResult> {
    let tcx = out.tcx;
    let contract = tcx.def_path_str(method);
    let item = tcx
        .impl_item_implementor_ids(impl_def)
        .get(&method)
        .copied();
    let r = match item {
        Some(item) if tcx.is_mir_available(item) => {
            let r = Analysis::run(tcx, crates, item, mark);
            verdict(
                out,
                item,
                mark,
                crates.requires_of(item),
                Some(&contract),
                &r,
            );
            Some(r)
        }
        Some(_) => None,
        None => {
            let r = Analysis::run_default(tcx, crates, impl_def, method, mark);
            if let Some(r) = &r {
                verdict(out, impl_def, mark, None, Some(&contract), r);
            }
            r
        }
    };
    if r.is_none() {
        out.error(
            tcx.def_span(impl_def),
            &format!(
                "cannot check the implementation of `{contract}` for `{}` against its contract `{}`: no MIR",
                tcx.type_of(impl_def).skip_binder(),
                mark.tag()
            ),
        );
    }
    r
}

/// Generation mode (`cargo fip-prelint --std-summaries`): the local crate is the seed.
/// Every standard-library function without MIR in the shipped `std` that its roots
/// reach, and every such function those reach, is summarised from the `-Zbuild-std`
/// MIR ([`Analysis::summarize`]) and written to the file named by
/// `FIP_PRELINT_STD_SUMMARIES_OUT`, stamped with this compiler and the target.
pub fn generate(tcx: TyCtxt<'_>) {
    const MAX_FUNCTIONS: usize = 5_000;
    let start = std::time::Instant::now();
    let crates = Crates::new(tcx);
    let mut out = Out {
        tcx,
        warn_only: false,
        errors: 0,
        warnings: 0,
        notes: 0,
    };
    let seeds = roots(tcx, &mut out);
    let mut todo: Vec<DefId> = Vec::new();
    for (d, m) in &seeds {
        todo.extend(Analysis::reached_std(tcx, &crates, *d, m));
    }
    todo.reverse();
    let mut seen: HashSet<DefId> = HashSet::new();
    let mut fns = std::collections::BTreeMap::new();
    while let Some(d) = todo.pop() {
        if !seen.insert(d) {
            continue;
        }
        if seen.len() > MAX_FUNCTIONS {
            tcx.dcx().err(format!(
                "fip-prelint: more than {MAX_FUNCTIONS} standard-library functions reached; summaries not written"
            ));
            return;
        }
        let (s, reached) = Analysis::summarize(tcx, &crates, d);
        fns.insert(crate::analysis::def_path_pub(tcx, d), s);
        todo.extend(reached.into_iter().rev());
    }
    let sc = crate::stdsum::Sidecar {
        stamp: crate::stdsum::Stamp {
            format: crate::stdsum::FORMAT,
            rustc: crate::analysis::rustc_version().to_string(),
            target: tcx.sess.opts.target_triple.tuple().to_string(),
            settings: "opt-level=3 debug-assertions=off overflow-checks=off (-Zbuild-std, -Zalways-encode-mir)"
                .to_string(),
            std_src: {
                let lib = std::path::Path::new(&crate::sysroot(None))
                    .join("lib/rustlib/src/rust/library");
                let dirs: Vec<std::path::PathBuf> = ["core", "alloc", "std"]
                    .iter()
                    .map(|c| lib.join(c).join("src"))
                    .collect();
                crate::stdsum::hash_tree(&dirs).unwrap_or_else(|e| format!("unknown ({e})"))
            },
        },
        fns,
    };
    let Some(path) = std::env::var_os(crate::GENERATE_ENV) else {
        return;
    };
    if let Err(e) = std::fs::write(&path, sc.render()) {
        tcx.dcx().err(format!(
            "fip-prelint: cannot write `{}`: {e}",
            std::path::Path::new(&path).display()
        ));
        return;
    }
    tcx.dcx().note(format!(
        "fip-prelint: std summaries: {} functions from {} seed roots in {:.1} s, written to `{}`",
        sc.fns.len(),
        seeds.len(),
        start.elapsed().as_secs_f64(),
        std::path::Path::new(&path).display()
    ));
}
