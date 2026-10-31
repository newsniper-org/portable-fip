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
//! | terms left: callable parameters without `param(..)`, trait methods on generic parameters, drops of generic values | warning |
//! | unknown name under `fip::`, misplaced or malformed attribute | error |
//!
//! `FIP_PRELINT_WARN_ONLY=1` turns the errors into warnings tagged `[error]`.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::{Attribute, CRATE_OWNER_ID, ItemLocalId};
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_span::Span;

use crate::analysis::{Analysis, Crates, RootResult, Witness};
use crate::marks::{self, Kind, Mark};

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

/// `file:line` of a span in the analysed sources; `None` for the standard library
/// and the cargo registry, whose paths and lines depend on the toolchain.
fn user_location(tcx: TyCtxt<'_>, span: Span) -> Option<String> {
    if span.is_dummy() {
        return None;
    }
    let sp = span.source_callsite();
    let s = tcx.sess.source_map().span_to_diagnostic_string(sp);
    let file_line = s.split(": ").next().unwrap_or(&s);
    let mut parts = file_line.rsplitn(3, ':');
    let _col = parts.next();
    let line = parts.next()?;
    let file = parts.next()?;
    if file.starts_with("/rustc/")
        || file.contains("/.rustup/")
        || file.contains("/.cargo/registry/")
        || file.starts_with('<')
    {
        return None;
    }
    Some(format!("{file}:{line}"))
}

/// `root -> a (file:line) -> b (in loop) (file:line): what (file:line)`: each call
/// with its call site when that lies in the analysed sources. Calls made inside the
/// standard library are elided as `…`, except the last one.
fn render(tcx: TyCtxt<'_>, root: &str, w: &Witness) -> String {
    let mut parts = vec![format!("`{root}`")];
    let n = w.steps.len();
    let mut elided = false;
    let mut elided_loop = false;
    for (k, s) in w.steps.iter().enumerate() {
        let loc = user_location(tcx, s.span);
        if k == 0 || loc.is_some() || k + 1 == n {
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
                    other => Some(format!(
                        "unknown attribute `fip::{other}`; the tool `fip` has only {}",
                        marks::KNOWN
                            .iter()
                            .map(|k| format!("`fip::{k}`"))
                            .collect::<Vec<_>>()
                            .join(" and ")
                    )),
                };
                if let Some(m) = msg {
                    bad.push((item.span, m));
                }
            }
        }
    }
    bad.sort_by_key(|(sp, _)| *sp);
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

/// Verdicts of one root.
fn verdict(out: &mut Out<'_>, def_id: DefId, mark: &Mark, r: &RootResult) {
    let label = r.label.as_str();
    let s = &r.summary;
    let tcx = out.tcx;
    let fspan = tcx.def_span(def_id);
    let tag = mark.tag();
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

/// Entry point after analysis: validate attributes, analyse every root, report.
pub fn check_crate(tcx: TyCtxt<'_>) {
    let mut out = Out {
        tcx,
        warn_only: std::env::var("FIP_PRELINT_WARN_ONLY").is_ok_and(|v| v == "1"),
        errors: 0,
        warnings: 0,
        notes: 0,
    };
    validate_tool_attrs(&mut out);
    let crates = Crates::new(tcx);
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
    let roots = roots(tcx, &mut out);
    if roots.is_empty() {
        return;
    }
    let mut passed = 0usize;
    for (def_id, mark) in &roots {
        let before = (out.errors, out.warnings);
        let r = Analysis::run(tcx, &crates, *def_id);
        verdict(&mut out, *def_id, mark, &r);
        if (out.errors, out.warnings) == before {
            passed += 1;
        }
    }
    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
    tcx.dcx().note(format!(
        "fip-prelint: crate `{crate_name}`: {} roots, {passed} passed, {} errors, {} warnings, {} notes",
        roots.len(),
        out.errors,
        out.warnings,
        out.notes
    ));
}
