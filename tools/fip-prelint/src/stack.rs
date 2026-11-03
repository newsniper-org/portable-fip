// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Stack mode, driver side (limits plan L9; `cargo fip-prelint --stack`).
//!
//! In a `cargo build` with `FIP_PRELINT_STACK=1`, every crate the driver compiles
//! (`-Zemit-stack-sizes -Zshare-generics=no`, the profile's opt-level) records, next to
//! its rlib (`<rlib>.fip-stack`), what the stack bound needs from MIR:
//!
//! - `root`: each root (`fip::mark`) with the symbol of its instance, or why it has
//!   none (a generic root is not codegened by itself);
//! - `fn`: every function this crate codegens (symbol, then the instance) (its mono items, shims included) by
//!   symbol, with the reason it cannot be bounded, if any: a call through a function
//!   pointer, a dynamic call (trait object, also a drop of a `dyn` value), a call that
//!   does not resolve, inline assembly, a local of unsized type (a dynamic stack
//!   allocation, which no frame size covers). Machine code shows direct calls (relocations),
//!   not these; so every function a bound passes through must be listed here, mapped
//!   to its MIR instance, and free of them;
//! - `div`: the symbols of diverging `core`/`alloc`/`std` functions this crate calls
//!   and of the diverging standard-library lang items (the panic functions codegen
//!   calls for bounds and overflow checks): panic paths, excluded from the bound, as
//!   the claim states;
//! - `ext`: labels of the other functions called but not codegened here (messages);
//! - `leaf`: the crate's declared stack leaves (`fip::stack_leaf`, top plan T8b):
//!   symbol, bytes, evidence;
//! - `generic` / `inst`: a generic root (by a key, its `DefPathHash`), and every
//!   instance of a generic root (of any crate) this crate codegens, with its symbol
//!   (top plan T8e);
//! - `objs`: for an executable (a bin or a test, top plan T8f), the directory and file
//!   stem of its objects, kept by `-Csave-temps` (an executable's relocations are
//!   resolved, so the call graph needs the objects); executables contribute functions
//!   and instances, not roots (their roots are the library's).
//!
//! The bound itself is computed by `cargo-fip-prelint` from the objects
//! (`src/stackbound.rs`).

use std::fmt::Write as _;

use rustc_hir::def::DefKind;
use rustc_middle::mir::{Operand, TerminatorKind};
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, EarlyBinder, Instance, InstanceKind, TyCtxt, TypingEnv};
use rustc_session::config::CrateType;

use crate::analysis::is_std_crate;
use crate::marks::{Mark, StackLeaves};

/// Set by `cargo fip-prelint --stack`.
pub const STACK_ENV: &str = "FIP_PRELINT_STACK";

/// Format version of the `.fip-stack` file.
pub const FORMAT: u32 = 2;

/// The declared stack leaves of the attribute `fip::stack_leaf(..)` at `span` (its
/// source text, as written inside `cfg_attr`).
pub fn stack_leaf_of(tcx: TyCtxt<'_>, span: rustc_span::Span) -> Result<StackLeaves, String> {
    let text = tcx
        .sess
        .source_map()
        .span_to_snippet(span)
        .map_err(|_| "its source text is not available".to_string())?;
    let printed = format!("#[{}]", text.trim());
    match crate::marks::tool_attr_of_printed(&printed) {
        Some(("stack_leaf", args)) => crate::marks::parse_stack_leaf(args),
        _ => Err(format!("cannot read `{}`", text.trim())),
    }
}

/// The crate's `fip::stack_leaf` declarations (malformed ones are reported by the
/// attribute validation of a check, and skipped here with an error).
#[allow(
    deprecated,
    reason = "tool attributes are unparsed; `find_attr!` covers parsed ones only"
)]
fn crate_stack_leaves(tcx: TyCtxt<'_>) -> Vec<StackLeaves> {
    let mut v = Vec::new();
    for a in tcx.hir_krate_attrs() {
        let rustc_hir::Attribute::Unparsed(item) = a else {
            continue;
        };
        let segs: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
        if segs != ["fip", "stack_leaf"] {
            continue;
        }
        match stack_leaf_of(tcx, item.span) {
            Ok(l) => v.push(l),
            Err(e) => {
                tcx.dcx()
                    .err(format!("fip-prelint: malformed `fip::stack_leaf`: {e}"));
            }
        }
    }
    v
}

/// `true` if `def_id` carries `fip::mark` (a root, in this crate or a dependency).
#[allow(
    deprecated,
    reason = "tool attributes are unparsed; `find_attr!` covers parsed ones only"
)]
fn is_marked(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
    tcx.get_all_attrs(def_id).iter().any(|a| match a {
        rustc_hir::Attribute::Unparsed(item) => {
            let segs: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
            segs == ["fip", "mark"]
        }
        _ => false,
    })
}

/// The key of a generic root, equal in every crate that names it.
fn root_key(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> String {
    let (a, b) = tcx.def_path_hash(def_id).0.split();
    format!("{a:016x}{b:016x}")
}

pub fn enabled() -> bool {
    std::env::var_os(STACK_ENV).is_some_and(|v| v == "1")
}

/// Why a mono item cannot be part of a bound (`None`: it can), and the diverging
/// standard-library functions it calls.
fn facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: Instance<'tcx>,
    div: &mut Vec<String>,
    ext: &mut Vec<(String, String)>,
) -> Option<String> {
    let env = TypingEnv::fully_monomorphized();
    let body = tcx.instance_mir(inst.def);
    // A local of unsized type (`unsized_fn_params`, `unsized_locals`) is a dynamic
    // stack allocation, which a frame size does not cover.
    for decl in body.local_decls.iter() {
        let t = inst.instantiate_mir_and_normalize_erasing_regions(
            tcx,
            env,
            EarlyBinder::bind(tcx, decl.ty),
        );
        if !t.is_sized(tcx, env) {
            return Some(format!(
                "a local of unsized type `{t}` (a dynamic stack allocation)"
            ));
        }
    }
    for data in body.basic_blocks.iter() {
        let Some(term) = &data.terminator else {
            continue;
        };
        match &term.kind {
            TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                let Operand::Constant(c) = func else {
                    return Some("a call through a function pointer".to_string());
                };
                let fty = inst.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    env,
                    EarlyBinder::bind(tcx, c.const_.ty()),
                );
                let ty::FnDef(def_id, args) = *fty.kind() else {
                    return Some(format!("a call through a value of type `{fty}`"));
                };
                let Some(args) = args.no_bound_vars() else {
                    return Some(format!(
                        "a call of `{}` with bound variables",
                        tcx.def_path_str(def_id)
                    ));
                };
                match Instance::try_resolve(tcx, env, def_id, args) {
                    Ok(Some(callee)) => match callee.def {
                        InstanceKind::Virtual(..) => {
                            return Some(format!(
                                "a dynamic call to `{}` (trait object)",
                                tcx.def_path_str(def_id)
                            ));
                        }
                        InstanceKind::Intrinsic(_) => {}
                        _ => {
                            ext.push((
                                tcx.symbol_name(callee).name.to_string(),
                                with_no_trimmed_paths!(callee.to_string()),
                            ));
                            let krate = tcx.crate_name(def_id.krate);
                            if is_std_crate(krate.as_str())
                                && matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
                                && tcx
                                    .fn_sig(def_id)
                                    .skip_binder()
                                    .skip_binder()
                                    .output()
                                    .is_never()
                            {
                                div.push(tcx.symbol_name(callee).name.to_string());
                            }
                        }
                    },
                    _ => {
                        return Some(format!(
                            "a call of `{}` that does not resolve",
                            tcx.def_path_str_with_args(def_id, args)
                        ));
                    }
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let pty = place.ty(&body.local_decls, tcx).ty;
                let pty = inst.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    env,
                    EarlyBinder::bind(tcx, pty),
                );
                if matches!(pty.kind(), ty::Dynamic(..)) {
                    return Some(format!("a drop of `{pty}` (trait object)"));
                }
            }
            TerminatorKind::InlineAsm { .. } => {
                return Some("inline assembly".to_string());
            }
            _ => {}
        }
    }
    None
}

/// Writes `<rlib>.fip-stack` for the crate being compiled (see the module
/// documentation). `roots`: the crate's roots (empty for an exported dependency).
pub fn record(tcx: TyCtxt<'_>, roots: &[(rustc_hir::def_id::DefId, Mark)]) {
    let types = tcx.crate_types();
    let exe = !types.contains(&CrateType::Rlib);
    if exe && !types.contains(&CrateType::Executable) {
        return;
    }
    let outputs = tcx.output_filenames(());
    let rlib = rustc_session::output::out_filename(
        tcx.sess,
        if exe {
            CrateType::Executable
        } else {
            CrateType::Rlib
        },
        outputs,
        tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE),
    );
    let rlib = rlib.as_path().to_path_buf();
    // An executable's roots are its library's; it contributes functions and
    // instances.
    let roots = if exe { &[][..] } else { roots };
    let mut text = String::new();
    let _ = writeln!(text, "fip-prelint stack {FORMAT}");
    let _ = writeln!(
        text,
        "crate\t{}",
        tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE)
    );
    let _ = writeln!(text, "target\t{}", tcx.sess.opts.target_triple.tuple());
    let opt = match format!("{:?}", tcx.sess.opts.optimize).as_str() {
        "No" => "0".to_string(),
        "Less" => "1".to_string(),
        "More" => "2".to_string(),
        "Aggressive" => "3".to_string(),
        "Size" => "s".to_string(),
        "SizeMin" => "z".to_string(),
        other => other.to_string(),
    };
    let _ = writeln!(text, "opt-level\t{opt}");
    let _ = writeln!(text, "rlib\t{}", rlib.display());
    if exe {
        let dir = rlib.parent().unwrap_or(std::path::Path::new("."));
        let stem = rlib
            .file_stem()
            .map_or_else(String::new, |s| s.to_string_lossy().into_owned());
        let _ = writeln!(text, "objs\t{}\t{stem}", dir.display());
    }
    for l in if exe {
        Vec::new()
    } else {
        crate_stack_leaves(tcx)
    } {
        for (sym, bytes) in &l.leaves {
            let _ = writeln!(
                text,
                "leaf\t{sym}\t{bytes}\t{}",
                l.evidence.replace(['\t', '\n'], " ")
            );
        }
    }
    for (def_id, _) in roots {
        let label = with_no_trimmed_paths!(tcx.def_path_str(*def_id));
        if tcx.generics_of(*def_id).requires_monomorphization(tcx) {
            let _ = writeln!(
                text,
                "root\t{label}\t-\tgeneric: no instance of it in this build (a generic root is bounded per instance the build codegens)"
            );
            let _ = writeln!(text, "generic\t{label}\t{}", root_key(tcx, *def_id));
        } else {
            let inst = Instance::mono(tcx, *def_id);
            let _ = writeln!(text, "root\t{label}\t{}", tcx.symbol_name(inst).name);
        }
    }
    let parts = tcx.collect_and_partition_mono_items(());
    // Diverging standard-library lang items: the panic functions codegen calls for
    // `Assert` terminators (bounds and overflow checks), unwinding and UB checks.
    let mut div = Vec::new();
    for (_, def_id) in tcx.lang_items().iter() {
        if is_std_crate(tcx.crate_name(def_id.krate).as_str())
            && matches!(tcx.def_kind(def_id), DefKind::Fn)
            && !tcx.generics_of(def_id).requires_monomorphization(tcx)
            && tcx
                .fn_sig(def_id)
                .skip_binder()
                .skip_binder()
                .output()
                .is_never()
        {
            div.push(
                tcx.symbol_name(Instance::mono(tcx, def_id))
                    .name
                    .to_string(),
            );
        }
    }
    let mut ext = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for cgu in parts.codegen_units {
        for item in cgu.items().keys() {
            let MonoItem::Fn(inst) = item else {
                continue;
            };
            let sym = tcx.symbol_name(*inst).name.to_string();
            let label = with_no_trimmed_paths!(inst.to_string()).replace('\t', " ");
            if !seen.insert(sym.clone()) {
                continue;
            }
            if let InstanceKind::Item(def_id) = inst.def
                && tcx.generics_of(def_id).requires_monomorphization(tcx)
                && is_marked(tcx, def_id)
            {
                let _ = writeln!(text, "inst\t{}\t{label}\t{sym}", root_key(tcx, def_id));
            }
            // A body rustc cannot build is unknown, never an abort.
            let hook = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));
            let found = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut d = Vec::new();
                let mut e = Vec::new();
                let f = facts(tcx, *inst, &mut d, &mut e);
                (f, d, e)
            }));
            std::panic::set_hook(hook);
            let found = match found {
                Ok((f, d, e)) => {
                    div.extend(d);
                    ext.extend(e);
                    f
                }
                Err(_) => {
                    Some("its MIR cannot be built (internal compiler error caught)".to_string())
                }
            };
            match found {
                None => {
                    let _ = writeln!(text, "fn\t{sym}\t{label}");
                }
                Some(why) => {
                    let _ = writeln!(text, "fn\t{sym}\t{label}\t{why}");
                }
            }
        }
    }
    div.sort();
    div.dedup();
    for d in div {
        let _ = writeln!(text, "div\t{d}");
    }
    // Labels of the functions called but not codegened here (for messages).
    ext.sort();
    ext.dedup();
    for (sym, label) in ext {
        if !seen.contains(&sym) {
            let _ = writeln!(text, "ext\t{sym}\t{}", label.replace('\t', " "));
        }
    }
    let mut path = rlib.into_os_string();
    path.push(".fip-stack");
    if let Err(e) = std::fs::write(&path, text) {
        tcx.dcx().err(format!(
            "fip-prelint: cannot write {}: {e}",
            std::path::Path::new(&path).display()
        ));
    }
}
