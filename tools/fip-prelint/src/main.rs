// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # `fip-prelint` — the rustc driver
//!
//! Used as `RUSTC_WRAPPER` (by `cargo fip-prelint`): `argv[1]` is the real `rustc`.
//! Per crate the driver picks a [`Role`]: workspace members are compiled by the driver
//! itself and analysed; dependencies whose source declares `fip::export` are compiled
//! by the driver without analysis; every other crate is handed to the real `rustc`
//! unchanged. The driver is that compiler (same version, same sysroot) plus an
//! analysis after type checking. For every crate it compiles itself it adds `-Zalways-encode-mir -Copt-level=0 --cfg fip_prelint` and registers the tool
//! `fip` (decision record `docs/decisions/2026-11-01-fip-prelint.md`, item 4).
//!
//! Environment:
//! - `FIP_PRELINT_SYSROOT`: sysroot to compile against (default: the sysroot of the
//!   compiler that built the driver);
//! - `FIP_PRELINT_WARN_ONLY=1`: report violations as warnings, so that dependants are
//!   still compiled and checked (used for whole-workspace surveys);
//! - `FIP_PRELINT_DUMP=1`: print every root's explored call graph to stderr, and every
//!   checked call site of a callee with `param(..)` with the argument's bound.

#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_span;

mod analysis;
mod marks;
mod report;

use std::path::Path;
use std::process::Command;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

/// Set in the driver's own process; `fip-macros` emits `fip::mark` only when it sees
/// it (plain builds stay free of the attribute and of `unexpected_cfgs` warnings).
const MARK_ENV: &str = "FIP_PRELINT_DRIVER";

/// Flags added to every crate the driver compiles (decision record, item 4).
const CRATE_FLAGS: &[&str] = &[
    "-Zalways-encode-mir",
    "-Copt-level=0",
    "--cfg",
    "fip_prelint",
    "--check-cfg",
    "cfg(fip_prelint)",
    "-Zcrate-attr=feature(register_tool)",
    "-Zcrate-attr=feature(custom_inner_attributes)",
    "-Zcrate-attr=register_tool(fip)",
    // `custom_inner_attributes` is used only by crates with `#![fip::export]`.
    "-Aunused_features",
];

struct Prelint {
    analyse: bool,
}

/// Environment variables that change the driver's output; recorded in the dep-info
/// so that cargo re-checks a crate (instead of replaying cached diagnostics) when
/// they change. `FIP_PRELINT_DRIVER_ID` is set by `cargo fip-prelint` from the
/// driver binary (size and modification time).
const TRACKED_ENV: &[&str] = &[
    "FIP_PRELINT_WARN_ONLY",
    "FIP_PRELINT_DUMP",
    "FIP_PRELINT_DRIVER_ID",
];

impl Callbacks for Prelint {
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut deps = tcx.sess.env_depinfo.borrow_mut();
        for var in TRACKED_ENV {
            let value = std::env::var(var).ok().map(|v| Symbol::intern(&v));
            deps.insert((Symbol::intern(var), value));
        }
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if self.analyse {
            let run = rustc_public::rustc_internal::run(tcx, || report::check_crate(tcx));
            if run.is_err() {
                tcx.dcx()
                    .err("fip-prelint: internal error: rustc_public context failed");
            }
        }
        Compilation::Continue
    }
}

fn is_rustc_path(arg: &str) -> bool {
    !arg.starts_with('-')
        && Path::new(arg)
            .file_stem()
            .is_some_and(|s| s == "rustc" || s.to_string_lossy().starts_with("rustc-"))
}

fn sysroot(real_rustc: Option<&str>) -> String {
    if let Ok(s) = std::env::var("FIP_PRELINT_SYSROOT")
        && !s.is_empty()
    {
        return s;
    }
    let built = env!("FIP_PRELINT_BUILD_SYSROOT");
    if Path::new(built).is_dir() {
        return built.to_string();
    }
    if let Some(rustc) = real_rustc
        && let Ok(out) = Command::new(rustc).args(["--print", "sysroot"]).output()
        && out.status.success()
    {
        return String::from_utf8_lossy(&out.stdout).trim().to_string();
    }
    built.to_string()
}

/// How the driver treats the crate being compiled.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Role {
    /// A package selected by the cargo invocation (`CARGO_PRIMARY_PACKAGE`, i.e. the
    /// workspace members under `--workspace`): driver flags, attribute validation and
    /// analysis.
    Primary,
    /// A dependency whose crate root declares `fip::export`: driver flags so its MIR
    /// and marks are encoded for downstream crates; no analysis, no verdicts.
    ExportedDependency,
    /// Any other crate (other dependencies, version probes): the real rustc, unchanged.
    PassThrough,
}

/// The crate root source file: the `.rs` argument that is not an option value.
fn crate_root(args: &[String]) -> Option<&str> {
    const TAKES_VALUE: &[&str] = &[
        "--crate-name",
        "--crate-type",
        "--edition",
        "--emit",
        "--out-dir",
        "-o",
        "-L",
        "--extern",
        "--cfg",
        "--check-cfg",
        "--cap-lints",
        "--target",
        "--error-format",
        "--json",
        "--sysroot",
        "-C",
        "-Z",
        "-A",
        "-W",
        "-D",
        "-F",
        "--remap-path-prefix",
        "--print",
        "--explain",
        "--diagnostic-width",
    ];
    let mut skip = false;
    let mut found = None;
    for a in args.iter().skip(1) {
        if skip {
            skip = false;
            continue;
        }
        if TAKES_VALUE.contains(&a.as_str()) {
            skip = true;
            continue;
        }
        if !a.starts_with('-') && Path::new(a).extension().is_some_and(|e| e == "rs") {
            found = Some(a.as_str());
        }
    }
    found
}

/// `true` if the crate root's inner attributes contain `fip::export`, either as
/// `#![cfg_attr(fip_prelint, fip::export)]` or as `#![fip::export]` (whitespace
/// ignored). Only the source text is available before compilation.
fn declares_export_in_source(root: &Path) -> bool {
    let Ok(text) = std::fs::read_to_string(root) else {
        return false;
    };
    let compact: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    compact.contains("#![cfg_attr(fip_prelint,fip::export)]") || compact.contains("#![fip::export]")
}

fn role(args: &[String]) -> Role {
    if !args.iter().any(|a| a == "--crate-name") {
        return Role::PassThrough;
    }
    if std::env::var_os("CARGO_PRIMARY_PACKAGE").is_some() {
        return Role::Primary;
    }
    match crate_root(args) {
        Some(root) if declares_export_in_source(Path::new(root)) => Role::ExportedDependency,
        _ => Role::PassThrough,
    }
}

fn main() -> std::process::ExitCode {
    let mut args: Vec<String> = std::env::args().collect();
    let mut real_rustc = None;
    if args.len() > 1 && is_rustc_path(&args[1]) {
        real_rustc = Some(args.remove(1));
    }
    let role = role(&args);
    if role == Role::PassThrough
        && let Some(rustc) = &real_rustc
    {
        // Unchanged compilation by the real rustc.
        return match Command::new(rustc).args(&args[1..]).status() {
            Ok(st) => {
                std::process::ExitCode::from(u8::try_from(st.code().unwrap_or(1)).unwrap_or(1))
            }
            Err(e) => {
                eprintln!("fip-prelint: cannot run {rustc}: {e}");
                std::process::ExitCode::from(1)
            }
        };
    }
    if !args
        .iter()
        .any(|a| a == "--sysroot" || a.starts_with("--sysroot="))
    {
        args.push("--sysroot".to_string());
        args.push(sysroot(real_rustc.as_deref()));
    }
    let compiles = role != Role::PassThrough;
    if compiles {
        // Skip flags already present (e.g. from RUSTFLAGS): a repeated
        // `register_tool(fip)` is an error.
        let mut i = 0;
        while i < CRATE_FLAGS.len() {
            let f = CRATE_FLAGS[i];
            let pair = matches!(f, "--cfg" | "--check-cfg");
            let present = if pair {
                args.windows(2)
                    .any(|w| w[0] == f && w[1] == CRATE_FLAGS[i + 1])
            } else {
                args.iter().any(|a| a == f)
            };
            if !present {
                args.push(f.to_string());
                if pair {
                    args.push(CRATE_FLAGS[i + 1].to_string());
                }
            }
            i += if pair { 2 } else { 1 };
        }
    }
    // SAFETY: single-threaded here, before the compiler starts any thread.
    unsafe { std::env::set_var(MARK_ENV, "1") };
    rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(
            &args,
            &mut Prelint {
                analyse: role == Role::Primary,
            },
        );
    })
}
