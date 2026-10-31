// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # `fip-prelint` — the rustc driver
//!
//! Used as `RUSTC_WORKSPACE_WRAPPER` (by `cargo fip-prelint`): `argv[1]` is the real
//! `rustc`, which is dropped; the driver is that compiler (same version, same
//! sysroot) plus an analysis after type checking. For every crate it compiles it
//! adds `-Zalways-encode-mir -Copt-level=0 --cfg fip_prelint` and registers the tool
//! `fip` (decision record `docs/decisions/2026-11-01-fip-prelint.md`, item 4).
//!
//! Environment:
//! - `FIP_PRELINT_SYSROOT`: sysroot to compile against (default: the sysroot of the
//!   compiler that built the driver);
//! - `FIP_PRELINT_WARN_ONLY=1`: report violations as warnings, so that dependants are
//!   still compiled and checked (used for whole-workspace surveys);
//! - `FIP_PRELINT_DUMP=1`: print every root's explored call graph to stderr.

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

fn main() -> std::process::ExitCode {
    let mut args: Vec<String> = std::env::args().collect();
    let mut real_rustc = None;
    if args.len() > 1 && is_rustc_path(&args[1]) {
        real_rustc = Some(args.remove(1));
    }
    if !args
        .iter()
        .any(|a| a == "--sysroot" || a.starts_with("--sysroot="))
    {
        args.push("--sysroot".to_string());
        args.push(sysroot(real_rustc.as_deref()));
    }
    // Version queries (`-vV`) and `--print` probes have no crate to analyse.
    let compiles = args.iter().any(|a| a == "--crate-name");
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
        rustc_driver::run_compiler(&args, &mut Prelint { analyse: compiles });
    })
}
