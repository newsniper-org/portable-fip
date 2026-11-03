// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # `fip-prelint` — the rustc driver
//!
//! Used as `RUSTC_WRAPPER` (by `cargo fip-prelint`): `argv[1]` is the real `rustc`.
//! Per crate the driver picks a [`Role`]: workspace members are compiled by the driver
//! itself and analysed; dependencies whose source declares `fip::export` are compiled
//! by the driver without roots (only their implementations of trait methods with a
//! contract are checked); every other crate is handed to the real `rustc`
//! unchanged. The driver is that compiler (same version, same sysroot) plus an
//! analysis after type checking. For every crate it compiles itself it adds `-Zalways-encode-mir -Copt-level=0 --cfg fip_prelint` and registers the tool
//! `fip` (decision record `docs/decisions/2026-11-01-fip-prelint.md`, item 4). Since
//! `-Copt-level=0` alone would switch debug assertions and overflow checks on, it also
//! passes `-Cdebug-assertions=..` and `-Coverflow-checks=..` with the values the
//! profile's own arguments imply ([`profile_checks`]), so the analysed MIR has exactly
//! the checks of the build (top plan T14.1).
//!
//! Environment:
//! - `FIP_PRELINT_SYSROOT`: sysroot to compile against (default: the sysroot of the
//!   compiler that built the driver);
//! - `FIP_PRELINT_WARN_ONLY=1`: report violations as warnings, so that dependants are
//!   still compiled and checked (used for whole-workspace surveys);
//! - `FIP_PRELINT_DUMP=1`: print every root's explored call graph to stderr, and every
//!   checked call site of a callee with `param(..)` with the argument's bound;
//! - `FIP_PRELINT_DUMP_MIR=<text>`: print the MIR of every body the value analysis
//!   reads whose path contains `<text>` (a debugging aid);
//! - `FIP_PRELINT_STD_SUMMARIES=<file>`: the std summaries to use (default: the file
//!   for this compiler and target in `tools/fip-prelint/std-summaries/`);
//! - `FIP_PRELINT_STD_SUMMARIES_OUT=<file>` (set by `cargo fip-prelint
//!   --std-summaries`): generation mode. Crates of a `-Zbuild-std` build are compiled
//!   by the driver with `-Zalways-encode-mir` and the release settings of the shipped
//!   `std`; the workspace member (the seed crate) is not checked, its roots seed the
//!   summaries written to `<file>` ([`stdsum`]);
//! - `FIP_PRELINT_STACK=1` (set by `cargo fip-prelint --stack`, a `cargo build`):
//!   stack mode. Crates the driver compiles get `-Zemit-stack-sizes
//!   -Zshare-generics=no` and keep the profile's opt-level; instead of verdicts, each
//!   records its roots and codegened functions next to its rlib ([`stack`]).

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_public;
extern crate rustc_session;
extern crate rustc_span;

mod analysis;
mod export;
mod marks;
mod report;
mod stack;
mod stdsum;
mod value;

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
    role: Role,
}

/// Environment variables that change the driver's output; recorded in the dep-info
/// so that cargo re-checks a crate (instead of replaying cached diagnostics) when
/// they change. `FIP_PRELINT_DRIVER_ID` is set by `cargo fip-prelint` from the
/// driver binary (size and modification time), `FIP_PRELINT_INPUTS_ID` from the
/// content of the std summaries files (a sidecar-only change re-checks the crate even
/// when its modification time is unchanged), `FIP_PRELINT_SYSROOT` names the standard
/// library the analysis reads.
const TRACKED_ENV: &[&str] = &[
    "FIP_PRELINT_WARN_ONLY",
    "FIP_PRELINT_INPUTS_ID",
    "FIP_PRELINT_SYSROOT",
    "FIP_PRELINT_DUMP",
    "FIP_PRELINT_DUMP_MIR",
    "FIP_PRELINT_DRIVER_ID",
    "FIP_PRELINT_STD_SUMMARIES",
    "FIP_PRELINT_STD_SUMMARIES_OUT",
    "FIP_MACROS_MARK_ONLY",
    "FIP_PRELINT_STACK",
];

/// Added in stack mode (`cargo fip-prelint --stack`, [`stack`]):
/// frame sizes, every generic instance codegened in the crate that uses it, and every
/// function with a symbol of its own (no function kept only for cross-crate inlining,
/// top plan T8d). The report states them.
const STACK_FLAGS: &[&str] = &[
    "-Zemit-stack-sizes",
    "-Zshare-generics=no",
    "-Zcross-crate-inline-threshold=never",
];

/// Generation mode of the std summaries (see the module documentation).
pub const GENERATE_ENV: &str = "FIP_PRELINT_STD_SUMMARIES_OUT";

/// Release settings of the shipped `std` (rustc's `dist` profile), applied to the
/// standard library crates of a `-Zbuild-std` build in generation mode; later `-C`
/// options override cargo's profile.
const STD_RELEASE_FLAGS: &[&str] = &[
    "-Zalways-encode-mir",
    "-Copt-level=3",
    "-Cdebug-assertions=off",
    "-Coverflow-checks=off",
    "-Cdebuginfo=0",
];

impl Callbacks for Prelint {
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut deps = tcx.sess.env_depinfo.borrow_mut();
        for var in TRACKED_ENV {
            let value = std::env::var(var).ok().map(|v| Symbol::intern(&v));
            deps.insert((Symbol::intern(var), value));
        }
        // A regenerated std summaries file re-checks the crate.
        if self.role == Role::Primary {
            let target = tcx.sess.opts.target_triple.tuple().to_string();
            let path = analysis::std_summaries_path(&target);
            if path.is_file() {
                tcx.sess
                    .file_depinfo
                    .borrow_mut()
                    .insert(Symbol::intern(&path.to_string_lossy()));
            }
        }
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let check = match self.role {
            Role::Primary if stack::enabled() => report::stack_record,
            Role::ExportedDependency | Role::StdBuild if stack::enabled() => {
                report::stack_record_dependency
            }
            Role::Primary if std::env::var_os(GENERATE_ENV).is_some() => report::generate,
            Role::Primary => report::check_crate,
            // An exported dependency's implementations of trait methods with a
            // contract are checked where they are compiled (limits plan L4).
            Role::ExportedDependency => report::check_dependency,
            Role::PassThrough | Role::StdBuild => return Compilation::Continue,
        };
        let run = rustc_public::rustc_internal::run(tcx, || check(tcx));
        if run.is_err() {
            tcx.dcx()
                .err("fip-prelint: internal error: rustc_public context failed");
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

pub(crate) fn sysroot(real_rustc: Option<&str>) -> String {
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
    /// and marks are encoded for downstream crates; no roots, no verdicts, except that
    /// its implementations of trait methods with a contract are checked.
    ExportedDependency,
    /// Any other crate (other dependencies, version probes): the real rustc, unchanged.
    PassThrough,
    /// A standard library crate of a `-Zbuild-std` build (`-Z
    /// force-unstable-if-unmarked`). Generation mode: compiled with its MIR encoded
    /// and the release settings of the shipped `std`; no analysis. Stack mode
    /// (`--stack --build-std`, top plan T8c): compiled with the profile's settings and
    /// the stack flags, its codegened functions recorded.
    StdBuild,
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

fn role(args: &[String]) -> Role {
    if !args.iter().any(|a| a == "--crate-name") {
        return Role::PassThrough;
    }
    if (std::env::var_os(GENERATE_ENV).is_some() || stack::enabled())
        && args
            .iter()
            .any(|a| a.ends_with("force-unstable-if-unmarked"))
    {
        return Role::StdBuild;
    }
    if std::env::var_os("CARGO_PRIMARY_PACKAGE").is_some() {
        return Role::Primary;
    }
    match crate_root(args) {
        Some(root) if export::declares_export(Path::new(root), args) => Role::ExportedDependency,
        _ => Role::PassThrough,
    }
}

/// Debug assertions and overflow checks of the build as cargo's arguments ask for
/// them: the last explicit `-C debug-assertions` / `-C overflow-checks`, else rustc's
/// defaults (debug assertions on exactly at opt-level 0, overflow checks as debug
/// assertions). The driver replaces the opt-level with `-Copt-level=0` and passes
/// both values explicitly, so that the analysed MIR keeps the profile's semantics.
fn profile_checks(args: &[String]) -> (bool, bool) {
    fn flag(v: Option<&str>) -> Option<bool> {
        match v {
            None | Some("y" | "yes" | "on" | "true") => Some(true),
            Some("n" | "no" | "off" | "false") => Some(false),
            Some(_) => None,
        }
    }
    let mut opt_zero = true;
    let mut debug_assertions = None;
    let mut overflow_checks = None;
    let mut it = args.iter().skip(1);
    while let Some(a) = it.next() {
        let cg = if a == "-C" || a == "--codegen" {
            match it.next() {
                Some(v) => v.as_str(),
                None => break,
            }
        } else if let Some(v) = a.strip_prefix("--codegen=") {
            v
        } else if let Some(v) = a.strip_prefix("-C") {
            v
        } else {
            if a == "-O" {
                opt_zero = false;
            }
            continue;
        };
        let (key, value) = match cg.split_once('=') {
            Some((k, v)) => (k, Some(v)),
            None => (cg, None),
        };
        match key {
            "opt-level" => opt_zero = value == Some("0"),
            "debug-assertions" => {
                if let Some(b) = flag(value) {
                    debug_assertions = Some(b);
                }
            }
            "overflow-checks" => {
                if let Some(b) = flag(value) {
                    overflow_checks = Some(b);
                }
            }
            _ => {}
        }
    }
    let debug_assertions = debug_assertions.unwrap_or(opt_zero);
    (
        debug_assertions,
        overflow_checks.unwrap_or(debug_assertions),
    )
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
    let stack = stack::enabled();
    if role == Role::StdBuild && !stack {
        args.extend(STD_RELEASE_FLAGS.iter().map(|f| (*f).to_string()));
    }
    if stack
        && matches!(
            role,
            Role::Primary | Role::ExportedDependency | Role::StdBuild
        )
    {
        // Frame sizes of the build as profiled (no `-Copt-level=0` below), every
        // generic instance codegened in the crate that uses it.
        for f in STACK_FLAGS {
            if !args.iter().any(|a| a == f) {
                args.push((*f).to_string());
            }
        }
        // An executable (a bin, a test): keep its objects, whose relocations the
        // call graph is read from (top plan T8f).
        let exe = args.iter().any(|a| a == "--test")
            || args
                .windows(2)
                .any(|w| w[0] == "--crate-type" && w[1] == "bin");
        if role == Role::Primary && exe && !args.iter().any(|a| a == "-Csave-temps") {
            args.push("-Csave-temps".to_string());
        }
    }
    let compiles = matches!(role, Role::Primary | Role::ExportedDependency);
    if compiles && !stack {
        // Read before the driver's flags are appended; ours come last and win.
        let (debug_assertions, overflow_checks) = profile_checks(&args);
        let on_off = |b: bool| if b { "on" } else { "off" };
        args.push("-Copt-level=0".to_string());
        args.push(format!("-Cdebug-assertions={}", on_off(debug_assertions)));
        args.push(format!("-Coverflow-checks={}", on_off(overflow_checks)));
    }
    if compiles {
        // Skip flags already present (e.g. from RUSTFLAGS): a repeated
        // `register_tool(fip)` is an error.
        let mut i = 0;
        while i < CRATE_FLAGS.len() {
            let f = CRATE_FLAGS[i];
            if f == "-Copt-level=0" {
                // Added above with the profile's checks; stack mode keeps the
                // profile's opt-level.
                i += 1;
                continue;
            }
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
        rustc_driver::run_compiler(&args, &mut Prelint { role });
    })
}

#[cfg(test)]
mod tests {
    use super::profile_checks;

    fn args(a: &[&str]) -> Vec<String> {
        std::iter::once("rustc")
            .chain(a.iter().copied())
            .map(str::to_string)
            .collect()
    }

    #[test]
    fn profile_defaults_follow_the_opt_level() {
        assert_eq!(profile_checks(&args(&["--crate-name", "c"])), (true, true));
        assert_eq!(
            profile_checks(&args(&["-C", "opt-level=3"])),
            (false, false)
        );
        assert_eq!(profile_checks(&args(&["-Copt-level=s"])), (false, false));
        assert_eq!(profile_checks(&args(&["-O"])), (false, false));
        assert_eq!(
            profile_checks(&args(&["-C", "opt-level=3", "-C", "opt-level=0"])),
            (true, true)
        );
    }

    #[test]
    fn explicit_flags_win() {
        assert_eq!(
            profile_checks(&args(&["-C", "opt-level=3", "-C", "overflow-checks=on"])),
            (false, true)
        );
        assert_eq!(
            profile_checks(&args(&["-C", "debug-assertions=off"])),
            (false, false)
        );
        assert_eq!(
            profile_checks(&args(&["-C", "debug-assertions=off", "-Coverflow-checks"])),
            (false, true)
        );
        assert_eq!(
            profile_checks(&args(&[
                "--codegen=opt-level=2",
                "--codegen",
                "debug-assertions=yes"
            ])),
            (true, true)
        );
    }
}
