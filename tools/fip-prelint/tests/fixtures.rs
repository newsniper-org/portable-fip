// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Runs `cargo fip-prelint --message-format short` on every workspace under
//! `tests/fixtures/` and compares its diagnostics with `expected.txt` there (or
//! `expected-<variant>.txt` for a run with extra environment variables).
//!
//! Compared: every line mentioning `fip-prelint` and every rustc error code line
//! (`error[E..]`), sorted and deduplicated (cargo checks `lib` and `lib test`), plus
//! the exit status (`exit: success` / `exit: failure`, first line). Lines starting with
//! `#` in `expected.txt` are comments. `FIP_PRELINT_BLESS=1` rewrites the files.

use std::path::{Path, PathBuf};
use std::process::Command;

fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}

fn run(name: &str, variant: &str, envs: &[(&str, std::ffi::OsString)]) -> Vec<String> {
    let dir = fixtures_dir().join(name);
    let target = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("fixtures")
        .join(format!("{name}{variant}"));
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-fip-prelint"));
    cmd.args(["fip-prelint", "--message-format", "short"])
        .current_dir(&dir)
        .env("FIP_PRELINT_TARGET_DIR", &target)
        .env("FIP_PRELINT_DRIVER_PATH", env!("CARGO_BIN_EXE_fip-prelint"))
        .env_remove("FIP_PRELINT_WARN_ONLY")
        .env_remove("FIP_PRELINT_DUMP")
        .env_remove("FIP_PRELINT_DUMP_MIR")
        .env_remove("FIP_PRELINT_STD_SUMMARIES")
        .env_remove("FIP_PRELINT_STD_SUMMARIES_OUT")
        .env_remove("CARGO_TARGET_DIR");
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("run cargo-fip-prelint");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let mut lines: Vec<String> = stderr
        .lines()
        .filter(|l| l.contains("fip-prelint") || l.contains("error[E"))
        .filter(|l| {
            !l.trim_start().starts_with("Checking") && !l.trim_start().starts_with("Compiling")
        })
        .map(|l| l.trim_end().to_string())
        .collect();
    lines.sort();
    lines.dedup();
    let status = if out.status.success() {
        "exit: success"
    } else {
        "exit: failure"
    };
    let mut v = vec![status.to_string()];
    v.extend(lines);
    v
}

fn check(name: &str) {
    check_with(name, "", &[]);
}

/// `check` with extra environment variables, compared with `expected{variant}.txt`.
fn check_with(name: &str, variant: &str, envs: &[(&str, std::ffi::OsString)]) {
    let got = run(name, variant, envs);
    let path = fixtures_dir()
        .join(name)
        .join(format!("expected{variant}.txt"));
    if std::env::var("FIP_PRELINT_BLESS").is_ok_and(|v| v == "1") {
        let mut text = String::from(
            "# Expected `cargo fip-prelint --message-format short` diagnostics (tests/fixtures.rs).\n",
        );
        for l in &got {
            text.push_str(l);
            text.push('\n');
        }
        std::fs::write(&path, text).expect("write the expected file");
        return;
    }
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: {e} (run with FIP_PRELINT_BLESS=1)", path.display()));
    let want: Vec<String> = text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| l.trim_end().to_string())
        .collect();
    if got != want {
        let missing: Vec<&String> = want.iter().filter(|l| !got.contains(l)).collect();
        let extra: Vec<&String> = got.iter().filter(|l| !want.contains(l)).collect();
        panic!(
            "fixture `{name}` differs from expected{variant}.txt\nmissing:\n{}\nunexpected:\n{}",
            missing
                .iter()
                .map(|s| format!("  {s}"))
                .collect::<Vec<_>>()
                .join("\n"),
            extra
                .iter()
                .map(|s| format!("  {s}"))
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
}

/// `Box::new` directly, through an exported callee, through a non-exported one (`⊤`),
/// through a `use` alias.
#[test]
fn cross_crate() {
    check("cross_crate");
}

/// Implicit `Drop` (accepted by the token-level `#[fip]`), an allocating `Add` used
/// via `+`, indexing panics under `panic_macros = false`, method resolution.
#[test]
fn implicit() {
    check("implicit");
}

/// Bounds, overflow and division checks behind guards (value analysis): guarded
/// index, `while i < xs.len()` and `for i in 0..xs.len()` loops, a second counter
/// bounded by the first, `x - 1` after `x == 0` returns, `d != 0` division pass;
/// unguarded, off-by-one, guards on another variable, a local changed through
/// `&mut`, a replaced slice, `0..=len`, signed `i - 1` under `i < 0` are reported.
/// Values returned by calls (return summaries): `usize::from(u8)`, a wrapper's
/// `len`/`get`/`is_empty` over a `Vec` field, `len() - 1` after `is_empty()`,
/// `count_ones` (intrinsic table) pass; `usize::from(u16)`, a `Cell`-backed `len`, a
/// replaced reference, a `&mut` wrapper changed in between are reported. Iterator
/// contracts: `(0..len).rev()`, `0..=len - 1` after `is_empty`, `enumerate` indexing
/// a longer slice, a counter of `zip`'s items pass; off-by-one controls of each are
/// reported.
#[test]
fn guards() {
    check("guards");
}

/// Generic instantiation, closure arguments, higher-order roots, `fip(N)` bounds and
/// the loop rule, recursion through two functions; drops of generic values through
/// their glue (`Vec<T>`, `Box<T>` may free; `Option<T>`, `T` are the term `drop(T)`;
/// a glue rustc cannot build for the generic type is `⊤`, without aborting).
#[test]
fn generics() {
    check("generics");
}

/// `fip::exprot`, `fip::mrak` and a malformed mark are rejected.
#[test]
fn bad_attr() {
    check("bad_attr");
}

/// Defence in depth: a dependency whose `fip::export` is active (injected by RUSTFLAGS)
/// although it was compiled without `-Zalways-encode-mir`: a hard error naming the
/// crate, and the call is unresolved, never 0.
#[test]
fn export_unencoded() {
    check("export_unencoded");
}

/// Path dependencies that are not workspace members, as other projects consume
/// portable-fip: the one declaring `fip::export` is compiled with the driver's flags
/// and analysed (allocation found, allocation-free callee passes); the other is ⊤.
#[test]
fn nonmember_export() {
    check("nonmember_export");
}

/// Declared parameter bounds at call sites (`param(g = K)`): the reproducer of
/// `TODOs/fip-prelint.md` (a non-root caller, a `#[fip]` and a `#[fip(1)]` root passing
/// an allocating `fip_fn!` for `param(g = 0)`), and the argument kinds: allocation-free
/// and allocating closures, a named function, a function pointer (`⊤`), a generic
/// forwarder instantiated from a root, a root's own `param(h = K)` forwarded, a call
/// inside a closure. Function pointers and `&dyn Fn` with a declared bound (limits plan
/// L4): the call through the parameter costs `K`; a function reified or a closure
/// unsized at the call site is checked (passes or is reported), a pointer loaded from
/// data or an undeclared parameter is `⊤` at the call site, a declared one passed on is
/// checked against its own bound; an argument that frees or recurses under a `fip`
/// callee is reported, and a `fip` root calling an `fbip` callee inherits the frees and
/// recursion `fbip` allows its argument.
#[test]
fn param_bounds() {
    check("param_bounds");
}

/// Allocation and free sources (limits plan L7), from the allocator probe: marked
/// arena and slab in an exported crate (one allocation, `∞` in a loop, a free,
/// `alloc_source(n = 2)`, `fbip`), the unmarked arena as the pinned residue (passes),
/// a source whose body loops, recurses and allocates (counts 1, nothing from its body),
/// a source declared on a trait method (an implementation and a generic call),
/// `GlobalAlloc` methods called directly, by default body and through `dyn`, the
/// system allocator, foreign `malloc`/`free`, a marked foreign function, an unknown
/// one (`⊤`), a Rust function named `malloc`; rejected: a FIP mark on a source or on
/// a `GlobalAlloc` method, `n = 0`, unknown keys, a misplaced source mark.
#[test]
fn alloc_sources() {
    check("alloc_sources");
}

/// Declared preconditions and callee contexts (limits plan L1): `fip::requires`
/// established by guards or constants passes, a root is checked under its own; a
/// call site that does not establish it, a function with a precondition used as a
/// value, `split_at_mut` without `j < len`, and a callee whose context is too weak
/// are reported; an allocation hidden behind a broken precondition is counted;
/// malformed and unsatisfiable preconditions are errors.
#[test]
fn preconditions() {
    check("preconditions");
}

/// Drops are frees only when their drop glue deallocates (limits plan L12): `Cell`,
/// a `RefMut` store and a user guard pass; dropping an `Rc` may free.
#[test]
fn cells() {
    check("cells");
}

/// Function pointers and trait objects (limits plan L4): resolved from one origin on
/// every path of the body (a reified function or closure, an unsized concrete type),
/// `⊤` for two origins, data or an unknown receiver; contracts on trait methods: a
/// dynamic call costs the contract (`n`, panic paths of a non-strict contract), every
/// implementation is checked in its crate (a default body for each impl keeping it),
/// one in a crate without `fip::export` is `⊤`, `param(..)` in a contract is
/// rejected.
#[test]
fn indirect() {
    check("indirect");
}

/// A dependency declaring `fip::export` (not a workspace member, compiled without
/// roots) whose implementation breaks a trait method's contract: rejected where it
/// is compiled (limits plan L4).
#[test]
fn contract_dep() {
    check("contract_dep");
}

/// Generated std summaries (limits plan L6, sidecar of L10e): `write!` into a fixed
/// buffer through a local `fmt::Write` impl (integers, strings, a user `Display`
/// writing through the `Formatter`) passes; `format!` is a violation (allocations,
/// a free) without `⊤`; `{:?}` of a derived `Debug` (`&dyn Debug` inside `core`) stays
/// `⊤`; under `strict = true` the bounds checks inside `core`'s integer formatting
/// are panic paths.
#[test]
fn std_summaries() {
    check("std_summaries");
}

/// The same crate with a std summaries file stamped for another compiler: not used,
/// every function without MIR stays `⊤` (never a silent pass).
#[test]
fn std_summaries_stale() {
    let stale = fixtures_dir()
        .join("std_summaries")
        .join("stale-summaries.txt");
    check_with(
        "std_summaries",
        "-stale",
        &[("FIP_PRELINT_STD_SUMMARIES", stale.into_os_string())],
    );
}

/// Negative control: marks from `fip-macros`, every root passes, exit status 0.
#[test]
fn clean() {
    check("clean");
}
