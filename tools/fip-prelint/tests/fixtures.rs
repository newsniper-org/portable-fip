// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Runs `cargo fip-prelint --message-format short` on every workspace under
//! `tests/fixtures/` and compares its diagnostics with `expected.txt` there.
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

fn run(name: &str) -> Vec<String> {
    let dir = fixtures_dir().join(name);
    let target = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("fixtures")
        .join(name);
    let out = Command::new(env!("CARGO_BIN_EXE_cargo-fip-prelint"))
        .args(["fip-prelint", "--message-format", "short"])
        .current_dir(&dir)
        .env("FIP_PRELINT_TARGET_DIR", &target)
        .env("FIP_PRELINT_DRIVER_PATH", env!("CARGO_BIN_EXE_fip-prelint"))
        .env_remove("FIP_PRELINT_WARN_ONLY")
        .env_remove("FIP_PRELINT_DUMP")
        .env_remove("FIP_PRELINT_DUMP_MIR")
        .env_remove("CARGO_TARGET_DIR")
        .output()
        .expect("run cargo-fip-prelint");
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
    let got = run(name);
    let path = fixtures_dir().join(name).join("expected.txt");
    if std::env::var("FIP_PRELINT_BLESS").is_ok_and(|v| v == "1") {
        let mut text = String::from(
            "# Expected `cargo fip-prelint --message-format short` diagnostics (tests/fixtures.rs).\n",
        );
        for l in &got {
            text.push_str(l);
            text.push('\n');
        }
        std::fs::write(&path, text).expect("write expected.txt");
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
            "fixture `{name}` differs from expected.txt\nmissing:\n{}\nunexpected:\n{}",
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
/// inside a closure.
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

/// Negative control: marks from `fip-macros`, every root passes, exit status 0.
#[test]
fn clean() {
    check("clean");
}
