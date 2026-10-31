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

/// Generic instantiation, closure arguments, higher-order roots, `fip(N)` bounds and
/// the loop rule, recursion through two functions.
#[test]
fn generics() {
    check("generics");
}

/// `fip::exprot`, `fip::mrak` and a malformed mark are rejected.
#[test]
fn bad_attr() {
    check("bad_attr");
}

/// A dependency that declares `fip::export` but was compiled without
/// `-Zalways-encode-mir` (a non-member, built by plain rustc): a hard error naming the
/// crate, and the call is unresolved, never 0.
#[test]
fn export_unencoded() {
    check("export_unencoded");
}

/// Negative control: marks from `fip-macros`, every root passes, exit status 0.
#[test]
fn clean() {
    check("clean");
}
