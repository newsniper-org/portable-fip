// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Self-check: `cargo fip-prelint --warn-only` on the portable-fip workspace (all
//! targets, so `crates/*/tests` too). Compares the violations, `⊤` reports and
//! conditional results (not the panic-path notes, which follow every line shift)
//! and the per-crate summaries with `tests/selfcheck.expected`.
//! `FIP_PRELINT_BLESS=1` rewrites the file. Investigation of each reported line:
//! `TODOs/fip-prelint.md`.

use std::path::Path;
use std::process::Command;

#[test]
fn workspace_self_check() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = manifest.join("../..");
    let target = Path::new(env!("CARGO_TARGET_TMPDIR")).join("selfcheck");
    let out = Command::new(env!("CARGO_BIN_EXE_cargo-fip-prelint"))
        .args(["fip-prelint", "--warn-only", "--message-format", "short"])
        .current_dir(&root)
        .env("FIP_PRELINT_TARGET_DIR", &target)
        .env("FIP_PRELINT_DRIVER_PATH", env!("CARGO_BIN_EXE_fip-prelint"))
        .env_remove("FIP_PRELINT_DUMP")
        .env_remove("CARGO_TARGET_DIR")
        .output()
        .expect("run cargo-fip-prelint");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "self-check failed to build:\n{stderr}"
    );
    let mut got: Vec<String> = stderr
        .lines()
        .filter(|l| {
            l.contains("fip-prelint [error]:")
                || (l.contains("warning: fip-prelint:"))
                || l.contains("note: fip-prelint: crate `")
                || l.contains("error[E")
        })
        .map(|l| l.trim_end().to_string())
        .collect();
    got.sort();
    got.dedup();
    let path = manifest.join("tests").join("selfcheck.expected");
    if std::env::var("FIP_PRELINT_BLESS").is_ok_and(|v| v == "1") {
        let mut text = String::from(
            "# `cargo fip-prelint --warn-only` on the workspace (tests/selfcheck.rs); notes omitted.\n",
        );
        for l in &got {
            text.push_str(l);
            text.push('\n');
        }
        std::fs::write(&path, text).expect("write selfcheck.expected");
        return;
    }
    let text = std::fs::read_to_string(&path).expect("selfcheck.expected (FIP_PRELINT_BLESS=1)");
    let want: Vec<String> = text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| l.trim_end().to_string())
        .collect();
    let missing: Vec<&String> = want.iter().filter(|l| !got.contains(l)).collect();
    let extra: Vec<&String> = got.iter().filter(|l| !want.contains(l)).collect();
    assert!(
        missing.is_empty() && extra.is_empty(),
        "self-check differs from selfcheck.expected\nmissing:\n{missing:#?}\nunexpected:\n{extra:#?}"
    );
}
