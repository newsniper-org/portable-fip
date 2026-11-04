// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The rejected behaviour examples of `fip-macros` through the driver (limits plan
//! L10d).
//!
//! Every ```` ```compile_fail ```` example in `crates/fip-macros/src/lib.rs` with a
//! hidden line `# // prelint: <text>` is a behaviour case (an allocation, a free,
//! recursion, a loop bound, a panic). The test extracts them into a generated
//! workspace, one crate per example, and runs `cargo fip-prelint` on it with
//! `FIP_MACROS_MARK_ONLY=1`: `#[fip]`/`#[fbip]` then emit only the mark and skip their
//! own token-level checks, so each example compiles and the driver alone decides.
//! Each must be rejected by the driver with an error containing `<text>` at its
//! crate, and must have no other compile error. The number of such examples is
//! pinned, so that dropping a marker is noticed.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Examples with a `# // prelint:` line (see the module documentation).
const EXAMPLES: usize = 19;

struct Example {
    index: usize,
    code: String,
    reason: String,
}

fn examples(src: &str) -> Vec<Example> {
    let mut out = Vec::new();
    let mut block: Option<Vec<String>> = None;
    let mut index = 0;
    for line in src.lines() {
        let Some(doc) = line.strip_prefix("//!") else {
            continue;
        };
        let doc = doc.strip_prefix(' ').unwrap_or(doc);
        match &mut block {
            None if doc == "```compile_fail" => block = Some(Vec::new()),
            None => {}
            Some(lines) if doc == "```" => {
                let lines = std::mem::take(lines);
                block = None;
                let mut reason = None;
                let mut code = String::new();
                for l in &lines {
                    if let Some(r) = l.strip_prefix("# // prelint: ") {
                        reason = Some(r.trim().to_string());
                    } else if l.starts_with("# // expect: ") {
                    } else if let Some(hidden) = l.strip_prefix("# ") {
                        code.push_str(hidden);
                        code.push('\n');
                    } else if l != "#" {
                        code.push_str(l);
                        code.push('\n');
                    }
                }
                if let Some(reason) = reason {
                    out.push(Example {
                        index,
                        code,
                        reason,
                    });
                }
                index += 1;
            }
            Some(lines) => lines.push(doc.to_string()),
        }
    }
    out
}

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().expect("parent")).expect("create a directory");
    std::fs::write(path, text).expect("write a generated file");
}

#[test]
fn behaviour_examples_rejected_by_the_driver() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo = manifest
        .join("../..")
        .canonicalize()
        .expect("repository root");
    let src = std::fs::read_to_string(repo.join("crates/fip-macros/src/lib.rs"))
        .expect("read fip-macros");
    let exs = examples(&src);
    assert_eq!(
        exs.len(),
        EXAMPLES,
        "number of `# // prelint:` examples in fip-macros changed"
    );

    let ws: PathBuf = Path::new(env!("CARGO_TARGET_TMPDIR")).join("compile_fail_ws");
    let _ = std::fs::remove_dir_all(&ws);
    let mut members = String::new();
    for e in &exs {
        let name = format!("ex{:02}", e.index);
        let _ = write!(members, "\"{name}\", ");
        write(
            &ws.join(&name).join("Cargo.toml"),
            &format!(
                "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n\
                 [lib]\npath = \"src/lib.rs\"\n\n[dependencies]\n\
                 fip-macros = {{ path = {:?} }}\nfip-strict = {{ path = {:?} }}\n\n\
                 [lints.rust]\nunexpected_cfgs = {{ level = \"allow\" }}\ndead_code = {{ level = \"allow\" }}\n",
                repo.join("crates/fip-macros"),
                repo.join("crates/fip-strict"),
            ),
        );
        write(&ws.join(&name).join("src/lib.rs"), &e.code);
    }
    write(
        &ws.join("Cargo.toml"),
        &format!("[workspace]\nresolver = \"3\"\nmembers = [{members}]\n"),
    );

    let out = Command::new(env!("CARGO_BIN_EXE_cargo-fip-prelint"))
        .args(["fip-prelint", "--message-format", "short"])
        .current_dir(&ws)
        .env("FIP_PRELINT_TARGET_DIR", ws.join("target"))
        .env("FIP_PRELINT_DRIVER_PATH", env!("CARGO_BIN_EXE_fip-prelint"))
        .env("FIP_MACROS_MARK_ONLY", "1")
        .env_remove("FIP_PRELINT_WARN_ONLY")
        .env_remove("FIP_PRELINT_DUMP")
        .env_remove("FIP_PRELINT_DUMP_MIR")
        .env_remove("CARGO_TARGET_DIR")
        .output()
        .expect("run cargo-fip-prelint");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let mut bad = Vec::new();
    for e in &exs {
        let name = format!("ex{:02}", e.index);
        let at = format!("{name}/src/lib.rs:");
        let lines: Vec<&str> = stderr
            .lines()
            .filter(|l| l.starts_with(&at) && (l.contains(": error:") || l.contains(": error[")))
            .collect();
        let ours = lines
            .iter()
            .any(|l| l.contains("error: fip-prelint:") && l.contains(&e.reason));
        let others: Vec<&&str> = lines
            .iter()
            .filter(|l| !l.contains("error: fip-prelint:"))
            .collect();
        let summary = stderr
            .lines()
            .any(|l| l.contains(&format!("note: fip-prelint: crate `{name}`:")));
        if !ours || !others.is_empty() || !summary {
            bad.push(format!(
                "example {} (`{}`): driver ran: {summary}, rejected for the reason: {ours}, other errors: {others:?}\n  {}",
                e.index,
                e.reason,
                lines.join("\n  ")
            ));
        }
    }
    assert!(
        bad.is_empty(),
        "{} of {} examples not rejected by the driver for their reason:\n{}\n\nfull output:\n{stderr}",
        bad.len(),
        exs.len(),
        bad.join("\n")
    );
}
