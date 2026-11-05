// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Self-check per installed target (limits plan L10b): `cargo fip-prelint
//! --warn-only --target <triple>` on the portable-fip workspace for every target whose
//! standard library is installed in the driver's toolchain, so `cfg(target_arch)` and
//! `cfg(target_os)` code (`fip-arch`) is analysed as each target compiles it.
//!
//! A target with `std` is checked like the host self-check (all targets of every
//! member); a target with only `core`/`alloc` (e.g. `x86_64-unknown-none`) checks the
//! `no_std` libraries (`fip-core`, `fip-alloc`, `fip-arch`, `fip-strict`, as `just
//! nostd` builds them). The violations, `⊤` reports, conditional results and per-crate
//! summaries (not the notes) are compared with the target's section in
//! `tests/targets.expected`. An installed target without a section fails (record it
//! with `FIP_PRELINT_BLESS=1`); a recorded target that is not installed is skipped
//! (a failure under `FIP_PRELINT_REQUIRE_TARGETS=1`, which `just ci` sets)
//! with a message.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

const NO_STD_PACKAGES: &[&str] = &["fip-core", "fip-alloc", "fip-arch", "fip-strict"];

fn toolchain() -> String {
    std::env::var("FIP_PRELINT_TOOLCHAIN")
        .unwrap_or_else(|_| env!("FIP_PRELINT_DEFAULT_TOOLCHAIN").to_string())
}

/// A test (or part) skipped for a missing target, tool or host: a failure under
/// `FIP_PRELINT_REQUIRE_TARGETS=1` (set by `just ci`), else a note on stderr (which
/// libtest hides for a passing test).
fn skipped(msg: &str) {
    if std::env::var_os("FIP_PRELINT_REQUIRE_TARGETS").is_some_and(|v| v == "1") {
        panic!("{msg} (FIP_PRELINT_REQUIRE_TARGETS=1: install it, or unset the variable)");
    }
    eprintln!("{msg}");
}

/// Installed targets of the toolchain: `(triple, has std)`.
fn installed() -> Vec<(String, bool)> {
    let out = Command::new("rustc")
        .env("RUSTUP_TOOLCHAIN", toolchain())
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc --print sysroot");
    let sysroot = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    let rustlib = sysroot.join("lib").join("rustlib");
    let mut v = Vec::new();
    for entry in std::fs::read_dir(&rustlib).expect("read the sysroot's rustlib") {
        let entry = entry.expect("rustlib entry");
        let lib = entry.path().join("lib");
        let Ok(files) = std::fs::read_dir(&lib) else {
            continue;
        };
        let names: Vec<String> = files
            .filter_map(Result::ok)
            .map(|f| f.file_name().to_string_lossy().into_owned())
            .collect();
        let has = |p: &str| {
            names
                .iter()
                .any(|n| n.starts_with(p) && n.ends_with(".rlib"))
        };
        if has("libcore-") {
            v.push((
                entry.file_name().to_string_lossy().into_owned(),
                has("libstd-"),
            ));
        }
    }
    v.sort();
    v
}

fn check_target(root: &Path, triple: &str, std: bool) -> Vec<String> {
    let target = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("targets")
        .join(triple);
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-fip-prelint"));
    cmd.args([
        "fip-prelint",
        "--warn-only",
        "--message-format",
        "short",
        "--locked",
        "--target",
        triple,
    ]);
    if !std {
        for p in NO_STD_PACKAGES {
            cmd.args(["-p", p]);
        }
        cmd.arg("--lib");
    }
    let out = cmd
        .current_dir(root)
        .env("FIP_PRELINT_TARGET_DIR", &target)
        .env("FIP_PRELINT_DRIVER_PATH", env!("CARGO_BIN_EXE_fip-prelint"))
        .env_remove("FIP_PRELINT_DUMP")
        .env_remove("FIP_PRELINT_DUMP_MIR")
        .env_remove("FIP_MACROS_MARK_ONLY")
        .env_remove("CARGO_TARGET_DIR")
        .output()
        .expect("run cargo-fip-prelint");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "check for `{triple}` failed to build:\n{stderr}"
    );
    let mut got: Vec<String> = stderr
        .lines()
        .filter(|l| {
            l.contains("fip-prelint [error]:")
                || l.contains("warning: fip-prelint:")
                || l.contains("note: fip-prelint: crate `")
                || l.contains("error[E")
        })
        .map(|l| l.trim_end().to_string())
        .collect();
    got.sort();
    got.dedup();
    got
}

/// Sections of `targets.expected`: `== <triple> std|no_std`, then its lines.
fn parse(text: &str) -> BTreeMap<String, (String, Vec<String>)> {
    let mut m = BTreeMap::new();
    let mut cur: Option<String> = None;
    for l in text.lines() {
        if l.starts_with('#') || l.trim().is_empty() {
            continue;
        }
        if let Some(h) = l.strip_prefix("== ") {
            let (t, kind) = h.split_once(' ').unwrap_or((h, ""));
            m.insert(t.to_string(), (kind.to_string(), Vec::new()));
            cur = Some(t.to_string());
        } else if let Some(t) = &cur
            && let Some((_, v)) = m.get_mut(t)
        {
            v.push(l.trim_end().to_string());
        }
    }
    m
}

#[test]
fn every_installed_target() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = manifest.join("../..");
    let targets = installed();
    assert!(!targets.is_empty(), "no installed target found");
    // At most four checks at a time (each is a cargo build of the workspace).
    let mut results: Vec<(String, bool, Vec<String>)> = Vec::new();
    for chunk in targets.chunks(4) {
        let handles: Vec<_> = chunk
            .iter()
            .map(|(t, std)| {
                let (t, std, root) = (t.clone(), *std, root.clone());
                std::thread::spawn(move || {
                    let got = check_target(&root, &t, std);
                    (t, std, got)
                })
            })
            .collect();
        for h in handles {
            results.push(h.join().expect("target check thread"));
        }
    }
    let path = manifest.join("tests").join("targets.expected");
    let text = std::fs::read_to_string(&path).unwrap_or_default();
    let mut recorded = parse(&text);
    if std::env::var("FIP_PRELINT_BLESS").is_ok_and(|v| v == "1") {
        for (t, std, got) in &results {
            let kind = if *std { "std" } else { "no_std" };
            recorded.insert(t.clone(), (kind.to_string(), got.clone()));
        }
        let mut out = String::from(
            "# `cargo fip-prelint --warn-only --target <triple>` per installed target (tests/targets.rs);\n\
             # notes omitted. `no_std` targets check the libraries of `just nostd` only.\n",
        );
        for (t, (kind, lines)) in &recorded {
            out.push_str(&format!("\n== {t} {kind}\n"));
            for l in lines {
                out.push_str(l);
                out.push('\n');
            }
        }
        std::fs::write(&path, out).expect("write targets.expected");
        return;
    }
    let mut bad = Vec::new();
    for (t, _, got) in &results {
        match recorded.remove(t) {
            None => bad.push(format!(
                "target `{t}` is installed but not recorded in targets.expected (FIP_PRELINT_BLESS=1)"
            )),
            Some((_, want)) if &want != got => {
                let missing: Vec<&String> = want.iter().filter(|l| !got.contains(l)).collect();
                let extra: Vec<&String> = got.iter().filter(|l| !want.contains(l)).collect();
                bad.push(format!(
                    "target `{t}` differs\nmissing:\n{missing:#?}\nunexpected:\n{extra:#?}"
                ));
            }
            Some(_) => {}
        }
    }
    for t in recorded.keys() {
        skipped(&format!(
            "targets.rs: `{t}` is recorded but not installed; skipped"
        ));
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}
