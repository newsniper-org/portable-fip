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
//! `tests/targets.expected`.
//!
//! Two target sets (`FIP_PRELINT_TARGETS`):
//!
//! - `recorded` (the default; `just prelint-targets`, and what `just ci` runs): the
//!   targets that have a section in `targets.expected`. An installed target without a
//!   section is not built and not a failure; it is named in a note on stderr. A
//!   recorded target that is not installed is skipped with a message (a failure under
//!   `FIP_PRELINT_REQUIRE_TARGETS=1`, which `just ci` sets).
//! - `all` (`just prelint-targets-all`): every installed target. One without a section
//!   fails (record it with `FIP_PRELINT_BLESS=1`, after reviewing its output).
//!
//! `FIP_PRELINT_BLESS=1` rewrites the sections of the targets that were checked, so
//! under `recorded` it never adds a target.

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

/// Whether every installed target is checked (`FIP_PRELINT_TARGETS=all`) or only the
/// recorded ones (unset or `recorded`). Any other value is an error, not a default.
fn all_targets() -> bool {
    match std::env::var("FIP_PRELINT_TARGETS") {
        Err(_) => false,
        Ok(v) if v == "recorded" => false,
        Ok(v) if v == "all" => true,
        Ok(v) => panic!("FIP_PRELINT_TARGETS must be `recorded` or `all`, not `{v}`"),
    }
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

/// `Err` carries the build's stderr: a target the workspace does not build for is
/// reported with the others, it does not abort the run.
fn check_target(root: &Path, triple: &str, std: bool) -> Result<Vec<String>, String> {
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
    if !out.status.success() {
        return Err(stderr.into_owned());
    }
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
    Ok(got)
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
    let path = manifest.join("tests").join("targets.expected");
    let text = std::fs::read_to_string(&path).unwrap_or_default();
    let mut recorded = parse(&text);
    let mut targets = installed();
    assert!(!targets.is_empty(), "no installed target found");
    if !all_targets() {
        let unrecorded: Vec<&str> = targets
            .iter()
            .filter(|(t, _)| !recorded.contains_key(t))
            .map(|(t, _)| t.as_str())
            .collect();
        if !unrecorded.is_empty() {
            eprintln!(
                "targets.rs: {} installed target(s) without a section in targets.expected are \
                 not checked (FIP_PRELINT_TARGETS=all checks them): {}",
                unrecorded.len(),
                unrecorded.join(" ")
            );
        }
        targets.retain(|(t, _)| recorded.contains_key(t));
        // A missing, empty or unparsable `targets.expected` must not pass by checking
        // nothing.
        assert!(
            !recorded.is_empty(),
            "targets.expected records no target ({})",
            path.display()
        );
        assert!(
            !targets.is_empty(),
            "none of the {} recorded targets is installed",
            recorded.len()
        );
    }
    // At most four checks at a time (each is a cargo build of the workspace).
    let mut results: Vec<(String, bool, Vec<String>)> = Vec::new();
    let mut unbuilt: Vec<(String, String)> = Vec::new();
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
            match h.join().expect("target check thread") {
                (t, std, Ok(got)) => results.push((t, std, got)),
                (t, _, Err(stderr)) => unbuilt.push((t, stderr)),
            }
        }
    }
    if std::env::var("FIP_PRELINT_BLESS").is_ok_and(|v| v == "1") {
        for (t, std, got) in &results {
            let kind = if *std { "std" } else { "no_std" };
            recorded.insert(t.clone(), (kind.to_string(), got.clone()));
        }
        let mut out = String::from(
            "# `cargo fip-prelint --warn-only --target <triple>` per recorded target (tests/targets.rs);\n\
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
        // A target that did not build was not recorded; blessing must not hide it.
        assert!(
            unbuilt.is_empty(),
            "not recorded, the check failed to build: {}",
            unbuilt
                .iter()
                .map(|(t, _)| t.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        );
        return;
    }
    let mut bad = Vec::new();
    for (t, stderr) in &unbuilt {
        // The last lines name the cause; the whole stderr of ~100 targets would bury it.
        let tail: Vec<&str> = stderr.lines().rev().take(6).collect();
        let tail: Vec<&str> = tail.into_iter().rev().collect();
        let known = if recorded.remove(t).is_some() {
            "recorded"
        } else {
            "not recorded"
        };
        bad.push(format!(
            "target `{t}` ({known}): the check failed to build:\n  {}",
            tail.join("\n  ")
        ));
    }
    for (t, _, got) in &results {
        match recorded.remove(t) {
            None => bad.push(format!(
                "target `{t}` is installed but not recorded in targets.expected \
                 (FIP_PRELINT_TARGETS=all: review its output, then FIP_PRELINT_BLESS=1)"
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
