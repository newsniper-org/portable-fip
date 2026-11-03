// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `cargo fip-prelint [--warn-only] [cargo check args..]`
//!
//! Runs `cargo check --workspace --all-targets --keep-going` on the pinned toolchain
//! (`FIP_PRELINT_TOOLCHAIN`, default `1.99.1`) into `<workspace>/target/fip-prelint`
//! (or `FIP_PRELINT_TARGET_DIR`), with the driver `fip-prelint` (next to this binary,
//! or `FIP_PRELINT_DRIVER_PATH`) as `RUSTC_WRAPPER`, `RUSTC_BOOTSTRAP=1`, and
//! `LD_LIBRARY_PATH` pointing at the toolchain's `lib` directory.
//!
//! `--warn-only` reports violations as warnings, so every crate is checked even if a
//! dependency has violations. `--pool-hints` (top plan T17) adds heuristic notes for
//! methods of crates declaring `fip::export` that look like unmarked pool allocators
//! (`src/poolhint.rs`); off by default, they change no verdict, count or exit status.
//! A target selection (`--lib`, `--tests`, ..) replaces `--all-targets`. The exit
//! status is cargo's.
//!
//! `cargo fip-prelint --std-summaries [--target <triple>] [--out <file>]` (maintainers)
//! regenerates the std summaries (limits plan L6, sidecar of L10e): `cargo check
//! -Zbuild-std=core,alloc,std,panic_abort,panic_unwind` of the seed crate
//! `std-summaries/seed` (or `--manifest-path`) with the driver in generation mode,
//! into `FIP_PRELINT_TARGET_DIR` (default: a directory under the system temporary
//! directory, never the repository's `target/`), writing
//! `std-summaries/<release>-<target>.txt` (or `--out`).
//!
//! `cargo fip-prelint --stack [--build-std] [cargo build args..]` (limits plan L9) runs
//! `cargo build --workspace --lib` (a target selection such as `--lib --tests`
//! replaces `--lib`; bins and tests contribute their functions and instances, top plan
//! T8f) with the driver in stack mode (`FIP_PRELINT_STACK=1`) into
//! `<workspace>/target/fip-prelint-stack` (or `FIP_PRELINT_TARGET_DIR`), with the
//! profile cargo selects (`--release`, `--profile ..`), and reports per root a byte
//! bound for that build, read from the objects' `.stack_sizes`, or `⊤` with the reason
//! (`src/stackbound.rs`); a generic root is bounded per instance the build codegens
//! (top plan T8e). `--build-std` (top plan T8c) builds against a `-Zbuild-std`
//! standard library with the profile's settings (`--target` defaults to the host), so
//! its frames are those of the artefact built. The exit status is 1 if the build fails
//! or a root is `⊤`.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};

#[path = "../stackbound.rs"]
mod stackbound;

const DEFAULT_TOOLCHAIN: &str = "1.99.1";

fn driver_path() -> PathBuf {
    if let Some(p) = std::env::var_os("FIP_PRELINT_DRIVER_PATH") {
        return PathBuf::from(p);
    }
    let me = std::env::current_exe().expect("current executable");
    me.with_file_name(format!("fip-prelint{}", std::env::consts::EXE_SUFFIX))
}

/// Identity of the driver binary, so that a rebuilt driver re-checks every crate.
fn driver_id(driver: &std::path::Path) -> String {
    match std::fs::metadata(driver) {
        Ok(m) => {
            let mtime = m
                .modified()
                .ok()
                .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                .map_or(0, |d| d.as_nanos());
            format!("{}-{mtime}", m.len())
        }
        Err(_) => "unknown".to_string(),
    }
}

/// Content hash of the std summaries the driver may read: the file named by
/// `FIP_PRELINT_STD_SUMMARIES`, or else every `*.txt` file of the driver's
/// `std-summaries/` directory (file name and content, in name order). Passed to the
/// driver as `FIP_PRELINT_INPUTS_ID`, which it records in the dep-info: a sidecar
/// change re-checks every crate even if the file's modification time did not move
/// (cargo's file dep-info compares modification times only).
fn inputs_id() -> String {
    // FNV-1a, 64 bit: not cryptographic, only a change detector.
    fn feed(h: &mut u64, bytes: &[u8]) {
        for &b in bytes {
            *h ^= u64::from(b);
            *h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut files: Vec<PathBuf> = Vec::new();
    if let Some(p) = std::env::var_os("FIP_PRELINT_STD_SUMMARIES") {
        files.push(PathBuf::from(p));
    } else {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("std-summaries");
        if let Ok(rd) = std::fs::read_dir(&dir) {
            for e in rd.flatten() {
                let p = e.path();
                if p.extension().is_some_and(|x| x == "txt") {
                    files.push(p);
                }
            }
        }
        files.sort();
    }
    for f in &files {
        feed(&mut h, f.to_string_lossy().as_bytes());
        feed(&mut h, &[0]);
        match std::fs::read(f) {
            Ok(bytes) => {
                feed(&mut h, &(bytes.len() as u64).to_le_bytes());
                feed(&mut h, &bytes);
            }
            Err(_) => feed(&mut h, b"<unreadable>"),
        }
    }
    format!("std-summaries-{}-{h:016x}", files.len())
}

fn sysroot(toolchain: &str) -> Result<String, String> {
    let out = Command::new("rustc")
        .env("RUSTUP_TOOLCHAIN", toolchain)
        .args(["--print", "sysroot"])
        .output()
        .map_err(|e| format!("cannot run rustc: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "`rustc +{toolchain} --print sysroot` failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn workspace_root(toolchain: &str, manifest: Option<&str>) -> Result<PathBuf, String> {
    let mut cmd = Command::new("cargo");
    cmd.env("RUSTUP_TOOLCHAIN", toolchain).args([
        "locate-project",
        "--workspace",
        "--message-format",
        "plain",
    ]);
    if let Some(m) = manifest {
        cmd.args(["--manifest-path", m]);
    }
    let out = cmd.output().map_err(|e| format!("cannot run cargo: {e}"))?;
    if !out.status.success() {
        return Err(String::from_utf8_lossy(&out.stderr).to_string());
    }
    let manifest = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    Ok(manifest
        .parent()
        .map_or_else(|| PathBuf::from("."), PathBuf::from))
}

/// `rustc -vV` of the toolchain: (release, host).
fn rustc_vv(toolchain: &str) -> Result<(String, String), String> {
    let out = Command::new("rustc")
        .env("RUSTUP_TOOLCHAIN", toolchain)
        .arg("-vV")
        .output()
        .map_err(|e| format!("cannot run rustc: {e}"))?;
    let text = String::from_utf8_lossy(&out.stdout);
    let field = |k: &str| {
        text.lines()
            .find_map(|l| l.strip_prefix(k).map(|v| v.trim().to_string()))
    };
    match (field("release:"), field("host:")) {
        (Some(r), Some(h)) => Ok((r, h)),
        _ => Err(format!("unexpected `rustc -vV` output: {text}")),
    }
}

/// The value after `flag` in `args` (removing both), or of `flag=value`.
fn take_value(args: &mut Vec<String>, flag: &str) -> Option<String> {
    if let Some(i) = args.iter().position(|a| a == flag)
        && i + 1 < args.len()
    {
        let v = args.remove(i + 1);
        args.remove(i);
        return Some(v);
    }
    let prefix = format!("{flag}=");
    let i = args.iter().position(|a| a.starts_with(&prefix))?;
    Some(args.remove(i)[prefix.len()..].to_string())
}

/// `--std-summaries`: regenerates the std summaries (see the module documentation).
fn std_summaries(mut args: Vec<String>, toolchain: &str, sysroot: &str, ld: &str) -> ExitCode {
    let here = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let (release, host) = match rustc_vv(toolchain) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("cargo-fip-prelint: {e}");
            return ExitCode::from(2);
        }
    };
    let target = take_value(&mut args, "--target").unwrap_or(host);
    let out = take_value(&mut args, "--out").map_or_else(
        || {
            here.join("std-summaries")
                .join(format!("{release}-{target}.txt"))
        },
        PathBuf::from,
    );
    let manifest = take_value(&mut args, "--manifest-path").map_or_else(
        || here.join("std-summaries").join("seed").join("Cargo.toml"),
        PathBuf::from,
    );
    let target_dir = std::env::var_os("FIP_PRELINT_TARGET_DIR").map_or_else(
        || std::env::temp_dir().join("fip-prelint-std-summaries"),
        PathBuf::from,
    );
    let driver = driver_path();
    let start = std::time::Instant::now();
    let status = Command::new("cargo")
        .env("RUSTUP_TOOLCHAIN", toolchain)
        .env("FIP_PRELINT_DRIVER_ID", driver_id(&driver))
        .env("RUSTC_WRAPPER", &driver)
        .env("RUSTC_BOOTSTRAP", "1")
        .env("LD_LIBRARY_PATH", ld)
        .env("FIP_PRELINT_SYSROOT", sysroot)
        .env("FIP_PRELINT_STD_SUMMARIES_OUT", &out)
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("RUSTC")
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("FIP_PRELINT_WARN_ONLY")
        .args([
            "check",
            "-Zbuild-std=core,alloc,std,panic_abort,panic_unwind",
            "--target",
            &target,
            "--manifest-path",
        ])
        .arg(&manifest)
        .arg("--target-dir")
        .arg(&target_dir)
        .args(&args)
        .status();
    match status {
        Ok(st) if st.success() => {
            eprintln!(
                "cargo-fip-prelint: std summaries for `{target}` written to {} ({:.1} s)",
                out.display(),
                start.elapsed().as_secs_f64()
            );
            ExitCode::SUCCESS
        }
        Ok(st) => ExitCode::from(u8::try_from(st.code().unwrap_or(1)).unwrap_or(1)),
        Err(e) => {
            eprintln!("cargo-fip-prelint: cannot run cargo: {e}");
            ExitCode::from(2)
        }
    }
}

/// The `"filenames":[..]` of cargo's `compiler-artifact` JSON messages.
fn artifact_files(json: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for line in json.lines() {
        if !line.contains("\"reason\":\"compiler-artifact\"") {
            continue;
        }
        let Some(i) = line.find("\"filenames\":[") else {
            continue;
        };
        let mut chars = line[i + "\"filenames\":[".len()..].chars();
        let mut cur: Option<String> = None;
        while let Some(c) = chars.next() {
            match cur.as_mut() {
                None if c == ']' => break,
                None if c == '"' => cur = Some(String::new()),
                None => {}
                Some(s) if c == '"' => {
                    out.push(PathBuf::from(std::mem::take(s)));
                    cur = None;
                }
                Some(s) if c == '\\' => match chars.next() {
                    Some('n') => s.push('\n'),
                    Some('t') => s.push('\t'),
                    Some(o) => s.push(o),
                    None => {}
                },
                Some(s) => s.push(c),
            }
        }
    }
    out
}

/// The file in `<dir>/deps/` that the uplifted executable `p` is a copy of (same
/// content; cargo hard-links it), whose `.fip-stack` record the driver wrote.
fn deps_copy_of(p: &Path) -> Option<PathBuf> {
    let name = p.file_stem()?.to_string_lossy().replace('-', "_");
    let deps = p.parent()?.join("deps");
    let bytes = std::fs::read(p).ok()?;
    let prefix = format!("{name}-");
    std::fs::read_dir(&deps)
        .ok()?
        .flatten()
        .map(|e| e.path())
        .filter(|c| {
            c.extension().is_none()
                && c.file_name()
                    .is_some_and(|n| n.to_string_lossy().starts_with(&prefix))
        })
        .find(|c| {
            std::fs::metadata(c).is_ok_and(|m| m.len() == bytes.len() as u64)
                && std::fs::read(c).is_ok_and(|b| b == bytes)
        })
}

/// `--stack`: builds and reports stack bounds (see the module documentation).
fn stack(args: &[String], toolchain: &str, sysroot: &str, ld: &str, target_dir: &Path) -> ExitCode {
    let driver = driver_path();
    let mut args = args.to_vec();
    let build_std = {
        let before = args.len();
        args.retain(|a| a != "--build-std");
        args.len() != before
    };
    if build_std
        && !args
            .iter()
            .any(|a| a == "--target" || a.starts_with("--target="))
    {
        match rustc_vv(toolchain) {
            Ok((_, host)) => {
                args.push("--target".to_string());
                args.push(host);
            }
            Err(e) => {
                eprintln!("cargo-fip-prelint: {e}");
                return ExitCode::from(2);
            }
        }
    }
    let selects_targets = args.iter().any(|a| {
        matches!(
            a.split('=').next().unwrap_or(""),
            "--lib" | "--bins" | "--bin" | "--tests" | "--test" | "--all-targets"
        )
    });
    let selects_packages = args
        .iter()
        .any(|a| a == "-p" || a.starts_with("--package") || a == "--workspace");
    let mut cmd = Command::new("cargo");
    cmd.env("RUSTUP_TOOLCHAIN", toolchain)
        .env("FIP_PRELINT_DRIVER_ID", driver_id(&driver))
        .env("RUSTC_WRAPPER", &driver)
        .env("RUSTC_BOOTSTRAP", "1")
        .env("LD_LIBRARY_PATH", ld)
        .env("FIP_PRELINT_SYSROOT", sysroot)
        .env("FIP_PRELINT_STACK", "1")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("RUSTC")
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("FIP_PRELINT_WARN_ONLY")
        .arg("build");
    if !selects_packages {
        cmd.arg("--workspace");
    }
    if !selects_targets {
        cmd.arg("--lib");
    }
    if build_std {
        cmd.arg("-Zbuild-std=core,alloc,std,panic_abort,panic_unwind");
    }
    cmd.args([
        "--keep-going",
        "--message-format",
        "json-render-diagnostics",
        "--target-dir",
    ])
    .arg(target_dir)
    .args(&args)
    .stdout(Stdio::piped())
    .stderr(Stdio::inherit());
    let out = match cmd.output() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("cargo-fip-prelint: cannot run cargo: {e}");
            return ExitCode::from(2);
        }
    };
    let built = out.status.success();
    let json = String::from_utf8_lossy(&out.stdout);
    // The rlib in `deps/` (next to its `.rmeta`; cargo also lists an uplifted copy
    // of a member's rlib, without the side file); an executable in `deps/` (a test),
    // or the `deps/` file an uplifted executable (a bin) is a copy of.
    let has_side = |p: &Path| {
        let mut side = p.to_path_buf().into_os_string();
        side.push(".fip-stack");
        Path::new(&side).is_file()
    };
    let mut rlibs: Vec<PathBuf> = artifact_files(&json)
        .into_iter()
        .filter_map(|p| match p.extension().and_then(|e| e.to_str()) {
            Some("rmeta") => Some(p.with_extension("rlib")),
            Some("rlib") => Some(p),
            Some("d" | "rcgu" | "o" | "so" | "dylib" | "dll" | "pdb" | "wasm") => None,
            _ if has_side(&p) => Some(p),
            _ => deps_copy_of(&p),
        })
        .filter(|p| has_side(p))
        .collect();
    rlibs.sort();
    rlibs.dedup();
    let mut build = stackbound::Build::default();
    let mut records = Vec::new();
    for rlib in &rlibs {
        let mut side = rlib.clone().into_os_string();
        side.push(".fip-stack");
        // Only crates the driver compiled have one: the functions of a dependency
        // passed through to the real rustc are not in the graph, so calls into them
        // are `⊤`.
        let Ok(text) = std::fs::read_to_string(&side) else {
            continue;
        };
        match stackbound::parse_record(&text) {
            Ok(r) => {
                match &r.objs {
                    Some((dir, stem)) => build.add_objects(Path::new(dir), stem),
                    None => build.add_rlib(rlib),
                }
                build.add_record(&r);
                records.push(r);
            }
            Err(e) => {
                eprintln!(
                    "error: fip-prelint: stack: {}: {e}",
                    Path::new(&side).display()
                );
                return ExitCode::from(1);
            }
        }
    }
    // Instances of generic roots, from every crate of the build (a test or another
    // library instantiates them): key → (label, symbol).
    let mut insts: std::collections::BTreeMap<&str, Vec<(&str, &str)>> = Default::default();
    for r in &records {
        for (key, label, sym) in &r.insts {
            insts.entry(key).or_default().push((label, sym));
        }
    }
    for v in insts.values_mut() {
        v.sort();
        v.dedup();
    }
    if !records.is_empty() {
        eprintln!(
            "note: fip-prelint: stack: built with `-Zemit-stack-sizes -Zshare-generics=no -Zcross-crate-inline-threshold=never`{} ({} objects; the bounds hold for this build)",
            if build_std {
                ", against a `-Zbuild-std` standard library built with the profile's settings (not the shipped one)"
            } else {
                ""
            },
            build.machine()
        );
    }
    let ra = build.return_address();
    let mut tops = 0usize;
    for r in &records {
        let leaves: HashMap<String, u64> =
            r.leaves.iter().map(|(s, b, _)| (s.clone(), *b)).collect();
        let mut bounded = 0usize;
        let report = |label: &str, found: Result<(u64, Vec<(String, u64)>), String>| match found {
            Ok((b, path)) => {
                let chain: Vec<String> = path.iter().map(|(l, f)| format!("`{l}` {f}")).collect();
                eprintln!(
                    "note: fip-prelint: stack: `{label}` uses at most {b} bytes in this build (target {}, opt-level {}; frames from `.stack_sizes` plus {ra} bytes of return address each, longest path: {}; panic paths, unwinding, signal and interrupt contexts excluded)",
                    r.target,
                    r.opt_level,
                    chain.join(" -> ")
                );
                true
            }
            Err(why) => {
                eprintln!("error: fip-prelint: stack: `{label}` has no bound (⊤): {why}");
                false
            }
        };
        for (label, sym) in &r.roots {
            let generic = r.generics.iter().find(|(l, _)| l == label);
            let found = match (sym, generic.and_then(|(_, k)| insts.get(k.as_str()))) {
                (Err(_), Some(list)) if !list.is_empty() => {
                    let mut all = true;
                    for (ilabel, isym) in list {
                        all &= report(ilabel, build.bound_with(isym, &leaves));
                    }
                    all
                }
                _ => report(
                    label,
                    sym.clone().and_then(|s| build.bound_with(&s, &leaves)),
                ),
            };
            if found {
                bounded += 1;
            } else {
                tops += 1;
            }
        }
        for (sym, bytes, evidence) in &r.leaves {
            eprintln!(
                "note: fip-prelint: stack: crate `{}` declares `{sym}` a stack leaf of at most {bytes} bytes (return address included; trusted, not measured; evidence: {evidence})",
                r.krate
            );
        }
        if !r.roots.is_empty() {
            let leaves_note = if r.leaves.is_empty() {
                String::new()
            } else {
                format!(", {} declared stack leaves", r.leaves.len())
            };
            eprintln!(
                "note: fip-prelint: stack: crate `{}`: {} roots, {bounded} bounded, {} ⊤{leaves_note}",
                r.krate,
                r.roots.len(),
                r.roots.len() - bounded
            );
        }
    }
    if !built {
        eprintln!("cargo-fip-prelint: the build failed");
        return ExitCode::from(1);
    }
    if tops > 0 {
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    // `cargo fip-prelint ..` passes the subcommand name first.
    if args.first().is_some_and(|a| a == "fip-prelint") {
        args.remove(0);
    }
    let mut generate = false;
    args.retain(|a| {
        if a == "--std-summaries" {
            generate = true;
            false
        } else {
            true
        }
    });
    let mut stack_mode = false;
    args.retain(|a| {
        if a == "--stack" {
            stack_mode = true;
            false
        } else {
            true
        }
    });
    let mut warn_only = false;
    args.retain(|a| {
        if a == "--warn-only" {
            warn_only = true;
            false
        } else {
            true
        }
    });
    let mut pool_hints = false;
    args.retain(|a| {
        if a == "--pool-hints" {
            pool_hints = true;
            false
        } else {
            true
        }
    });
    let toolchain =
        std::env::var("FIP_PRELINT_TOOLCHAIN").unwrap_or_else(|_| DEFAULT_TOOLCHAIN.to_string());
    let manifest = args
        .iter()
        .position(|a| a == "--manifest-path")
        .and_then(|i| args.get(i + 1).cloned())
        .or_else(|| {
            args.iter()
                .find_map(|a| a.strip_prefix("--manifest-path=").map(str::to_string))
        });
    let sysroot = match sysroot(&toolchain) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cargo-fip-prelint: {e}");
            return ExitCode::from(2);
        }
    };
    if generate {
        let lib = format!("{sysroot}/lib");
        let ld = match std::env::var("LD_LIBRARY_PATH") {
            Ok(old) if !old.is_empty() => format!("{lib}:{old}"),
            _ => lib,
        };
        return std_summaries(args, &toolchain, &sysroot, &ld);
    }
    let target_dir = match std::env::var_os("FIP_PRELINT_TARGET_DIR") {
        Some(d) => PathBuf::from(d),
        None => match workspace_root(&toolchain, manifest.as_deref()) {
            Ok(root) if stack_mode => root.join("target").join("fip-prelint-stack"),
            Ok(root) => root.join("target").join("fip-prelint"),
            Err(e) => {
                eprintln!("cargo-fip-prelint: {e}");
                return ExitCode::from(2);
            }
        },
    };
    let lib = format!("{sysroot}/lib");
    let ld = match std::env::var("LD_LIBRARY_PATH") {
        Ok(old) if !old.is_empty() => format!("{lib}:{old}"),
        _ => lib,
    };
    if stack_mode {
        return stack(&args, &toolchain, &sysroot, &ld, &target_dir);
    }

    let selects_packages = args
        .iter()
        .any(|a| a == "-p" || a.starts_with("--package") || a == "--workspace");
    let driver = driver_path();
    let mut cmd = Command::new("cargo");
    cmd.env("RUSTUP_TOOLCHAIN", &toolchain)
        .env("FIP_PRELINT_DRIVER_ID", driver_id(&driver))
        .env("FIP_PRELINT_INPUTS_ID", inputs_id())
        // Every crate goes through the driver, dependencies included: a dependency
        // that declares `fip::export` (e.g. `fip-core` used as a git or path
        // dependency by another project) must be compiled with the driver's flags so
        // its MIR is readable. The driver decides per crate (see `src/main.rs`).
        .env("RUSTC_WRAPPER", &driver)
        .env("RUSTC_BOOTSTRAP", "1")
        .env("LD_LIBRARY_PATH", ld)
        .env("FIP_PRELINT_SYSROOT", &sysroot)
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("RUSTC")
        .env_remove("CARGO_TARGET_DIR")
        .arg("check");
    if !selects_packages {
        cmd.arg("--workspace");
    }
    // Target selection of the caller (e.g. `--lib` for a target without `std`)
    // replaces `--all-targets`.
    let selects_targets = args.iter().any(|a| {
        matches!(
            a.split('=').next().unwrap_or(""),
            "--lib"
                | "--bins"
                | "--bin"
                | "--tests"
                | "--test"
                | "--examples"
                | "--example"
                | "--benches"
                | "--bench"
                | "--all-targets"
        )
    });
    if !selects_targets {
        cmd.arg("--all-targets");
    }
    cmd.args(["--keep-going", "--target-dir"])
        .arg(&target_dir)
        .args(&args);
    if warn_only {
        cmd.env("FIP_PRELINT_WARN_ONLY", "1");
    }
    if pool_hints {
        cmd.env("FIP_PRELINT_POOL_HINTS", "1");
    } else {
        cmd.env_remove("FIP_PRELINT_POOL_HINTS");
    }
    match cmd.status() {
        Ok(st) => match st.code() {
            Some(0) => ExitCode::SUCCESS,
            Some(c) => ExitCode::from(u8::try_from(c).unwrap_or(1)),
            None => ExitCode::from(1),
        },
        Err(e) => {
            eprintln!("cargo-fip-prelint: cannot run cargo: {e}");
            ExitCode::from(2)
        }
    }
}
