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
//! dependency has violations. A target selection (`--lib`, `--tests`, ..) replaces
//! `--all-targets`. The exit status is cargo's.
//!
//! `cargo fip-prelint --std-summaries [--target <triple>] [--out <file>]` (maintainers)
//! regenerates the std summaries (limits plan L6, sidecar of L10e): `cargo check
//! -Zbuild-std=core,alloc,std,panic_abort,panic_unwind` of the seed crate
//! `std-summaries/seed` (or `--manifest-path`) with the driver in generation mode,
//! into `FIP_PRELINT_TARGET_DIR` (default: a directory under the system temporary
//! directory, never the repository's `target/`), writing
//! `std-summaries/<release>-<target>.txt` (or `--out`).
//!
//! `cargo fip-prelint --stack [cargo build args..]` (limits plan L9) runs `cargo build
//! --workspace --lib` with the driver in stack mode (`FIP_PRELINT_STACK=1`) into
//! `<workspace>/target/fip-prelint-stack` (or `FIP_PRELINT_TARGET_DIR`), with the
//! profile cargo selects (`--release`, `--profile ..`), and reports per root a byte
//! bound for that build, read from the objects' `.stack_sizes`, or `⊤` with the reason
//! (`src/stackbound.rs`). The exit status is 1 if the build fails or a root is `⊤`.

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

/// `--stack`: builds and reports stack bounds (see the module documentation).
fn stack(args: &[String], toolchain: &str, sysroot: &str, ld: &str, target_dir: &Path) -> ExitCode {
    let driver = driver_path();
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
    cmd.args([
        "--lib",
        "--keep-going",
        "--message-format",
        "json-render-diagnostics",
        "--target-dir",
    ])
    .arg(target_dir)
    .args(args)
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
    // of a member's rlib, without the side file).
    let mut rlibs: Vec<PathBuf> = artifact_files(&json)
        .into_iter()
        .filter_map(|p| match p.extension().and_then(|e| e.to_str()) {
            Some("rmeta") => Some(p.with_extension("rlib")),
            Some("rlib") => Some(p),
            _ => None,
        })
        .filter(|p| {
            let mut side = p.clone().into_os_string();
            side.push(".fip-stack");
            Path::new(&side).is_file()
        })
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
                build.add_rlib(rlib);
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
    let mut tops = 0usize;
    for r in &records {
        let mut bounded = 0usize;
        for (label, sym) in &r.roots {
            match sym.clone().and_then(|s| build.bound(&s)) {
                Ok((b, path)) => {
                    bounded += 1;
                    let chain: Vec<String> =
                        path.iter().map(|(l, f)| format!("`{l}` {f}")).collect();
                    eprintln!(
                        "note: fip-prelint: stack: `{label}` uses at most {b} bytes in this build (target {}, opt-level {}; frames from `.stack_sizes` plus {} bytes of return address each, longest path: {}; panic paths, unwinding, signal and interrupt contexts excluded)",
                        r.target,
                        r.opt_level,
                        stackbound::RETURN_ADDRESS,
                        chain.join(" -> ")
                    );
                }
                Err(why) => {
                    tops += 1;
                    eprintln!("error: fip-prelint: stack: `{label}` has no bound (⊤): {why}");
                }
            }
        }
        if !r.roots.is_empty() {
            eprintln!(
                "note: fip-prelint: stack: crate `{}`: {} roots, {bounded} bounded, {} ⊤",
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
