// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `cargo fip-prelint [--warn-only] [cargo check args..]`
//!
//! Runs `cargo check --workspace --all-targets --keep-going` on the pinned toolchain
//! (`FIP_PRELINT_TOOLCHAIN`, default `1.99.1`) into `<workspace>/target/fip-prelint`
//! (or `FIP_PRELINT_TARGET_DIR`), with the driver `fip-prelint` (next to this binary,
//! or `FIP_PRELINT_DRIVER_PATH`) as `RUSTC_WORKSPACE_WRAPPER`, `RUSTC_BOOTSTRAP=1`, and
//! `LD_LIBRARY_PATH` pointing at the toolchain's `lib` directory.
//!
//! `--warn-only` reports violations as warnings, so every crate is checked even if a
//! dependency has violations. The exit status is cargo's.

use std::path::PathBuf;
use std::process::{Command, ExitCode};

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

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    // `cargo fip-prelint ..` passes the subcommand name first.
    if args.first().is_some_and(|a| a == "fip-prelint") {
        args.remove(0);
    }
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
    let target_dir = match std::env::var_os("FIP_PRELINT_TARGET_DIR") {
        Some(d) => PathBuf::from(d),
        None => match workspace_root(&toolchain, manifest.as_deref()) {
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
    let selects_packages = args
        .iter()
        .any(|a| a == "-p" || a.starts_with("--package") || a == "--workspace");
    let driver = driver_path();
    let mut cmd = Command::new("cargo");
    cmd.env("RUSTUP_TOOLCHAIN", &toolchain)
        .env("FIP_PRELINT_DRIVER_ID", driver_id(&driver))
        .env("RUSTC_WORKSPACE_WRAPPER", &driver)
        .env("RUSTC_BOOTSTRAP", "1")
        .env("LD_LIBRARY_PATH", ld)
        .env("FIP_PRELINT_SYSROOT", &sysroot)
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC")
        .env_remove("CARGO_TARGET_DIR")
        .arg("check");
    if !selects_packages {
        cmd.arg("--workspace");
    }
    cmd.args(["--all-targets", "--keep-going", "--target-dir"])
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
