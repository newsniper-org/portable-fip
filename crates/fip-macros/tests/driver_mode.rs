// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Without the driver it does not pass: a crate using the driver-checked
//! `fip_fn!(prelint, N, ..)` (`docs/decisions/2026-11-03-fip-fn-driver-mode.md`) is
//! written to `CARGO_TARGET_TMPDIR` and built with a nested `cargo` (offline; no
//! crates.io dependencies), each build in its own directory and target directory (proc-macro reads of
//! environment variables are not tracked by cargo):
//!
//! - plainly: the `fip-macros` error naming `cargo fip-prelint`;
//! - with the driver's environment variables forged (`FIP_PRELINT_DRIVER=1`,
//!   `FIP_PRELINT_CHECKS=1`): the expansion's `#[cfg(not(fip_prelint))]
//!   compile_error!`;
//! - with `--cfg fip_prelint` forged as well: `fip-strict` itself does not compile (its
//!   `#![cfg_attr(fip_prelint, fip::export)]` needs the tool namespace `fip` the driver
//!   registers).
//!
//! The constructions are honest (bound 0 for an allocation-free body, 1 for one
//! allocation), so each failure is the mode's guard, not a wrong claim.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const LIB: &str = r"
use fip_strict::FipFn;

pub fn ones(x: u32) -> u32 {
    let f = fip_macros::fip_fn!(prelint, 0, |x: u32| x.wrapping_add(1).count_ones());
    f.call((x,))
}

pub fn boxed(x: u32) -> u32 {
    let f = fip_macros::fip_fn!(prelint, 1, |x: u32| Box::new(x));
    *f.call((x,))
}
";

/// The error `fip-macros` emits outside a checking driver run.
const UNCHECKED: &str = "fip_fn!(prelint, ..) is checked only by `cargo fip-prelint`";

/// The expansion's guard when the environment variables are forged.
const NO_CFG: &str = "fip_fn!(prelint, ..): `cfg(fip_prelint)` is not set";

fn crates_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/")
        .to_path_buf()
}

fn root() -> PathBuf {
    Path::new(env!("CARGO_TARGET_TMPDIR")).join("driver-mode-fixture")
}

/// Writes the crate `drvmode` under `<name>/` (one copy per test: the tests run in
/// parallel) and returns its directory.
fn fixture(name: &str) -> PathBuf {
    let dir = root().join(name).join("drvmode");
    fs::create_dir_all(dir.join("src")).expect("mkdir drvmode");
    let crates = crates_dir();
    let dep = |c: &str| crates.join(c).display().to_string().replace('\\', "/");
    fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"drvmode\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [dependencies]\nfip-macros = {{ path = \"{}\" }}\nfip-strict = {{ path = \"{}\" }}\n\n\
             [lints.rust]\nunexpected_cfgs = {{ level = \"allow\" }}\n\n[workspace]\n",
            dep("fip-macros"),
            dep("fip-strict")
        ),
    )
    .expect("write manifest");
    fs::write(dir.join("src/lib.rs"), LIB).expect("write lib.rs");
    dir
}

/// `cargo build` of the fixture into `<name>/target` with `envs` (and nothing of the
/// driver's environment inherited).
fn build(name: &str, envs: &[(&str, &str)]) -> Output {
    let dir = fixture(name);
    let mut cmd = Command::new(env!("CARGO"));
    cmd.args(["build", "-q", "--offline", "--target-dir"])
        .arg(root().join(name).join("target"))
        .current_dir(&dir)
        .env_remove("FIP_PRELINT_DRIVER")
        .env_remove("FIP_PRELINT_CHECKS")
        .env_remove("FIP_MACROS_MARK_ONLY")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER");
    for (k, v) in envs {
        cmd.env(k, v);
    }
    cmd.output().expect("run cargo")
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

#[test]
fn plain_build_is_a_compile_error() {
    let o = build("plain", &[]);
    let err = stderr(&o);
    assert!(
        !o.status.success(),
        "a plain build accepted fip_fn!(prelint, ..):\n{err}"
    );
    assert_eq!(err.matches(UNCHECKED).count(), 2, "{err}");
}

#[test]
fn forged_environment_hits_the_cfg_guard() {
    let o = build(
        "env",
        &[("FIP_PRELINT_DRIVER", "1"), ("FIP_PRELINT_CHECKS", "1")],
    );
    let err = stderr(&o);
    assert!(
        !o.status.success(),
        "forged driver environment accepted fip_fn!(prelint, ..):\n{err}"
    );
    assert!(!err.contains(UNCHECKED), "the macro was not fooled:\n{err}");
    assert_eq!(err.matches(NO_CFG).count(), 2, "{err}");
}

#[test]
fn forged_cfg_breaks_fip_strict() {
    let o = build(
        "cfg",
        &[
            ("FIP_PRELINT_DRIVER", "1"),
            ("FIP_PRELINT_CHECKS", "1"),
            ("RUSTFLAGS", "--cfg fip_prelint"),
        ],
    );
    let err = stderr(&o);
    assert!(
        !o.status.success(),
        "forged driver environment and cfg accepted fip_fn!(prelint, ..):\n{err}"
    );
    assert!(
        err.contains("could not compile `fip-strict`") && err.contains("`fip`"),
        "{err}"
    );
}
