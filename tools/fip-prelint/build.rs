// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Records the sysroot of the compiler building the driver: the driver links that
//! compiler's `librustc_driver` and must analyse with the same standard library.

use std::process::Command;

fn main() {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let out = Command::new(&rustc)
        .args(["--print", "sysroot"])
        .output()
        .expect("run rustc --print sysroot");
    let sysroot = String::from_utf8(out.stdout).expect("utf-8 sysroot");
    let sysroot = sysroot.trim();
    println!("cargo:rustc-env=FIP_PRELINT_BUILD_SYSROOT={sysroot}");
    // Lets the binaries find `librustc_driver-*.so` without `LD_LIBRARY_PATH`.
    println!("cargo:rustc-link-arg-bins=-Wl,-rpath,{sysroot}/lib");
    // The host triple: the target a Verus run compiles for unless it passes `--target`
    // (recorded in a Verus sidecar's `cfg` line).
    let host = std::env::var("TARGET").expect("TARGET");
    println!("cargo:rustc-env=FIP_PRELINT_HOST={host}");
    // The pinned toolchain, read from `rust-toolchain.toml` (its only pin site): the
    // default of `FIP_PRELINT_TOOLCHAIN` in `cargo-fip-prelint` and the driver tests.
    let pin = std::fs::read_to_string("rust-toolchain.toml").expect("read rust-toolchain.toml");
    let channel = pin
        .lines()
        .find_map(|l| {
            let (k, v) = l.split_once('=')?;
            (k.trim() == "channel").then(|| v.trim().trim_matches('"').to_string())
        })
        .expect("`channel = \"..\"` in rust-toolchain.toml");
    println!("cargo:rustc-env=FIP_PRELINT_DEFAULT_TOOLCHAIN={channel}");
    println!("cargo:rerun-if-changed=rust-toolchain.toml");
    println!("cargo:rerun-if-changed=build.rs");
}
