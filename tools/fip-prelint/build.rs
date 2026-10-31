// SPDX-License-Identifier: Apache-2.0
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
    println!("cargo:rerun-if-changed=build.rs");
}
