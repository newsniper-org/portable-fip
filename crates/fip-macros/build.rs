// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Records the version of the compiling rustc as `FIP_RUSTC_VERSION`, so
//! `tests/strict_toolchain.rs` can check it against the toolchains the `core` table
//! and the non-allocating constructors were audited at
//! (`fip_lint_rules::CORE_TABLE_AUDITED_AT`,
//! `fip_lint_rules::NON_ALLOCATING_CONSTRUCTORS_AUDITED_AT`).

use std::process::Command;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-env-changed=RUSTC");
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    // `rustc -V`: "rustc 1.99.1 (hash date)"; an unreadable answer records "unknown",
    // which no audit list contains, so the test fails rather than passes.
    let version = Command::new(rustc)
        .arg("-V")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.split_whitespace().nth(1).map(str::to_string))
        .unwrap_or_else(|| "unknown".to_string());
    println!("cargo::rustc-env=FIP_RUSTC_VERSION={version}");
}
