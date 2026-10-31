// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The audited `core` table (`fip_lint_rules::CORE_TABLE`) holds only for the
//! toolchains whose `core` sources were read. This test fails on any other rustc, so
//! a toolchain bump cannot silently extend the audit: re-read the implementations
//! (`docs/decisions/2026-11-01-strict-core-table.md`) and add the version.

#[test]
fn compiling_rustc_is_covered_by_the_core_table_audit() {
    let running = env!("FIP_RUSTC_VERSION");
    assert!(
        fip_lint_rules::CORE_TABLE_AUDITED_AT.contains(&running),
        "rustc {running} is not in CORE_TABLE_AUDITED_AT {:?}: audit the `core` table entries for it first",
        fip_lint_rules::CORE_TABLE_AUDITED_AT
    );
}
