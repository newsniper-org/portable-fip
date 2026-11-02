// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Foreign function certification and exclusion (limits plan Item 3).

use fip_macros::{fip, fip_cert, fip_exclude, fip_extern};

#[fip_extern]
unsafe extern "C" {
    /// Certified with 0 allocations: passes for #[fip].
    #[fip_cert(evidence = "manual audit 2026-11-02", allocs = 0)]
    pub fn c_pure(x: i32) -> i32;

    /// Certified with 1 allocation: passes within fip(1).
    #[fip(1, evidence = "POSIX specification: single heap buffer")]
    pub fn c_alloc_one() -> *mut u8;

    /// Certified with 2 allocations: weaker than fip(1) needs.
    #[fip_cert(evidence = "specification", allocs = 2)]
    pub fn c_alloc_two() -> *mut u8;

    /// Excluded from FIP aggregation: calls contribute no events.
    #[fip_exclude(reason = "OS kernel trap")]
    pub fn c_log(msg: *const u8);

    /// Unannotated foreign function: neither certified nor excluded.
    pub fn c_mystery(x: i32) -> i32;

    /// Both certified and excluded: error.
    #[cfg_attr(fip_prelint, fip::cert(kind = "fip", n = 0, evidence = "audit"))]
    #[cfg_attr(fip_prelint, fip::exclude)]
    pub fn c_both();
}

/// 1. Certified 0-alloc foreign function: passes.
#[fip]
pub fn call_pure(x: i32) -> i32 {
    unsafe { c_pure(x) }
}

/// 2. Certified 1-alloc foreign function within budget: passes (1 allocation counted).
#[fip(1)]
pub fn call_alloc_one() -> *mut u8 {
    unsafe { c_alloc_one() }
}

/// 3. Certified foreign function weaker than caller budget: error.
#[fip(1)]
pub fn call_weaker() -> *mut u8 {
    unsafe { c_alloc_two() }
}

/// 4. Excluded foreign function: passes (0 events).
#[fip]
pub fn call_excluded(msg: *const u8) {
    unsafe { c_log(msg) }
}

/// 5. Neither certified nor excluded: specific error.
#[fip]
pub fn call_neither(x: i32) -> i32 {
    unsafe { c_mystery(x) }
}

/// 6. Both certified and excluded: error.
#[fip]
pub fn call_both() {
    unsafe { c_both() }
}

/// 7. Strict caller via certificate: passes.
#[fip(strict = true)]
pub fn call_strict(x: i32) -> i32 {
    unsafe { c_pure(x) }
}
