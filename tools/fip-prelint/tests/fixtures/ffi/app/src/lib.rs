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

/// Marks by link symbol: they apply to every foreign declaration of the symbol,
/// here the unmarked declarations of the dependency `cdep` and of `std`.
mod by_symbol {
    use core::ffi::{c_int, c_long};

    #[fip_macros::fip_extern]
    unsafe extern "C" {
        #[fip_cert(evidence = "C standard 7.24.6.1: computes a value, no allocation", allocs = 0)]
        fn labs(x: c_long) -> c_long;
        #[fip_exclude(reason = "C standard 7.24.6.1")]
        fn abs(x: c_int) -> c_int;
        /// `std` declares it as `std::sys::io::error::unix::errno_location`.
        #[fip_exclude(reason = "returns the address of the thread's errno")]
        #[link_name = "__errno_location"]
        fn errno_location() -> *mut c_int;
        /// `cdep` declares it `extern "C-unwind"`.
        #[fip_cert(evidence = "C standard 7.4.2.2", allocs = 0)]
        fn toupper(c: c_int) -> c_int;
    }

    // Certified here and excluded in `other`: every call is an error.
    #[fip_macros::fip_extern]
    unsafe extern "C" {
        #[fip_cert(evidence = "audit", allocs = 0)]
        pub fn c_split();
        #[fip_cert(evidence = "audit", allocs = 0)]
        pub fn c_twice();
    }

    pub mod other {
        #[fip_macros::fip_extern]
        unsafe extern "C" {
            #[fip_exclude]
            pub fn c_split();
            /// Another certificate of the same symbol with other properties.
            #[fip_cert(evidence = "another audit", allocs = 1)]
            pub fn c_twice();
        }
    }
}

/// 8. A dependency's declaration certified by symbol: passes.
#[fip]
pub fn call_dep_certified(x: core::ffi::c_long) -> core::ffi::c_long {
    unsafe { cdep::labs(x) }
}

/// 9. A dependency's declaration excluded by symbol: passes.
#[fip]
pub fn call_dep_excluded(x: core::ffi::c_int) -> core::ffi::c_int {
    unsafe { cdep::abs(x) }
}

/// 10. A dependency's declaration nobody marks: the specific error, naming the symbol.
#[fip]
pub fn call_dep_neither(s: *const core::ffi::c_char) -> core::ffi::c_int {
    unsafe { cdep::atoi(s) }
}

/// 11. Marked under another ABI: no match, an error.
#[fip]
pub fn call_dep_other_abi(c: core::ffi::c_int) -> core::ffi::c_int {
    unsafe { cdep::toupper(c) }
}

/// 12. `std`'s declaration of `__errno_location` is excluded by symbol; the std
/// function without MIR on the same path is summarised (top plan 8b): passes.
#[fip]
pub fn call_std_errno() -> std::io::Error {
    std::io::Error::last_os_error()
}

/// 13. Certified on one declaration of the symbol and excluded on another: error.
#[fip]
pub fn call_split() {
    unsafe { by_symbol::c_split() }
}

/// 14. Two certificates of the symbol with different properties: error.
#[fip]
pub fn call_twice() {
    unsafe { by_symbol::other::c_twice() }
}

/// Declarations a strict caller maps a dependency's foreign function to
/// (`#[fip(strict = true, ffi(dep::sym = local::sym))]`, top plan T10.2).
pub mod mapped {
    use core::ffi::{c_int, c_long};

    #[fip_macros::fip_extern]
    unsafe extern "C" {
        /// The symbol of `cdep::labs`, same ABI.
        #[fip_cert(evidence = "C standard 7.24.6.1: computes a value, no allocation", allocs = 0)]
        pub fn labs(x: c_long) -> c_long;
        /// Another symbol with the same signature.
        #[fip_cert(evidence = "C standard 7.24.6.1: computes a value, no allocation", allocs = 0)]
        pub fn llabs(x: c_long) -> c_long;
        /// The symbol of `cdep::toupper`, declared `extern "C-unwind"` there.
        #[fip_cert(evidence = "C standard 7.4.2.2", allocs = 0)]
        pub fn toupper(c: c_int) -> c_int;
    }
}

/// 15. Strict call of a dependency's foreign function mapped to a declaration of the
/// same symbol and ABI: passes.
#[fip(strict = true, ffi(cdep::labs = mapped::labs))]
pub fn strict_dep_mapped(x: core::ffi::c_long) -> core::ffi::c_long {
    unsafe { cdep::labs(x) }
}

/// 16. Mapped to a declaration of another symbol: error at the mapping.
#[fip(strict = true, ffi(cdep::labs = mapped::llabs))]
pub fn strict_dep_other_symbol(x: core::ffi::c_long) -> core::ffi::c_long {
    unsafe { cdep::labs(x) }
}

/// 17. Mapped to a declaration of the same symbol under another ABI: error at the
/// mapping (and at the call: marks do not apply across ABIs).
#[fip(strict = true, ffi(cdep::toupper = mapped::toupper))]
pub fn strict_dep_other_abi(c: core::ffi::c_int) -> core::ffi::c_int {
    unsafe { cdep::toupper(c) }
}
