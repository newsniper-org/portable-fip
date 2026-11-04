// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A `libc`-like dependency: foreign declarations without any FIP marks, and no
//! `fip::export`. Its declarations can only be certified or excluded by link symbol
//! from the crate that calls them.

use core::ffi::{c_char, c_int, c_long};

unsafe extern "C" {
    /// Certified by symbol in `app`.
    pub fn labs(x: c_long) -> c_long;
    /// Excluded by symbol in `app`.
    pub fn abs(x: c_int) -> c_int;
    /// Neither certified nor excluded anywhere.
    pub fn atoi(s: *const c_char) -> c_int;
}

unsafe extern "C-unwind" {
    /// Certified in `app` under `extern "C"`: another ABI, so no match.
    pub fn toupper(c: c_int) -> c_int;
}
