// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Foreign calls inside std summaries (`§ffi` terms): a mark on a declaration with
//! another ABI than the one std calls (`write` as `extern "system"`) does not apply,
//! and a symbol both certified and excluded is an error, as for direct calls.

use core::ffi::{c_int, c_void};

#[allow(dead_code, reason = "declarations exist only to carry the marks")]
mod sys {
    use super::{c_int, c_void};

    unsafe extern "system" {
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn write(fd: c_int, buf: *const c_void, n: usize) -> isize;
    }

    unsafe extern "C" {
        #[cfg_attr(fip_prelint, fip::cert(kind = "fip", n = 0, evidence = "fixture"))]
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn __errno_location() -> *mut c_int;
    }
}

std::thread_local! {
    static LAZY: core::cell::Cell<u32> = core::cell::Cell::new(u32::from(u8::MAX));
}

/// The stderr path of the lazy initialisation reaches `write` (ABI mismatch) and
/// `__errno_location` (both certified and excluded): errors.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn thread_local_lazy() -> u32 {
    LAZY.with(core::cell::Cell::get)
}
