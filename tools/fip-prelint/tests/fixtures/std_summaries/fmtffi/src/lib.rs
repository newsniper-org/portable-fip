// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Foreign calls inside std summaries (`§ffi` terms, top plan item 8b): this crate
//! certifies or excludes the foreign functions that `HashMap::new` and a lazily
//! initialised thread local reach inside `std` (its random source, paths printing to
//! stderr). The marks match by link symbol and ABI, so the summaries' foreign calls
//! get these verdicts instead of the "neither certified nor excluded" errors of
//! `fmtuse`. The evidence strings are fixture data.

use core::ffi::{c_char, c_int, c_long, c_void};

#[allow(dead_code, reason = "declarations exist only to carry the marks")]
mod sys {
    use super::{c_char, c_int, c_long, c_void};

    unsafe extern "C" {
        #[cfg_attr(fip_prelint, fip::cert(kind = "fip", n = 0, evidence = "fixture: returns a thread-local address"))]
        pub fn __errno_location() -> *mut c_int;
        #[cfg_attr(fip_prelint, fip::cert(kind = "fip", n = 0, evidence = "fixture: vDSO clock read"))]
        pub fn clock_gettime(clock: c_int, tp: *mut c_void) -> c_int;
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn syscall(num: c_long, ...) -> c_long;
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn open64(path: *const c_char, flags: c_int, ...) -> c_int;
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn read(fd: c_int, buf: *mut c_void, n: usize) -> isize;
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn write(fd: c_int, buf: *const c_void, n: usize) -> isize;
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn close(fd: c_int) -> c_int;
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn fcntl(fd: c_int, cmd: c_int, ...) -> c_int;
        #[cfg_attr(fip_prelint, fip::exclude)]
        pub fn poll(fds: *mut c_void, n: u64, timeout: c_int) -> c_int;
    }
}

std::thread_local! {
    static LAZY: core::cell::Cell<u32> = core::cell::Cell::new(u32::from(u8::MAX));
}

/// A lazily initialised thread local: its foreign calls get this crate's verdicts.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn thread_local_lazy() -> u32 {
    LAZY.with(core::cell::Cell::get)
}

/// `HashMap::new`: its foreign calls get this crate's verdicts.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn hashmap_new() -> usize {
    std::collections::HashMap::<u8, u8>::new().len()
}
