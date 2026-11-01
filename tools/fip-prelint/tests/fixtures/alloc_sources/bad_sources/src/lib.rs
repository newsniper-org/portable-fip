// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Rejected source declarations. A crate of its own: its errors must not stop the
//! other crates of the fixture from being checked.
use core::alloc::{GlobalAlloc, Layout};

/// A FIP mark on a declared source: rejected (its body is out of scope).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
#[cfg_attr(fip_prelint, fip::alloc_source)]
pub fn marked_source(x: u32) -> u32 {
    x
}

/// `n = 0` would claim "allocation-free" without a check: rejected.
#[cfg_attr(fip_prelint, fip::alloc_source(n = 0))]
pub fn zero(x: u32) -> u32 {
    x
}

/// Unknown key: rejected.
#[cfg_attr(fip_prelint, fip::alloc_source(count = 1))]
pub fn bad_key(x: u32) -> u32 {
    x
}

/// Arguments to `free_source`: rejected.
#[cfg_attr(fip_prelint, fip::free_source(n = 1))]
pub fn bad_free(x: u32) -> u32 {
    x
}

/// Not a function: rejected.
#[cfg_attr(fip_prelint, fip::alloc_source)]
pub struct NotAFunction;

pub struct Null;

unsafe impl GlobalAlloc for Null {
    /// A FIP mark on a `GlobalAlloc` method: rejected like on a declared source.
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        core::ptr::null_mut()
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}
