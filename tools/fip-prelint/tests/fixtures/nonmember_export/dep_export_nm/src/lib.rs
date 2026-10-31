// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A non-member dependency that declares `fip::export`.
#![cfg_attr(fip_prelint, fip::export)]

/// Allocates once; non-generic, not `#[inline]`.
pub fn make(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Allocation-free; non-generic, not `#[inline]`, with a loop.
pub fn twice(x: u32) -> u32 {
    let mut s = 0u32;
    let mut i = 0;
    while i < 2 {
        s = s.wrapping_add(x);
        i += 1;
    }
    s
}
