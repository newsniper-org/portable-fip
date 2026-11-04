// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A comment inside the `cfg_attr`: the text test missed it.
#![cfg_attr(fip_prelint, /* opt in */ fip::export)]

/// Allocates once; non-generic, not `#[inline]`.
pub fn make(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Allocation-free; non-generic, not `#[inline]`.
pub fn twice(x: u32) -> u32 {
    x.wrapping_mul(2)
}
