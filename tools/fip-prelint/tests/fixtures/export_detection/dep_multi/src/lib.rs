// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `fip::export` in a `cfg_attr` with several attributes: the text test missed it.
#![cfg_attr(fip_prelint, allow(dead_code), fip::export)]

/// Allocates once; non-generic, not `#[inline]`.
pub fn make(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Allocation-free; non-generic, not `#[inline]`.
pub fn twice(x: u32) -> u32 {
    x.wrapping_mul(2)
}
