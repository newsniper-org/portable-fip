// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The same functions, without `fip::export`: every call into it is unknown.

/// Allocates once.
pub fn make(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Allocation-free, but not readable for the checker.
pub fn twice(x: u32) -> u32 {
    x.wrapping_mul(2)
}
