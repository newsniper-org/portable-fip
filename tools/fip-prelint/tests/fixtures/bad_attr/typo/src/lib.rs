// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Unknown names under `fip::` are rejected (rustc itself accepts them).
#![cfg_attr(fip_prelint, fip::exprot)]

/// Typo in the function attribute.
#[cfg_attr(fip_prelint, fip::mrak(kind = "fip"))]
pub fn f(x: u32) -> u32 {
    x
}

/// Malformed mark.
#[cfg_attr(fip_prelint, fip::mark(kind = "fop"))]
pub fn g(x: u32) -> u32 {
    x
}

/// Valid mark: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn h(x: u32) -> u32 {
    x
}
