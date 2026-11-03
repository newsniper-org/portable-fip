// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Release defaults: in dev both roots have a panic path (overflow check, debug
//! assertion); under `--release` neither has one, because the build has neither check.

/// `a + b`: an overflow check exactly when the profile has overflow checks.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

/// `debug_assert!`: a panic path exactly when the profile has debug assertions.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
pub fn positive(x: u32) -> u32 {
    debug_assert!(x > 0);
    x
}
