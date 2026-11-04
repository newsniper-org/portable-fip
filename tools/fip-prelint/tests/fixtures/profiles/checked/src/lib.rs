// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `[profile.release.package.checked] overflow-checks = true`: the overflow check of
//! `a + b` stays under `--release`; the debug assertion does not.

/// `a + b`: an overflow check in dev and in release.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

/// `debug_assert!`: a panic path in dev only.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
pub fn positive(x: u32) -> u32 {
    debug_assert!(x > 0);
    x
}
