// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A non-member dependency without `fip::export`.

/// Allocation-free, but its MIR is not used.
pub fn twice(x: u32) -> u32 {
    x.wrapping_mul(2)
}
