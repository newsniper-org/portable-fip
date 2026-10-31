// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Declares `fip::export`: its MIR is used for verdicts downstream.
#![cfg_attr(fip_prelint, fip::export)]

/// Allocates once.
pub fn make(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Allocation-free.
pub fn twice(x: u32) -> u32 {
    x.wrapping_mul(2)
}
