// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

#![cfg_attr(fip_prelint, fip::export)]
#[cfg_attr(fip_prelint, fip::mark(fip, 0))]
pub fn marked(x: u32) -> u32 { let mut s = 0; let mut i = 0; while i < x { s += i; i += 1; } s }
pub fn plain(x: u32) -> u32 { x * 2 }
