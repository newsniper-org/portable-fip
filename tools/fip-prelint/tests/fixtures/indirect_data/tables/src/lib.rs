// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A dependency that declares `fip::export`: its static table is read from the
//! evaluated initializer in the crate that loads from it.

#![cfg_attr(fip_prelint, fip::export)]

pub fn inc(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn dec(x: u32) -> u32 {
    x.wrapping_sub(1)
}

pub static EXT: [fn(u32) -> u32; 2] = [inc, dec];
