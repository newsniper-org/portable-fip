// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: `#[fip(strict = true)]` composes with Verus attribute-syntax specifications.
//! The generated certificate constants are outside Verus (external); the body check is
//! compiled out under `verus_keep_ghost`; the specs still verify.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use fip_macros::fip;

#[fip(strict = true)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(a) == *old(b), *final(b) == *old(a),
))]
pub fn swap2(a: &mut u32, b: &mut u32) {
    core::mem::swap(a, b);
}

#[fip(strict = true)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(a) == *old(a), *final(b) == *old(b),
))]
pub fn swap_twice(a: &mut u32, b: &mut u32) {
    swap2(a, b);
    swap2(a, b);
}
