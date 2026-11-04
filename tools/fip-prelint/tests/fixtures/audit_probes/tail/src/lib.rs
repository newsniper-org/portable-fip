// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Probe of the 2026-11-04 soundness audit (finding 1): a callee that leaves only
//! through `become` returns to its caller; the rest of the caller stays live.
#![allow(unused, incomplete_features)]
#![feature(explicit_tail_calls)]

#[inline(never)]
pub fn id(x: usize) -> usize {
    x
}
#[inline(never)]
pub fn tail(x: usize) -> usize {
    become id(x)
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn root_tail(i: usize, a: &[u8; 4]) -> u8 {
    let j = tail(i);
    if j < 3 {
        return 0;
    }
    let b = Box::new(1u8);
    a[j & 3] + *b
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn root_tail_strict(i: usize, a: &[u8; 4]) -> u8 {
    let j = tail(i);
    a[j]
}
