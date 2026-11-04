// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Declared stack leaves (top plan T8b) and an instance of a generic root of another
//! crate (top plan T8e).

#![cfg_attr(
    fip_prelint,
    fip::stack_leaf(
        memcpy = 64,
        evidence = "fixture declaration, not an audit: a test of the mechanism only"
    )
)]

/// Copying a 512-byte array calls `memcpy` (at opt-level 0), which this crate
/// declares a stack leaf: bounded with the declared 64 bytes. `chain::copy_big` is
/// the undeclared control.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn copy_declared(a: &[u64; 64]) -> [u64; 64] {
    *a
}

/// Instantiates the generic root `chain::generic` with `u32`: the build codegens
/// `chain::generic::<u32>` here (`-Zshare-generics=no`), and that instance is bounded.
#[inline(never)]
pub fn use_generic(x: u32) -> u32 {
    chain::generic(x)
}
