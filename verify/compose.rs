// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: `#[fip]` composes with Verus attribute-syntax specifications.
//! `#[fip]` is written above `verus_spec`, as the fip-macros docs require.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use fip_macros::fip;

#[fip]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures r == n,
))]
pub fn count(n: u32) -> u32 {
    let mut i: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= n,
        decreases n - i,
    ))]
    while i < n {
        proof! { assert(i < n); }
        i += 1;
    }
    i
}

/// `requires(..)` (the precondition `fip-prelint` checks at call sites) must be a
/// conjunct of the `verus_spec` requires: `#[fip]` sees it here (above `verus_spec`)
/// and rejects any drift (negative control in `just verify-compose`).
#[fip(requires(i < xs.len()))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires i < xs@.len(),
    ensures r == xs@[i as int],
))]
pub fn at(xs: &[u8], i: usize) -> u8 {
    xs[i]
}
