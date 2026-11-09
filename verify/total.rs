// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: `#[fip(total)]` and `#[fip(strict)]` generate the Verus contract (decision
//! 2026-11-06-redesign-verus-allocates, section 7). Under Verus's driver the macro
//! merges into the hand-written `verus_spec` (which keeps `ensures`) the `requires` of
//! `requires(..)`, `allocates N`, and for `total` `no_unwind` and
//! `#[verifier::fip(strict)]`. `just verify-compose` verifies this file with the fork
//! (`-V alloc-check`); `just verify-negative` rejects controls appended to a copy
//! (a callee that may unwind, an allocation hidden from the token scan behind a
//! hand-written certificate, a free); `just verify-upstream` verifies it with
//! upstream Verus with the macro's fork-only clauses switched off
//! (`FIP_MACROS_UPSTREAM=1`), and shows that without the switch upstream rejects it.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
extern crate alloc;

use fip_macros::fip;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// `x + 1` cannot overflow under the generated `requires x < 100`.
#[fip(total, requires(x < 100))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == x + 1,
))]
pub fn inc(x: u32) -> u32 {
    x + 1
}

/// `total` without a hand-written `requires`.
#[fip(total)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == x,
))]
pub fn same_total(x: u32) -> u32 {
    x
}

/// `strict` with a hand-written `#[verifier::fip]` and no `no_unwind`: no free, but
/// it may unwind as far as Verus knows, so a `total` caller cannot call it.
#[fip(strict)]
#[cfg_attr(verus_keep_ghost, verifier::fip)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == x,
))]
pub fn same_fip(x: u32) -> u32 {
    x
}

/// A `total` caller of `total` callees: each callee is `no_unwind`, `allocates 0` and
/// `#[verifier::fip(strict)]`, which the caller's generated contract needs (a callee
/// that is only `#[verifier::fip]` fails the strict call check: control
/// `total-nonstrict-callee` of `just verify-negative`).
#[fip(total, requires(x < 50))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == x + 1,
))]
pub fn inc_same(x: u32) -> u32 {
    inc(same_total(x))
}

/// `strict(N)`: the generated bound is the declared one.
#[fip(1, strict)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        *r == x,
))]
pub fn boxed(x: u32) -> alloc::boxed::Box<u32> {
    alloc::boxed::Box::new(x)
}

/// A `strict` caller of `same_fip` (not `no_unwind`): allowed, `strict` does not
/// generate `no_unwind`.
#[fip(strict)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == x,
))]
pub fn same_strict(x: u32) -> u32 {
    same_fip(x)
}
