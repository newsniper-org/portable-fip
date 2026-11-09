// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-alloc — explicit reuse of heap cells
//!
//! In FP² a destructive match on a uniquely owned constructor yields a *reuse
//! credit* that the next constructor of the same size consumes, so the cell is
//! updated in place. Rust gives no such guarantee: dropping a `Box` and calling
//! `Box::new` may or may not return the same block. This crate makes the reuse
//! explicit instead: the matched `Box` is kept and refilled.
//!
//! - `#![no_std]`, links `alloc` (it handles `Box`), no `unsafe` token
//!   (`#![forbid(unsafe_code)]`). [`refill`] is `#[fip_macros::fip(total)]`
//!   (decision 2026-11-06-redesign-verus-allocates, phase 5): the attribute generates
//!   its strict certificate `__fip_strict_refill` and, under Verus, the contract
//!   `no_unwind allocates 0` and `#[verifier::fip]`. Depends on `fip-strict` and the
//!   proc-macro `fip-macros`.
//! - **Allocation bounds, by proof (Verus fork `-V alloc-check`).** [`refill`]
//!   carries `allocates 0`, which Verus proves under `T: fip_strict::AllocFreeDrop`
//!   (decision 2026-11-06-redesign-verus-allocates, phase 2). Frees (property F2) are
//!   not counted by `allocates`; since phase 5 the fork's `#[verifier::fip]` proves
//!   that a normal return of `refill` frees nothing (a free mutant is rejected by
//!   `just verify-negative`). Allocation-count tests (`fip-testkit`) remain as run-time
//!   evidence for both allocations and frees.
//! - Every function carries a Verus specification and is verified with
//!   `verus --no-cheating -V alloc-check`, like `fip-core`. Plain builds see the
//!   blanket-implemented marker trait `AllocFreeDrop`, so the API is unchanged.
//!
//! Use `fip-core` instead where no heap is involved: that crate cannot allocate at all.

#![no_std]
#![cfg_attr(fip_prelint, fip::export)]
#![forbid(unsafe_code)]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]

extern crate alloc;

use alloc::boxed::Box;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Puts `value` into the existing heap cell `cell` and returns the cell together with
/// its previous content. The allocation is reused; nothing is allocated or freed.
///
/// This is the Rust form of FP²'s reuse credit: match on an owned constructor, keep
/// its `Box`, and build the result in it.
///
/// ```
/// let cell = Box::new(1_u32);
/// let (cell, prev) = fip_alloc::refill(cell, 2);
/// assert_eq!((*cell, prev), (2, 1));
/// ```
///
/// `total` (decision 2026-11-06-redesign-verus-allocates, 7.1): the attribute
/// generates the certificate `__fip_strict_refill` and, under Verus, `no_unwind`,
/// `allocates 0` and `#[verifier::fip]`, which proves that a normal return frees
/// nothing (the `Box` is reused).
#[fip_macros::fip(total)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        *r.0 == value,
        r.1 == *cell,
))]
#[inline]
pub fn refill<T: fip_strict::AllocFreeDrop>(cell: Box<T>, value: T) -> (Box<T>, T) {
    let mut cell = cell;
    let mut prev = value;
    ::core::mem::swap(&mut *cell, &mut prev);
    (cell, prev)
}
