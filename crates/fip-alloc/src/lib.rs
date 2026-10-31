// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-alloc — explicit reuse of heap cells
//!
//! In FP² a destructive match on a uniquely owned constructor yields a *reuse
//! credit* that the next constructor of the same size consumes, so the cell is
//! updated in place. Rust gives no such guarantee: dropping a `Box` and calling
//! `Box::new` may or may not return the same block. This crate makes the reuse
//! explicit instead: the matched `Box` is kept and refilled.
//!
//! - `#![no_std]`, links `alloc` (it handles `Box`), no `unsafe` operation
//!   (`#![deny(unsafe_code)]`; the only `unsafe` token is the hand-written strict
//!   certificate `__fip_strict_refill`). Depends only on `fip-strict`.
//! - The functions here never allocate or free; that is checked by allocation-count
//!   tests (`fip-testkit`), not by proof.
//! - Every function carries a Verus specification and is verified with
//!   `verus --no-cheating`, like `fip-core`.
//!
//! Use `fip-core` instead where no heap is involved: that crate cannot allocate at all.

#![no_std]
#![deny(unsafe_code)]
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
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        *r.0 == value,
        r.1 == *cell,
))]
#[inline]
pub fn refill<T>(cell: Box<T>, value: T) -> (Box<T>, T) {
    let mut cell = cell;
    let mut prev = value;
    core::mem::swap(&mut *cell, &mut prev);
    (cell, prev)
}

/// Strict certificate for [`refill`] (`#[fip(strict = true)]` callers may call it).
///
/// Hand-written. Justification: the body calls only `core::mem::swap` (in the
/// audited `core` table of `fip-macros`), moves the `Box` without dropping it, and
/// does not recurse. Allocation-free behaviour is also measured
/// (`tests/reuse.rs`, `refill_reuses_the_same_block`).
#[cfg(not(verus_keep_ghost))]
#[doc(hidden)]
#[allow(
    unsafe_code,
    non_upper_case_globals,
    reason = "hand-written strict certificate"
)]
pub const __fip_strict_refill: fip_strict::Cert = unsafe { fip_strict::Cert::assume(0) };
