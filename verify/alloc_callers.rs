// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: verified callers bound their allocations through `fip_core`'s `allocates`
//! clauses (decision 2026-11-06-redesign-verus-allocates, phase 2). Every function
//! here is `allocates 0` and calls one `fip_core` function with a `Copy` closure that
//! is itself `allocates 0` (`DropFreeFn` is `Copy` under Verus).
//!
//! `map_in_place`, `compact` and `compact_map` are bounded by the sum of their
//! callbacks' `call_allocates` (`fip_core::spec::map_allocs` and friends); the lemmas
//! of `fip_core::spec::group_allocs_zero` turn "every call allocates nothing" into a
//! zero sum (without them the three sum-bounded callers fail, measured 2026-11-06).
//! `dedup_by` and `map_in_place_st` require every call to allocate nothing.
//!
//! Verus-only (`verus!` syntax, verified by `just verify-compose` against the Verus
//! builds of `fip_strict` and `fip_core`); not in the upstream strip gate, since it
//! states nothing but allocation bounds. `just verify-negative` checks that an
//! allocating closure and a closure without a bound are rejected.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
extern crate alloc;

use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

broadcast use fip_core::spec::group_allocs_zero;

/// A closure with a precondition.
pub fn incremented(xs: &mut [u8]) -> (h: u8)
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> old(xs)@[i] < 100,
    allocates 0
{
    fip_core::map_in_place(xs, 0, |v: u8| -> (r: u8) requires v < 100 allocates 0 { v + 1 })
}

/// A closure capturing a reference (`Copy`).
pub fn clamped(xs: &mut [u8], k: &u8) -> (h: u8)
    allocates 0
{
    fip_core::map_in_place(xs, 0, |v: u8| -> (r: u8) allocates 0 { if v < *k { v } else { *k } })
}

pub fn bumped(x: &mut u64) -> (h: u64)
    requires
        *old(x) < 100,
    ensures
        *final(x) == *old(x) + 1,
    allocates 0
{
    fip_core::update(x, 0, |v: u64| -> (r: u64) requires v < 100 ensures r == v + 1 allocates 0 { v + 1 })
}

/// Element type with drop glue (`Box`): vstd's `AllocFreeDrop` impl for `Box<u8>`.
pub fn swapped(xs: &mut [Box<u8>])
    requires
        old(xs)@.len() == 2,
    allocates 0
{
    fip_core::swap(xs, 0, 1);
}

pub fn evens(xs: &mut [u32]) -> (n: usize)
    allocates 0
{
    fip_core::compact(xs, |v: &u32| -> (r: bool) allocates 0 { *v % 2 == 0 })
}

pub fn halved_odds(xs: &mut [u32]) -> (r: (usize, u32))
    allocates 0
{
    fip_core::compact_map(xs, 0, |v: u32| -> (r: (u32, bool)) allocates 0 { (v / 2, v % 2 == 1) })
}

pub fn deduped(xs: &mut [u32]) -> (n: usize)
    allocates 0
{
    fip_core::dedup_by(xs, |a: &u32, b: &u32| -> (r: bool) allocates 0 { *a == *b })
}

pub fn kept_state(xs: &mut [u32]) -> (r: (u32, u32))
    allocates 0
{
    fip_core::map_in_place_st(xs, 0, 0u32, |s: u32, x: u32| -> (r: (u32, u32)) allocates 0 { (s, x) })
}

} // verus!
