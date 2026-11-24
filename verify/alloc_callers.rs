// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: verified callers bound their allocations through `fip_core`'s `allocates`
//! clauses (decision 2026-11-06-redesign-verus-allocates, phase 2). Every function
//! here is `allocates 0` and calls one `fip_core` function with a closure that is
//! itself `allocates 0` and whose drop neither allocates nor deallocates (the
//! `requires` of the `Fn`-based functions: `vstd::alloc_check::bound_drop_alloc_free`
//! and `!drop_may_deallocate`, which the fork shows from the closure's captures;
//! until 2026-11-25 a bound that was `Copy` under Verus).
//!
//! `map_in_place`, `compact` and `compact_map` are bounded by the sum of their
//! callbacks' `call_allocations` (`fip_core::spec::map_allocs` and friends); the lemmas
//! of `fip_core::spec::group_allocs_zero` turn "every call allocates nothing" into a
//! zero sum (without them the three sum-bounded callers fail, measured 2026-11-06).
//! `dedup_by` and `map_in_place_st` require every call to allocate nothing.
//!
//! Verus-only (`verus!` syntax, verified by `just verify-compose` against the Verus
//! builds of `fip_strict` and `fip_core`); not in the upstream strip gate, since it
//! states nothing but allocation bounds. `just verify-negative` checks that an
//! allocating closure and a closure without a bound are rejected, and that a
//! `Certified<0, _>` wrapping a closure that allocates fails `Certified::pre`.
//!
//! Phase 3: `boxed_once` and `incremented_strict` call strict callables
//! (`fip_strict::Certified`, `fip_core::strict::map_in_place`), bounded by
//! `FipSpec::allocs`.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
extern crate alloc;

use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

broadcast use fip_core::spec::group_allocs_zero, fip_core::dealloc_spec::group_deallocs_zero;

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

/// A threshold that is not `Copy`, and has no drop glue.
pub struct Limit {
    pub at: u32,
}

/// A closure that owns a value without drop glue is not `Copy`; its drop neither
/// allocates nor deallocates (`just verify-negative`: one that owns a `Vec` is
/// refused).
pub fn below(xs: &mut [u32], limit: Limit) -> (n: usize)
    allocates 0
    deallocates 0
{
    fip_core::compact(xs, move |v: &u32| -> (r: bool) allocates 0 deallocates 0 { *v < limit.at })
}

pub fn halved_odds(xs: &mut [u32]) -> (r: (usize, u32))
    allocates 0
{
    fip_core::compact_map(xs, 0, |v: u32| -> (r: (u32, bool)) allocates 0 { (v / 2, v % 2 == 1) })
}

pub fn deduped(xs: &mut [u32]) -> (n: usize)
    allocates 0
{
    fip_core::dedup_by(xs, |a: &u32, b: &u32| -> (r: bool) allocates 0 deallocates 0 { *a == *b })
}

pub fn kept_state(xs: &mut [u32]) -> (r: (u32, u32))
    allocates 0
{
    fip_core::map_in_place_st(xs, 0, 0u32, |s: u32, x: u32| -> (r: (u32, u32)) allocates 0 deallocates 0 { (s, x) })
}

// Strict callables (phase 3): `FipFn::call` allocates at most `allocs()`, which is
// `ALLOCS` for a `Certified<ALLOCS, _>`; `Certified::pre` requires
// `call_allocations(closure, args) <= ALLOCS`. The values are wrapped by hand with the
// `unsafe` constructor that `fip_fn!` expands to.

/// A closure that allocates once, certified with 1.
pub fn boxed_once(x: u32) -> (r: Box<u32>)
    ensures
        *r == x,
    allocates 1
{
    let f = unsafe {
        fip_strict::Certified::<1, _, false>::assume(|v: u32| -> (r: Box<u32>) ensures *r == v allocates 1 deallocates 0 { Box::new(v) })
    };
    fip_strict::FipFn::call(&f, (x,))
}

/// `fip_core::strict::map_in_place` allocates at most `len * f.allocs()`, zero for a
/// `Certified<0, _>`.
pub fn incremented_strict(xs: &mut [u8]) -> (h: u8)
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> old(xs)@[i] < 100,
    allocates 0
{
    let f = unsafe {
        fip_strict::Certified::<0, _, false>::assume(|v: u8| -> (r: u8) requires v < 100 allocates 0 deallocates 0 { v + 1 })
    };
    fip_core::strict::map_in_place(xs, 0, f)
}

// Deallocation bounds (the fork's `deallocates`, 2026-11-22): `map_in_place`, `compact`
// and `compact_map` are bounded by the sum of their callbacks' `call_deallocations`
// (`fip_core::dealloc_spec`), `update` by its one call; the lemmas of
// `group_deallocs_zero` turn "no call deallocates" into a zero sum. A caller with a
// `deallocates` bound, or a `#[verifier::fip]` one, can call them.

pub fn incremented_no_free(xs: &mut [u8]) -> (h: u8)
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> old(xs)@[i] < 100,
    allocates 0
    deallocates 0
{
    fip_core::map_in_place(xs, 0, |v: u8| -> (r: u8) requires v < 100 allocates 0 deallocates 0 { v + 1 })
}

pub fn evens_no_free(xs: &mut [u32]) -> (n: usize)
    allocates 0
    deallocates 0
{
    fip_core::compact(xs, |v: &u32| -> (r: bool) allocates 0 deallocates 0 { *v % 2 == 0 })
}

pub fn halved_odds_no_free(xs: &mut [u32]) -> (r: (usize, u32))
    allocates 0
    deallocates 0
{
    fip_core::compact_map(xs, 0, |v: u32| -> (r: (u32, bool)) allocates 0 deallocates 0 { (v / 2, v % 2 == 1) })
}

pub fn bumped_no_free(x: &mut u64) -> (h: u64)
    requires
        *old(x) < 100,
    allocates 0
    deallocates 0
{
    fip_core::update(x, 0, |v: u64| -> (r: u64) requires v < 100 allocates 0 deallocates 0 { v + 1 })
}

/// A fully in-place caller with a fully in-place closure.
#[verifier::fip]
pub fn evens_fip(xs: &mut [u32]) -> (n: usize) {
    fip_core::compact(xs, #[verifier::fip] |v: &u32| -> (r: bool) { *v % 2 == 0 })
}

/// A closure that frees once per call, on a slice of two: at most two deallocations.
pub fn reboxed_pair(xs: &mut [Box<u8>], hole: Box<u8>) -> (h: Box<u8>)
    requires
        old(xs)@.len() == 2,
    deallocates 2
{
    proof {
        reveal_with_fuel(fip_core::dealloc_spec::map_deallocs, 3);
    }
    fip_core::map_in_place(xs, hole, |b: Box<u8>| -> (r: Box<u8>) allocates 1 deallocates 1 { Box::new(*b) })
}

} // verus!
