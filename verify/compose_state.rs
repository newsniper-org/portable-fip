// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: verified callers of the state-passing combinators use their specifications.
//! `fip_core` is the Verus build exported by `just verify-core`, so its
//! `map_st_by_post` / `compact_map_st_by_post` postconditions are visible here.
//!
//! The counter case is Y4's `fip_map!` example (a closure capturing a counter, state
//! 10, elements `[11, 12, 13]`), with the state passed explicitly: the caller proves
//! the final state and every element from the postcondition alone.
//! `just verify-negative` checks that claiming final state 14 is rejected.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
#[cfg(verus_keep_ghost)]
use fip_core::spec::state::{compact_map_st_by_post, map_st_by_post};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Counter step: the next count, which also becomes the element (saturating at 1000
/// so the step has no precondition).
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r.0 == if c < 1000 { (c + 1) as u32 } else { c },
        r.1 == r.0,
))]
pub fn tick(c: u32, _x: u32) -> (u32, u32) {
    let n = if c < 1000 { c + 1 } else { c };
    (n, n)
}

#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        old(xs)@ == seq![0u32, 0u32, 0u32],
    ensures
        final(xs)@ == seq![11u32, 12u32, 13u32],
        r == 13,
))]
pub fn counter(xs: &mut [u32]) -> u32 {
    let (c, _hole) = fip_core::map_in_place_st(xs, 0, 10, tick);
    proof! {
        let ss = choose|ss: Seq<u32>| map_st_by_post(old(xs)@, xs@, tick, 10u32, c, ss);
        assert(xs@[0] == 11 && xs@[1] == 12 && xs@[2] == 13);
        assert(xs@ =~= seq![11u32, 12u32, 13u32]);
    }
    c
}

/// Counts odd elements in the state; elements are kept unchanged, the odd ones kept.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r.0 == if x % 2 == 1 && c < 1000 { (c + 1) as u32 } else { c },
        r.1 == x,
        r.2 == (x % 2 == 1),
))]
pub fn count_odd(c: u32, x: u32) -> (u32, u32, bool) {
    let odd = x % 2 == 1;
    (if odd && c < 1000 { c + 1 } else { c }, x, odd)
}

#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        old(xs)@ == seq![1u32, 2u32, 3u32],
    ensures
        r == 2,
))]
pub fn odd_count(xs: &mut [u32]) -> u32 {
    let (_n, odd, _hole) = fip_core::compact_map_st(xs, 0, 0, count_odd);
    proof! {
        let (ss, ys, ks, idx, pos) = choose|ss: Seq<u32>, ys: Seq<u32>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>|
            compact_map_st_by_post(old(xs)@, xs@, _n as int, count_odd, 0u32, odd, ss, ys, ks, idx, pos);
        assert(ys[0] == 1 && ys[1] == 2 && ys[2] == 3);
    }
    odd
}
