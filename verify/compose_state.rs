// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: verified callers of the state-passing combinators use their specifications.
//! `fip_core` is the Verus build exported by `just verify-core`, so its `spec::state`
//! predicates are visible here.
//!
//! - `counter`: a downstream project's `fip_map!` example (a closure capturing a counter, state 10,
//!   elements `[11, 12, 13]`), with the state passed explicitly; the caller names the
//!   trace with `map_st_by_trace` instead of choosing one.
//! - `number_from_11` / `number_from_11_strict`: a counter step that would overflow
//!   without a bound (`tick_checked` requires the count below 1000) on a slice of any
//!   length below 990. The caller states the invariant `c == 10 + k` (count before call
//!   `k`) and gets it back along the trace; the strict form passes `tick_checked` as
//!   `fip_fn!(tick_checked)`, so `FipFn::pre` / `post` are its `requires` / `ensures`.
//! - `number_from_11_closure`: the same step as a closure in `fip_fn!` carrying a
//!   `verus_spec` attribute, which `fip_fn!` keeps on the closure: `pre` / `post` are
//!   the closure's `requires` / `ensures`.
//! - `doubled_stateless` / `quadrupled` / `numbered_doubled`: the adapters
//!   `fip_strict::Stateless` (a one-argument step that keeps the state),
//!   `fip_strict::Compose` and `fip_strict::Then` (two state steps; the counter
//!   closure certified with `panic_macros = false`), whose `pre` / `post` are built
//!   from the wrapped closures' specifications.
//! - `odd_count` / `keep_odd`: the same for `compact_map_st`, naming the witnesses with
//!   `compact_map_st_by_witnesses`; `keep_odd`'s count is bounded by the invariant `c <= k`.
//!
//! Allocation (the Verus fork's `allocates`, checked with `-V alloc-check`): the step
//! functions and every `fip_fn!` closure carry `allocates 0`, which Verus proves. The
//! callers of `fip_core` carry none yet: Verus refuses `allocates` on a caller of a
//! function without an `allocates` specification ("cannot bound the allocations of
//! this call", measured 2026-11-06), and `fip_core` / `fip_strict` get theirs in
//! phases 2 and 3 of decision 2026-11-06-redesign-verus-allocates (then the callers get
//! `allocates 0` and the adapter hints of its section 4).
//!
//! `just verify-negative` checks that wrong final claims, a missing invariant, an
//! invariant the step does not preserve, a closure without its spec attribute, a
//! closure whose body breaks its `ensures`, wrong claims through the adapters and an
//! allocation in a step or closure bounded by `allocates 0` are rejected.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
#[cfg(verus_keep_ghost)]
use fip_core::spec::state::{
    compact_map_st_by_inv, compact_map_st_by_witnesses, map_st_by_inv, map_st_by_trace,
    map_st_fip_inv, map_st_fip_trace, st_trace_inv,
};
use fip_macros::fip;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Counter step: the next count, which also becomes the element (saturating at 1000
/// so the step has no precondition).
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r.0 == if c < 1000 { (c + 1) as u32 } else { c },
        r.1 == r.0,
    allocates 0
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
        let ss = map_st_by_trace(old(xs)@, xs@, tick, 10u32, c);
        assert(xs@[0] == 11 && xs@[1] == 12 && xs@[2] == 13);
        assert(ss =~= seq![10u32, 11u32, 12u32, 13u32]);
        assert(xs@ =~= seq![11u32, 12u32, 13u32]);
    }
    c
}

/// Counter step without saturation: the caller keeps the count below 1000. Strict, so
/// its generated certificate bounds the `Certified` value in `number_from_11_strict`.
#[fip(strict = true)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        c < 1000,
    ensures
        r.0 == c + 1,
        r.1 == r.0,
    allocates 0
))]
pub fn tick_checked(c: u32, _x: u32) -> (u32, u32) {
    (c + 1, c + 1)
}

/// Numbers a slice of any length below 990 from 11. `tick_checked` needs the count
/// below 1000 on every call; the invariant `c == 10 + k` guarantees it.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        old(xs)@.len() < 990,
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|k: int| 0 <= k < final(xs)@.len() ==> final(xs)@[k] == 11 + k,
        r == 10 + old(xs)@.len(),
))]
pub fn number_from_11(xs: &mut [u32]) -> u32 {
    proof! { assert(map_st_by_inv(old(xs)@, tick_checked, 10u32, |k: int, c: u32| c == 10 + k)); }
    let (c, _hole) = fip_core::map_in_place_st(xs, 0, 10, tick_checked);
    proof! {
        let ss = map_st_by_trace(old(xs)@, xs@, tick_checked, 10u32, c);
        assert(st_trace_inv(ss, |k: int, c: u32| c == 10 + k));
        assert(ss[old(xs)@.len() as int] == c);
        assert forall|k: int| 0 <= k < xs@.len() implies xs@[k] == 11 + k by {
            assert(ss[k] == 10 + k);
        };
    }
    c
}

/// `number_from_11` through `fip_core::strict::map_in_place_st`: `tick_checked` as a
/// `FipFn` value (`fip_fn!(tick_checked)`, a `Certified` whose `pre` / `post` are the
/// function's `requires` / `ensures`), with the allocation bound of its generated
/// certificate in the plain build (`Certified<0, _>` under Verus, which reads no
/// certificate) and no `unsafe` here.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        old(xs)@.len() < 990,
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|k: int| 0 <= k < final(xs)@.len() ==> final(xs)@[k] == 11 + k,
        r == 10 + old(xs)@.len(),
))]
pub fn number_from_11_strict(xs: &mut [u32]) -> u32 {
    let f = fip_macros::fip_fn!(tick_checked);
    proof! { assert(map_st_fip_inv(old(xs)@, f, 10u32, |k: int, c: u32| c == 10 + k)); }
    let (c, _hole) = fip_core::strict::map_in_place_st(xs, 0, 10, f);
    proof! {
        let ss = map_st_fip_trace(old(xs)@, xs@, f, 10u32, c);
        assert(st_trace_inv(ss, |k: int, c: u32| c == 10 + k));
        assert(ss[old(xs)@.len() as int] == c);
        assert forall|k: int| 0 <= k < xs@.len() implies xs@[k] == 11 + k by {
            assert(ss[k] == 10 + k);
        };
    }
    c
}

/// `number_from_11_strict` with a closure instead of a named function: `fip_fn!`
/// keeps the closure's `verus_spec` attribute, so the value's `pre` / `post` are the
/// closure's `requires` / `ensures`. Verus needs the closure's return type (`r: T =>`
/// here, or `-> T`).
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        old(xs)@.len() < 990,
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|k: int| 0 <= k < final(xs)@.len() ==> final(xs)@[k] == 11 + k,
        r == 10 + old(xs)@.len(),
))]
pub fn number_from_11_closure(xs: &mut [u32]) -> u32 {
    let f = fip_macros::fip_fn!(
        bound <= 0,
        #[cfg_attr(verus_keep_ghost, verus_spec(r: (u32, u32) =>
            requires
                c < 1000,
            ensures
                r.0 == c + 1,
                r.1 == r.0,
            allocates 0
        ))]
        |c: u32, _x: u32| (c + 1, c + 1)
    );
    proof! { assert(map_st_fip_inv(old(xs)@, f, 10u32, |k: int, c: u32| c == 10 + k)); }
    let (c, _hole) = fip_core::strict::map_in_place_st(xs, 0, 10, f);
    proof! {
        let ss = map_st_fip_trace(old(xs)@, xs@, f, 10u32, c);
        assert(st_trace_inv(ss, |k: int, c: u32| c == 10 + k));
        assert(ss[old(xs)@.len() as int] == c);
        assert forall|k: int| 0 <= k < xs@.len() implies xs@[k] == 11 + k by {
            assert(ss[k] == 10 + k);
        };
    }
    c
}

/// Doubles every element through `fip_strict::Stateless`: a one-argument specified
/// closure as a state-passing step that keeps the state (7 here).
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        forall|k: int| 0 <= k < old(xs)@.len() ==> old(xs)@[k] < 1000,
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|k: int| 0 <= k < final(xs)@.len() ==> final(xs)@[k] == 2 * old(xs)@[k],
        r == 7,
))]
pub fn doubled_stateless(xs: &mut [u32]) -> u32 {
    let g = fip_macros::fip_fn!(
        #[cfg_attr(verus_keep_ghost, verus_spec(r: u32 => requires x < 1000, ensures r == 2 * x, allocates 0))]
        |x: u32| x * 2
    );
    let f = fip_strict::Stateless(g);
    proof! { assert(map_st_fip_inv(old(xs)@, f, 7u32, |k: int, c: u32| c == 7 && forall|j: int| 0 <= j < old(xs)@.len() ==> old(xs)@[j] < 1000)); }
    let (c, _hole) = fip_core::strict::map_in_place_st(xs, 0, 7, f);
    proof! {
        let ss = map_st_fip_trace(old(xs)@, xs@, f, 7u32, c);
        assert(st_trace_inv(ss, |k: int, c: u32| c == 7 && forall|j: int| 0 <= j < old(xs)@.len() ==> old(xs)@[j] < 1000));
        assert(ss[old(xs)@.len() as int] == c);
    }
    c
}

/// Multiplies every element by 4 through `fip_strict::Compose` of two specified
/// closures: `post` is "some intermediate result satisfies both".
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        forall|k: int| 0 <= k < old(xs)@.len() ==> old(xs)@[k] < 250,
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|k: int| 0 <= k < final(xs)@.len() ==> final(xs)@[k] == 4 * old(xs)@[k],
))]
pub fn quadrupled(xs: &mut [u32]) {
    let d1 = fip_macros::fip_fn!(
        #[cfg_attr(verus_keep_ghost, verus_spec(r: u32 => requires x < 1000, ensures r == 2 * x, allocates 0))]
        |x: u32| x * 2
    );
    let d2 = fip_macros::fip_fn!(
        #[cfg_attr(verus_keep_ghost, verus_spec(r: u32 => requires x < 1000, ensures r == 2 * x, allocates 0))]
        |x: u32| x * 2
    );
    let _hole = fip_core::strict::map_in_place(xs, 0, fip_strict::Compose(d1, d2));
}

/// Numbers from 11 and doubles in one pass: `fip_strict::Then` runs the counter step
/// and a `Stateless` doubling step, its `post` is "some intermediate result satisfies
/// both". The counter closure is certified with `panic_macros = false`
/// (`Certified<0, _, true>`).
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        old(xs)@.len() < 990,
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|k: int| 0 <= k < final(xs)@.len() ==> final(xs)@[k] == 2 * (11 + k),
        r == 10 + old(xs)@.len(),
))]
pub fn numbered_doubled(xs: &mut [u32]) -> u32 {
    let t = fip_macros::fip_fn!(
        panic_macros = false,
        #[cfg_attr(verus_keep_ghost, verus_spec(r: (u32, u32) =>
            requires
                c < 1000,
            ensures
                r.0 == c + 1,
                r.1 == r.0,
            allocates 0
        ))]
        |c: u32, _x: u32| (c + 1, c + 1)
    );
    let d = fip_macros::fip_fn!(
        #[cfg_attr(verus_keep_ghost, verus_spec(r: u32 => requires x < 1000, ensures r == 2 * x, allocates 0))]
        |x: u32| x * 2
    );
    let f = fip_strict::Then(t, fip_strict::Stateless(d));
    proof! { assert(map_st_fip_inv(old(xs)@, f, 10u32, |k: int, c: u32| c == 10 + k)); }
    let (c, _hole) = fip_core::strict::map_in_place_st(xs, 0, 10, f);
    proof! {
        let ss = map_st_fip_trace(old(xs)@, xs@, f, 10u32, c);
        assert(st_trace_inv(ss, |k: int, c: u32| c == 10 + k));
        assert(ss[old(xs)@.len() as int] == c);
        assert forall|k: int| 0 <= k < xs@.len() implies xs@[k] == 2 * (11 + k) by {
            assert(ss[k] == 10 + k);
        };
    }
    c
}

/// Counts odd elements in the state; elements are kept unchanged, the odd ones kept.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r.0 == if x % 2 == 1 && c < 1000 { (c + 1) as u32 } else { c },
        r.1 == x,
        r.2 == (x % 2 == 1),
    allocates 0
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
    let (n, odd, _hole) = fip_core::compact_map_st(xs, 0, 0, count_odd);
    proof! {
        let (ss, ys, ks, idx, pos) = compact_map_st_by_witnesses(old(xs)@, xs@, n as int, count_odd, 0u32, odd);
        assert(ys[0] == 1 && ys[1] == 2 && ys[2] == 3);
    }
    odd
}

/// Counts odd elements without saturation: the caller keeps the count below 1000.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        c < 1000,
    ensures
        r.0 == if x % 2 == 1 { c + 1 } else { c as int },
        r.1 == x,
        r.2 == (x % 2 == 1),
    allocates 0
))]
pub fn count_odd_checked(c: u32, x: u32) -> (u32, u32, bool) {
    let odd = x % 2 == 1;
    (if odd { c + 1 } else { c }, x, odd)
}

/// Keeps the odd elements of a slice of any length below 1000 and counts them. The
/// invariant `c <= k` keeps the count below 1000 on every call.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        old(xs)@.len() < 1000,
    ensures
        r.0 <= old(xs)@.len(),
        r.1 <= old(xs)@.len(),
        forall|i: int| 0 <= i < r.0 ==> final(xs)@[i] % 2 == 1,
))]
pub fn keep_odd(xs: &mut [u32]) -> (usize, u32) {
    proof! { assert(compact_map_st_by_inv(old(xs)@, count_odd_checked, 0u32, |k: int, c: u32| c <= k)); }
    let (n, odd, _hole) = fip_core::compact_map_st(xs, 0, 0, count_odd_checked);
    proof! {
        let (ss, ys, ks, idx, pos) = compact_map_st_by_witnesses(old(xs)@, xs@, n as int, count_odd_checked, 0u32, odd);
        assert(st_trace_inv(ss, |k: int, c: u32| c <= k));
        assert(ss[old(xs)@.len() as int] == odd);
        assert forall|i: int| 0 <= i < n implies xs@[i] % 2 == 1 by {
            assert(xs@[i] == ys[idx[i]]);
        };
    }
    (n, odd)
}
