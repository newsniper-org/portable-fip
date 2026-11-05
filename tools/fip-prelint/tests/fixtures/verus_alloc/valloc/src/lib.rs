// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Allocation bounds proved by Verus (`allocates`, `-V alloc-check`; decision
//! 2026-11-06-redesign-verus-allocates, phase 4). The sidecar records each listed
//! function's bound; the driver takes a literal bound in place of its own count only
//! where its count is not a finite number at most the bound, for a non-generic function
//! without `requires`. Frees, panics and recursion stay the driver's.

#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Proved 0, counted 0: passes either way.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == a / 2,
    allocates 0
))]
pub fn zero(a: u32) -> u32 {
    a / 2
}

/// Proved 1, counted 1: the driver's count is kept. Its box is freed: an error for
/// `#[fip]` (frees are never taken from Verus).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == 1,
    allocates 1
))]
pub fn one() -> u32 {
    let b = Box::new(1u32);
    *b
}

/// Two calls of `one` in a loop: the driver counts `∞` (a call in a loop), Verus
/// proves 2, so the count is 2 and `n = 2` holds; the frees stay reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == 2,
    allocates 2
))]
pub fn twice() -> u32 {
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            s == i,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        s = s + one();
        i = i + 1;
    }
    s
}

/// A bound linear in a parameter is recorded (`0+1*n`) but not evaluated: the
/// driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == n,
    allocates n as nat
))]
pub fn times(n: u32) -> u32 {
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= n,
            s == i,
            allocated() <= i as nat,
        decreases n - i,
    ))]
    while i < n {
        s = s + one();
        i = i + 1;
    }
    s
}

/// With a `requires`: the fork assumes the bound only under it, which a caller Verus
/// did not verify may break, so the driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        k <= 2,
    ensures
        r == k,
    allocates 2
))]
pub fn upto(k: u32) -> u32 {
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= k,
            k <= 2,
            s == i,
            allocated() <= i as nat,
        decreases k - i,
    ))]
    while i < k {
        s = s + one();
        i = i + 1;
    }
    s
}

/// Generic: the Verus premise `T: Copy` of the drop is not re-established per instance,
/// so the driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == 2,
    allocates 2
))]
pub fn twice_with<T: Copy>(x: T) -> u32 {
    let _keep = x;
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            s == i,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        s = s + one();
        i = i + 1;
    }
    s
}

/// A caller of `twice`: its count is `twice`'s, 2 (from the proof), with no proof of
/// its own.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
pub fn use_twice() -> u32 {
    twice()
}
