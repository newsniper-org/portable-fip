// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Callers of `ypool's sources, verified with `--import ypool`: `two_counted`,
//! `two_pages` and `two_slabs` take Verus's 2 and pass; `drain` keeps the driver's
//! `∞` (its source states `allocates 0`).

#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use ypool::{Backend, Pages, Pool};

/// Two calls of a source of another crate that states 1: Verus's 2 is taken.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn two_counted(p: &mut Pool) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        let _ = p.take_counted();
        i = i + 1;
    }
}

/// Calls of a source of another crate that states 0: the driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 0
))]
pub fn drain(p: &mut Pool, n: usize) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            allocated() == 0,
        decreases n - i,
    ))]
    while i < n {
        let _ = p.take();
        i = i + 1;
    }
}

/// Two calls of a trait-declared source of another crate, resolved.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn two_pages(b: &mut Pages) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        let _ = b.reserve();
        i = i + 1;
    }
}

/// Two calls of a generic source of another crate.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn two_slabs(b: &mut Pages) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        let _ = ypool::alloc_from(b);
        i = i + 1;
    }
}

/// Two rounds of an allocation and a free through the pool: Verus proves 2, the sources
/// state their counts (`encapsulates alloc(1, 0)` and `alloc(0, 1)`), so the count is 2
/// in place of the driver's `∞` (above the 0 of `#[fbip]`: the error names 2).
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn take_put_twice(p: &mut Pool) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        let s = p.take_counted();
        p.put(s);
        i = i + 1;
    }
}
