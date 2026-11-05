// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: a `fip_fn!` value has the same `Certified<N, _>` type in the plain build and
//! under Verus (decision 2026-11-06-redesign-verus-allocates, section 4). `just
//! verify-compose` compiles this file with plain `rustc` and verifies it with Verus;
//! each annotated type below fails one of the two builds (E0308) if the builds
//! disagree, and a mutant with a wrong `N` must fail both.
//!
//! - a closure: `N` scanned from the body (here 1, one `Box::new`), in both builds;
//! - `fip_fn!(bound <= K, path)`: `Certified<K, _>` in both builds (here `K` = 2 for a
//!   function certified with 0);
//! - a struct field typed `Certified<N, C>`, filled from a closure.
//!
//! Not here: `fip_fn!(path)` without `bound`, which is `Certified<N, _>` in the plain
//! build and `Certified<0, _>` under Verus (documented on `fip_fn!`).
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
extern crate alloc;

use alloc::boxed::Box;
use fip_macros::{fip, fip_fn};
use fip_strict::Certified;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[fip(strict = true)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == x / 2,
))]
pub fn halve(x: u32) -> u32 {
    x / 2
}

/// A certified callable held in a field: the field's type names the bound.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Held<C> {
    pub step: Certified<1, C>,
}

#[cfg_attr(verus_keep_ghost, verus_spec())]
pub fn types_agree() {
    let boxing: Certified<1, _> = fip_fn!(|x: u32| Box::new(x));
    let limited: Certified<2, _> = fip_fn!(bound <= 2, halve);
    let held = Held {
        step: fip_fn!(|x: u32| Box::new(x)),
    };
    let _ = (boxing, limited, held);
}
