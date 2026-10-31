// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: `#[fip(strict = true)]` composes with Verus attribute-syntax specifications.
//! The generated certificate constants are outside Verus (external); the body check is
//! compiled out under `verus_keep_ghost`; the specs still verify. `fip_strict` is the
//! Verus build (`just verify-strict`), so `FipFn` has its `pre` / `post` specs.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use fip_macros::{fip, fip_fn};
use fip_strict::FipFn;

#[fip(strict = true)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(a) == *old(b), *final(b) == *old(a),
))]
pub fn swap2(a: &mut u32, b: &mut u32) {
    core::mem::swap(a, b);
}

#[fip(strict = true)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(a) == *old(a), *final(b) == *old(b),
))]
pub fn swap_twice(a: &mut u32, b: &mut u32) {
    swap2(a, b);
    swap2(a, b);
}

// Higher-order: a `FipFn` parameter with a declared bound, specified through
// `FipFn::pre` / `FipFn::post` (the Verus declarations of `fip-strict`).
#[fip(strict = true, param(keep = 0))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        keep.pre((&x,)),
    ensures
        keep.post((&x,), r),
))]
pub fn test_one<F: for<'a> FipFn<(&'a u32,), Output = bool>>(x: u32, keep: F) -> bool {
    keep.call((&x,))
}

// A verified caller passing a `fip_fn!` closure: the macro output declares no item,
// so Verus accepts it inside a verified body, and proves `test_one`'s precondition
// (the closure's `requires`, here none).
#[fip(strict = true)]
#[cfg_attr(verus_keep_ghost, verus_spec())]
pub fn caller(x: u32) -> bool {
    test_one(x, fip_fn!(|v: &u32| *v > 1))
}
