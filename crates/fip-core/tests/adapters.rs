// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `fip_strict::Stateless` and `fip_strict::Compose`: certified callables built from
//! certified callables, passed to the strict combinators, also from strict code;
//! bounds and allocation behaviour measured.

#![forbid(unsafe_code)] // the adapters' `FipBound` impls live in `fip-strict`
#![allow(clippy::unnecessary_box_returns)]

use fip_macros::{fip, fip_fn};
use fip_strict::{Compose, FipBound, FipFn, Stateless};
use fip_testkit::{assert_fip, assert_fip_n};

fip_testkit::install!();

fn bound<B: FipBound>(_: &B) -> u64 {
    B::ALLOCS
}

#[fip(strict = true)]
fn double(x: u32) -> u32 {
    if x < 1000 { x * 2 } else { x }
}

#[fip(1, strict = true)]
fn boxed(x: u32) -> Box<u32> {
    Box::new(x)
}

/// A strict caller: a stateless step through `map_in_place_st`, the state untouched.
#[fip(strict = true)]
fn double_all(xs: &mut [u32]) -> u32 {
    let (c, _hole) = fip_core::strict::map_in_place_st(xs, 0, 7, Stateless(fip_fn!(double)));
    c
}

/// A strict caller composing two certified functions for a `param(g = 0)` callee.
#[fip(strict = true)]
fn quadruple_all(xs: &mut [u32]) {
    let _hole = fip_core::strict::map_in_place(
        xs,
        0,
        Compose(fip_fn!(|x: u32| x * 2), fip_fn!(|x: u32| x * 2)),
    );
}

#[test]
fn stateless_keeps_the_state() {
    let mut xs = [1_u32, 2, 3];
    assert_eq!(assert_fip!(double_all(&mut xs)), 7);
    assert_eq!(xs, [2, 4, 6]);
    let s = Stateless(fip_fn!(|x: u8| x ^ 1));
    assert_eq!(s.call(("state", 2)), ("state", 3));
    assert_eq!(bound(&s), 0);
    assert_eq!(bound(&Stateless(fip_fn!(boxed))), 1);
}

#[test]
fn compose_adds_the_bounds() {
    let mut xs = [1_u32, 2, 3];
    assert_fip!(quadruple_all(&mut xs));
    assert_eq!(xs, [4, 8, 12]);
    let c = Compose(fip_fn!(double), fip_fn!(boxed));
    assert_eq!(bound(&c), 1);
    let b = assert_fip_n!(1, c.call((5,)));
    assert_eq!(*b, 10);
    // Two allocations, nothing freed inside the call: the bounds add up.
    let two = Compose(fip_fn!(boxed), fip_fn!(|b: Box<u32>| (b, Box::new(1_u32))));
    assert_eq!(bound(&two), 2);
    let (p, q) = assert_fip_n!(2, two.call((1,)));
    assert_eq!((*p, *q), (1, 1));
}
