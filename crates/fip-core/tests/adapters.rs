// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `fip_strict::Stateless`, `fip_strict::Compose` and `fip_strict::Then`: certified callables built from
//! certified callables, passed to the strict combinators, also from strict code;
//! bounds and allocation behaviour measured.

#![forbid(unsafe_code)] // the adapters' `FipBound` impls live in `fip-strict`
#![allow(clippy::unnecessary_box_returns)]

use fip_macros::{fip, fip_fn};
use fip_strict::{Compose, FipBound, FipFn, Stateless, Then};
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

/// One counting step: `(c, x)` to `(c + 1, x + c + 1)`.
#[fip(strict = true)]
fn tick(c: u32, x: u32) -> (u32, u32) {
    if c < 1000 && x < 1000 {
        (c + 1, x + c + 1)
    } else {
        (c, x)
    }
}

/// A strict caller chaining two state steps with `Then` for `map_in_place_st`.
#[fip(strict = true)]
fn tick_twice_all(xs: &mut [u32]) -> u32 {
    let (c, _hole) = fip_core::strict::map_in_place_st(
        xs,
        0,
        0,
        Then(fip_fn!(tick), Stateless(fip_fn!(double))),
    );
    c
}

#[test]
fn then_chains_state_steps() {
    let mut xs = [1_u32, 2, 3];
    assert_eq!(assert_fip!(tick_twice_all(&mut xs)), 3);
    // Element k: (x + k + 1) * 2.
    assert_eq!(xs, [4, 8, 12]);
    let t = Then(fip_fn!(tick), fip_fn!(|c: u32, y: u32| (c, Box::new(y))));
    assert_eq!(bound(&t), 1);
    let (c, b) = assert_fip_n!(1, t.call((4, 10)));
    assert_eq!((c, *b), (5, 15));
}

#[test]
fn compose_maps_the_output_of_any_arity() {
    // `f` takes two arguments; `g` maps its output.
    let c = Compose(fip_fn!(|a: u32, b: u32| a ^ b), fip_fn!(boxed));
    assert_eq!(bound(&c), 1);
    let b = assert_fip_n!(1, c.call((6, 3)));
    assert_eq!(*b, 5);
    let none = Compose(fip_fn!(|| 7_u32), fip_fn!(double));
    assert_eq!(bound(&none), 0);
    assert_eq!(assert_fip!(none.call(())), 14);
}

#[fip(strict = true, panic_macros = false)]
fn halve(x: u32) -> u32 {
    x / 2
}

fn no_panic<B: FipBound>(_: &B) -> bool {
    B::NO_PANIC_MACROS
}

/// `FipBound::NO_PANIC_MACROS` of the adapters: true only if every part's is.
#[test]
fn adapters_carry_panic_strictness() {
    let strict = fip_fn!(panic_macros = false, halve);
    let plain = fip_fn!(double);
    assert!(no_panic(&strict));
    assert!(!no_panic(&plain));
    assert!(no_panic(&Stateless(fip_fn!(panic_macros = false, halve))));
    assert!(!no_panic(&Stateless(fip_fn!(double))));
    assert!(no_panic(&Compose(
        fip_fn!(panic_macros = false, halve),
        fip_fn!(panic_macros = false, |x: u32| x ^ 1)
    )));
    assert!(!no_panic(&Compose(
        fip_fn!(panic_macros = false, halve),
        fip_fn!(double)
    )));
    assert!(no_panic(&Then(
        fip_fn!(panic_macros = false, |c: u32, x: u32| (c, x)),
        Stateless(fip_fn!(panic_macros = false, halve))
    )));
    assert!(!no_panic(&Then(
        fip_fn!(tick),
        Stateless(fip_fn!(panic_macros = false, halve))
    )));
}
