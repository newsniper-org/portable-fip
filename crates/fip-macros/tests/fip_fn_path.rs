// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `fip_fn!(path)`: certified function items (free, generic, `#[fip_impl]` methods,
//! trait-impl methods) as `FipFn` values, with the bound of their own certificate and
//! no `unsafe` at the call site; also from strict callers, and as
//! `Certified<N, fn(..)>` pointers; closures keep their (Verus) spec attributes.

#![forbid(unsafe_code)] // the macro output carries the `unsafe`, not this crate
#![allow(
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    clippy::unnecessary_box_returns
)]

use fip_macros::{fip, fip_fn};
use fip_strict::{Certified, FipBound, FipFn};
use fip_testkit::{assert_fip, assert_fip_n};

fip_testkit::install!();

mod shapes {
    use fip_macros::{fip, fip_impl, fip_trait};

    pub struct Slot<T> {
        pub v: T,
    }

    #[fip_impl]
    impl<T> Slot<T> {
        /// One allocation, certificate `__fip_strict_Slot__boxed`.
        #[fip(1, strict = true)]
        pub fn boxed(self) -> Box<T> {
            Box::new(self.v)
        }

        #[fip(strict = true)]
        pub fn get(self) -> T {
            self.v
        }
    }

    #[fip_trait]
    pub trait Step {
        #[fip(strict = true)]
        fn step(&self, x: u32) -> u32;
    }

    pub struct Ticker;

    #[fip_impl]
    impl Step for Ticker {
        #[fip(strict = true)]
        fn step(&self, x: u32) -> u32 {
            if x < 1000 { x + 1 } else { x }
        }
    }
}

use shapes::*; // the types and their `#[fip_impl]` certificates

#[fip(strict = true)]
fn tick(c: u32, _x: u32) -> (u32, u32) {
    let n = if c < 1000 { c + 1 } else { c };
    (n, n)
}

#[fip(strict = true)]
fn double(x: u32) -> u32 {
    if x < 1000 { x * 2 } else { x }
}

#[fip(1, strict = true)]
fn boxed(x: u32) -> Box<u32> {
    Box::new(x)
}

#[fip(strict = true)]
fn id<T>(x: T) -> T {
    x
}

#[fip(strict = true, param(g = 0))]
fn apply0<F: FipFn<(u32,), Output = u32>>(g: F, x: u32) -> u32 {
    g.call((x,))
}

#[fip(1, strict = true, param(g = 1))]
fn apply1<F: FipFn<(u32,), Output = Box<u32>>>(g: F, x: u32) -> Box<u32> {
    g.call((x,))
}

/// A strict caller passing a named function: it could not write the
/// `Certified::assume` line itself (no method calls, no generic callee paths).
#[fip(strict = true)]
fn number(xs: &mut [u32]) -> u32 {
    let (c, _hole) = fip_core::strict::map_in_place_st(xs, 0, 10, fip_fn!(tick));
    c
}

/// A strict caller passing a generic function instance and a free function, the
/// latter with a creation-site bound.
#[fip(strict = true)]
fn step_twice(x: u32) -> u32 {
    apply0(fip_fn!(id::<u32>), apply0(fip_fn!(bound <= 0, double), x))
}

fn bound<B: FipBound>(_: &B) -> u64 {
    B::ALLOCS
}

#[test]
fn named_functions_carry_their_certificate() {
    assert_eq!(<Certified<0, fn(u32) -> u32> as FipBound>::ALLOCS, 0);
    let d = fip_fn!(double);
    assert_eq!(assert_fip!(apply0(d, 4)), 8);
    let b = fip_fn!(boxed);
    assert_eq!(*assert_fip_n!(1, apply1(b, 9)), 9);
    // The bound is the certificate's: `boxed` is certified with 1.
    assert_eq!(bound(&fip_fn!(boxed)), 1);
    assert_eq!(bound(&fip_fn!(double)), 0);
    assert_eq!(bound(&fip_fn!(<Slot<u32>>::boxed)), 1);
}

#[test]
fn generic_and_associated_functions() {
    let g = fip_fn!(id::<u32>);
    assert_eq!(assert_fip!(apply0(g, 3)), 3);
    let s = fip_fn!(<Slot<u8>>::get);
    assert_eq!(s.call((Slot { v: 5_u8 },)), 5);
    let q = fip_fn!(<Slot<u32>>::boxed);
    assert_eq!(*q.call((Slot { v: 6_u32 },)), 6);
    let t = fip_fn!(<Ticker as Step>::step);
    assert_eq!(t.call((&Ticker, 1)), 2);
}

#[test]
fn strict_callers_pass_named_functions() {
    let mut xs = [0_u32; 3];
    assert_eq!(assert_fip!(number(&mut xs)), 13);
    assert_eq!(xs, [11, 12, 13]);
    assert_eq!(assert_fip!(step_twice(5)), 10);
}

#[test]
fn certified_function_pointers() {
    // The expected type makes `Certified::<N, _>::assume`'s argument a coercion site:
    // the function item becomes a pointer, the bound stays the certificate's.
    let table: [Certified<0, fn(u32) -> u32>; 2] = [fip_fn!(double), fip_fn!(id::<u32>)];
    let out: [u32; 2] = [table[0].call((3,)), table[1].call((3,))];
    assert_eq!(out, [6, 3]);
    let p: Certified<1, fn(u32) -> Box<u32>> = fip_fn!(boxed);
    assert_eq!(*apply1(p, 2), 2);
    // Closures without captures too.
    let c: Certified<0, fn(u32) -> u32> = fip_fn!(|x: u32| x ^ 1);
    assert_eq!(apply0(c, 2), 3);
}

#[test]
fn std_and_core_paths() {
    // Audited `core` table: bound 0; a std heap constructor: an allocation site.
    let sw = fip_fn!(core::mem::swap::<u8>);
    let (mut a, mut b) = (1_u8, 2_u8);
    sw.call((&mut a, &mut b));
    assert_eq!((a, b), (2, 1));
    let mk = fip_fn!(Box::new);
    assert_eq!(bound(&mk), 1);
    let b: Box<u32> = assert_fip_n!(1, mk.call((7,)));
    assert_eq!(*b, 7);
}

#[test]
fn spec_attributes_stay_on_the_closure() {
    // `cfg_attr(verus_keep_ghost, ..)`: a Verus specification, dropped in plain builds;
    // not part of the checked body (its `requires`/`ensures` tokens are not calls).
    let inc = fip_fn!(
        #[cfg_attr(verus_keep_ghost, verus_spec(r: u32 => requires x < 10, ensures r == x + 1))]
        |x: u32| x + 1
    );
    assert_eq!(assert_fip!(apply0(inc, 5)), 6);
    let k = 2_u32;
    let add = fip_fn!(
        #[cfg_attr(verus_keep_ghost, verus_spec(r: Box<u32> => ensures *r == x + k))]
        #[allow(clippy::unnecessary_box_returns)]
        move |x: u32| Box::new(x + k)
    );
    assert_eq!(bound(&add), 1);
    assert_eq!(*assert_fip_n!(1, apply1(add, 1)), 3);
}

#[test]
fn creation_site_bounds() {
    let f = fip_fn!(bound <= 0, |x: u32| x + 1);
    assert_eq!(bound(&f), 0);
    // A limit above the bound is accepted; the value keeps its computed bound.
    let b = fip_fn!(bound <= 3, boxed);
    assert_eq!(bound(&b), 1);
    let c = fip_fn!(
        bound <= 1_u64,
        #[cfg_attr(verus_keep_ghost, verus_spec(r: Box<u32> => ensures *r == x))]
        |x: u32| Box::new(x)
    );
    assert_eq!(*assert_fip_n!(1, apply1(c, 4)), 4);
}
