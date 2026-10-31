// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `strict = true` cases that must compile, with their allocation behaviour measured.

#![forbid(unsafe_code)] // generated certificates still compile; hand-written ones could not
#![allow(
    clippy::many_single_char_names,
    clippy::needless_pass_by_value,
    clippy::unnecessary_box_returns
)]

use fip_macros::{fip, fip_fn};
use fip_strict::FipFn;
use fip_testkit::{assert_fip, assert_fip_n};

fip_testkit::install!();

/// Calls only the audited `core` table and certified `fip-core` / `fip-alloc` functions.
#[fip(strict = true)]
fn rotate3(a: &mut u32, b: &mut u32, c: &mut u32) -> u32 {
    core::mem::swap(a, b);
    std::mem::swap(b, c);
    let old = fip_core::replace(a, 0);
    let mut xs = [1_u8, 2];
    fip_core::swap(&mut xs, 0, 1);
    core::hint::black_box(old)
}

/// One allocation site, certified with bound 1.
#[fip(1, strict = true)]
fn boxed(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Bound 2: two calls to a bound-1 function, outside loops.
#[fip(2, strict = true)]
fn two_boxes(x: u32) -> (Box<u32>, Box<u32>) {
    (boxed(x), boxed(x + 1))
}

/// A bound-0 callee may be called in a loop.
#[fip(strict = true)]
fn sum_rotations(n: u32) -> u32 {
    let (mut a, mut b, mut c) = (1, 2, 3);
    let mut s = 0;
    for _ in 0..n {
        s += rotate3(&mut a, &mut b, &mut c);
    }
    s
}

/// Reuses a heap cell through the certified `fip_alloc::refill`.
#[fip(strict = true)]
fn reuse(cell: Box<u32>, v: u32) -> (Box<u32>, u32) {
    fip_alloc::refill(cell, v)
}

/// A counter with strict methods.
pub struct Counter {
    n: u32,
}

impl Counter {
    /// Strict method; its certificate is an associated constant.
    #[fip(strict = true)]
    pub fn bump(&mut self) -> u32 {
        let old = core::mem::replace(&mut self.n, 0);
        self.n = old + 1;
        old
    }

    /// Strict associated function calling a strict method by path.
    #[fip(strict = true)]
    pub fn bump_twice(c: &mut Counter) -> u32 {
        Counter::bump(c);
        Self::bump(c)
    }
}

/// Higher-order: `keep` is a certified callable with declared bound 0, called in a loop.
#[fip(strict = true, param(keep = 0))]
fn count_kept<F>(xs: &[u8], keep: F) -> usize
where
    F: for<'a> FipFn<(&'a u8,), Output = bool>,
{
    let mut n = 0;
    let mut i = 0;
    while i < <[u8]>::len(xs) {
        if keep.call((&xs[i],)) {
            n += 1;
        }
        i += 1;
    }
    n
}

/// Higher-order with a non-zero declared bound, called once (not in a loop).
#[fip(1, strict = true, param(make = 1))]
fn make_once<F>(make: F, x: u32) -> Box<u32>
where
    F: FipFn<(u32,), Output = Box<u32>>,
{
    FipFn::call(&make, (x,))
}

#[test]
fn strict_functions_run_with_their_bounds() {
    let (mut a, mut b, mut c) = (1, 2, 3);
    assert_eq!(assert_fip!(rotate3(&mut a, &mut b, &mut c)), 2);
    assert_eq!((a, b, c), (0, 3, 1));
    assert_eq!(*assert_fip_n!(1, boxed(7)), 7);
    let (x, y) = assert_fip_n!(2, two_boxes(1));
    assert_eq!((*x, *y), (1, 2));
    assert_fip!(sum_rotations(10));
    let cell = Box::new(1);
    let (cell, prev) = assert_fip!(reuse(cell, 2));
    assert_eq!((*cell, prev), (2, 1));
    let mut ctr = Counter { n: 5 };
    assert_eq!(assert_fip!(Counter::bump_twice(&mut ctr)), 6);
}

#[test]
fn certified_closures_and_declared_parameter_bounds() {
    let gt1 = fip_fn!(|v: &u8| *v > 1);
    assert_eq!(assert_fip!(count_kept(&[0, 1, 2, 3], gt1)), 2);
    let threshold = 2_u8;
    let ge = fip_fn!(move |v: &u8| *v >= threshold);
    assert_eq!(count_kept(&[0, 1, 2, 3], ge), 2);
    let mk = fip_fn!(|x: u32| Box::new(x));
    assert_eq!(*assert_fip_n!(1, make_once(mk, 9)), 9);
    // A certified closure calling a strict function.
    let via = fip_fn!(|x: u32| boxed(x));
    assert_eq!(*make_once(via, 4), 4);
}
