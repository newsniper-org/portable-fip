// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Cases the lint must accept. Each mirrors a rejected doctest in `src/lib.rs` with
//! the violation removed, so a rejection there is caused by the violation itself.

#![allow(clippy::needless_pass_by_value)]

use fip_macros::{fbip, fip};

/// Same name as a callee reached through a path or a method on another value:
/// not self-recursion.
#[fip]
fn swap(a: &mut u32, b: &mut u32) {
    core::mem::swap(a, b);
}

#[fip]
fn len(x: &[u8]) -> usize {
    x.len()
}

/// Mirrors the `Box::new` rejection: same shape, no allocation.
#[fip]
fn unboxed(x: i32) -> i32 {
    x
}

/// Mirrors the `fip(1)` loop rejection: the single allocation is outside the loop.
#[fip(1)]
fn one_box_outside_loop(n: u32) -> Box<u32> {
    let mut s = 0;
    for i in 0..n {
        s += i;
    }
    Box::new(s)
}

/// Mirrors the two-site rejection with `N = 2`.
#[fip(2)]
fn two_boxes(a: u8, b: u8) -> (Box<u8>, Box<u8>) {
    (Box::new(a), Box::new(b))
}

/// Recursion is allowed under `fbip`.
#[fbip]
fn count_down(n: u32) -> u32 {
    if n == 0 { 0 } else { count_down(n - 1) }
}

/// Ghost code (Verus) is skipped: `proof!` blocks and attributes in the body may
/// contain `.push(..)` on ghost sequences.
macro_rules! proof {
    ($($t:tt)*) => {};
}

#[fip]
fn with_ghost_code(xs: &mut [u32]) -> usize {
    let mut i = 0;
    #[allow(unused)]
    while i < xs.len() {
        proof! { idx = idx.push(i as int); }
        xs[i] += 1;
        i += 1;
    }
    i
}

/// Qualifiers and visibility in front of `fn`.
#[fip]
pub(crate) const unsafe extern "C" fn qualified(x: u32) -> u32 {
    x
}

#[test]
fn accepted_functions_behave() {
    let (mut a, mut b) = (1, 2);
    swap(&mut a, &mut b);
    assert_eq!((a, b), (2, 1));
    assert_eq!(len(&[1, 2, 3]), 3);
    assert_eq!(unboxed(4), 4);
    assert_eq!(*one_box_outside_loop(4), 6);
    let (x, y) = two_boxes(1, 2);
    assert_eq!((*x, *y), (1, 2));
    assert_eq!(count_down(10), 0);
    let mut xs = [1, 2];
    assert_eq!(with_ghost_code(&mut xs), 2);
    assert_eq!(xs, [2, 3]);
    // SAFETY: `qualified` has no safety requirements; `unsafe` is only there to test parsing.
    assert_eq!(unsafe { qualified(7) }, 7);
}
