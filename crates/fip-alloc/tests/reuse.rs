// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! FP²'s `reverse-acc` written with `refill`: every `Cons` cell of the input becomes a
//! `Cons` cell of the output. Checked with allocation counts against a copying control.

use fip_alloc::refill;
use fip_testkit::{assert_fbip, assert_fip, measure};

fip_testkit::install!();

enum List {
    Nil,
    Cons(u32, Box<List>),
}

fn build(n: u32) -> List {
    let mut acc = List::Nil;
    for i in 0..n {
        acc = List::Cons(i, Box::new(acc));
    }
    acc
}

/// In-place reverse: the matched cell is refilled with the accumulator.
fn reverse(xs: List) -> List {
    let mut acc = List::Nil;
    let mut cur = xs;
    while let List::Cons(x, cell) = cur {
        let (cell, tail) = refill(cell, acc);
        acc = List::Cons(x, cell);
        cur = tail;
    }
    acc
}

/// Control: allocates a fresh cell per element and frees the input cells.
fn reverse_copying(xs: List) -> List {
    let mut acc = List::Nil;
    let mut cur = xs;
    while let List::Cons(x, tail) = cur {
        acc = List::Cons(x, Box::new(acc));
        cur = *tail;
    }
    acc
}

fn to_vec(xs: &List) -> Vec<u32> {
    let mut out = Vec::new();
    let mut cur = xs;
    while let List::Cons(x, t) = cur {
        out.push(*x);
        cur = t;
    }
    out
}

/// Iterative drop, so long lists do not overflow the stack.
fn free(xs: List) {
    let mut cur = xs;
    while let List::Cons(_, t) = cur {
        cur = *t;
    }
}

#[test]
fn reverse_is_correct() {
    let r = reverse(build(5));
    assert_eq!(to_vec(&r), vec![0, 1, 2, 3, 4]);
    free(r);
}

#[test]
fn reverse_is_fip() {
    let xs = build(100_000);
    let r = assert_fip!(reverse(xs));
    assert_eq!(to_vec(&r).len(), 100_000);
    free(r);
}

#[test]
fn copying_control_allocates_and_frees_per_element() {
    let xs = build(1_000);
    let (r, s) = measure(|| reverse_copying(xs));
    assert_eq!((s.allocs, s.frees), (1_000, 1_000));
    free(r);
}

#[test]
fn freeing_is_fbip_not_fip() {
    let xs = build(10);
    assert_fbip!(free(xs));
}

#[test]
fn refill_reuses_the_same_block() {
    let cell = Box::new(1_u64);
    let addr = std::ptr::from_ref::<u64>(&cell).addr();
    let (cell, prev) = assert_fip!(refill(cell, 2));
    assert_eq!((prev, *cell), (1, 2));
    assert_eq!(std::ptr::from_ref::<u64>(&cell).addr(), addr);
}
