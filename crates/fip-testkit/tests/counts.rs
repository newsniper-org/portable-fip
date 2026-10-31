// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Tests for the counting allocator itself. If forwarding to `System` were wrong
//! (wrong layout, wrong pointer), the data-integrity tests would fail or crash.

use fip_testkit::{AllocStats, assert_fbip, assert_fip, assert_fip_n, measure};
use std::hint::black_box;

fip_testkit::install!();

#[test]
fn installed() {
    assert!(fip_testkit::is_installed());
}

#[test]
fn box_new_and_drop_are_counted_exactly() {
    let (b, s) = measure(|| black_box(Box::new(7_u64)));
    assert_eq!(
        s,
        AllocStats {
            allocs: 1,
            reallocs: 0,
            frees: 0,
            bytes_requested: 8
        }
    );
    let ((), s) = measure(|| drop(b));
    assert_eq!((s.allocs, s.frees), (0, 1));
}

#[test]
fn realloc_preserves_contents_and_is_counted() {
    let mut v: Vec<u32> = Vec::with_capacity(1);
    v.push(0xDEAD_BEEF);
    let ((), s) = measure(|| {
        for i in 1..1000 {
            v.push(i);
        }
    });
    assert!(s.reallocs >= 1, "{s:?}");
    assert_eq!(v[0], 0xDEAD_BEEF);
    assert_eq!(v[999], 999);
    assert_eq!(v.iter().skip(1).copied().sum::<u32>(), (1..1000).sum());
}

#[test]
fn zeroed_allocation_is_zero() {
    let (v, s) = measure(|| black_box(vec![0_u8; 4096]));
    assert_eq!(s.allocs, 1);
    assert!(v.iter().all(|&b| b == 0));
}

#[test]
fn other_threads_are_not_counted() {
    let ((), s) = measure(|| {
        std::thread::scope(|sc| {
            sc.spawn(|| {
                for _ in 0..100 {
                    drop(black_box(Box::new(1_u8)));
                }
            });
        });
    });
    // Spawning a thread may allocate a little on this thread; the 100 boxes on the
    // child thread must not show up.
    assert!(s.allocs < 100, "{s:?}");
}

#[test]
fn assert_fip_passes_on_in_place_code() {
    let mut xs = [5, 1, 4, 2, 3];
    let n = assert_fip!(fip_core::compact(&mut xs, |v| *v % 2 == 1));
    assert_eq!(&xs[..n], &[5, 1, 3]);
}

#[test]
#[should_panic(expected = "fip violated")]
fn assert_fip_rejects_allocation() {
    let b = assert_fip!(black_box(Box::new(1_u8)));
    drop(b);
}

#[test]
#[should_panic(expected = "fip violated")]
fn assert_fip_rejects_free() {
    let b = Box::new(1_u8);
    assert_fip!(drop(black_box(b)));
}

#[test]
fn assert_fbip_allows_free_only() {
    let b = Box::new(1_u8);
    assert_fbip!(drop(black_box(b)));
}

#[test]
#[should_panic(expected = "fbip violated")]
fn assert_fbip_rejects_allocation() {
    drop(assert_fbip!(black_box(Box::new(1_u8))));
}

#[test]
fn assert_fip_n_bounds_allocations() {
    let (a, b) = assert_fip_n!(2, (black_box(Box::new(1_u8)), black_box(Box::new(2_u8))));
    assert_eq!((*a, *b), (1, 2));
}

#[test]
#[should_panic(expected = "fip(n) violated")]
fn assert_fip_n_rejects_excess() {
    drop(assert_fip_n!(
        1,
        (black_box(Box::new(1_u8)), black_box(Box::new(2_u8)))
    ));
}
