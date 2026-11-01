// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! What the slice holds when the closure panics, and that nothing is dropped twice or
//! leaked. These are the measurements behind the `# Panics` sections of the docs; the
//! Verus proofs say nothing about unwinding.
//!
//! `compact_panic_leaves_a_permutation` and `compact_drops_each_element_exactly_once`
//! are ported from Y4 (`fip/core/src/lib.rs` at commit 6e6e8b1).

#![forbid(unsafe_code)]

use fip_macros::fip_fn;
use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// Counts its own drops in a shared cell.
struct D<'a>(u32, &'a Cell<u32>);

impl Drop for D<'_> {
    fn drop(&mut self) {
        self.1.set(self.1.get() + 1);
    }
}

fn sorted(xs: &[u32]) -> Vec<u32> {
    let mut v = xs.to_vec();
    v.sort_unstable();
    v
}

#[test]
fn compact_panic_leaves_a_permutation() {
    let mut xs = [1, 2, 3, 4, 5, 6];
    let r = catch_unwind(AssertUnwindSafe(|| {
        fip_core::compact(&mut xs, |v| {
            assert!(*v != 4, "boom");
            v % 2 == 1
        })
    }));
    assert!(r.is_err());
    assert_eq!(sorted(&xs), [1, 2, 3, 4, 5, 6]);
    // Measured: the odd elements seen before the panic were moved to the front.
    assert_eq!(xs, [1, 3, 2, 4, 5, 6]);
}

#[test]
fn compact_drops_each_element_exactly_once() {
    let drops = Cell::new(0);
    {
        let mut xs = [D(1, &drops), D(2, &drops), D(3, &drops), D(4, &drops)];
        let n = fip_core::compact(&mut xs, |d| d.0 % 2 == 0);
        assert_eq!(n, 2);
        assert_eq!(drops.get(), 0, "compact itself drops nothing");
    }
    assert_eq!(drops.get(), 4);
}

#[test]
fn dedup_by_panic_leaves_a_permutation() {
    let mut xs = [1, 1, 2, 3, 3, 4];
    let r = catch_unwind(AssertUnwindSafe(|| {
        fip_core::dedup_by(&mut xs, |a, b| {
            assert!(*b != 3, "boom");
            a == b
        })
    }));
    assert!(r.is_err());
    assert_eq!(sorted(&xs), [1, 1, 2, 3, 3, 4]);
    assert_eq!(xs, [1, 2, 1, 3, 3, 4]);
}

#[test]
fn map_in_place_panic_leaves_hole_in_the_failing_slot() {
    let mut xs = [1, 2, 3];
    let r = catch_unwind(AssertUnwindSafe(|| {
        fip_core::map_in_place(&mut xs, 0, |v| {
            assert!(v != 2, "boom");
            v * 10
        })
    }));
    assert!(r.is_err());
    assert_eq!(xs, [10, 0, 3]);
}

#[test]
fn compact_map_panic_leaves_mapped_prefix_hole_and_rest() {
    let mut xs = [1, 2, 3, 4, 5];
    let r = catch_unwind(AssertUnwindSafe(|| {
        fip_core::compact_map(&mut xs, 0, |v| {
            assert!(v != 4, "boom");
            (v * 10, v % 2 == 1)
        })
    }));
    assert!(r.is_err());
    // Kept mapped values first, then the dropped mapped one, the hole, the rest.
    assert_eq!(xs, [10, 30, 20, 0, 5]);
}

#[test]
fn map_in_place_st_panic_leaves_hole_in_the_failing_slot() {
    let mut xs = [1, 2, 3];
    let r = catch_unwind(AssertUnwindSafe(|| {
        fip_core::map_in_place_st(&mut xs, 0, 0, |c: u32, v| {
            assert!(v != 2, "boom");
            (c + v, v * 10)
        })
    }));
    assert!(r.is_err());
    assert_eq!(xs, [10, 0, 3]);
}

#[test]
fn compact_map_st_panic_leaves_mapped_prefix_hole_and_rest() {
    let mut xs = [1, 2, 3, 4, 5];
    let r = catch_unwind(AssertUnwindSafe(|| {
        fip_core::compact_map_st(&mut xs, 0, 0, |c: u32, v| {
            assert!(v != 4, "boom");
            (c + 1, v * 10 + c, v % 2 == 1)
        })
    }));
    assert!(r.is_err());
    assert_eq!(xs, [10, 32, 21, 0, 5]);
}

#[test]
fn strict_st_variants_panic_like_the_fn_versions() {
    let mut xs = [1_u32, 2, 3];
    let r = catch_unwind(AssertUnwindSafe(|| {
        fip_core::strict::map_in_place_st(
            &mut xs,
            0,
            0,
            fip_fn!(|c: u32, v: u32| {
                assert!(v != 2, "boom");
                (c + v, v * 10)
            }),
        )
    }));
    assert!(r.is_err());
    assert_eq!(xs, [10, 0, 3]);

    let mut ys = [1_u32, 2, 3, 4, 5];
    let r = catch_unwind(AssertUnwindSafe(|| {
        fip_core::strict::compact_map_st(
            &mut ys,
            0,
            0,
            fip_fn!(|c: u32, v: u32| {
                assert!(v != 4, "boom");
                (c + 1, v * 10 + c, v % 2 == 1)
            }),
        )
    }));
    assert!(r.is_err());
    assert_eq!(ys, [10, 32, 21, 0, 5]);
}

#[test]
fn st_variants_drop_each_value_exactly_once_even_on_panic() {
    let drops = Cell::new(0);
    {
        let mut xs = [D(1, &drops), D(2, &drops), D(3, &drops)];
        let r = catch_unwind(AssertUnwindSafe(|| {
            fip_core::map_in_place_st(&mut xs, D(0, &drops), D(100, &drops), |s, d| {
                assert!(d.0 != 2, "boom");
                (s, D(d.0 * 10, d.1))
            })
        }));
        assert!(r.is_err());
        // Dropped so far: element 1's old value (replaced by `f`'s), the state and
        // element 2 inside `f` during unwinding.
        assert_eq!(drops.get(), 3);
        assert_eq!([xs[0].0, xs[1].0, xs[2].0], [10, 0, 3]);
    }
    assert_eq!(drops.get(), 6, "3 elements + 1 mapped value + hole + state");
}

/// `compact_map_st` itself drops nothing: elements, state and `hole` are moved.
#[test]
fn compact_map_st_drops_nothing_itself() {
    let drops = Cell::new(0);
    {
        let mut xs = [D(1, &drops), D(2, &drops), D(3, &drops), D(4, &drops)];
        let (n, s, hole) = fip_core::compact_map_st(&mut xs, D(0, &drops), D(7, &drops), |s, d| {
            let keep = d.0 % 2 == 1;
            (s, d, keep)
        });
        assert_eq!((n, s.0, hole.0), (2, 7, 0));
        assert_eq!(drops.get(), 0, "compact_map_st itself drops nothing");
    }
    assert_eq!(drops.get(), 6);
}
