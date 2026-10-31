// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Runtime checks next to the proofs: results agree with `std` on many generated
//! inputs, and every function runs without touching the heap.

use fip_testkit::assert_fip;

fip_testkit::install!();

/// Deterministic pseudo-random inputs (xorshift), small values so runs repeat.
fn inputs() -> impl Iterator<Item = Vec<u8>> {
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    (0..2000).map(move |k| {
        let len = k % 40;
        (0..len)
            .map(|_| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                u8::try_from(s % 4).unwrap_or(0)
            })
            .collect()
    })
}

#[test]
fn compact_matches_std_retain() {
    for v in inputs() {
        let mut expected = v.clone();
        expected.retain(|x| x % 2 == 0);
        let mut xs = v.clone();
        let n = assert_fip!(fip_core::compact(&mut xs, |x| x % 2 == 0));
        assert_eq!(&xs[..n], &expected[..]);
        let mut all = xs.clone();
        all.sort_unstable();
        let mut orig = v;
        orig.sort_unstable();
        assert_eq!(all, orig, "not a permutation");
    }
}

#[test]
fn dedup_by_matches_std_dedup_by() {
    for v in inputs() {
        let mut expected = v.clone();
        // std calls `same(candidate, kept)`; ours calls `same(kept, candidate)`.
        expected.dedup_by(|cand, kept| kept.abs_diff(*cand) <= 1);
        let mut xs = v.clone();
        let n = assert_fip!(fip_core::dedup_by(&mut xs, |kept, cand| kept
            .abs_diff(*cand)
            <= 1));
        assert_eq!(&xs[..n], &expected[..], "input {v:?}");
        let mut all = xs.clone();
        all.sort_unstable();
        let mut orig = v;
        orig.sort_unstable();
        assert_eq!(all, orig, "not a permutation");
    }
}

#[test]
fn compact_map_matches_map_then_filter() {
    for v in inputs() {
        let expected: Vec<u8> = v
            .iter()
            .map(|x| (x * 3, x % 2 == 1))
            .filter(|(_, k)| *k)
            .map(|(y, _)| y)
            .collect();
        let mut all_mapped: Vec<u8> = v.iter().map(|x| x * 3).collect();
        let mut xs = v.clone();
        let (n, hole) = assert_fip!(fip_core::compact_map(&mut xs, 0, |x| (x * 3, x % 2 == 1)));
        assert_eq!(hole, 0);
        assert_eq!(&xs[..n], &expected[..]);
        all_mapped.sort_unstable();
        xs.sort_unstable();
        assert_eq!(xs, all_mapped, "not a permutation of the mapped values");
    }
}

#[test]
fn heap_values_are_moved_not_cloned() {
    // Elements owning heap memory: compact_map must move them, so the measured
    // region allocates and frees nothing even though the closure rebuilds values.
    let mut xs: Vec<Box<u32>> = (0..64).map(Box::new).collect();
    let hole = Box::new(0);
    let (n, hole) = assert_fip!(fip_core::compact_map(&mut xs, hole, |b| {
        let keep = *b % 3 == 0;
        (b, keep)
    }));
    assert_eq!(*hole, 0);
    assert_eq!(n, 22);
    assert!(xs[..n].iter().all(|b| **b % 3 == 0));
    let n = assert_fip!(fip_core::dedup_by(&mut xs[..n], |a, b| **a / 10 == **b / 10));
    assert_eq!(n, 7);
}

#[test]
fn other_functions_are_allocation_free() {
    let mut xs = [5_u32, 4, 3, 2, 1];
    assert_fip!(fip_core::swap(&mut xs, 0, 4));
    let hole = assert_fip!(fip_core::map_in_place(&mut xs, 0, |v| v + 1));
    assert_eq!((xs, hole), ([2, 5, 4, 3, 6], 0));
    let mut slot = 1_u32;
    assert_eq!(assert_fip!(fip_core::replace(&mut slot, 2)), 1);
    assert_eq!(assert_fip!(fip_core::update(&mut slot, 0, |v| v * 7)), 0);
    assert_eq!(slot, 14);
}
