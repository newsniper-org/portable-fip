// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The strict variants (`fip_core::strict`) agree with the `Fn` versions on generated
//! inputs, run without touching the heap, and are callable from strict code.

#![forbid(unsafe_code)]

use fip_macros::{fip, fip_fn};
use fip_strict::FipFn;
use fip_testkit::assert_fip;

fip_testkit::install!();

fn inputs() -> impl Iterator<Item = Vec<u8>> {
    let mut s: u64 = 0x2545_F491_4F6C_DD1D;
    (0..1000).map(move |k| {
        let len = k % 30;
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

/// A strict caller: passes its own certified parameter on to a strict `fip-core`
/// function (certificate `fip_core::strict::__fip_strict_compact`).
#[fip(strict = true, param(keep = 0))]
fn count_and_compact<F: for<'a> FipFn<(&'a u8,), Output = bool>>(xs: &mut [u8], keep: F) -> usize {
    fip_core::strict::compact(xs, keep)
}

/// A strict caller of every strict variant.
#[fip(strict = true)]
fn pipeline(xs: &mut [u8], slot: &mut u8) -> (usize, usize) {
    let _ = fip_core::strict::map_in_place(xs, 0, fip_fn!(|v: u8| v + 1));
    let kept = fip_core::strict::dedup_by(xs, fip_fn!(|a: &u8, b: &u8| *a == *b));
    let (mapped, _) = fip_core::strict::compact_map(xs, 0, fip_fn!(|v: u8| (v * 2, v > 1)));
    let _ = fip_core::strict::update(slot, 0, fip_fn!(|v: u8| v + 10));
    let (_, _) = fip_core::strict::map_in_place_st(xs, 0, 0_u8, fip_fn!(|c: u8, v: u8| (c, v)));
    let (_, _, _) =
        fip_core::strict::compact_map_st(xs, 0, 0_u8, fip_fn!(|c: u8, v: u8| (c, v, true)));
    (kept, mapped)
}

#[test]
fn strict_variants_match_the_fn_versions() {
    for v in inputs() {
        let (mut a, mut b) = (v.clone(), v.clone());
        let n = fip_core::compact(&mut a, |x| x & 1 == 0);
        let m = assert_fip!(fip_core::strict::compact(
            &mut b,
            fip_fn!(|x: &u8| x & 1 == 0)
        ));
        assert_eq!((n, &a[..n]), (m, &b[..m]));

        let (mut a, mut b) = (v.clone(), v.clone());
        let n = fip_core::dedup_by(&mut a, |x, y| x == y);
        let m = assert_fip!(fip_core::strict::dedup_by(
            &mut b,
            fip_fn!(|x: &u8, y: &u8| x == y)
        ));
        assert_eq!((n, &a[..n]), (m, &b[..m]));

        let (mut a, mut b) = (v.clone(), v.clone());
        let (n, _) = fip_core::compact_map(&mut a, 0, |x| (x * 3, x != 2));
        let (m, _) = assert_fip!(fip_core::strict::compact_map(
            &mut b,
            0,
            fip_fn!(|x: u8| (x * 3, x != 2))
        ));
        assert_eq!((n, &a[..n]), (m, &b[..m]));

        let (mut a, mut b) = (v.clone(), v.clone());
        let _ = fip_core::map_in_place(&mut a, 0, |x| x + 7);
        let _ = assert_fip!(fip_core::strict::map_in_place(
            &mut b,
            0,
            fip_fn!(|x: u8| x + 7)
        ));
        assert_eq!(a, b);

        let (mut a, mut b) = (v.clone(), v.clone());
        let ra = fip_core::map_in_place_st(&mut a, 0, 1_u8, |c, x| (c ^ x, x | c));
        let rb = assert_fip!(fip_core::strict::map_in_place_st(
            &mut b,
            0,
            1_u8,
            fip_fn!(|c: u8, x: u8| (c ^ x, x | c))
        ));
        assert_eq!((ra, a), (rb, b));

        let (mut a, mut b) = (v.clone(), v);
        let (n, sa, _) = fip_core::compact_map_st(&mut a, 0, 1_u8, |c, x| (c ^ x, x | c, x != 2));
        let (m, sb, _) = assert_fip!(fip_core::strict::compact_map_st(
            &mut b,
            0,
            1_u8,
            fip_fn!(|c: u8, x: u8| (c ^ x, x | c, x != 2))
        ));
        assert_eq!((n, sa, &a[..n]), (m, sb, &b[..m]));
    }
    let mut x = 4_u8;
    assert_eq!(
        assert_fip!(fip_core::strict::update(&mut x, 0, fip_fn!(|v: u8| v * 3))),
        0
    );
    assert_eq!(x, 12);
}

#[test]
fn strict_callers_run_without_allocation() {
    let mut xs = [1_u8, 2, 3, 4];
    assert_eq!(
        assert_fip!(count_and_compact(&mut xs, fip_fn!(|v: &u8| *v > 2))),
        2
    );
    let mut ys = [1_u8, 1, 2, 3, 3];
    let mut slot = 1_u8;
    assert_eq!(assert_fip!(pipeline(&mut ys, &mut slot)), (3, 5));
    assert_eq!(slot, 11);
    assert_eq!(
        fip_core::strict::__fip_strict_compact.allocs_for("compact"),
        0
    );
}
