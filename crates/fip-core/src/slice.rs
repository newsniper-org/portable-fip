// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! In-place operations on `&mut [T]`. Elements are only moved by swapping; nothing is
//! allocated, cloned or dropped.

#[cfg(verus_keep_ghost)]
use crate::spec::strictly_increasing_below;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Swaps `xs[i]` and `xs[j]` for `i < j`, built only from `vstd`-specified primitives
/// (`split_at_mut`, `core::mem::swap`); `<[T]>::swap` has no `vstd` specification.
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        i < j < old(xs)@.len(),
    ensures
        final(xs)@ == old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int]),
))]
fn swap_lt<T>(xs: &mut [T], i: usize, j: usize) {
    let (a, b) = xs.split_at_mut(j);
    core::mem::swap(&mut a[i], &mut b[0]);
    proof! {
        assert(final(xs)@ =~= old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int]));
    }
}

/// Swaps `xs[i]` and `xs[j]`. `i == j` is a no-op.
///
/// # Panics
///
/// Panics if `i` or `j` is out of bounds (the verified precondition rules this out).
///
/// ```
/// let mut xs = [1, 2, 3];
/// fip_core::swap(&mut xs, 0, 2);
/// assert_eq!(xs, [3, 2, 1]);
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        i < old(xs)@.len(),
        j < old(xs)@.len(),
    ensures
        final(xs)@ == old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int]),
))]
pub fn swap<T>(xs: &mut [T], i: usize, j: usize) {
    if i != j {
        let (lo, hi) = if i < j { (i, j) } else { (j, i) };
        swap_lt(xs, lo, hi);
    }
    proof! {
        assert(final(xs)@ =~= old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int]));
    }
}

/// Moves the elements for which `keep` returns `true` to the front of `xs`, in their
/// original relative order, and returns how many there are.
///
/// Elements at and after the returned length are the rejected ones, in unspecified
/// order. None is dropped; the slice is only permuted.
///
/// Verified: the result is a permutation of the input (equal multisets); `keep`
/// returned `true` for every element before the returned length and `false` for every
/// element after it; and the retained elements appear in their original order.
///
/// ```
/// let mut xs = [1, 2, 3, 4, 5, 6];
/// let n = fip_core::compact(&mut xs, |v| v % 2 == 0);
/// assert_eq!(&xs[..n], &[2, 4, 6]);
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(w =>
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> keep.requires((&old(xs)@[i],)),
    ensures
        w <= old(xs)@.len(),
        final(xs)@.len() == old(xs)@.len(),
        final(xs)@.to_multiset() == old(xs)@.to_multiset(),
        forall|i: int| 0 <= i < w ==> keep.ensures((&final(xs)@[i],), true),
        forall|i: int| w <= i < final(xs)@.len() ==> keep.ensures((&final(xs)@[i],), false),
        exists|idx: Seq<int>| idx.len() == w
            && #[trigger] strictly_increasing_below(idx, old(xs)@.len() as int)
            && forall|i: int| 0 <= i < w ==> final(xs)@[i] == old(xs)@[idx[i]],
))]
#[must_use = "elements at and after the returned length are the rejected ones"]
pub fn compact<T, F: Fn(&T) -> bool>(xs: &mut [T], keep: F) -> usize {
    let n = xs.len();
    let mut w: usize = 0;
    let mut r: usize = 0;
    proof_decl! { let ghost mut idx: Seq<int> = Seq::empty(); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            w <= r <= n,
            n == old(xs)@.len(),
            xs@.len() == n,
            xs@.to_multiset() == old(xs)@.to_multiset(),
            forall|k: int| r <= k < n ==> xs@[k] == old(xs)@[k],
            forall|i: int| 0 <= i < w ==> keep.ensures((&xs@[i],), true),
            forall|i: int| w <= i < r ==> keep.ensures((&xs@[i],), false),
            forall|i: int| 0 <= i < old(xs)@.len() ==> keep.requires((&old(xs)@[i],)),
            idx.len() == w,
            strictly_increasing_below(idx, r as int),
            forall|i: int| 0 <= i < w ==> xs@[i] == old(xs)@[idx[i]],
        decreases n - r,
    ))]
    while r < n {
        if keep(&xs[r]) {
            if w < r {
                proof_decl! { let ghost prev = xs@; }
                swap_lt(xs, w, r);
                proof! {
                    let a = prev[w as int];
                    let b = prev[r as int];
                    let s1 = prev.update(w as int, b);
                    vstd::seq_lib::to_multiset_update(prev, w as int, b);
                    vstd::seq_lib::to_multiset_update(s1, r as int, a);
                    vstd::seq_lib::to_multiset_contains(prev, a);
                    assert(s1[r as int] == b);
                    assert(xs@.to_multiset() =~= prev.to_multiset());
                }
            }
            proof! { idx = idx.push(r as int); }
            w += 1;
        }
        r += 1;
    }
    w
}

/// Replaces every element `x` of `xs` with `f(x)`, in place, using `hole` as the
/// temporary occupant of each slot, and returns `hole`.
///
/// `f` is bound once and called once per element, in index order.
///
/// ```
/// let mut xs = [1, 2, 3];
/// let hole = fip_core::map_in_place(&mut xs, 0, |v| v * 2);
/// assert_eq!((xs, hole), ([2, 4, 6], 0));
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(h =>
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> f.requires((old(xs)@[i],)),
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|i: int| 0 <= i < old(xs)@.len() ==> f.ensures((old(xs)@[i],), final(xs)@[i]),
        h == hole,
))]
pub fn map_in_place<T, F: Fn(T) -> T>(xs: &mut [T], hole: T, f: F) -> T {
    let n = xs.len();
    let mut spare = hole;
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= n,
            n == old(xs)@.len(),
            xs@.len() == n,
            spare == hole,
            forall|k: int| i <= k < n ==> xs@[k] == old(xs)@[k],
            forall|k: int| 0 <= k < i ==> f.ensures((old(xs)@[k],), xs@[k]),
            forall|k: int| 0 <= k < n ==> f.requires((old(xs)@[k],)),
        decreases n - i,
    ))]
    while i < n {
        let prev = crate::slot::replace(&mut xs[i], spare);
        let next = f(prev);
        spare = crate::slot::replace(&mut xs[i], next);
        i += 1;
    }
    spare
}
