// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! In-place operations on `&mut [T]`. Elements are only moved by swapping; nothing is
//! allocated, cloned or dropped.

#[cfg(verus_keep_ghost)]
use crate::spec::state::{compact_map_st_by_post, map_st_by_post};
#[cfg(verus_keep_ghost)]
use crate::spec::{
    compact_map_by_post, dedup_by_post, dedup_src_ok, prefix_ok, strictly_increasing_below,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Swaps `xs[i]` and `xs[j]` for `i < j`, built only from `vstd`-specified primitives
/// (`split_at_mut`, `core::mem::swap`); `<[T]>::swap` has no `vstd` specification.
/// Strict (certificate `__fip_strict_swap_lt`), so `crate::strict` can call it.
#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        i < j < old(xs)@.len(),
    ensures
        final(xs)@ == old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int]),
))]
pub(crate) fn swap_lt<T>(xs: &mut [T], i: usize, j: usize) {
    let (a, b) = <[T]>::split_at_mut(xs, j);
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
/// # Panics
///
/// Only if `keep` panics. The slice is then still a permutation of the input
/// (elements are only swapped, none is dropped): the elements accepted so far are at
/// the front in order, followed by the rejected ones and the unexamined rest
/// (`tests/panic_state.rs`).
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
                    crate::spec::lemma_swap_multiset(prev, w as int, r as int);
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
/// # Panics
///
/// Only if `f` panics. Then the elements before the failing one hold `f`'s values,
/// the failing slot holds `hole`, and the elements after it are unchanged; the
/// failing element was moved into `f` and is dropped by it. Measured: `[1, 2, 3]`,
/// `hole = 0`, `f = |v| v * 10` panicking on 2 leaves `[10, 0, 3]`
/// (`tests/panic_state.rs`).
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

/// [`map_in_place`] with an explicit state: replaces every element `x` of `xs` with
/// the value of `f(s, x)`, threading the state `s` through the calls in index order
/// (starting from `s0`), and returns the final state and `hole`.
///
/// The state is passed by value instead of being captured mutably by an `FnMut`
/// closure, so Verus can state what the calls did to it.
///
/// Verified (`map_st_by_post` in `spec::state`): there is a state trace `ss` with
/// `ss[0] == s0` and `ss[len]` the returned state, and call `k` took
/// `(ss[k], old xs[k])` to `(ss[k + 1], new xs[k])`: `f` was called once per element,
/// in index order, each time on the state the previous call returned.
/// `f` must accept every element with any state.
///
/// # Panics
///
/// Only if `f` panics. Then the elements before the failing one hold `f`'s values,
/// the failing slot holds `hole`, and the elements after it are unchanged; the
/// state and the failing element were moved into `f` and are dropped by it
/// (`tests/panic_state.rs`).
///
/// ```
/// let mut xs = [0, 0, 0];
/// let (count, hole) = fip_core::map_in_place_st(&mut xs, 0, 10, |c, _v| (c + 1, c + 1));
/// assert_eq!((xs, count, hole), ([11, 12, 13], 13, 0));
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        forall|s: S, i: int| 0 <= i < old(xs)@.len() ==> #[trigger] f.requires((s, old(xs)@[i])),
    ensures
        r.1 == hole,
        exists|ss: Seq<S>| #[trigger] map_st_by_post(old(xs)@, final(xs)@, f, s0, r.0, ss),
))]
pub fn map_in_place_st<S, T, F: Fn(S, T) -> (S, T)>(xs: &mut [T], hole: T, s0: S, f: F) -> (S, T) {
    let n = xs.len();
    let mut spare = hole;
    proof_decl! { let ghost mut ss: Seq<S> = seq![s0]; }
    let mut s = s0;
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= n,
            n == old(xs)@.len(),
            xs@.len() == n,
            spare == hole,
            ss.len() == i + 1,
            ss[0] == s0,
            ss[i as int] == s,
            forall|k: int| i <= k < n ==> xs@[k] == old(xs)@[k],
            forall|k: int| 0 <= k < i ==> f.ensures((ss[k], old(xs)@[k]), (ss[k + 1], #[trigger] xs@[k])),
            forall|s: S, k: int| 0 <= k < n ==> #[trigger] f.requires((s, old(xs)@[k])),
        decreases n - i,
    ))]
    while i < n {
        let prev = crate::slot::replace(&mut xs[i], spare);
        let (s1, next) = f(s, prev);
        spare = crate::slot::replace(&mut xs[i], next);
        s = s1;
        proof! { ss = ss.push(s); }
        i += 1;
    }
    proof_decl! { let ghost last = s; }
    let res = (s, spare);
    proof! {
        assert(res.0 == last);
        assert(map_st_by_post(old(xs)@, xs@, f, s0, res.0, ss));
    }
    res
}

/// Removes consecutive runs of elements that `same` considers equal, keeping the first
/// of each run, by moving the kept elements to the front. Returns how many are kept.
///
/// Each element is compared with the **last kept** element (as `Vec::dedup_by` does,
/// with the arguments in the order `(kept, candidate)`). Elements at and after the
/// returned length are the removed ones, in unspecified order; none is dropped.
///
/// Verified (`dedup_by_post` in `spec`): the slice is permuted; the kept elements
/// appear in their original order, starting with the first; each kept element was
/// found different from the one kept before it; every removed element was found the
/// same as the last element kept before it.
///
/// # Panics
///
/// Only if `same` panics. The slice is then still a permutation of the input
/// (elements are only swapped, none is dropped): the elements kept so far are at the
/// front in order, followed by the removed ones and the uncompared rest
/// (`tests/panic_state.rs`).
///
/// ```
/// let mut xs = [1, 1, 2, 3, 3, 3, 1];
/// let n = fip_core::dedup_by(&mut xs, |a, b| a == b);
/// assert_eq!(&xs[..n], &[1, 2, 3, 1]);
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(w =>
    requires
        forall|i: int, j: int| 0 <= i < old(xs)@.len() && 0 <= j < old(xs)@.len()
            ==> same.requires((&old(xs)@[i], &old(xs)@[j])),
    ensures
        exists|idx: Seq<int>, src: Seq<int>|
            #[trigger] dedup_by_post(old(xs)@, final(xs)@, w as int, same, idx, src),
))]
#[must_use = "elements at and after the returned length are the removed ones"]
pub fn dedup_by<T, F: Fn(&T, &T) -> bool>(xs: &mut [T], same: F) -> usize {
    let n = xs.len();
    if n == 0 {
        proof! {
            let idx = Seq::<int>::empty();
            let src = Seq::<int>::empty();
            assert(final(xs)@ =~= old(xs)@);
            assert(dedup_by_post(old(xs)@, final(xs)@, 0, same, idx, src));
        }
        return 0;
    }
    let mut w: usize = 1;
    let mut r: usize = 1;
    proof_decl! {
        let ghost mut idx: Seq<int> = seq![0int];
        let ghost mut src: Seq<int> = seq![0int];
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            1 <= w <= r <= n,
            n == old(xs)@.len(),
            xs@.len() == n,
            xs@.to_multiset() == old(xs)@.to_multiset(),
            forall|k: int| r <= k < n ==> xs@[k] == old(xs)@[k],
            forall|i: int, j: int| 0 <= i < n && 0 <= j < n
                ==> same.requires((&old(xs)@[i], &old(xs)@[j])),
            idx.len() == w,
            strictly_increasing_below(idx, r as int),
            idx[0] == 0,
            forall|i: int| 0 <= i < w ==> #[trigger] xs@[i] == old(xs)@[idx[i]],
            forall|i: int| 0 < i < w ==> #[trigger] same.ensures((&xs@[i - 1], &xs@[i]), false),
            src.len() == r,
            forall|j: int| 0 <= j < r ==> dedup_src_ok(
                old(xs)@, w as int, |a: T, b: T, r: bool| same.ensures((&a, &b), r), idx, #[trigger] src[j], j),
        decreases n - r,
    ))]
    while r < n {
        proof! {
            assert(xs@[w as int - 1] == old(xs)@[idx[w as int - 1]]);
            assert(0 <= idx[w as int - 1] < n);
        }
        let differs = !same(&xs[w - 1], &xs[r]);
        proof_decl! { let ghost ow = w as int; }
        if differs {
            proof_decl! { let ghost prev = xs@; }
            if w < r {
                swap_lt(xs, w, r);
                proof! { crate::spec::lemma_swap_multiset(prev, w as int, r as int); }
            }
            proof! {
                assert forall|j: int| 0 <= j < r implies dedup_src_ok(
                    old(xs)@, ow + 1, |a: T, b: T, r: bool| same.ensures((&a, &b), r), idx.push(r as int), #[trigger] src[j], j) by {
                    assert(dedup_src_ok(old(xs)@, ow, |a: T, b: T, r: bool| same.ensures((&a, &b), r), idx, src[j], j));
                };
                idx = idx.push(r as int);
                src = src.push(ow);
                assert(xs@[ow] == old(xs)@[r as int]);
            }
            w += 1;
        }
        proof! {
            if !differs {
                src = src.push(ow - 1);
            }
        }
        r += 1;
    }
    proof! {
        assert(dedup_by_post(old(xs)@, xs@, w as int, same, idx, src));
    }
    w
}

/// Maps every element through `f` and moves the ones `f` marks to keep to the front,
/// in their original order. Returns how many are kept, and `hole`.
///
/// `f` takes each element **by value** and returns `(new_value, keep)`, so an element
/// can be transformed and filtered in one pass without cloning and without a `&mut`
/// closure. `hole` is the temporary occupant of the slot being mapped and is
/// returned. Elements at and after the returned length are the mapped values that
/// `f` marked to drop, in unspecified order; none is dropped.
///
/// Verified (`compact_map_by_post` in `spec`): every element was passed to `f` once
/// and replaced by `f`'s value; the result is a permutation of those values; the
/// first `w` are exactly the ones marked `keep`, in original order.
///
/// # Panics
///
/// Only if `f` panics. Then the slots before the failing one hold the values `f`
/// returned for the elements before it (those marked keep first, in order), the
/// failing slot holds `hole`, and the elements after it are unchanged; the failing
/// element was moved into `f` and is dropped by it (`tests/panic_state.rs`).
///
/// ```
/// let mut xs = [1, 2, 3, 4];
/// let (n, hole) = fip_core::compact_map(&mut xs, 0, |v| (v * 10, v % 2 == 1));
/// assert_eq!((&xs[..n], hole), (&[10, 30][..], 0));
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> f.requires((old(xs)@[i],)),
    ensures
        r.1 == hole,
        exists|ys: Seq<T>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>|
            #[trigger] compact_map_by_post(old(xs)@, final(xs)@, r.0 as int, f, ys, ks, idx, pos),
))]
#[must_use = "elements at and after the returned length are the dropped ones"]
pub fn compact_map<T, F: Fn(T) -> (T, bool)>(xs: &mut [T], hole: T, f: F) -> (usize, T) {
    let len = xs.len();
    let mut spare = hole;
    let mut w: usize = 0;
    let mut r: usize = 0;
    proof_decl! {
        let ghost mut ys: Seq<T> = Seq::empty();
        let ghost mut ks: Seq<bool> = Seq::empty();
        let ghost mut idx: Seq<int> = Seq::empty();
        let ghost mut pos: Seq<int> = Seq::empty();
    }
    proof! { assert(xs@.subrange(0, 0) =~= ys); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            w <= r <= len,
            len == old(xs)@.len(),
            xs@.len() == len,
            spare == hole,
            forall|k: int| r <= k < len ==> xs@[k] == old(xs)@[k],
            forall|i: int| 0 <= i < len ==> f.requires((old(xs)@[i],)),
            ys.len() == r,
            ks.len() == r,
            forall|j: int| 0 <= j < r ==> f.ensures((old(xs)@[j],), (#[trigger] ys[j], ks[j])),
            xs@.subrange(0, r as int).to_multiset() == ys.to_multiset(),
            idx.len() == w,
            strictly_increasing_below(idx, r as int),
            prefix_ok(xs@, ys, ks, idx, w as int),
            pos.len() == r,
            forall|j: int| 0 <= j < r && #[trigger] ks[j] ==> 0 <= pos[j] < w && idx[pos[j]] == j,
        decreases len - r,
    ))]
    while r < len {
        proof_decl! { let ghost pre = xs@; let ghost pys = ys; let ghost pks = ks; }
        let item = crate::slot::replace(&mut xs[r], spare);
        let (mapped, keep) = f(item);
        spare = crate::slot::replace(&mut xs[r], mapped);
        proof_decl! { let ghost stored = xs@; }
        proof! {
            assert(stored =~= pre.update(r as int, mapped));
            assert(stored.subrange(0, r as int) =~= pre.subrange(0, r as int));
            assert(stored.subrange(0, r as int + 1) =~= stored.subrange(0, r as int).push(mapped));
            vstd::seq_lib::to_multiset_build(stored.subrange(0, r as int), mapped);
            vstd::seq_lib::to_multiset_build(pys, mapped);
            ys = pys.push(mapped);
            ks = pks.push(keep);
            assert(stored.subrange(0, r as int + 1).to_multiset() == ys.to_multiset());
            crate::spec::lemma_prefix_frame(pre, stored, pys, pks, ys, ks, idx, w as int, mapped, keep);
            assert forall|j: int| 0 <= j < r + 1 && #[trigger] ks[j] implies 0 <= pos[j] < w && idx[pos[j]] == j || j == r by {
                if j < r { assert(ks[j] == pks[j]); }
            };
            assert(ys[r as int] == mapped && ks[r as int] == keep);
        }
        if keep {
            if w < r {
                swap_lt(xs, w, r);
                proof! {
                    let p = stored.subrange(0, r as int + 1);
                    crate::spec::lemma_swap_multiset(p, w as int, r as int);
                    assert(xs@.subrange(0, r as int + 1) =~= p.update(w as int, p[r as int]).update(r as int, p[w as int]));
                }
            }
            proof! {
                assert(xs@[w as int] == mapped);
                crate::spec::lemma_prefix_push(stored, xs@, ys, ks, idx, w as int, r as int);
                pos = pos.push(w as int);
                idx = idx.push(r as int);
            }
            w += 1;
        }
        proof! {
            if !keep {
                pos = pos.push(-1);
            }
        }
        r += 1;
    }
    proof! {
        assert(xs@.subrange(0, len as int) =~= xs@);
        assert(compact_map_by_post(old(xs)@, xs@, w as int, f, ys, ks, idx, pos));
    }
    let res = (w, spare);
    proof! {
        assert(res.0 == w);
        assert(compact_map_by_post(old(xs)@, xs@, res.0 as int, f, ys, ks, idx, pos));
    }
    res
}

/// [`compact_map`] with an explicit state: maps every element through `f(s, x)`,
/// threading the state `s` through the calls in index order (starting from `s0`), and
/// moves the values `f` marks to keep to the front, in their original order. Returns
/// how many are kept, the final state, and `hole`.
///
/// The state is passed by value instead of being captured mutably by an `FnMut`
/// closure, so Verus can state what the calls did to it.
///
/// Verified (`compact_map_st_by_post` in `spec::state`): everything
/// [`compact_map`] guarantees, and a state trace `ss` with `ss[0] == s0` and
/// `ss[len]` the returned state such that call `j` took `(ss[j], old xs[j])` to
/// `(ss[j + 1], ys[j], ks[j])`, where `ys[j]`, `ks[j]` are the value and keep flag
/// it returned. `f` must accept every element with any state.
///
/// # Panics
///
/// Only if `f` panics. Then the slice holds the values `f` returned for the elements
/// before the failing one (those marked keep at the front, in order, then the others),
/// `hole` in the failing slot, and the original elements after it; the state and the
/// failing element were moved into `f` and are dropped by it (`tests/panic_state.rs`).
///
/// ```
/// let mut xs = [1, 2, 3, 4];
/// // Number the odd elements: each becomes 10 * value + how many odd ones came before.
/// let (n, odd, hole) = fip_core::compact_map_st(&mut xs, 0, 0, |c, v| {
///     if v % 2 == 1 { (c + 1, v * 10 + c, true) } else { (c, v, false) }
/// });
/// assert_eq!((&xs[..n], odd, hole), (&[10, 31][..], 2, 0));
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        forall|s: S, i: int| 0 <= i < old(xs)@.len() ==> #[trigger] f.requires((s, old(xs)@[i])),
    ensures
        r.2 == hole,
        exists|ss: Seq<S>, ys: Seq<T>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>|
            #[trigger] compact_map_st_by_post(old(xs)@, final(xs)@, r.0 as int, f, s0, r.1, ss, ys, ks, idx, pos),
))]
#[must_use = "elements at and after the returned length are the dropped ones"]
pub fn compact_map_st<S, T, F: Fn(S, T) -> (S, T, bool)>(
    xs: &mut [T],
    hole: T,
    s0: S,
    f: F,
) -> (usize, S, T) {
    let len = xs.len();
    let mut spare = hole;
    proof_decl! { let ghost mut ss: Seq<S> = seq![s0]; }
    let mut s = s0;
    let mut w: usize = 0;
    let mut r: usize = 0;
    proof_decl! {
        let ghost mut ys: Seq<T> = Seq::empty();
        let ghost mut ks: Seq<bool> = Seq::empty();
        let ghost mut idx: Seq<int> = Seq::empty();
        let ghost mut pos: Seq<int> = Seq::empty();
    }
    proof! { assert(xs@.subrange(0, 0) =~= ys); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            w <= r <= len,
            len == old(xs)@.len(),
            xs@.len() == len,
            spare == hole,
            forall|k: int| r <= k < len ==> xs@[k] == old(xs)@[k],
            forall|s: S, i: int| 0 <= i < len ==> #[trigger] f.requires((s, old(xs)@[i])),
            ss.len() == r + 1,
            ss[0] == s0,
            ss[r as int] == s,
            ys.len() == r,
            ks.len() == r,
            forall|j: int| 0 <= j < r ==> f.ensures((ss[j], old(xs)@[j]), (ss[j + 1], #[trigger] ys[j], ks[j])),
            xs@.subrange(0, r as int).to_multiset() == ys.to_multiset(),
            idx.len() == w,
            strictly_increasing_below(idx, r as int),
            prefix_ok(xs@, ys, ks, idx, w as int),
            pos.len() == r,
            forall|j: int| 0 <= j < r && #[trigger] ks[j] ==> 0 <= pos[j] < w && idx[pos[j]] == j,
        decreases len - r,
    ))]
    while r < len {
        proof_decl! { let ghost pre = xs@; let ghost pys = ys; let ghost pks = ks; let ghost pss = ss; }
        let item = crate::slot::replace(&mut xs[r], spare);
        let (s1, mapped, keep) = f(s, item);
        spare = crate::slot::replace(&mut xs[r], mapped);
        s = s1;
        proof_decl! { let ghost stored = xs@; }
        proof! {
            assert(stored =~= pre.update(r as int, mapped));
            assert(stored.subrange(0, r as int) =~= pre.subrange(0, r as int));
            assert(stored.subrange(0, r as int + 1) =~= stored.subrange(0, r as int).push(mapped));
            vstd::seq_lib::to_multiset_build(stored.subrange(0, r as int), mapped);
            vstd::seq_lib::to_multiset_build(pys, mapped);
            ys = pys.push(mapped);
            ks = pks.push(keep);
            ss = pss.push(s);
            assert(stored.subrange(0, r as int + 1).to_multiset() == ys.to_multiset());
            crate::spec::lemma_prefix_frame(pre, stored, pys, pks, ys, ks, idx, w as int, mapped, keep);
            assert forall|j: int| 0 <= j < r + 1 && #[trigger] ks[j] implies 0 <= pos[j] < w && idx[pos[j]] == j || j == r by {
                if j < r { assert(ks[j] == pks[j]); }
            };
            assert forall|j: int| 0 <= j < r + 1 implies f.ensures((ss[j], old(xs)@[j]), (ss[j + 1], #[trigger] ys[j], ks[j])) by {
                if j < r {
                    assert(pys[j] == ys[j] && pks[j] == ks[j] && pss[j] == ss[j] && pss[j + 1] == ss[j + 1]);
                }
            };
            assert(ys[r as int] == mapped && ks[r as int] == keep);
        }
        if keep {
            if w < r {
                swap_lt(xs, w, r);
                proof! {
                    let p = stored.subrange(0, r as int + 1);
                    crate::spec::lemma_swap_multiset(p, w as int, r as int);
                    assert(xs@.subrange(0, r as int + 1) =~= p.update(w as int, p[r as int]).update(r as int, p[w as int]));
                }
            }
            proof! {
                assert(xs@[w as int] == mapped);
                crate::spec::lemma_prefix_push(stored, xs@, ys, ks, idx, w as int, r as int);
                pos = pos.push(w as int);
                idx = idx.push(r as int);
            }
            w += 1;
        }
        proof! {
            if !keep {
                pos = pos.push(-1);
            }
        }
        r += 1;
    }
    proof! {
        assert(xs@.subrange(0, len as int) =~= xs@);
        assert(compact_map_st_by_post(old(xs)@, xs@, w as int, f, s0, s, ss, ys, ks, idx, pos));
    }
    proof_decl! { let ghost last = s; }
    let res = (w, s, spare);
    proof! {
        assert(res.0 == w && res.1 == last);
        assert(compact_map_st_by_post(old(xs)@, xs@, res.0 as int, f, s0, res.1, ss, ys, ks, idx, pos));
    }
    res
}

/// Strict certificate for [`swap`]; made and justified in `fip_strict::certs`.
#[cfg(not(verus_keep_ghost))]
#[doc(hidden)]
pub use fip_strict::certs::__fip_strict_swap;
