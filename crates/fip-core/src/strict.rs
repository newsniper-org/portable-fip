// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Strict variants of the higher-order functions: the callable is a
//! [`fip_strict::FipFn`] (from `fip_macros::fip_fn!`) instead of an `Fn` closure, so
//! these functions carry generated certificates and can be called from
//! `#[fip(strict = true)]` code. Each is `#[fip(strict = true, param(f = 0))]`: the
//! callable must be certified allocation-free (it is called in a loop).
//!
//! Specified like their `Fn` counterparts, with `FipFn::pre` / `FipFn::post` in place
//! of a closure's `requires` / `ensures`; `compact`, `dedup_by` and `compact_map` use
//! the pre-verified predicates `compact_fip_post`, `dedup_fip_post` and
//! `compact_map_fip_post` (`spec.rs`). Verified with `--no-cheating`.
//!
//! The strict check runs in plain builds only (`cfg_attr(not(verus_keep_ghost))`);
//! under `verus` the bodies are verified as written.
//!
//! ```
//! use fip_strict::FipFn;
//! let mut xs = [1_u8, 2, 3, 4];
//! let n = fip_core::strict::compact(&mut xs, fip_macros::fip_fn!(|v: &u8| *v % 2 == 0));
//! assert_eq!(&xs[..n], &[2, 4]);
//! ```

#![allow(
    clippy::needless_pass_by_value,
    reason = "callables are taken by value, like the `Fn` closures of the other variants"
)]

use fip_strict::FipFn;

#[cfg(verus_keep_ghost)]
use crate::spec::{
    compact_fip_post, compact_map_fip_post, dedup_fip_post, dedup_src_ok, prefix_ok,
    strictly_increasing_below,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Transforms `*slot` in place with `f`, using `hole` as the temporary occupant, and
/// returns `hole`. Strict variant of [`crate::update`].
///
/// ```
/// use fip_strict::FipFn;
/// let mut x = 5_i32;
/// let hole = fip_core::strict::update(&mut x, 0, fip_macros::fip_fn!(|v: i32| v * 2));
/// assert_eq!((x, hole), (10, 0));
/// ```
#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict = true, param(f = 0)))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        f.pre((*old(slot),)),
    ensures
        f.post((*old(slot),), *final(slot)),
        r == hole,
))]
#[inline]
pub fn update<T, F: FipFn<(T,), Output = T>>(slot: &mut T, hole: T, f: F) -> T {
    let prev = crate::slot::replace(slot, hole);
    let next = f.call((prev,));
    crate::slot::replace(slot, next)
}

/// Replaces every element `x` of `xs` with `f(x)`, in place, using `hole` as the
/// temporary occupant of each slot, and returns `hole`. Strict variant of
/// [`crate::map_in_place`].
///
/// ```
/// use fip_strict::FipFn;
/// let mut xs = [1, 2, 3];
/// let hole = fip_core::strict::map_in_place(&mut xs, 0, fip_macros::fip_fn!(|v: i32| v * 2));
/// assert_eq!((xs, hole), ([2, 4, 6], 0));
/// ```
#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict = true, param(f = 0)))]
#[cfg_attr(verus_keep_ghost, verus_spec(h =>
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> f.pre((old(xs)@[i],)),
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|i: int| 0 <= i < old(xs)@.len() ==> f.post((old(xs)@[i],), final(xs)@[i]),
        h == hole,
))]
pub fn map_in_place<T, F: FipFn<(T,), Output = T>>(xs: &mut [T], hole: T, f: F) -> T {
    let n = <[T]>::len(xs);
    let mut spare = hole;
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= n,
            n == old(xs)@.len(),
            xs@.len() == n,
            spare == hole,
            forall|k: int| i <= k < n ==> xs@[k] == old(xs)@[k],
            forall|k: int| 0 <= k < i ==> f.post((old(xs)@[k],), xs@[k]),
            forall|k: int| 0 <= k < n ==> f.pre((old(xs)@[k],)),
        decreases n - i,
    ))]
    while i < n {
        let prev = crate::slot::replace(&mut xs[i], spare);
        let next = f.call((prev,));
        spare = crate::slot::replace(&mut xs[i], next);
        i += 1;
    }
    spare
}

/// Moves the elements for which `keep` returns `true` to the front of `xs`, in their
/// original order, and returns how many there are. Strict variant of
/// [`crate::compact`].
///
/// Verified (`compact_fip_post`): the slice is permuted; `keep` returned `true`
/// before the returned length and `false` after it; the kept elements keep their
/// original order.
///
/// ```
/// use fip_strict::FipFn;
/// let mut xs = [1, 2, 3, 4, 5, 6];
/// let n = fip_core::strict::compact(&mut xs, fip_macros::fip_fn!(|v: &i32| v % 2 == 0));
/// assert_eq!(&xs[..n], &[2, 4, 6]);
/// ```
#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict = true, param(keep = 0)))]
#[cfg_attr(verus_keep_ghost, verus_spec(w =>
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> keep.pre((&old(xs)@[i],)),
    ensures
        compact_fip_post(old(xs)@, final(xs)@, w as int, keep),
))]
#[must_use = "elements at and after the returned length are the rejected ones"]
pub fn compact<T, F: for<'a> FipFn<(&'a T,), Output = bool>>(xs: &mut [T], keep: F) -> usize {
    let n = <[T]>::len(xs);
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
            forall|i: int| 0 <= i < w ==> keep.post((&xs@[i],), true),
            forall|i: int| w <= i < r ==> keep.post((&xs@[i],), false),
            forall|i: int| 0 <= i < old(xs)@.len() ==> keep.pre((&old(xs)@[i],)),
            idx.len() == w,
            strictly_increasing_below(idx, r as int),
            forall|i: int| 0 <= i < w ==> xs@[i] == old(xs)@[idx[i]],
        decreases n - r,
    ))]
    while r < n {
        if keep.call((&xs[r],)) {
            if w < r {
                proof_decl! { let ghost prev = xs@; }
                crate::slice::swap_lt(xs, w, r);
                proof! {
                    crate::spec::lemma_swap_multiset(prev, w as int, r as int);
                }
            }
            proof! { idx = idx.push(r as int); }
            w += 1;
        }
        r += 1;
    }
    proof! {
        assert(strictly_increasing_below(idx, n as int));
        assert(compact_fip_post(old(xs)@, xs@, w as int, keep));
    }
    w
}

/// Removes consecutive runs of elements that `same` considers equal, keeping the first
/// of each run, by moving the kept elements to the front. Returns how many are kept.
/// Strict variant of [`crate::dedup_by`] (same comparison order: `(kept, candidate)`).
///
/// Verified (`dedup_fip_post`).
///
/// ```
/// use fip_strict::FipFn;
/// let mut xs = [1, 1, 2, 3, 3, 3, 1];
/// let n = fip_core::strict::dedup_by(&mut xs, fip_macros::fip_fn!(|a: &i32, b: &i32| a == b));
/// assert_eq!(&xs[..n], &[1, 2, 3, 1]);
/// ```
#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict = true, param(same = 0)))]
#[cfg_attr(verus_keep_ghost, verus_spec(w =>
    requires
        forall|i: int, j: int| 0 <= i < old(xs)@.len() && 0 <= j < old(xs)@.len()
            ==> same.pre((&old(xs)@[i], &old(xs)@[j])),
    ensures
        exists|idx: Seq<int>, src: Seq<int>|
            #[trigger] dedup_fip_post(old(xs)@, final(xs)@, w as int, same, idx, src),
))]
#[must_use = "elements at and after the returned length are the removed ones"]
pub fn dedup_by<T, F: for<'a, 'b> FipFn<(&'a T, &'b T), Output = bool>>(
    xs: &mut [T],
    same: F,
) -> usize {
    let n = <[T]>::len(xs);
    if n == 0 {
        proof! {
            let idx = Seq::<int>::empty();
            let src = Seq::<int>::empty();
            assert(final(xs)@ =~= old(xs)@);
            assert(dedup_fip_post(old(xs)@, final(xs)@, 0, same, idx, src));
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
                ==> same.pre((&old(xs)@[i], &old(xs)@[j])),
            idx.len() == w,
            strictly_increasing_below(idx, r as int),
            idx[0] == 0,
            forall|i: int| 0 <= i < w ==> #[trigger] xs@[i] == old(xs)@[idx[i]],
            forall|i: int| 0 < i < w ==> #[trigger] same.post((&xs@[i - 1], &xs@[i]), false),
            src.len() == r,
            forall|j: int| 0 <= j < r ==> dedup_src_ok(
                old(xs)@, w as int, |a: T, b: T, r: bool| same.post((&a, &b), r), idx, #[trigger] src[j], j),
        decreases n - r,
    ))]
    while r < n {
        proof! {
            assert(xs@[w as int - 1] == old(xs)@[idx[w as int - 1]]);
            assert(0 <= idx[w as int - 1] < n);
        }
        let differs = !same.call((&xs[w - 1], &xs[r]));
        proof_decl! { let ghost ow = w as int; }
        if differs {
            proof_decl! { let ghost prev = xs@; }
            if w < r {
                crate::slice::swap_lt(xs, w, r);
                proof! { crate::spec::lemma_swap_multiset(prev, w as int, r as int); }
            }
            proof! {
                assert forall|j: int| 0 <= j < r implies dedup_src_ok(
                    old(xs)@, ow + 1, |a: T, b: T, r: bool| same.post((&a, &b), r), idx.push(r as int), #[trigger] src[j], j) by {
                    assert(dedup_src_ok(old(xs)@, ow, |a: T, b: T, r: bool| same.post((&a, &b), r), idx, src[j], j));
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
        assert(dedup_fip_post(old(xs)@, xs@, w as int, same, idx, src));
    }
    w
}

/// Maps every element through `f` and moves the ones `f` marks to keep to the front,
/// in their original order. Returns how many are kept, and `hole`. Strict variant of
/// [`crate::compact_map`].
///
/// Verified (`compact_map_fip_post`).
///
/// ```
/// use fip_strict::FipFn;
/// let mut xs = [1, 2, 3, 4];
/// let (n, hole) = fip_core::strict::compact_map(&mut xs, 0, fip_macros::fip_fn!(|v: i32| (v * 10, v % 2 == 1)));
/// assert_eq!((&xs[..n], hole), (&[10, 30][..], 0));
/// ```
#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict = true, param(f = 0)))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        forall|i: int| 0 <= i < old(xs)@.len() ==> f.pre((old(xs)@[i],)),
    ensures
        r.1 == hole,
        exists|ys: Seq<T>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>|
            #[trigger] compact_map_fip_post(old(xs)@, final(xs)@, r.0 as int, f, ys, ks, idx, pos),
))]
#[must_use = "elements at and after the returned length are the dropped ones"]
pub fn compact_map<T, F: FipFn<(T,), Output = (T, bool)>>(
    xs: &mut [T],
    hole: T,
    f: F,
) -> (usize, T) {
    let len = <[T]>::len(xs);
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
            forall|i: int| 0 <= i < len ==> f.pre((old(xs)@[i],)),
            ys.len() == r,
            ks.len() == r,
            forall|j: int| 0 <= j < r ==> f.post((old(xs)@[j],), (#[trigger] ys[j], ks[j])),
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
        let (mapped, keep) = f.call((item,));
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
                crate::slice::swap_lt(xs, w, r);
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
        assert(compact_map_fip_post(old(xs)@, xs@, w as int, f, ys, ks, idx, pos));
    }
    let res = (w, spare);
    proof! {
        assert(res.0 == w);
        assert(compact_map_fip_post(old(xs)@, xs@, res.0 as int, f, ys, ks, idx, pos));
    }
    res
}
