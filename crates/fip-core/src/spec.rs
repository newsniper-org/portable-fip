// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Specification helpers. Compiled only under the `verus` driver.

use fip_strict::FipFn;
use vstd::prelude::*;

verus! {

/// `idx` lists indices in strictly increasing order, all in `0..bound`.
///
/// Used to state that [`crate::compact`] keeps the relative order of the
/// elements it retains.
pub open spec fn strictly_increasing_below(idx: Seq<int>, bound: int) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < idx.len() ==> #[trigger] idx[i] < #[trigger] idx[j]
    &&& forall|i: int| 0 <= i < idx.len() ==> 0 <= #[trigger] idx[i] < bound
}

/// Swapping two positions of a sequence preserves its multiset.
pub proof fn lemma_swap_multiset<A>(s: Seq<A>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    let s1 = s.update(i, s[j]);
    vstd::seq_lib::to_multiset_update(s, i, s[j]);
    vstd::seq_lib::to_multiset_update(s1, j, s[i]);
    vstd::seq_lib::to_multiset_contains(s, s[i]);
    vstd::seq_lib::to_multiset_contains(s, s[j]);
    if i == j {
        assert(s.update(i, s[j]).update(j, s[i]) =~= s);
    } else {
        assert(s1[j] == s[j]);
        assert(s.update(i, s[j]).update(j, s[i]).to_multiset() =~= s.to_multiset());
    }
}

/// Postcondition of `dedup_by` on `old` → `new` with result `w`, where
/// `same(a, b, r)` means "the predicate returned `r` on `(a, b)`".
///
/// Witnesses: `idx[i]` is the original index of the `i`-th retained element;
/// `src[j]` is the retained slot that original element `j` was kept as or merged into.
///
/// - `new` is a permutation of `old`;
/// - the first `w` elements of `new` are `old[idx[0]], old[idx[1]], ...` with `idx`
///   strictly increasing and starting at 0 (the first element is always kept);
/// - each retained element was found *different* from the one retained before it;
/// - every original element `j` is either retained (`idx[src[j]] == j`) or was found
///   the *same* as the last element retained before it (`old[idx[src[j]]]`).
pub open spec fn dedup_post<A>(
    old: Seq<A>,
    new: Seq<A>,
    w: int,
    same: spec_fn(A, A, bool) -> bool,
    idx: Seq<int>,
    src: Seq<int>,
) -> bool {
    &&& new.len() == old.len()
    &&& new.to_multiset() == old.to_multiset()
    &&& 0 <= w <= old.len()
    &&& (old.len() > 0 ==> w >= 1)
    &&& idx.len() == w
    &&& strictly_increasing_below(idx, old.len() as int)
    &&& (w > 0 ==> idx[0] == 0)
    &&& forall|i: int| 0 <= i < w ==> #[trigger] new[i] == old[idx[i]]
    &&& forall|i: int| 0 < i < w ==> #[trigger] adjacent_distinct(new, same, i)
    &&& src.len() == old.len()
    &&& forall|j: int| 0 <= j < old.len() ==> dedup_src_ok(old, w, same, idx, #[trigger] src[j], j)
}

/// Retained neighbours `new[i - 1]`, `new[i]` were found different. A named predicate
/// so the quantifier in `dedup_post` triggers on it rather than on `new[i]`, which
/// would match its own instance's `new[i - 1]` again (a matching loop).
pub open spec fn adjacent_distinct<A>(new: Seq<A>, same: spec_fn(A, A, bool) -> bool, i: int) -> bool {
    same(new[i - 1], new[i], false)
}

/// Original element `j` is accounted for by retained slot `k`.
pub open spec fn dedup_src_ok<A>(
    old: Seq<A>,
    w: int,
    same: spec_fn(A, A, bool) -> bool,
    idx: Seq<int>,
    k: int,
    j: int,
) -> bool {
    &&& 0 <= k < w
    &&& idx[k] <= j
    &&& (k + 1 == w || j < idx[k + 1])
    &&& (idx[k] == j || same(old[idx[k]], old[j], true))
}

/// `dedup_post` for an exec predicate `f`: `same(a, b, r)` iff `f` may return `r` on `(&a, &b)`.
pub open spec fn dedup_by_post<A, F: Fn(&A, &A) -> bool>(
    old: Seq<A>,
    new: Seq<A>,
    w: int,
    f: F,
    idx: Seq<int>,
    src: Seq<int>,
) -> bool {
    dedup_post(old, new, w, |a: A, b: A, r: bool| f.ensures((&a, &b), r), idx, src)
}

// ---- Pre-verification of the `dedup_post` specification (written and verified
// before `dedup_by` was implemented): on concrete inputs it accepts the intended
// answer and rejects the two ways an implementation could be wrong.

/// Equality as the `same` relation.
pub open spec fn eq_rel(a: u8, b: u8, r: bool) -> bool {
    r == (a == b)
}

/// Accepts the intended answer: `[1, 1, 2]` → `[1, 2 | 1]`, `w = 2`.
pub proof fn lemma_dedup_spec_accepts_intended()
    ensures
        dedup_post(seq![1u8, 1u8, 2u8], seq![1u8, 2u8, 1u8], 2, |a: u8, b: u8, r: bool| eq_rel(a, b, r), seq![0int, 2int], seq![0int, 0int, 1int]),
{
    let old = seq![1u8, 1u8, 2u8];
    let new = seq![1u8, 2u8, 1u8];
    lemma_swap_multiset(old, 1, 2);
    assert(new =~= old.update(1, old[2]).update(2, old[1]));
    let idx = seq![0int, 2int];
    let src = seq![0int, 0int, 1int];
    assert(dedup_src_ok(old, 2, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src[0], 0));
    assert(dedup_src_ok(old, 2, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src[1], 1));
    assert(dedup_src_ok(old, 2, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src[2], 2));
    assert(adjacent_distinct(new, |a: u8, b: u8, r: bool| eq_rel(a, b, r), 1));
    assert(dedup_post(old, new, 2, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src));
}

/// Rejects keeping a duplicate: `[1, 1, 2]` with `w = 3`, whatever the witnesses.
pub proof fn lemma_dedup_spec_rejects_kept_duplicate(new: Seq<u8>, idx: Seq<int>, src: Seq<int>)
    ensures
        !dedup_post(seq![1u8, 1u8, 2u8], new, 3, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src),
{
    let old = seq![1u8, 1u8, 2u8];
    if dedup_post(old, new, 3, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src) {
        assert(idx[0] < idx[1] && idx[1] < idx[2] && idx[2] < 3);
        assert(idx[0] == 0 && idx[1] == 1);
        assert(new[0] == old[idx[0]] && new[1] == old[idx[1]]);
        assert(adjacent_distinct(new, |a: u8, b: u8, r: bool| eq_rel(a, b, r), 1));
        assert(eq_rel(new[0], new[1], false));
    }
}

/// Rejects merging different elements: `[1, 2]` with `w = 1`, whatever the witnesses.
pub proof fn lemma_dedup_spec_rejects_wrong_merge(new: Seq<u8>, idx: Seq<int>, src: Seq<int>)
    ensures
        !dedup_post(seq![1u8, 2u8], new, 1, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src),
{
    let old = seq![1u8, 2u8];
    if dedup_post(old, new, 1, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src) {
        assert(dedup_src_ok(old, 1, |a: u8, b: u8, r: bool| eq_rel(a, b, r), idx, src[1], 1));
        assert(src[1] == 0 && idx[0] == 0);
        assert(eq_rel(old[0], old[1], true));
    }
}

/// Postcondition of `compact_map` on `old` → `new` with result `w`, where
/// `step(a, b, k)` means "the function may map `a` to `(b, k)`".
///
/// Witnesses: `ys[j], ks[j]` is what the function returned for `old[j]`; `idx[i]` is
/// the original index of the `i`-th retained element; `pos[j]` is the slot of a
/// retained original element `j`.
///
/// - every original element was mapped exactly once, in place of itself:
///   `new` is a permutation of `ys`;
/// - the first `w` elements of `new` are `ys[idx[0]], ys[idx[1]], ...`, all with
///   `ks == true`, in original order;
/// - every element with `ks == true` is among them.
pub open spec fn compact_map_post<A>(
    old: Seq<A>,
    new: Seq<A>,
    w: int,
    step: spec_fn(A, A, bool) -> bool,
    ys: Seq<A>,
    ks: Seq<bool>,
    idx: Seq<int>,
    pos: Seq<int>,
) -> bool {
    &&& ys.len() == old.len()
    &&& ks.len() == old.len()
    &&& forall|j: int| 0 <= j < old.len() ==> step(old[j], #[trigger] ys[j], ks[j])
    &&& new.len() == old.len()
    &&& new.to_multiset() == ys.to_multiset()
    &&& 0 <= w <= old.len()
    &&& idx.len() == w
    &&& strictly_increasing_below(idx, old.len() as int)
    &&& forall|i: int| 0 <= i < w ==> #[trigger] new[i] == ys[idx[i]] && ks[idx[i]]
    &&& pos.len() == old.len()
    &&& forall|j: int| 0 <= j < old.len() && #[trigger] ks[j] ==> 0 <= pos[j] < w && idx[pos[j]] == j
}

/// `compact_map_post` for an exec function `f`.
pub open spec fn compact_map_by_post<A, F: Fn(A) -> (A, bool)>(
    old: Seq<A>,
    new: Seq<A>,
    w: int,
    f: F,
    ys: Seq<A>,
    ks: Seq<bool>,
    idx: Seq<int>,
    pos: Seq<int>,
) -> bool {
    compact_map_post(old, new, w, |a: A, b: A, k: bool| f.ensures((a,), (b, k)), ys, ks, idx, pos)
}

/// The first `w` elements of `s` are `ys[idx[i]]`, each with `ks[idx[i]]`.
/// Loop invariant of `compact_map`, named so that its frame reasoning lives in the
/// two lemmas below rather than in assertions spread over the loop body.
pub open spec fn prefix_ok<A>(s: Seq<A>, ys: Seq<A>, ks: Seq<bool>, idx: Seq<int>, w: int) -> bool {
    forall|i: int| 0 <= i < w ==> #[trigger] s[i] == ys[idx[i]] && ks[idx[i]]
}

/// Frame: overwriting positions at or beyond `w` and appending one entry to `ys`/`ks`
/// keeps the prefix, provided every `idx[i]` points into the old `ys`.
pub proof fn lemma_prefix_frame<A>(
    pre: Seq<A>, stored: Seq<A>, pys: Seq<A>, pks: Seq<bool>,
    ys: Seq<A>, ks: Seq<bool>, idx: Seq<int>, w: int, y: A, k: bool,
)
    requires
        prefix_ok(pre, pys, pks, idx, w),
        forall|i: int| 0 <= i < w ==> #[trigger] stored[i] == pre[i],
        forall|i: int| 0 <= i < w ==> 0 <= #[trigger] idx[i] < pys.len(),
        pks.len() == pys.len(),
        ys == pys.push(y),
        ks == pks.push(k),
    ensures
        prefix_ok(stored, ys, ks, idx, w),
{
    assert(forall|i: int| 0 <= i < w ==> #[trigger] pre[i] == pys[idx[i]] && pks[idx[i]]);
    assert(forall|i: int| 0 <= i < w ==> #[trigger] ys[idx[i]] == pys[idx[i]]);
    assert(forall|i: int| 0 <= i < w ==> #[trigger] ks[idx[i]] == pks[idx[i]]);
}

/// Extending the prefix by one retained element `ys[r]` (with `ks[r]`) at slot `w`.
pub proof fn lemma_prefix_push<A>(
    old_s: Seq<A>, new_s: Seq<A>, ys: Seq<A>, ks: Seq<bool>, idx: Seq<int>, w: int, r: int,
)
    requires
        prefix_ok(old_s, ys, ks, idx, w),
        idx.len() == w,
        forall|i: int| 0 <= i < w ==> #[trigger] new_s[i] == old_s[i],
        new_s[w] == ys[r],
        ks[r],
    ensures
        prefix_ok(new_s, ys, ks, idx.push(r), w + 1),
{
    let idx2 = idx.push(r);
    assert(forall|i: int| 0 <= i < w ==> #[trigger] old_s[i] == ys[idx[i]] && ks[idx[i]]);
    assert(forall|i: int| 0 <= i < w ==> #[trigger] idx2[i] == idx[i]);
    assert(idx2[w] == r);
}

// ---- Pre-verification of the `compact_map_post` specification (written and verified
// before `compact_map` was implemented).

/// Example step: multiply by 10, keep odd inputs.
pub open spec fn times10_keep_odd(a: u8, b: u8, k: bool) -> bool {
    b == a * 10 && k == (a % 2 == 1)
}

/// Accepts the intended answer: `[1, 2, 3]` → `[10, 30 | 20]`, `w = 2`.
pub proof fn lemma_compact_map_spec_accepts_intended()
    ensures
        compact_map_post(seq![1u8, 2u8, 3u8], seq![10u8, 30u8, 20u8], 2, |a: u8, b: u8, k: bool| times10_keep_odd(a, b, k),
            seq![10u8, 20u8, 30u8], seq![true, false, true], seq![0int, 2int], seq![0int, -1int, 1int]),
{
    let old = seq![1u8, 2u8, 3u8];
    let ys = seq![10u8, 20u8, 30u8];
    let ks = seq![true, false, true];
    let new = seq![10u8, 30u8, 20u8];
    lemma_swap_multiset(ys, 1, 2);
    assert(new =~= ys.update(1, ys[2]).update(2, ys[1]));
    let idx = seq![0int, 2int];
    let pos = seq![0int, -1int, 1int];
    assert(compact_map_post(old, new, 2, |a: u8, b: u8, k: bool| times10_keep_odd(a, b, k), ys, ks, idx, pos));
}

/// Rejects retaining an element the function said to drop (`w = 3`).
pub proof fn lemma_compact_map_spec_rejects_extra(
    new: Seq<u8>, ys: Seq<u8>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>,
)
    ensures
        !compact_map_post(seq![1u8, 2u8, 3u8], new, 3, |a: u8, b: u8, k: bool| times10_keep_odd(a, b, k), ys, ks, idx, pos),
{
    let old = seq![1u8, 2u8, 3u8];
    if compact_map_post(old, new, 3, |a: u8, b: u8, k: bool| times10_keep_odd(a, b, k), ys, ks, idx, pos) {
        assert(idx[0] < idx[1] && idx[1] < idx[2] && idx[2] < 3 && 0 <= idx[0]);
        assert(idx[1] == 1);
        assert(new[1] == ys[idx[1]] && ks[idx[1]]);
        assert(times10_keep_odd(old[1], ys[1], ks[1]));
    }
}

/// Rejects dropping an element the function said to keep (`w = 1`).
pub proof fn lemma_compact_map_spec_rejects_missing(
    new: Seq<u8>, ys: Seq<u8>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>,
)
    ensures
        !compact_map_post(seq![1u8, 2u8, 3u8], new, 1, |a: u8, b: u8, k: bool| times10_keep_odd(a, b, k), ys, ks, idx, pos),
{
    let old = seq![1u8, 2u8, 3u8];
    if compact_map_post(old, new, 1, |a: u8, b: u8, k: bool| times10_keep_odd(a, b, k), ys, ks, idx, pos) {
        assert(times10_keep_odd(old[0], ys[0], ks[0]));
        assert(times10_keep_odd(old[2], ys[2], ks[2]));
        assert(ks[0] && ks[2]);
        assert(idx[pos[0]] == 0 && idx[pos[2]] == 2);
    }
}

/// Rejects returning untransformed values (`new[0] == 1`).
pub proof fn lemma_compact_map_spec_rejects_unmapped(
    rest: Seq<u8>, ys: Seq<u8>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>,
)
    ensures
        !compact_map_post(seq![1u8, 2u8, 3u8], seq![1u8].add(rest), 2, |a: u8, b: u8, k: bool| times10_keep_odd(a, b, k), ys, ks, idx, pos),
{
    let old = seq![1u8, 2u8, 3u8];
    let new = seq![1u8].add(rest);
    if compact_map_post(old, new, 2, |a: u8, b: u8, k: bool| times10_keep_odd(a, b, k), ys, ks, idx, pos) {
        assert(new[0] == 1u8);
        assert(new[0] == ys[idx[0]]);
        assert(0 <= idx[0] < 3);
        assert(times10_keep_odd(old[idx[0]], ys[idx[0]], ks[idx[0]]));
    }
}

// ---- Specifications of the strict variants (`crate::strict`), whose callables are
// `fip_strict::FipFn` values: the relation is `FipFn::post` instead of a closure's
// `ensures`. Written and pre-verified before `crate::strict` was implemented.

/// Postcondition of `compact` on `old` → `new` with result `w`, where `keep(a, r)`
/// means "the predicate may return `r` on `a`": `new` is a permutation of `old`;
/// `keep` returned `true` before `w` and `false` from `w` on; the first `w` elements
/// are `old[idx[0]], old[idx[1]], ..` with `idx` strictly increasing.
pub open spec fn compact_post<A>(old: Seq<A>, new: Seq<A>, w: int, keep: spec_fn(A, bool) -> bool) -> bool {
    &&& 0 <= w <= old.len()
    &&& new.len() == old.len()
    &&& new.to_multiset() == old.to_multiset()
    &&& forall|i: int| 0 <= i < w ==> keep(#[trigger] new[i], true)
    &&& forall|i: int| w <= i < new.len() ==> keep(#[trigger] new[i], false)
    &&& exists|idx: Seq<int>| idx.len() == w
        && #[trigger] strictly_increasing_below(idx, old.len() as int)
        && forall|i: int| 0 <= i < w ==> new[i] == old[idx[i]]
}

/// `compact_post` for a `FipFn` predicate.
pub open spec fn compact_fip_post<A, F: for<'a> FipFn<(&'a A,), Output = bool>>(
    old: Seq<A>,
    new: Seq<A>,
    w: int,
    keep: F,
) -> bool {
    compact_post(old, new, w, |a: A, r: bool| keep.post((&a,), r))
}

/// `dedup_post` for a `FipFn` predicate.
pub open spec fn dedup_fip_post<A, F: for<'a, 'b> FipFn<(&'a A, &'b A), Output = bool>>(
    old: Seq<A>,
    new: Seq<A>,
    w: int,
    same: F,
    idx: Seq<int>,
    src: Seq<int>,
) -> bool {
    dedup_post(old, new, w, |a: A, b: A, r: bool| same.post((&a, &b), r), idx, src)
}

/// `compact_map_post` for a `FipFn` function.
pub open spec fn compact_map_fip_post<A, F: FipFn<(A,), Output = (A, bool)>>(
    old: Seq<A>,
    new: Seq<A>,
    w: int,
    f: F,
    ys: Seq<A>,
    ks: Seq<bool>,
    idx: Seq<int>,
    pos: Seq<int>,
) -> bool {
    compact_map_post(old, new, w, |a: A, b: A, k: bool| f.post((a,), (b, k)), ys, ks, idx, pos)
}

/// Example predicate: "is even".
pub open spec fn even_rel(a: u8, r: bool) -> bool {
    r == (a % 2 == 0)
}

/// `compact_post` accepts the intended answer: `[1, 2, 3, 4]` → `[2, 4 | 3, 1]`.
pub proof fn lemma_compact_spec_accepts_intended()
    ensures
        compact_post(seq![1u8, 2u8, 3u8, 4u8], seq![2u8, 4u8, 3u8, 1u8], 2, |a: u8, r: bool| even_rel(a, r)),
{
    let old = seq![1u8, 2u8, 3u8, 4u8];
    let mid = seq![2u8, 1u8, 3u8, 4u8];
    let new = seq![2u8, 4u8, 3u8, 1u8];
    lemma_swap_multiset(old, 0, 1);
    assert(mid =~= old.update(0, old[1]).update(1, old[0]));
    lemma_swap_multiset(mid, 1, 3);
    assert(new =~= mid.update(1, mid[3]).update(3, mid[1]));
    let idx = seq![1int, 3int];
    assert(strictly_increasing_below(idx, 4));
    assert(compact_post(old, new, 2, |a: u8, r: bool| even_rel(a, r)));
}

/// Rejects the unchanged slice with `w = 2` (an implementation that never swaps).
pub proof fn lemma_compact_spec_rejects_unmoved()
    ensures
        !compact_post(seq![1u8, 2u8, 3u8, 4u8], seq![1u8, 2u8, 3u8, 4u8], 2, |a: u8, r: bool| even_rel(a, r)),
{
    let s = seq![1u8, 2u8, 3u8, 4u8];
    if compact_post(s, s, 2, |a: u8, r: bool| even_rel(a, r)) {
        assert(even_rel(s[0], true));
    }
}

/// Rejects the kept elements out of order: `[4, 2 | 1, 3]`.
pub proof fn lemma_compact_spec_rejects_reordered()
    ensures
        !compact_post(seq![1u8, 2u8, 3u8, 4u8], seq![4u8, 2u8, 1u8, 3u8], 2, |a: u8, r: bool| even_rel(a, r)),
{
    let old = seq![1u8, 2u8, 3u8, 4u8];
    let new = seq![4u8, 2u8, 1u8, 3u8];
    if compact_post(old, new, 2, |a: u8, r: bool| even_rel(a, r)) {
        let idx = choose|idx: Seq<int>| idx.len() == 2
            && #[trigger] strictly_increasing_below(idx, 4)
            && forall|i: int| 0 <= i < 2 ==> new[i] == old[idx[i]];
        assert(new[0] == old[idx[0]] && new[1] == old[idx[1]]);
        assert(0 <= idx[0] < 4 && 0 <= idx[1] < 4 && idx[0] < idx[1]);
        assert(old[0] == 1 && old[1] == 2 && old[2] == 3 && old[3] == 4);
        assert(idx[0] == 3);
    }
}

/// The `FipFn` forms are the relational specs with `post` as the relation: for a
/// predicate whose `post` is "is even" / "equal", `compact_fip_post` and
/// `dedup_fip_post` accept and reject exactly what `compact_post` / `dedup_post` do
/// on the cases above.
pub proof fn lemma_fip_specs_follow_post<
    K: for<'a> FipFn<(&'a u8,), Output = bool>,
    S: for<'a, 'b> FipFn<(&'a u8, &'b u8), Output = bool>,
>(keep: K, same: S, new: Seq<u8>, idx: Seq<int>, src: Seq<int>)
    requires
        forall|a: u8, r: bool| #[trigger] keep.post((&a,), r) == even_rel(a, r),
        forall|a: u8, b: u8, r: bool| #[trigger] same.post((&a, &b), r) == eq_rel(a, b, r),
    ensures
        compact_fip_post(seq![1u8, 2u8, 3u8, 4u8], seq![2u8, 4u8, 3u8, 1u8], 2, keep),
        !compact_fip_post(seq![1u8, 2u8, 3u8, 4u8], seq![1u8, 2u8, 3u8, 4u8], 2, keep),
        !compact_fip_post(seq![1u8, 2u8, 3u8, 4u8], seq![4u8, 2u8, 1u8, 3u8], 2, keep),
        dedup_fip_post(seq![1u8, 1u8, 2u8], seq![1u8, 2u8, 1u8], 2, same, seq![0int, 2int], seq![0int, 0int, 1int]),
        !dedup_fip_post(seq![1u8, 1u8, 2u8], new, 3, same, idx, src),
        !dedup_fip_post(seq![1u8, 2u8], new, 1, same, idx, src),
{
    assert((|a: u8, r: bool| keep.post((&a,), r)) =~= (|a: u8, r: bool| even_rel(a, r)));
    assert((|a: u8, b: u8, r: bool| same.post((&a, &b), r)) =~= (|a: u8, b: u8, r: bool| eq_rel(a, b, r)));
    lemma_compact_spec_accepts_intended();
    lemma_compact_spec_rejects_unmoved();
    lemma_compact_spec_rejects_reordered();
    lemma_dedup_spec_accepts_intended();
    lemma_dedup_spec_rejects_kept_duplicate(new, idx, src);
    lemma_dedup_spec_rejects_wrong_merge(new, idx, src);
}

/// Same for `compact_map_fip_post` with `post` = "times 10, keep odd inputs".
pub proof fn lemma_compact_map_fip_spec_follows_post<F: FipFn<(u8,), Output = (u8, bool)>>(
    f: F, new: Seq<u8>, ys: Seq<u8>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>,
)
    requires
        forall|a: u8, b: u8, k: bool| #[trigger] f.post((a,), (b, k)) == times10_keep_odd(a, b, k),
    ensures
        compact_map_fip_post(seq![1u8, 2u8, 3u8], seq![10u8, 30u8, 20u8], 2, f,
            seq![10u8, 20u8, 30u8], seq![true, false, true], seq![0int, 2int], seq![0int, -1int, 1int]),
        !compact_map_fip_post(seq![1u8, 2u8, 3u8], new, 3, f, ys, ks, idx, pos),
        !compact_map_fip_post(seq![1u8, 2u8, 3u8], new, 1, f, ys, ks, idx, pos),
{
    assert((|a: u8, b: u8, k: bool| f.post((a,), (b, k))) =~= (|a: u8, b: u8, k: bool| times10_keep_odd(a, b, k)));
    lemma_compact_map_spec_accepts_intended();
    lemma_compact_map_spec_rejects_extra(new, ys, ks, idx, pos);
    lemma_compact_map_spec_rejects_missing(new, ys, ks, idx, pos);
}

} // verus!

/// Specifications of the state-passing variants (`map_in_place_st`, `compact_map_st`
/// and their strict forms). A separate module so that they do not enter the SMT
/// context of the module above: Verus gives each module's queries all of that
/// module's definitions, and with these definitions added there Z3 failed
/// `lemma_compact_map_spec_rejects_extra` (measured, deterministic across seeds).
pub mod state {

    use super::{lemma_swap_multiset, strictly_increasing_below};
    use fip_strict::FipFn;
    use vstd::prelude::*;

    verus! {

    // The callable takes the state by value and returns the next one, so the
    // specification can name every intermediate state. Written and pre-verified before
    // the functions were implemented.

    /// Postcondition of `map_in_place_st` on `old` → `new`, from state `s0` to the
    /// returned state `s`, where `step(a, x, b, y)` means "the function may map state `a`
    /// and element `x` to state `b` and element `y`".
    ///
    /// Witness: `ss` is the state trace, `ss[0] == s0`, `ss[len] == s`; step `k` took
    /// `(ss[k], old[k])` to `(ss[k + 1], new[k])`, so the calls happened once per
    /// element, in index order, each on the state the previous one returned.
    pub open spec fn map_st_post<S, A>(
        old: Seq<A>,
        new: Seq<A>,
        step: spec_fn(S, A, S, A) -> bool,
        s0: S,
        s: S,
        ss: Seq<S>,
    ) -> bool {
        &&& new.len() == old.len()
        &&& ss.len() == old.len() + 1
        &&& ss[0] == s0
        &&& ss[old.len() as int] == s
        &&& forall|k: int| 0 <= k < old.len() ==> step(ss[k], old[k], ss[k + 1], #[trigger] new[k])
    }

    /// `map_st_post` for an exec function `f`.
    pub open spec fn map_st_by_post<S, A, F: Fn(S, A) -> (S, A)>(
        old: Seq<A>,
        new: Seq<A>,
        f: F,
        s0: S,
        s: S,
        ss: Seq<S>,
    ) -> bool {
        map_st_post(old, new, |a: S, x: A, b: S, y: A| f.ensures((a, x), (b, y)), s0, s, ss)
    }

    /// `map_st_post` for a `FipFn` function.
    pub open spec fn map_st_fip_post<S, A, F: FipFn<(S, A), Output = (S, A)>>(
        old: Seq<A>,
        new: Seq<A>,
        f: F,
        s0: S,
        s: S,
        ss: Seq<S>,
    ) -> bool {
        map_st_post(old, new, |a: S, x: A, b: S, y: A| f.post((a, x), (b, y)), s0, s, ss)
    }

    /// Postcondition of `compact_map_st`, where `step(a, x, b, y, k)` means "the
    /// function may map state `a` and element `x` to state `b`, value `y` and keep flag
    /// `k`".
    ///
    /// Witnesses as in `compact_map_post`, plus the state trace `ss` (`ss[0] == s0`,
    /// `ss[len] == s`): step `j` took `(ss[j], old[j])` to `(ss[j + 1], ys[j], ks[j])`.
    /// The arrangement conjuncts are those of `compact_map_post` (`new` is a permutation
    /// of `ys`; the first `w` are the kept ones, in original order; every kept one is
    /// among them).
    pub open spec fn compact_map_st_post<S, A>(
        old: Seq<A>,
        new: Seq<A>,
        w: int,
        step: spec_fn(S, A, S, A, bool) -> bool,
        s0: S,
        s: S,
        ss: Seq<S>,
        ys: Seq<A>,
        ks: Seq<bool>,
        idx: Seq<int>,
        pos: Seq<int>,
    ) -> bool {
        &&& ss.len() == old.len() + 1
        &&& ss[0] == s0
        &&& ss[old.len() as int] == s
        &&& ys.len() == old.len()
        &&& ks.len() == old.len()
        &&& forall|j: int| 0 <= j < old.len() ==> step(ss[j], old[j], ss[j + 1], #[trigger] ys[j], ks[j])
        &&& new.len() == old.len()
        &&& new.to_multiset() == ys.to_multiset()
        &&& 0 <= w <= old.len()
        &&& idx.len() == w
        &&& strictly_increasing_below(idx, old.len() as int)
        &&& forall|i: int| 0 <= i < w ==> #[trigger] new[i] == ys[idx[i]] && ks[idx[i]]
        &&& pos.len() == old.len()
        &&& forall|j: int| 0 <= j < old.len() && #[trigger] ks[j] ==> 0 <= pos[j] < w && idx[pos[j]] == j
    }

    /// `compact_map_st_post` for an exec function `f`.
    pub open spec fn compact_map_st_by_post<S, A, F: Fn(S, A) -> (S, A, bool)>(
        old: Seq<A>,
        new: Seq<A>,
        w: int,
        f: F,
        s0: S,
        s: S,
        ss: Seq<S>,
        ys: Seq<A>,
        ks: Seq<bool>,
        idx: Seq<int>,
        pos: Seq<int>,
    ) -> bool {
        compact_map_st_post(old, new, w, |a: S, x: A, b: S, y: A, k: bool| f.ensures((a, x), (b, y, k)),
            s0, s, ss, ys, ks, idx, pos)
    }

    /// `compact_map_st_post` for a `FipFn` function.
    pub open spec fn compact_map_st_fip_post<S, A, F: FipFn<(S, A), Output = (S, A, bool)>>(
        old: Seq<A>,
        new: Seq<A>,
        w: int,
        f: F,
        s0: S,
        s: S,
        ss: Seq<S>,
        ys: Seq<A>,
        ks: Seq<bool>,
        idx: Seq<int>,
        pos: Seq<int>,
    ) -> bool {
        compact_map_st_post(old, new, w, |a: S, x: A, b: S, y: A, k: bool| f.post((a, x), (b, y, k)),
            s0, s, ss, ys, ks, idx, pos)
    }

    /// Example step: a counter state; each element becomes its value plus the new count.
    pub open spec fn count_up(s: u8, x: u8, s2: u8, y: u8) -> bool {
        s2 == s + 1 && y == x + s2
    }

    /// Accepts the intended answer: counter 10 over `[0, 0, 0]` → `[11, 12, 13]`, final 13.
    pub proof fn lemma_map_st_spec_accepts_intended()
        ensures
            map_st_post(seq![0u8, 0u8, 0u8], seq![11u8, 12u8, 13u8], |a: u8, x: u8, b: u8, y: u8| count_up(a, x, b, y),
                10u8, 13u8, seq![10u8, 11u8, 12u8, 13u8]),
    {
        let new = seq![11u8, 12u8, 13u8];
        assert(new[0] == 11 && new[1] == 12 && new[2] == 13);
    }

    /// Rejects a wrong final state (14), whatever the elements and the trace.
    pub proof fn lemma_map_st_spec_rejects_wrong_final(new: Seq<u8>, ss: Seq<u8>)
        ensures
            !map_st_post(seq![0u8, 0u8, 0u8], new, |a: u8, x: u8, b: u8, y: u8| count_up(a, x, b, y), 10u8, 14u8, ss),
    {
        let old = seq![0u8, 0u8, 0u8];
        if map_st_post(old, new, |a: u8, x: u8, b: u8, y: u8| count_up(a, x, b, y), 10u8, 14u8, ss) {
            assert(count_up(ss[0], old[0], ss[1], new[0]));
            assert(count_up(ss[1], old[1], ss[2], new[1]));
            assert(count_up(ss[2], old[2], ss[3], new[2]));
        }
    }

    /// Rejects a state that is not threaded (every call sees `s0`: `[11, 11, 11]`).
    pub proof fn lemma_map_st_spec_rejects_unthreaded(s: u8, ss: Seq<u8>)
        ensures
            !map_st_post(seq![0u8, 0u8, 0u8], seq![11u8, 11u8, 11u8], |a: u8, x: u8, b: u8, y: u8| count_up(a, x, b, y), 10u8, s, ss),
    {
        let old = seq![0u8, 0u8, 0u8];
        let new = seq![11u8, 11u8, 11u8];
        if map_st_post(old, new, |a: u8, x: u8, b: u8, y: u8| count_up(a, x, b, y), 10u8, s, ss) {
            assert(count_up(ss[0], old[0], ss[1], new[0]));
            assert(count_up(ss[1], old[1], ss[2], new[1]));
        }
    }

    /// Rejects the state threaded in reverse index order (`[13, 12, 11]`).
    pub proof fn lemma_map_st_spec_rejects_reversed(s: u8, ss: Seq<u8>)
        ensures
            !map_st_post(seq![0u8, 0u8, 0u8], seq![13u8, 12u8, 11u8], |a: u8, x: u8, b: u8, y: u8| count_up(a, x, b, y), 10u8, s, ss),
    {
        let old = seq![0u8, 0u8, 0u8];
        let new = seq![13u8, 12u8, 11u8];
        if map_st_post(old, new, |a: u8, x: u8, b: u8, y: u8| count_up(a, x, b, y), 10u8, s, ss) {
            assert(count_up(ss[0], old[0], ss[1], new[0]));
        }
    }

    /// Example step: a counter state; each element becomes its value plus the new count,
    /// kept if the input was odd.
    pub open spec fn count_up_keep_odd(s: u8, x: u8, s2: u8, y: u8, k: bool) -> bool {
        count_up(s, x, s2, y) && k == (x % 2 == 1)
    }

    /// Accepts the intended answer: counter 0 over `[1, 2, 3]` → `[2, 6 | 4]`, `w = 2`,
    /// final 3.
    pub proof fn lemma_compact_map_st_spec_accepts_intended()
        ensures
            compact_map_st_post(seq![1u8, 2u8, 3u8], seq![2u8, 6u8, 4u8], 2,
                |a: u8, x: u8, b: u8, y: u8, k: bool| count_up_keep_odd(a, x, b, y, k), 0u8, 3u8,
                seq![0u8, 1u8, 2u8, 3u8], seq![2u8, 4u8, 6u8], seq![true, false, true], seq![0int, 2int], seq![0int, -1int, 1int]),
    {
        let ys = seq![2u8, 4u8, 6u8];
        let new = seq![2u8, 6u8, 4u8];
        lemma_swap_multiset(ys, 1, 2);
        assert(new =~= ys.update(1, ys[2]).update(2, ys[1]));
        assert(ys[0] == 2 && ys[1] == 4 && ys[2] == 6);
    }

    /// Rejects a wrong final state (4), whatever the witnesses.
    pub proof fn lemma_compact_map_st_spec_rejects_wrong_final(
        new: Seq<u8>, w: int, ss: Seq<u8>, ys: Seq<u8>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>,
    )
        ensures
            !compact_map_st_post(seq![1u8, 2u8, 3u8], new, w,
                |a: u8, x: u8, b: u8, y: u8, k: bool| count_up_keep_odd(a, x, b, y, k), 0u8, 4u8, ss, ys, ks, idx, pos),
    {
        let old = seq![1u8, 2u8, 3u8];
        if compact_map_st_post(old, new, w, |a: u8, x: u8, b: u8, y: u8, k: bool| count_up_keep_odd(a, x, b, y, k),
            0u8, 4u8, ss, ys, ks, idx, pos) {
            assert(count_up_keep_odd(ss[0], old[0], ss[1], ys[0], ks[0]));
            assert(count_up_keep_odd(ss[1], old[1], ss[2], ys[1], ks[1]));
            assert(count_up_keep_odd(ss[2], old[2], ss[3], ys[2], ks[2]));
        }
    }

    /// The `FipFn` forms are the relational specs with `post` as the relation.
    pub proof fn lemma_st_fip_specs_follow_post<
        M: FipFn<(u8, u8), Output = (u8, u8)>,
        C: FipFn<(u8, u8), Output = (u8, u8, bool)>,
    >(m: M, c: C, new: Seq<u8>, w: int, ss: Seq<u8>, ys: Seq<u8>, ks: Seq<bool>, idx: Seq<int>, pos: Seq<int>)
        requires
            forall|a: u8, x: u8, b: u8, y: u8| #[trigger] m.post((a, x), (b, y)) == count_up(a, x, b, y),
            forall|a: u8, x: u8, b: u8, y: u8, k: bool| #[trigger] c.post((a, x), (b, y, k)) == count_up_keep_odd(a, x, b, y, k),
        ensures
            map_st_fip_post(seq![0u8, 0u8, 0u8], seq![11u8, 12u8, 13u8], m, 10u8, 13u8, seq![10u8, 11u8, 12u8, 13u8]),
            !map_st_fip_post(seq![0u8, 0u8, 0u8], new, m, 10u8, 14u8, ss),
            compact_map_st_fip_post(seq![1u8, 2u8, 3u8], seq![2u8, 6u8, 4u8], 2, c, 0u8, 3u8,
                seq![0u8, 1u8, 2u8, 3u8], seq![2u8, 4u8, 6u8], seq![true, false, true], seq![0int, 2int], seq![0int, -1int, 1int]),
            !compact_map_st_fip_post(seq![1u8, 2u8, 3u8], new, w, c, 0u8, 4u8, ss, ys, ks, idx, pos),
    {
        assert((|a: u8, x: u8, b: u8, y: u8| m.post((a, x), (b, y))) =~= (|a: u8, x: u8, b: u8, y: u8| count_up(a, x, b, y)));
        assert((|a: u8, x: u8, b: u8, y: u8, k: bool| c.post((a, x), (b, y, k)))
            =~= (|a: u8, x: u8, b: u8, y: u8, k: bool| count_up_keep_odd(a, x, b, y, k)));
        lemma_map_st_spec_accepts_intended();
        lemma_map_st_spec_rejects_wrong_final(new, ss);
        lemma_compact_map_st_spec_accepts_intended();
        lemma_compact_map_st_spec_rejects_wrong_final(new, w, ss, ys, ks, idx, pos);
    }

    } // verus!
} // mod state
