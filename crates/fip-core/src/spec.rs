// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Specification helpers. Compiled only under the `verus` driver.

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
pub proof fn lemma_dedup_spec_accepts_intended() {
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
pub proof fn lemma_compact_map_spec_accepts_intended() {
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

} // verus!
