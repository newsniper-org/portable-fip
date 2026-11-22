// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Deallocation totals of the slice combinators' callbacks (the fork's `deallocates`
//! clauses, 2026-11-22): the counterparts of `spec::map_allocs` and its like.

use vstd::prelude::*;

verus! {

/// `deallocates` total of calling `f` once on each of the first `n` elements of `s`.
pub open spec fn map_deallocs<T, F: Fn(T) -> T>(f: F, s: Seq<T>, n: int) -> nat
    decreases n,
{
    if n <= 0 { 0 } else { map_deallocs(f, s, n - 1) + call_deallocations(f, (s[n - 1],)) }
}

/// `deallocates` total of calling `keep` once on each of the first `n` elements of `s`.
pub open spec fn compact_deallocs<T, F: Fn(&T) -> bool>(keep: F, s: Seq<T>, n: int) -> nat
    decreases n,
{
    if n <= 0 { 0 } else { compact_deallocs(keep, s, n - 1) + call_deallocations(keep, (&s[n - 1],)) }
}

/// `deallocates` total of calling `f` once on each of the first `n` elements of `s`.
pub open spec fn compact_map_deallocs<T, F: Fn(T) -> (T, bool)>(f: F, s: Seq<T>, n: int) -> nat
    decreases n,
{
    if n <= 0 { 0 } else { compact_map_deallocs(f, s, n - 1) + call_deallocations(f, (s[n - 1],)) }
}

} // verus!

verus! {

/// Callbacks that deallocate nothing on every element make [`map_deallocs`] zero.
pub broadcast proof fn lemma_map_deallocs_zero<T, F: Fn(T) -> T>(f: F, s: Seq<T>, n: int)
    ensures
        (forall|i: int| 0 <= i < n ==> #[trigger] call_deallocations(f, (s[i],)) == 0) ==> #[trigger] map_deallocs(f, s, n) == 0,
    decreases n,
{
    if n > 0 { lemma_map_deallocs_zero(f, s, n - 1); }
}

/// Callbacks that deallocate nothing on every element make [`compact_deallocs`] zero.
pub broadcast proof fn lemma_compact_deallocs_zero<T, F: Fn(&T) -> bool>(keep: F, s: Seq<T>, n: int)
    ensures
        (forall|i: int| 0 <= i < n ==> #[trigger] call_deallocations(keep, (&s[i],)) == 0) ==> #[trigger] compact_deallocs(keep, s, n) == 0,
    decreases n,
{
    if n > 0 { lemma_compact_deallocs_zero(keep, s, n - 1); }
}

/// Callbacks that deallocate nothing on every element make [`compact_map_deallocs`] zero.
pub broadcast proof fn lemma_compact_map_deallocs_zero<T, F: Fn(T) -> (T, bool)>(f: F, s: Seq<T>, n: int)
    ensures
        (forall|i: int| 0 <= i < n ==> #[trigger] call_deallocations(f, (s[i],)) == 0) ==> #[trigger] compact_map_deallocs(f, s, n) == 0,
    decreases n,
{
    if n > 0 { lemma_compact_map_deallocs_zero(f, s, n - 1); }
}

pub broadcast group group_deallocs_zero {
    lemma_map_deallocs_zero,
    lemma_compact_deallocs_zero,
    lemma_compact_map_deallocs_zero,
}

} // verus!
