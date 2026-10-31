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

} // verus!
