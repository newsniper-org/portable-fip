// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
// Probe for docs/notes/verus-fnmut-monadic-workaround.md; run: verus a_generic.rs
use vstd::prelude::*;
verus! {
// (A) generic FnMut parameter, called in a loop
fn count_keep<F: FnMut(u32) -> bool>(xs: &Vec<u32>, mut keep: F) -> (n: usize)
    requires forall|x: u32| keep.requires((x,)),
    ensures n <= xs.len(),
{
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < xs.len()
        invariant n <= i <= xs.len(), forall|x: u32| keep.requires((x,)),
        decreases xs.len() - i,
    {
        if keep(xs[i]) { n += 1; }
        i += 1;
    }
    n
}
fn main() {}
}
