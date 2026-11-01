// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
// Probe for docs/notes/verus-fnmut-monadic-workaround.md; run: verus d_state_arg.rs
use vstd::prelude::*;
verus! {
fn count_with<S, F: Fn(&mut S, u32) -> bool>(xs: &Vec<u32>, st: &mut S, keep: F) -> (n: usize)
    requires forall|s: &mut S, x: u32| keep.requires((s, x)),
    ensures n <= xs.len(),
{
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < xs.len()
        invariant n <= i <= xs.len(), forall|s: &mut S, x: u32| keep.requires((s, x)),
        decreases xs.len() - i,
    {
        if keep(st, xs[i]) { n += 1; }
        i += 1;
    }
    n
}
fn main() {
    let xs = vec![1u32, 2, 3];
    let mut c: u32 = 0;
    let n = count_with(&xs, &mut c, |s: &mut u32, x: u32| -> (b: bool)
        ensures *final(s) == if *old(s) < 100 { (*old(s) + 1) as u32 } else { *old(s) }
    { if *s < 100 { *s = *s + 1; } x % 2 == 0 });
}
}
