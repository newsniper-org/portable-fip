// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
// Probe for docs/notes/verus-fnmut-monadic-workaround.md; run: verus c_state.rs
use vstd::prelude::*;
verus! {
fn pre_state_relation<F: FnMut(u32) -> bool>(mut f: F)
    requires forall|x: u32| f.requires((x,)),
{
    let ghost f0 = f;
    let b = f(1);
    assert(call_ensures(f0, (1u32,), b));
}
fn state_unchanged<F: FnMut(u32) -> bool>(mut f: F)
    requires forall|x: u32| f.requires((x,)),
{
    let ghost f0 = f;
    let b = f(1);
    assert(f == f0); // should fail if the post-state is modelled
}
fn main() {}
}
