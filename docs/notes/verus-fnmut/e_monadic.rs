// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
// Probe for docs/notes/verus-fnmut-monadic-workaround.md; run: verus e_monadic.rs
use vstd::prelude::*;
verus! {

// State-passing ("monadic") step: f : (S, x) -> (S', keep).  No &mut, no captured mutable state.
pub open spec fn chain<S, F: Fn(S, u32) -> (S, bool)>(f: F, xs: Seq<u32>, ss: Seq<S>, bs: Seq<bool>) -> bool {
    &&& ss.len() == xs.len() + 1
    &&& bs.len() == xs.len()
    &&& forall|k: int| 0 <= k < xs.len() ==> #[trigger] call_ensures(f, (ss[k], xs[k]), (ss[k + 1], bs[k]))
}

pub open spec fn count_true(bs: Seq<bool>) -> nat decreases bs.len() {
    if bs.len() == 0 { 0 } else { count_true(bs.drop_last()) + if bs.last() { 1nat } else { 0nat } }
}

fn count_st<S, F: Fn(S, u32) -> (S, bool)>(xs: &Vec<u32>, s0: S, f: F) -> (r: (usize, S))
    requires forall|s: S, x: u32| #[trigger] f.requires((s, x)),
    ensures exists|ss: Seq<S>, bs: Seq<bool>|
        chain(f, xs@, ss, bs) && ss[0] == s0 && ss.last() == r.1 && r.0 == count_true(bs),
{
    let mut s = s0;
    let mut n: usize = 0;
    let mut i: usize = 0;
    let ghost mut ss: Seq<S> = seq![s0];
    let ghost mut bs: Seq<bool> = Seq::empty();
    while i < xs.len()
        invariant
            i <= xs.len(),
            forall|s: S, x: u32| #[trigger] f.requires((s, x)),
            ss.len() == i + 1, bs.len() == i,
            ss[0] == s0, ss.last() == s,
            forall|k: int| 0 <= k < i ==> #[trigger] call_ensures(f, (ss[k], xs@[k]), (ss[k + 1], bs[k])),
            n == count_true(bs), n <= i,
        decreases xs.len() - i,
    {
        let ghost s_prev = s;
        let (s2, b) = f(s, xs[i]);
        proof {
            let ghost old_bs = bs;
            ss = ss.push(s2);
            bs = bs.push(b);
            assert(bs.drop_last() =~= old_bs);
            assert(call_ensures(f, (ss[i as int], xs@[i as int]), (ss[i as int + 1], bs[i as int])));
        }
        s = s2;
        if b { n += 1; }
        i += 1;
    }
    proof { assert(chain(f, xs@, ss, bs)); }
    (n, s)
}

// Verified caller: a counter threaded through the state.
fn caller() {
    let mut xs: Vec<u32> = Vec::new(); xs.push(1); xs.push(2); xs.push(3);
    assert(xs@ =~= seq![1u32, 2, 3]);
    let step = |s: u32, x: u32| -> (r: (u32, bool))
        ensures r.0 == if s < 1000 { (s + 1) as u32 } else { s }, r.1 == (x % 2 == 0)
    { (if s < 1000 { s + 1 } else { s }, x % 2 == 0) };
    let (n, s) = count_st(&xs, 0u32, step);
    assert(n <= 3) by {
        let (ss, bs) = choose|ss: Seq<u32>, bs: Seq<bool>|
            chain(step, xs@, ss, bs) && ss[0] == 0u32 && ss.last() == s && n == count_true(bs);
        assert(bs.len() == 3);
        reveal_with_fuel(count_true, 4);
    };
    assert(s == 3) by {
        let (ss, bs) = choose|ss: Seq<u32>, bs: Seq<bool>|
            chain(step, xs@, ss, bs) && ss[0] == 0u32 && ss.last() == s && n == count_true(bs);
        assert(call_ensures(step, (ss[0], xs@[0]), (ss[1], bs[0])));
        assert(call_ensures(step, (ss[1], xs@[1]), (ss[2], bs[1])));
        assert(call_ensures(step, (ss[2], xs@[2]), (ss[3], bs[2])));
    };
}

fn main() {}
}
