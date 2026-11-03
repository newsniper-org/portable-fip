// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Driver-checked `fip_fn!(prelint, N, ..)`: the declared bound `N` is checked by the
//! driver at the construction (allocations at most `N` per call, no free, no
//! recursion), not by `fip-macros` (no token scan of the body).

use fip_macros::{fip, fip_fn};
use fip_strict::FipFn;

/// Declares `param(g = 0)`: takes a certified value of bound 0.
#[fip(strict = true, param(g = 0))]
pub fn apply0<F: FipFn<(u32,), Output = u32>>(g: F) -> u32 {
    g.call((5,))
}

/// A method call (the strict token scan rejects it): passes.
pub fn ok_method() -> u32 {
    apply0(fip_fn!(prelint, 0, |x: u32| x.wrapping_add(1).count_ones()))
}

/// An inferred local and two parameters, one a reference: passes.
pub fn ok_two(y: u32) -> u32 {
    let f = fip_fn!(prelint, 0, |a: u32, b: &u32| {
        let s = a.rotate_left(3);
        s ^ *b
    });
    f.call((1, &y))
}

/// Allocates once, claims 0: rejected.
pub fn lie() -> u32 {
    let f = fip_fn!(prelint, 0, |x: u32| *Box::new(x));
    f.call((1,))
}

/// Recursive, not marked.
pub fn countdown(n: u32) -> u32 {
    if n == 0 { 0 } else { countdown(n - 1) }
}

/// Recursion reached from the closure: rejected.
pub fn recursive() -> u32 {
    let f = fip_fn!(prelint, 0, |x: u32| countdown(x));
    f.call((3,))
}

/// Frees its argument: rejected.
pub fn frees() -> u32 {
    let f = fip_fn!(prelint, 0, |b: Box<u32>| *b);
    f.call((Box::new(1),))
}

/// Allocates once within the claim 1 but drops the box: rejected (a free; the token
/// scan accepts this body with bound 1).
pub fn frees_own() -> u32 {
    let f = fip_fn!(prelint, 1, |x: u32| *Box::new(x));
    f.call((1,))
}

/// Honest claim 1 for one allocation: passes.
pub fn honest() -> u32 {
    let f = fip_fn!(prelint, 1, |x: u32| Box::new(x));
    *f.call((2,))
}

/// A construction inside a generic function capturing a value of the type
/// parameter: allocation-free, so its driver-mode check passes; the driver's
/// `Certified::assume` check reports the closure type as a generic callable type
/// (`⊤`), as it does for the default `fip_fn!` in a generic function.
pub fn generic_ok<T: Copy>(t: T) -> u32 {
    let f = fip_fn!(prelint, 0, move |x: u32| {
        let _keep = t;
        x ^ 1
    });
    f.call((1,))
}

/// The same, allocating under claim 0: rejected by the driver-mode check.
pub fn generic_lie<T: Copy>(t: T) -> u32 {
    let f = fip_fn!(prelint, 0, move |x: u32| {
        let _keep = t;
        *Box::new(x)
    });
    f.call((1,))
}

/// Instantiates both generic functions.
pub fn generic_instances() -> u32 {
    generic_ok::<u8>(1) + generic_lie::<u16>(2)
}
