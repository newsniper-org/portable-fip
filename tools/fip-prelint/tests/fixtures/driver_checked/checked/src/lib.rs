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
/// parameter: allocation-free, so its driver-mode check passes. The closure type is
/// generic only through `T` and never a function pointer, so the `Certified::assume`
/// check analyses it through its body (it was a generic callable type, `⊤`).
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

/// A default `fip_fn!` inside a generic function, passed to a `param(g = 0)`
/// callee: the closure type is generic only through `T`, never a function pointer,
/// so the `Certified::assume` check analyses it through its body: passes.
pub fn generic_default<T: Copy>(t: T) -> u32 {
    apply0(fip_fn!(move |x: u32| {
        let _keep = t;
        x ^ 1
    }))
}

/// A trait whose implementations differ in allocation.
pub trait Make {
    /// Makes a value.
    fn make(x: u32) -> u32;
}

/// Allocation-free.
pub struct Plain;
impl Make for Plain {
    fn make(x: u32) -> u32 {
        x
    }
}

/// Allocates.
pub struct Heap;
impl Make for Heap {
    fn make(x: u32) -> u32 {
        *Box::new(x)
    }
}

/// A driver-mode construction calling a method of the type parameter: the generic
/// body leaves the term `<T as Make>::make`, and the certificate claims bound 0 for
/// every instantiation (`generic_term::<Heap>` allocates): `⊤` with that reason.
pub fn generic_term<T: Make>() -> u32 {
    let f = fip_fn!(prelint, 0, |x: u32| T::make(x));
    f.call((1,))
}

/// Instantiates `generic_term` with both implementations and `generic_default`.
pub fn term_instances() -> u32 {
    generic_term::<Plain>() + generic_term::<Heap>() + generic_default::<u8>(1)
}

/// Parameter types naming the enclosing function's type parameter: the check function
/// is generic only over its own parameters, so no E0401 (it was with a
/// `&dyn Fn(T) -> R` parameter); allocation-free, passes.
pub fn generic_param<T: Copy>(t: T) -> T {
    let f = fip_fn!(prelint, 0, |x: T| x);
    f.call((t,))
}

/// The same allocating under claim 0: rejected.
pub fn generic_param_lie<T: Copy>(t: T) -> T {
    let f = fip_fn!(prelint, 0, |x: T| *Box::new(x));
    f.call((t,))
}

/// A closure returning a borrow of its parameter ("lifetime may not live long
/// enough" with a `&dyn Fn(&u32) -> R` parameter; the closure is now the check
/// function's argument, whose bound is its expected signature): passes. The return
/// type is written, as Rust needs for this closure without an expected signature.
pub fn borrowed(y: u32) -> u32 {
    let f = fip_fn!(prelint, 0, |x: &u32| -> &u32 { x });
    *f.call((&y,))
}

/// A borrow-returning closure that drops its boxed argument: the free is still found
/// (rejected).
pub fn borrowed_frees(y: u32) -> u32 {
    let f = fip_fn!(prelint, 0, |x: &u32, b: Box<u32>| -> &u32 {
        drop(b);
        x
    });
    *f.call((&y, Box::new(1)))
}

/// Instantiates the generic ones.
pub fn param_instances() -> (u8, u16) {
    (generic_param::<u8>(1), generic_param_lie::<u16>(2))
}
