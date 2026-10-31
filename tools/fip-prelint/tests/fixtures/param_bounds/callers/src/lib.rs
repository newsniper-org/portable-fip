// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Declared parameter bounds at call sites: every call of a function declaring
//! `param(g = K)` is checked against the bound of the argument passed for `g`, in
//! roots, in what they reach, and in local functions and closures that are not roots.

use fip_macros::fip;
use fip_strict::FipFn;

// The reproducer of `TODOs/fip-prelint.md` ("Declared parameter bounds at call
// sites") and `TODOs/strict-open-items.md` item 7.

/// Declares `param(g = 0)`. Itself: may free (`*g.call(..)` drops the `Box`).
#[fip(strict = true, param(g = 0))]
pub fn f<F: FipFn<(u8,), Output = Box<u8>>>(g: F) -> u8 {
    *g.call((1,))
}

/// Not a root: the argument exceeding `param(g = 0)` is reported.
pub fn non_root_caller() -> u8 {
    f(fip_macros::fip_fn!(|x: u8| Box::new(x)))
}

/// `#[fip]`: its own budget is exceeded, and the argument exceeds `param(g = 0)`.
#[fip]
pub fn root_caller() -> u8 {
    f(fip_macros::fip_fn!(|x: u8| Box::new(x)))
}

/// `#[fip(1)]`: its own budget holds (one allocation); the argument still exceeds
/// `param(g = 0)`.
#[fip(1)]
pub fn root_caller_budget1() -> u8 {
    f(fip_macros::fip_fn!(|x: u8| Box::new(x)))
}

// Argument kinds.

/// Declares `param(g = 0)` for a certified callable returning `u8`.
#[fip(strict = true, param(g = 0))]
pub fn apply_certified<F: FipFn<(u8,), Output = u8>>(g: F) -> u8 {
    g.call((1,))
}

/// An allocation-free `fip_fn!` argument: passes.
pub fn certified_ok() -> u8 {
    apply_certified(fip_macros::fip_fn!(|x: u8| x ^ 1))
}

/// Declares `param(g = 0)` for a plain closure parameter (hand-written mark).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(g = 0)))]
pub fn apply<G: Fn(u32) -> u32>(g: G, x: u32) -> u32 {
    g(x)
}

/// An allocation-free closure: passes.
pub fn closure_ok(x: u32) -> u32 {
    apply(|v| v.wrapping_add(1), x)
}

/// An allocating closure body: reported.
pub fn closure_alloc(x: u32) -> u32 {
    apply(|v| *Box::new(v), x)
}

/// Allocates once.
pub fn boxed_value(v: u32) -> u32 {
    *Box::new(v)
}

/// A named function: reported (through its `Fn` shim).
pub fn named_fn(x: u32) -> u32 {
    apply(boxed_value, x)
}

/// A function pointer: the bound is unknown (`⊤`), reported.
pub fn fn_pointer(x: u32, p: fn(u32) -> u32) -> u32 {
    apply(p, x)
}

/// Generic and not a root: the argument is the term `alloc(h)`; not reported here,
/// but where `forward` is instantiated.
pub fn forward<H: Fn(u32) -> u32>(h: H, x: u32) -> u32 {
    apply(h, x)
}

/// Instantiates `forward` with an allocating closure: its own `fip(1)` holds, the
/// call in `forward::<{closure}>` violates `param(g = 0)` (reported, for this root).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn through_forward(x: u32) -> u32 {
    forward(|v| *Box::new(v), x)
}

/// Passes `h` (declared `param(h = 1)`) for `param(g = 0)`: reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1, param(h = 1)))]
pub fn forward_declared<H: Fn(u32) -> u32>(h: H, x: u32) -> u32 {
    apply(h, x)
}

/// Passes `h` (declared `param(h = 0)`) for `param(g = 0)`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(h = 0)))]
pub fn forward_ok<H: Fn(u32) -> u32>(h: H, x: u32) -> u32 {
    apply(h, x)
}

/// The call inside a closure body: reported.
pub fn in_closure(x: u32) -> u32 {
    let c = |y: u32| apply(|v| *Box::new(v), y);
    c(x)
}
