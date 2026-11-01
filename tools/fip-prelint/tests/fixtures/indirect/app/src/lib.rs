// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Calls through function pointers and trait objects (limits plan L4).

use shapes::{Grow, Plain, Shape, Square};

pub fn add_one(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn boxed_value(x: u32) -> u32 {
    *Box::new(x)
}

// (1) Origin known in the body.

/// A local function pointer reified from one function on every path: resolved,
/// passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_reify(x: u32) -> u32 {
    let g: fn(u32) -> u32 = add_one;
    g(x)
}

/// The same, from an allocating function: resolved, its allocation is reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_reify_alloc(x: u32) -> u32 {
    let g: fn(u32) -> u32 = boxed_value;
    g(x)
}

/// A non-capturing closure coerced to a function pointer: resolved, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_closure_ptr(x: u32) -> u32 {
    let g: fn(u32) -> u32 = |v| v ^ 1;
    g(x)
}

/// Two origins: `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn two_origins(x: u32, c: bool) -> u32 {
    let g: fn(u32) -> u32 = if c { add_one } else { boxed_value };
    g(x)
}

/// A pointer loaded from data: `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn from_table(x: u32, t: &[fn(u32) -> u32; 2]) -> u32 {
    let g = t[1];
    g(x)
}

/// A local trait object unsized from one concrete type: resolved, passes (the trait
/// has no contract).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_dyn(x: u32) -> u32 {
    let s = Square(x);
    let d: &dyn Plain = &s;
    d.size()
}

/// The same for an implementation that allocates once (it meets the contract of
/// `grow`, but the call is resolved to it): reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_dyn_alloc(x: u32) -> u32 {
    let s = Square(x);
    let d: &dyn Grow = &s;
    d.grow()
}

// (3) Contracts on trait methods.

/// A trait object of unknown origin, method without contract: `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn uncontracted(p: &dyn Plain) -> u32 {
    p.size()
}

/// A dynamic call of a contracted method costs the contract (0): passes. Every
/// implementation is checked in its own crate (`Square` in `shapes`, `Doubled` in
/// `plugins`, `Circle` and `Leaky` here); `Legacy` (crate `legacy`, no
/// `fip::export`) cannot be checked, which is reported for this crate (`⊤`).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn contract_call(s: &dyn Shape) -> u32 {
    s.area()
}

/// The contract of `grow` declares 1 allocation: over the budget of `#[fip]`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn grow_call(g: &dyn Grow) -> u32 {
    g.grow()
}

/// Within `fip(1)`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn grow_call_budget(g: &dyn Grow) -> u32 {
    g.grow()
}

/// Under `strict = true`, the contract of `area` is not strict: implementations may
/// panic (a panic path).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn contract_call_strict(s: &dyn Shape) -> u32 {
    s.area()
}

pub struct Circle(pub u32);

/// An implementation in this crate, checked against the contract: passes.
impl Shape for Circle {
    fn area(&self) -> u32 {
        self.0.wrapping_mul(3)
    }
}

/// `param(..)` in a contract is rejected.
pub trait Apply {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(g = 0)))]
    fn apply(&self, g: fn(u32) -> u32) -> u32;
}

pub struct Leaky(pub u32);

/// An implementation in this crate that breaks the contract: reported.
impl Shape for Leaky {
    fn area(&self) -> u32 {
        boxed_value(self.0)
    }
}

/// Values of types from the dependencies reach the dynamic call through
/// `contract_call` (not resolved there: its receiver is a parameter): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn from_dependencies(x: u32) -> u32 {
    contract_call(&legacy::Legacy(x)).wrapping_add(contract_call(&plugins::Doubled(x)))
}
