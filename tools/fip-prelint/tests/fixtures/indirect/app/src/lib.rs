// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Calls through function pointers and trait objects (limits plan L4).

use shapes::{Grow, Plain, Scaled, Shape, Square};

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

/// `param(..)` in a contract (top plan T5): accepted, `g` is a function pointer
/// (no implementation here).
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

// (4) Implementations with their own marks, preconditions.

pub struct Tight(pub u32);

/// An implementation declaring the contract's mark: passes (as a root, and against
/// the contract).
impl Shape for Tight {
    #[fip_macros::fip]
    fn area(&self) -> u32 {
        self.0
    }
}

pub struct Loose(pub u32);

/// An implementation declaring a weaker mark than the contract `#[fip]`: rejected,
/// although its body passes both checks.
impl Shape for Loose {
    #[fip_macros::fip(1)]
    fn area(&self) -> u32 {
        self.0
    }
}

/// A strict contract (by hand: `#[fip]` rejects `strict = true` on a declaration).
pub trait Pick {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
    fn pick(&self, xs: &[u32], i: usize) -> u32;
}

pub struct Indexed;

/// An implementation whose own precondition rules out the bounds check failing: it
/// is checked against the contract without it (a dynamic call does not establish
/// it), so the bounds check is a reachable panic path, reported.
impl Pick for Indexed {
    #[cfg_attr(fip_prelint, fip::requires(i < xs.len()))]
    fn pick(&self, xs: &[u32], i: usize) -> u32 {
        xs[i]
    }
}

/// Relies on the strict contract: passes (`Indexed` is reported instead).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn pick_dyn(p: &dyn Pick, xs: &[u32]) -> u32 {
    p.pick(xs, 7)
}

/// `fip::requires(..)` in a contract is rejected.
pub trait Bounded {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
    #[cfg_attr(fip_prelint, fip::requires(i < xs.len()))]
    fn at(&self, xs: &[u32], i: usize) -> u32;
}

// (5) Calls on `Self` or type parameters inside generic bodies.

/// Generic function bound by a contracted trait: uses the contract of `area`, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn generic_area<S: Shape>(s: &S) -> u32 {
    s.area()
}

/// Generic function calling a concrete instance: keeps instantiated analysis, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn call_generic_concrete() -> u32 {
    let sq = Square(4);
    generic_area(&sq)
}

/// Generic function calling a default body that calls a contracted method: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn generic_scaled<S: Scaled>(s: &S) -> u32 {
    s.scaled()
}

/// Generic function bound by an uncontracted trait: must stay a warning/term.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn generic_plain<P: Plain>(p: &P) -> u32 {
    p.size()
}

pub struct BadScaled(pub u32);

/// Breaks the contract of `scale_factor` (1 allocation, at most 0 allowed): reported at the impl.
impl Scaled for BadScaled {
    fn scale_factor(&self) -> u32 {
        boxed_value(self.0)
    }
}

// (6) `Box<dyn Fn*>` parameters (top plan T2): the `Box`'s `Fn` impl calls
// `(**self).call(..)`, bound to what the call site passes for the `&Box`.

/// Declares `param(g = 0)` for a `&Box<dyn Fn>`: the call through the box costs the
/// declaration, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(g = 0)))]
pub fn box_dyn_fn(g: &Box<dyn Fn(u32) -> u32>, x: u32) -> u32 {
    g(x)
}

/// The same without `param(..)`: `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn box_dyn_fn_undeclared(g: &Box<dyn Fn(u32) -> u32>, x: u32) -> u32 {
    g(x)
}

/// A caller (not a root) passing a box made from an allocation-free function: the
/// call site passes.
pub fn box_dyn_caller(x: u32) -> u32 {
    let b: Box<dyn Fn(u32) -> u32> = Box::new(add_one);
    box_dyn_fn(&b, x)
}

/// A box made from an allocating function: reported at the call site.
pub fn box_dyn_caller_alloc(x: u32) -> u32 {
    let b: Box<dyn Fn(u32) -> u32> = Box::new(boxed_value);
    box_dyn_fn(&b, x)
}

/// `Rc<dyn Fn>` (a control): reached through `Rc`'s `Deref`, an ordinary call; the
/// trait object's origin is not followed there, `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn rc_dyn_fn(g: &std::rc::Rc<dyn Fn(u32) -> u32>, x: u32) -> u32 {
    g(x)
}

// (7) Contracts with `param(..)` (top plan T5): every implementation is checked with
// the parameter costing its bound, every call through the contract checks its
// argument.

/// Through the macro: `#[fip]` with `param(g = 0)` on a declaration.
pub trait Visit {
    #[fip_macros::fip(param(g = 0))]
    fn visit(&self, g: &dyn Fn(u32) -> u32) -> u32;
}

/// By hand: one allocation per call, `g` may allocate once.
pub trait Fold {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1, param(g = 1)))]
    fn fold(&self, g: fn(u32) -> u32) -> u32;
}

pub struct Walk(pub u32);

/// Calls `g` (named `f` here: the bound follows the position) in a loop: `g` costs
/// 0, passes.
impl Visit for Walk {
    fn visit(&self, f: &dyn Fn(u32) -> u32) -> u32 {
        let mut s = 0u32;
        let mut i = 0u32;
        while i < self.0 {
            s = s.wrapping_add(f(i));
            i = i.wrapping_add(1);
        }
        s
    }
}

/// Calls `g` once: within the contract's one allocation, passes.
impl Fold for Walk {
    fn fold(&self, g: fn(u32) -> u32) -> u32 {
        g(self.0)
    }
}

pub struct Twice(pub u32);

/// Calls `g` twice: up to 2 allocations, over the contract's 1, reported.
impl Fold for Twice {
    fn fold(&self, g: fn(u32) -> u32) -> u32 {
        g(g(self.0))
    }
}

pub struct Hoard(pub u32);

/// Allocates itself: reported.
impl Visit for Hoard {
    fn visit(&self, g: &dyn Fn(u32) -> u32) -> u32 {
        g(boxed_value(self.0))
    }
}

pub struct Narrow(pub u32);

/// Declares a tighter bound for `g` than the contract (dynamic callers may pass a
/// function allocating once): weaker than the contract, reported.
impl Fold for Narrow {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1, param(g = 0)))]
    fn fold(&self, g: fn(u32) -> u32) -> u32 {
        g(self.0)
    }
}

/// A dynamic call passing an allocation-free function: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn visit_dyn(v: &dyn Visit) -> u32 {
    v.visit(&add_one)
}

/// A dynamic call passing an allocating closure: reported at the call site.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn visit_dyn_alloc(v: &dyn Visit) -> u32 {
    v.visit(&|x| boxed_value(x))
}

/// A call on a type parameter (costs the contract) passing an allocating function:
/// reported at the call site.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn visit_generic_alloc<V: Visit>(v: &V) -> u32 {
    v.visit(&boxed_value)
}

/// Allocates once and never frees.
pub fn leaked_value(x: u32) -> u32 {
    *Box::leak(Box::new(x))
}

/// A dynamic call of `fold` passing a function allocating once (no free): within
/// `param(g = 1)`, costs the contract's one allocation, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn fold_dyn(f: &dyn Fold) -> u32 {
    f.fold(leaked_value)
}

/// The same with a function that also frees: `Fold::fold`'s `#[fip(1)]` forbids
/// frees, reported at the call site.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn fold_dyn_frees(f: &dyn Fold) -> u32 {
    f.fold(boxed_value)
}

/// A caller that is not a root, passing an allocating function to a dynamic call:
/// reported at the call site.
pub fn visit_dyn_caller(v: &dyn Visit) -> u32 {
    v.visit(&boxed_value)
}
