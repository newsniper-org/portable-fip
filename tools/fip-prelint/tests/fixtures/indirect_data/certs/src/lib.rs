// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Certified function pointers (top plan T1.4): a field of type
//! `fip_strict::Certified<N, fn(..)>` is called at the certificate's bound `N`, and
//! every analysed construction (`Certified::assume`) is checked against `N`.

use fip_strict::{Certified, FipFn};

pub fn plus1(v: u8) -> u8 {
    v.wrapping_add(1)
}

/// Allocates once and never frees (the box is leaked).
pub fn leak_once(v: u8) -> u8 {
    core::mem::forget(Box::new(v));
    v
}

/// Allocates and frees.
pub fn boxed_round_trip(v: u8) -> u8 {
    *Box::new(v)
}

pub struct Ops {
    pub f: Certified<0, fn(u8) -> u8>,
}

pub struct Ops1 {
    pub f: Certified<1, fn(u8) -> u8>,
}

/// A call through a `Certified<0, fn>` field: costs 0 (passes).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn call_field(o: &Ops) -> u8 {
    o.f.call((1,))
}

/// A call through a `Certified<1, fn>` field under `#[fip(1)]`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn call_field1(o: &Ops1) -> u8 {
    o.f.call((1,))
}

/// The same under `#[fip]`: may allocate once (error).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn call_field1_over(o: &Ops1) -> u8 {
    o.f.call((1,))
}

/// Under `strict = true, panic_macros = false`: the certificate bounds allocations,
/// not panics, so the call is a panic path (error).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn call_field_strict(o: &Ops) -> u8 {
    o.f.call((1,))
}

/// An allocation-free function certified with 0: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn make_good() -> Ops {
    // SAFETY: not memory safety; `plus1` does not allocate (checked by the driver).
    Ops {
        f: unsafe { Certified::assume(plus1 as fn(u8) -> u8) },
    }
}

/// A function that allocates once, certified with 0: an error at the construction
/// (not a root: every body's constructions are checked).
pub fn make_over() -> Ops {
    // SAFETY: deliberately wrong certificate (fixture).
    Ops {
        f: unsafe { Certified::assume(leak_once as fn(u8) -> u8) },
    }
}

/// The same function certified with 1: passes.
pub fn make_one() -> Ops1 {
    // SAFETY: `leak_once` allocates once per call.
    Ops1 {
        f: unsafe { Certified::assume(leak_once as fn(u8) -> u8) },
    }
}

/// A function that frees, certified with 1: an error (the certificate forbids frees).
pub fn make_frees() -> Ops1 {
    // SAFETY: deliberately wrong certificate (fixture).
    Ops1 {
        f: unsafe { Certified::assume(boxed_round_trip as fn(u8) -> u8) },
    }
}

/// A pointer of unknown origin: `⊤` at the construction.
pub fn make_unknown(p: fn(u8) -> u8) -> Ops {
    // SAFETY: the driver cannot check `p` here (reported).
    Ops {
        f: unsafe { Certified::assume(p) },
    }
}

/// A parameter declared `param(p = 0)`: its callers are checked, the construction
/// passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(p = 0)))]
pub fn make_declared(p: fn(u8) -> u8) -> Ops {
    // SAFETY: `p` is checked against `param(p = 0)` at every analysed call site.
    Ops {
        f: unsafe { Certified::assume(p) },
    }
}

/// A caller of `make_declared` passing an allocating function: an error at this call.
pub fn declared_caller() -> u8 {
    let o = make_declared(leak_once);
    o.f.call((2,))
}

/// A generic wrapper: the construction's callable type is a type parameter, so a
/// function-pointer instantiation would carry an unchecked bound: `⊤` here.
pub fn wrap<C>(c: C) -> Certified<0, C> {
    // SAFETY: not checkable here (reported).
    unsafe { Certified::assume(c) }
}
