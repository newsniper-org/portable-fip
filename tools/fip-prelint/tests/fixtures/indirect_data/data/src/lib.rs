// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Calls through function pointers loaded from immutable data (top plan T1.1–T1.3):
//! a constant, an immutable static, a static table (every element a candidate, the
//! cost their maximum), a field of a static struct, a constant slice, a field of a
//! local aggregate. Controls stay `⊤`: interior mutability, `static mut`, a mutably
//! borrowed local, a parameter's field.

use std::cell::Cell;
use std::sync::atomic::{AtomicPtr, Ordering};

pub fn add_one(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn double(x: u32) -> u32 {
    x.wrapping_mul(2)
}

pub fn boxed_value(x: u32) -> u32 {
    *Box::new(x)
}

/// Allocates once and never frees.
pub fn leaked(x: u32) -> u32 {
    *Box::leak(Box::new(x))
}

#[cfg_attr(fip_prelint, fip::requires(x < 100))]
pub fn small(x: u32) -> u32 {
    x + 1
}

pub struct Ops {
    pub f: fn(u32) -> u32,
}

pub struct Outer {
    pub ops: Ops,
    pub k: u32,
}

pub const CONE: fn(u32) -> u32 = add_one;
pub static ONE: fn(u32) -> u32 = add_one;
pub static TABLE: [fn(u32) -> u32; 2] = [add_one, double];
pub static MIXED: [fn(u32) -> u32; 3] = [add_one, leaked, double];
pub static SOPS: Ops = Ops { f: double };
pub const CT: &[fn(u32) -> u32] = &[add_one, double];
pub static GUARDED: [fn(u32) -> u32; 1] = [small];

// (1) Resolved.

/// A constant: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_const(x: u32) -> u32 {
    CONE(x)
}

/// An immutable static: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_static(x: u32) -> u32 {
    ONE(x)
}

/// A static table indexed by an unknown index: both elements are candidates, both
/// allocation-free; passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_table(x: u32, i: usize) -> u32 {
    if i < 2 { TABLE[i](x) } else { x }
}

/// A table with one allocating element: its maximum is 1 allocation (not the sum of
/// the elements), so `#[fip(1)]` passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn via_mixed_one(x: u32, i: usize) -> u32 {
    if i < 3 { MIXED[i](x) } else { x }
}

/// The same table under `#[fip]`: the allocating candidate is reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_mixed(x: u32, i: usize) -> u32 {
    if i < 3 { MIXED[i](x) } else { x }
}

/// A constant index (an index local assigned one constant) selects one element:
/// passes, even though the table has an allocating one.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_mixed_constant_index(x: u32) -> u32 {
    MIXED[2](x)
}

/// A field of a static struct: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_static_field(x: u32) -> u32 {
    (SOPS.f)(x)
}

/// A constant slice: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_const_slice(x: u32, i: usize) -> u32 {
    if i < CT.len() { CT[i](x) } else { x }
}

/// A static table of a dependency that declares `fip::export`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_dependency_table(x: u32, i: usize) -> u32 {
    if i < 2 { tables::EXT[i](x) } else { x }
}

/// A field of a local aggregate: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_local_struct(x: u32) -> u32 {
    let o = Ops { f: add_one };
    (o.f)(x)
}

/// A field of a field of a local aggregate: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_local_nested(x: u32) -> u32 {
    let o = Outer {
        ops: Ops { f: double },
        k: 3,
    };
    (o.ops.f)(x).wrapping_add(o.k)
}

/// A local aggregate holding an allocating function: resolved, the allocation is
/// reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_local_struct_alloc(x: u32) -> u32 {
    let o = Ops { f: boxed_value };
    (o.f)(x)
}

/// A table element with `fip::requires(x < 100)`: the precondition is not
/// established at the call, a panic path (strict, `panic_macros = false`: an error).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn via_guarded_table(x: u32) -> u32 {
    GUARDED[0](x)
}

/// A callee with a declared parameter bound: arguments from constants and tables are
/// checked at the call site like reified functions.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(p = 0)))]
pub fn apply_ptr(p: fn(u32) -> u32, x: u32) -> u32 {
    p(x)
}

/// A constant argument: within `param(p = 0)`, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn pass_const(x: u32) -> u32 {
    apply_ptr(CONE, x)
}

/// A table element: both candidates within `param(p = 0)`, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn pass_table(x: u32, i: usize) -> u32 {
    if i < 2 { apply_ptr(TABLE[i], x) } else { x }
}

/// A table element that may be `leaked`: the argument may allocate once, more than
/// `param(p = 0)`: an error at the call site.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn pass_mixed(x: u32, i: usize) -> u32 {
    if i < 3 { apply_ptr(MIXED[i], x) } else { x }
}

// (2) Stay `⊤`.

/// A static with interior mutability (a `Cell` next to the pointer): its memory is
/// not immutable, so even the plain field is not read from the initializer: `⊤`
/// (conservative).
pub struct WithCell {
    pub f: fn(u32) -> u32,
    pub hits: Cell<u32>,
}

// SAFETY: the fixture is single-threaded; the static only shapes the MIR.
unsafe impl Sync for WithCell {}

pub static WITH_CELL: WithCell = WithCell {
    f: add_one,
    hits: Cell::new(0),
};

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_cell_struct(x: u32) -> u32 {
    (WITH_CELL.f)(x)
}

/// An atomic pointer: `⊤`.
pub static ATOMIC: AtomicPtr<u8> = AtomicPtr::new(std::ptr::null_mut());

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_atomic(x: u32) -> u32 {
    let p = ATOMIC.load(Ordering::Relaxed);
    if p.is_null() {
        return x;
    }
    // SAFETY: only ever stores pointers made from `fn(u32) -> u32` (none here).
    let f: fn(u32) -> u32 = unsafe { std::mem::transmute(p) };
    f(x)
}

/// `static mut`: `⊤`.
pub static mut MUTABLE: fn(u32) -> u32 = add_one;

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_static_mut(x: u32) -> u32 {
    // SAFETY: single-threaded fixture.
    let f = unsafe { MUTABLE };
    f(x)
}

/// A local aggregate whose field is written after construction: `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_local_written(x: u32, c: bool) -> u32 {
    let mut o = Ops { f: add_one };
    if c {
        o.f = boxed_value;
    }
    (o.f)(x)
}

/// A field of a parameter: `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_param_field(x: u32, o: &Ops) -> u32 {
    (o.f)(x)
}
