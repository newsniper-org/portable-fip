// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Function-pointer residue of top plan T1–T3: local arrays of function pointers,
//! pointers behind a reference stored in an immutable static, a function pointer
//! through an `FnMut` bound, and `Rc<dyn Fn>` / `Arc<dyn Fn>` parameters. Controls
//! stay `⊤`.

use std::cell::Cell;
use std::rc::Rc;
use std::sync::Arc;

pub fn add_one(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn double(x: u32) -> u32 {
    x.wrapping_mul(2)
}

/// Allocates and frees.
pub fn boxed_value(x: u32) -> u32 {
    *Box::new(x)
}

/// Allocates once and never frees.
pub fn leaked(x: u32) -> u32 {
    *Box::leak(Box::new(x))
}

// (1) Local arrays of function pointers.

/// Both elements are candidates, both allocation-free: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_array(x: u32, i: usize) -> u32 {
    let t: [fn(u32) -> u32; 2] = [add_one, double];
    if i < 2 { t[i](x) } else { x }
}

/// One candidate allocates once: 1 allocation, more than 0.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_array_alloc(x: u32, i: usize) -> u32 {
    let t: [fn(u32) -> u32; 2] = [add_one, leaked];
    if i < 2 { t[i](x) } else { x }
}

/// A constant index selects the allocation-free element: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_array_const_index(x: u32) -> u32 {
    let t: [fn(u32) -> u32; 2] = [add_one, leaked];
    t[0](x)
}

/// A repeated element: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_array_repeat(x: u32, i: usize) -> u32 {
    let t: [fn(u32) -> u32; 4] = [double; 4];
    if i < 4 { t[i](x) } else { x }
}

/// An element written after construction (control): `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn local_array_written(x: u32, i: usize, c: bool) -> u32 {
    let mut t: [fn(u32) -> u32; 2] = [add_one, double];
    if c {
        t[1] = boxed_value;
    }
    if i < 2 { t[i](x) } else { x }
}

// (2) Pointers behind a reference stored in an immutable static.

pub struct Ops {
    pub f: fn(u32) -> u32,
}

pub struct RefOps {
    pub ops: &'static Ops,
}

pub static SREF: &[fn(u32) -> u32] = &[add_one, double];
pub static SREF_MIXED: &[fn(u32) -> u32] = &[add_one, leaked];
pub static SREF_FIELD: RefOps = RefOps {
    ops: &Ops { f: double },
};
pub static SREF_ARRAY: &[fn(u32) -> u32; 2] = &[double, add_one];

/// A slice behind a reference in a static: both candidates allocation-free, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_static_ref(x: u32, i: usize) -> u32 {
    if i < SREF.len() { SREF[i](x) } else { x }
}

/// One candidate allocates once: 1 allocation, more than 0.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_static_ref_mixed(x: u32, i: usize) -> u32 {
    if i < SREF_MIXED.len() { SREF_MIXED[i](x) } else { x }
}

/// A field behind a reference field of a static: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_static_ref_field(x: u32) -> u32 {
    (SREF_FIELD.ops.f)(x)
}

/// An array behind a reference, constant index: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_static_ref_array(x: u32) -> u32 {
    SREF_ARRAY[1](x)
}

/// A function pointer next to a `Cell`, behind a reference in a static (control):
/// the memory behind the reference is not immutable, `⊤`.
pub struct WithCell {
    pub f: fn(u32) -> u32,
    pub hits: Cell<u32>,
}

// SAFETY: the fixture is single-threaded; the static only shapes the MIR.
unsafe impl Sync for WithCell {}

pub static CELL_INNER: WithCell = WithCell {
    f: add_one,
    hits: Cell::new(0),
};
pub static SREF_CELL: &WithCell = &CELL_INNER;

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_static_ref_cell(x: u32) -> u32 {
    (SREF_CELL.f)(x)
}

// (3) A function pointer through an `FnMut` bound.

/// Declares `param(g = 0)` for an `FnMut` parameter.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(g = 0)))]
pub fn apply_mut<G: FnMut(u32) -> u32>(mut g: G, x: u32) -> u32 {
    g(x)
}

/// An allocation-free function pointer through `FnMut`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn fnmut_ptr(x: u32) -> u32 {
    let p: fn(u32) -> u32 = add_one;
    apply_mut(p, x)
}

/// An allocating one: 1 allocation at the call site, more than `param(g = 0)`.
pub fn fnmut_ptr_alloc(x: u32) -> u32 {
    let p: fn(u32) -> u32 = leaked;
    apply_mut(p, x)
}

/// An `FnMut` bound called twice through a local function pointer.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn fnmut_twice<G: FnMut(u32) -> u32>(mut g: G, x: u32) -> u32 {
    let a = g(x);
    g(a)
}

/// Instantiates `fnmut_twice` with a function pointer: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn fnmut_twice_ptr(x: u32) -> u32 {
    let p: fn(u32) -> u32 = double;
    fnmut_twice(p, x)
}

/// A closure through `FnMut` that replaces its captured function pointer (control):
/// the closure's capture behind `&mut self` may change, `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn fnmut_closure_swaps(x: u32) -> u32 {
    let mut f: fn(u32) -> u32 = add_one;
    fnmut_twice(
        move |v| {
            let r = f(v);
            f = leaked;
            r
        },
        x,
    )
}

// (4) `Rc<dyn Fn>` and `Arc<dyn Fn>` parameters.

/// Declares `param(g = 0)` for a `&Rc<dyn Fn>`: the call costs the declaration,
/// passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(g = 0)))]
pub fn rc_declared(g: &Rc<dyn Fn(u32) -> u32>, x: u32) -> u32 {
    g(x)
}

/// The same for `&Arc<dyn Fn>`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(g = 0)))]
pub fn arc_declared(g: &Arc<dyn Fn(u32) -> u32>, x: u32) -> u32 {
    g(x)
}

/// Without `param(..)` (control): `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn rc_undeclared(g: &Rc<dyn Fn(u32) -> u32>, x: u32) -> u32 {
    g(x)
}

/// Callers (not roots): an allocation-free function passes at the call site, an
/// allocating one is reported there.
pub fn rc_caller(x: u32) -> u32 {
    let r: Rc<dyn Fn(u32) -> u32> = Rc::new(add_one);
    rc_declared(&r, x)
}

pub fn rc_caller_alloc(x: u32) -> u32 {
    let r: Rc<dyn Fn(u32) -> u32> = Rc::new(leaked);
    rc_declared(&r, x)
}

pub fn arc_caller(x: u32) -> u32 {
    let r: Arc<dyn Fn(u32) -> u32> = Arc::new(double);
    arc_declared(&r, x)
}

pub fn arc_caller_alloc(x: u32) -> u32 {
    let r: Arc<dyn Fn(u32) -> u32> = Arc::new(boxed_value);
    arc_declared(&r, x)
}

/// A clone of an `Rc` (a call result, control): `⊤` at the call site.
pub fn rc_caller_clone(x: u32, r: &Rc<dyn Fn(u32) -> u32>) -> u32 {
    let c = Rc::clone(r);
    rc_declared(&c, x)
}
