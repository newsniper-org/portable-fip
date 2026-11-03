// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Callable parameters bound at their call sites (top plan B): a callee without
//! `param(..)` that calls its function-pointer or `&dyn Fn` parameter is analysed, in
//! a root's graph, with what the call site passes (a must-fact there). Up to three
//! nested bound callees; deeper, the callee is analysed without the binding (`⊤` for
//! an undeclared parameter, as before).

pub fn add_one(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn boxed_value(x: u32) -> u32 {
    *Box::new(x)
}

pub static TABLE: [fn(u32) -> u32; 2] = [add_one, add_one];

/// No `param(..)`: calls through its parameter.
pub fn call_plain(p: fn(u32) -> u32, x: u32) -> u32 {
    p(x)
}

/// No `param(..)`: calls its trait object parameter.
pub fn call_dyn(f: &dyn Fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

/// A reified function passed to `call_plain`: bound there, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_plain_callee(x: u32) -> u32 {
    call_plain(add_one, x)
}

/// An allocating function passed: bound, its allocation (and free) reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_plain_callee_alloc(x: u32) -> u32 {
    call_plain(boxed_value, x)
}

/// A table element passed: bound to both candidates, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_plain_callee_table(x: u32, i: usize) -> u32 {
    if i < 2 { call_plain(TABLE[i], x) } else { x }
}

/// A trait object unsized from a function item: bound to that type, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_dyn_callee(x: u32) -> u32 {
    call_dyn(&add_one, x)
}

/// A parameter declared `param(p = 0)` passed on: `call_plain`'s calls cost the
/// declaration, passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(p = 0)))]
pub fn forward_declared(p: fn(u32) -> u32, x: u32) -> u32 {
    call_plain(p, x)
}

/// An undeclared parameter passed on: not bound, `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn forward_undeclared(p: fn(u32) -> u32, x: u32) -> u32 {
    call_plain(p, x)
}

pub fn level1(p: fn(u32) -> u32, x: u32) -> u32 {
    level2(p, x)
}

pub fn level2(p: fn(u32) -> u32, x: u32) -> u32 {
    level3(p, x)
}

pub fn level3(p: fn(u32) -> u32, x: u32) -> u32 {
    p(x)
}

pub fn level0(p: fn(u32) -> u32, x: u32) -> u32 {
    level1(p, x)
}

/// Three nested bound callees: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_three_levels(x: u32) -> u32 {
    level1(add_one, x)
}

/// Four: the fourth callee is analysed without the binding, `⊤` (the depth limit).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_four_levels(x: u32) -> u32 {
    level0(add_one, x)
}
