// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Generic functions, closure parameters, bounds and loops, recursion.

/// Produces a value.
pub trait Make {
    /// The value.
    fn make(&self) -> u32;
}

/// Allocation-free [`Make`].
pub struct Stack;
/// Allocating [`Make`].
pub struct Heap;

impl Make for Stack {
    fn make(&self) -> u32 {
        7
    }
}

impl Make for Heap {
    fn make(&self) -> u32 {
        *Box::new(7)
    }
}

/// Generic over [`Make`].
pub fn produce<T: Make>(t: &T) -> u32 {
    t.make()
}

/// Instantiated with `Stack`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn produce_stack() -> u32 {
    produce(&Stack)
}

/// Instantiated with `Heap`: violation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn produce_heap() -> u32 {
    produce(&Heap)
}

/// Generic root: conditional on `<T as Make>::make` (warning).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn produce_any<T: Make>(t: &T) -> u32 {
    produce(t)
}

/// Calls `g` in a loop.
pub fn each<F: FnMut(u32) -> u32>(n: u32, g: &mut F) -> u32 {
    let mut s = 0u32;
    let mut i = 0u32;
    while i < n {
        s = s.wrapping_add(g(i));
        i = i.wrapping_add(1);
    }
    s
}

/// With an allocation-free closure: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn each_plain(n: u32) -> u32 {
    each(n, &mut |x| x.wrapping_add(1))
}

/// With an allocating closure: unbounded (violation).
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn each_boxing(n: u32) -> u32 {
    each(n, &mut |x| *Box::new(x))
}

/// Higher-order root without a declared bound: conditional `∞·alloc(g)` (warning).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn each_generic<F: FnMut(u32) -> u32>(n: u32, g: &mut F) -> u32 {
    each(n, g)
}

/// The same with `param(g = 0)`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, param(g = 0)))]
pub fn each_declared<F: FnMut(u32) -> u32>(n: u32, g: &mut F) -> u32 {
    each(n, g)
}

/// Allocates once.
pub fn boxed(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Two allocations under `fip(2)`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
pub fn two(x: u32) -> (Box<u32>, Box<u32>) {
    (boxed(x), boxed(x))
}

/// Two allocations under `fip(1)`: violation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn two_over(x: u32) -> (Box<u32>, Box<u32>) {
    (boxed(x), boxed(x))
}

/// One allocation on either branch: passes `fip(1)` (maximum over paths).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn branches(c: bool, x: u32) -> Box<u32> {
    if c { boxed(x) } else { boxed(x.wrapping_add(1)) }
}

/// An allocating call in a loop: unbounded, violates `fip(3)`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 3))]
pub fn in_loop(n: u32) -> u32 {
    let mut s = 0u32;
    let mut i = 0u32;
    while i < n {
        s = s.wrapping_add(*Box::leak(boxed(i)));
        i = i.wrapping_add(1);
    }
    s
}

/// Recursion through two functions: violation for `fip`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn even(n: u32) -> bool {
    if n == 0 { true } else { odd(n - 1) }
}

/// See [`even`].
pub fn odd(n: u32) -> bool {
    if n == 0 { false } else { even(n - 1) }
}

/// `fbip` allows recursion: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn even_fbip(n: u32) -> bool {
    even(n)
}
