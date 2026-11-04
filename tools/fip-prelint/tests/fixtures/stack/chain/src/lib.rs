// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Roots for `cargo fip-prelint --stack`: a bounded three-level chain with arrays of
//! known size, and one root per reason a bound does not exist.

use core::hint::black_box;

/// The deepest frame: a 256-byte array.
#[inline(never)]
pub fn leaf(x: u64) -> u64 {
    let mut a = [x; 32];
    black_box(&mut a);
    a[3].wrapping_add(a[31])
}

/// The middle frame: a 64-byte array and two calls of `leaf`.
#[inline(never)]
pub fn mid(x: u64) -> u64 {
    let mut b = [x; 8];
    b[1] = leaf(x);
    black_box(&mut b);
    b[0].wrapping_add(leaf(b[7]))
}

/// A three-level chain: bounded.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn chain_top(x: u64) -> u64 {
    mid(x).wrapping_add(1)
}

/// Indexing: its bounds check calls a panic function, which is excluded (the claim
/// says so): bounded. At opt-level 3 this small function is not codegened on its own
/// (kept for cross-crate inlining), so it has no symbol: ⊤.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn indexed(xs: &[u64], i: usize) -> u64 {
    xs[i]
}

/// Recursion: ⊤ where the build recurses (opt-level 0); at opt-level 3 LLVM turns
/// the self-call into a loop, and that build has a bound.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn recursive(n: u64) -> u64 {
    if n == 0 { 0 } else { recursive(n - 1).wrapping_add(1) }
}

pub trait Shape {
    fn area(&self) -> u64;
}

/// A dynamic call: ⊤.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_dyn(s: &dyn Shape) -> u64 {
    s.area()
}

/// A call through a function pointer: ⊤.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_fn_ptr(g: fn(u64) -> u64) -> u64 {
    g(1)
}

unsafe extern "C" {
    safe fn labs(x: i64) -> i64;
}

/// A foreign function (no frame size in the build): ⊤ where the build calls it
/// (opt-level 0); at opt-level 3 LLVM computes `labs` inline.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn ffi(x: i64) -> i64 {
    labs(x)
}

/// A precompiled standard-library function (not generic, not `#[inline]`): ⊤.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn precompiled() -> u32 {
    std::process::id()
}

/// A generic root has no symbol of its own: ⊤.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn generic<T: Copy>(x: T) -> T {
    x
}

/// An iterator over a slice: at opt-level 0 the machine code calls the slice
/// iterator's functions and their `precondition_check`s (which MIR analysis does not
/// explore): bounded through all of them.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn summed(xs: &[u64]) -> u64 {
    xs.iter().fold(0, |a, b| a.wrapping_add(*b))
}

/// Copying a 512-byte array: codegen calls `memcpy` (a runtime function without a
/// frame size in the build): ⊤ (at opt-level 3: no symbol of its own, as `indexed`).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn copy_big(a: &[u64; 64]) -> [u64; 64] {
    *a
}

/// An allocation: `__rust_alloc` is the allocator's (no frame size in the build): ⊤.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn boxed(x: u64) -> Box<u64> {
    Box::new(x)
}
