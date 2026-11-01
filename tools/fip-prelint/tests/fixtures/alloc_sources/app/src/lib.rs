// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Roots using the sources of `pools` and foreign allocation functions.
use pools::{Arena, PlainArena, Pool, Slab};

/// One allocation from a marked arena.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn arena_once(a: &mut Arena) -> usize {
    match a.alloc(16) {
        Some(s) => s.len(),
        None => 0,
    }
}

/// A source in a loop: unbounded.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 3))]
pub fn arena_loop(a: &mut Arena, k: usize) -> usize {
    let mut got = 0;
    for _ in 0..k {
        if a.alloc(1).is_some() {
            got += 1;
        }
    }
    got
}

/// A free source.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn arena_reset(a: &mut Arena) {
    a.reset();
}

/// One allocation and a free.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn slab_cycle(s: &mut Slab, v: u32) -> Option<u32> {
    let i = s.insert(v)?;
    s.remove(i)
}

/// The same under `fbip`: the free is allowed, the allocation is not.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn slab_cycle_fbip(s: &mut Slab, v: u32) -> Option<u32> {
    let i = s.insert(v)?;
    s.remove(i)
}

/// `alloc_source(n = 2)` counts two per call: within `fip(2)`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
pub fn slab_pair(s: &mut Slab) -> bool {
    s.insert_pair(7).is_some()
}

/// The same above `fip(1)`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn slab_pair_over(s: &mut Slab) -> bool {
    s.insert_pair(7).is_some()
}

/// Allocation-free callee in the same exported crate: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn control(x: u32) -> u32 {
    pools::twice(x)
}

/// The unmarked arena: passes. This is the documented limit, not a finding: an
/// unmarked pure-Rust allocator is ordinary code for the driver.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn plain_arena_once(a: &mut PlainArena) -> usize {
    match a.alloc(16) {
        Some(s) => s.len(),
        None => 0,
    }
}

/// A source whose body loops, recurses and allocates: one allocation here, nothing
/// from its body (no `∞`, no recursion, no panic path).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn refill_once() -> usize {
    pools::refill(3)
}

/// A trait-declared source called on a generic parameter: one allocation, not a term.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn take_generic<P: Pool>(p: &mut P) -> Option<u32> {
    p.take()
}

/// The same through an implementation: one allocation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn take_slab(s: &mut Slab) -> Option<u32> {
    s.take()
}

unsafe extern "C" {
    fn malloc(n: usize) -> *mut u8;
    fn free(p: *mut u8);
    #[cfg_attr(fip_prelint, fip::alloc_source)]
    fn pool_get(n: usize) -> *mut u8;
    fn mystery(n: usize) -> *mut u8;
}

/// Foreign `malloc`: one allocation (`FOREIGN_ALLOC_SYMBOLS`).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn ffi_malloc() -> *mut u8 {
    unsafe { malloc(8) }
}

/// Foreign `free`: a possible free.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn ffi_free(p: *mut u8) {
    unsafe { free(p) }
}

/// A foreign function marked as a source: one allocation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn ffi_marked() -> *mut u8 {
    unsafe { pool_get(8) }
}

/// An unknown foreign function: `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn ffi_unknown() -> *mut u8 {
    unsafe { mystery(8) }
}

/// A Rust function named `malloc`: not foreign, analysed as usual.
pub mod rust {
    pub fn malloc(n: usize) -> usize {
        n.wrapping_add(1)
    }
}

/// Calls the Rust `malloc`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn rust_named_malloc(n: usize) -> usize {
    rust::malloc(n)
}
