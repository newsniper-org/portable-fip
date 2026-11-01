// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A `GlobalAlloc` in pure Rust over a static buffer, installed as the global
//! allocator. Every `GlobalAlloc` method is a source by the trait rule, without marks.
use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicUsize, Ordering};

pub struct Bump {
    pub buf: UnsafeCell<[u8; 4096]>,
    pub top: AtomicUsize,
}

unsafe impl Sync for Bump {}

unsafe impl GlobalAlloc for Bump {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let start = self.top.fetch_add(layout.size(), Ordering::Relaxed);
        if start + layout.size() > 4096 {
            return core::ptr::null_mut();
        }
        unsafe { (self.buf.get() as *mut u8).add(start) }
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
pub static BUMP: Bump = Bump {
    buf: UnsafeCell::new([0; 4096]),
    top: AtomicUsize::new(0),
};

/// `Box::new` under the custom global allocator: one allocation (`__rust_alloc*`).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn boxed() -> Box<u32> {
    Box::new(1)
}

/// The allocator called directly: one allocation (its body is not analysed).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn direct_global_alloc() -> *mut u8 {
    unsafe { BUMP.alloc(Layout::new::<u64>()) }
}

/// The default `alloc_zeroed` of the trait, not overridden: one allocation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn direct_alloc_zeroed() -> *mut u8 {
    unsafe { BUMP.alloc_zeroed(Layout::new::<u64>()) }
}

/// An empty `dealloc` is still a free.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn direct_dealloc(p: *mut u8) {
    unsafe { BUMP.dealloc(p, Layout::new::<u64>()) }
}

/// The system allocator called directly: one allocation, no `⊤` from `libc`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn direct_system_alloc() -> *mut u8 {
    unsafe { std::alloc::System.alloc(Layout::new::<u64>()) }
}

/// Through a trait object: one allocation, not a `⊤` dynamic call.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_dyn(a: &dyn GlobalAlloc) -> *mut u8 {
    unsafe { a.alloc(Layout::new::<u64>()) }
}

/// `Vec` reaches the allocator through `<Global as Allocator>` (trait rule): one
/// allocation (`allocate`), and a possible free (`grow` reallocates).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn vec_push(v: &mut Vec<u8>) {
    v.push(1)
}
