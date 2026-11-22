// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Probes of the 2026-11-04 soundness audit (findings 2, 3, 6, 7).
#![allow(unused, clippy::all)]

// Finding 2: a cycle through dynamic calls of a contracted method. The
// implementation checked against the contract recurses without bound through
// `d.m(d)`; the contract's leaf must not hide that.
pub trait Tr {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
    fn m(&self, d: &dyn Tr) -> u32;
}
pub struct A;
impl Tr for A {
    fn m(&self, d: &dyn Tr) -> u32 {
        d.m(d)
    }
}

// Finding 3: user items named like `core`'s UB checks are analysed, not skipped.
pub struct S;
impl S {
    pub fn precondition_check(&self) -> Box<u8> {
        Box::new(1)
    }
}
pub mod m {
    pub fn precondition_check_and_free(b: Box<u8>) {
        drop(b)
    }
}
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn ub_marker(s: &S) {
    let b = s.precondition_check();
    m::precondition_check_and_free(b);
}

// Finding 6: foreign functions are classified by link symbol, not Rust name.
unsafe extern "C" {
    #[link_name = "free"]
    fn __rust_no_alloc_shim_is_unstable_v2(p: *mut u8);
    #[link_name = "free"]
    fn malloc(p: *mut u8);
}
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn ffi_alias_free(p: *mut u8) {
    unsafe { __rust_no_alloc_shim_is_unstable_v2(p) }
}
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn ffi_alias_malloc(p: *mut u8) {
    unsafe { malloc(p) }
}

// Finding 7: a local module named `core` is not the standard library's.
pub mod core {
    pub mod panicking {
        pub fn leak() -> Box<u8> {
            Box::new(3)
        }
    }
}
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn panic_prefix() -> u8 {
    *self::core::panicking::leak()
}

// Audit 2026-11-22: the drop of a trait object. rustc's drop shim for `dyn Trait` has
// no statement (codegen emits the call through the vtable), so its MIR reads as
// "nothing happens"; the concrete type's drop may allocate, free and panic.
pub trait Obj {
    fn v(&self) -> u32;
}
pub struct Noisy {
    pub items: Vec<Box<u32>>,
}
impl Obj for Noisy {
    fn v(&self) -> u32 {
        0
    }
}
impl Drop for Noisy {
    fn drop(&mut self) {
        let _extra = Box::new(self.items.len());
    }
}
/// Dropping the box drops a `Noisy` (or anything else): not checkable.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn drop_boxed_obj(b: Box<dyn Obj>) {}
/// The same without a deallocation of its own: `#[fip]` passed before.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn drop_obj_in_place(p: *mut dyn Obj) {
    unsafe { ::core::ptr::drop_in_place(p) }
}
/// Inside another type's drop glue.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip", frees = 1))]
pub fn drop_opt_obj(o: Option<Box<dyn Obj>>) {}
/// Borrowing a trait object drops nothing.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn borrow_obj(o: &dyn Obj, s: &[u8]) -> usize {
    s.len()
}
