// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Drops that are frees only if their drop glue deallocates (limits plan L12), and the
//! pinned behaviour of interior mutability and dynamic uniqueness (limits plan L8: out
//! of scope, only their allocations, frees and panic paths are observed).
use std::cell::{Cell, RefCell};
use std::rc::Rc;

/// `Cell::set`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn cell_inc(c: &Cell<u32>) {
    c.set(c.get().wrapping_add(1));
}

/// `*c.borrow_mut() = 1` drops a `RefMut`, whose glue releases the borrow flag and
/// deallocates nothing: passes (it was "may free: drop of `RefMut<'_, u32>`").
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn refmut_store(c: &RefCell<u32>) {
    *c.borrow_mut() = 1;
}

/// A user guard whose `Drop` writes a flag: passes.
pub struct Guard<'a>(pub &'a Cell<bool>);

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        self.0.set(false);
    }
}

/// Creates and drops a [`Guard`]: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn guard_scope(flag: &Cell<bool>) {
    flag.set(true);
    let _g = Guard(flag);
}

/// Dropping an `Rc`: the last reference frees: may free (error).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn rc_drop(r: Rc<u32>) {
    drop(r);
}

// Uniqueness and interior mutability are outside `fip-prelint` (limits plan L8): the
// roots below pin what it reports today. Only the FIP-relevant effects are observed:
// allocations, frees, and the panic paths of dynamic borrow checks.

/// `Cell::replace` of a `u32`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn cell_replace(c: &Cell<u32>) -> u32 {
    c.replace(7)
}

/// Two shared references to one `Cell` (aliasing is not checked): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn cell_aliased(a: &Cell<u32>, b: &Cell<u32>) {
    a.set(b.get().wrapping_add(1));
    b.set(a.get().wrapping_add(1));
}

/// `Cell::take` of a `Box`, dropped: the drop frees (error).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn cell_take_box(c: &Cell<Option<Box<u8>>>) {
    drop(c.take());
}

/// `RefCell::borrow`: a dynamic borrow check whose failure panics; a root without
/// `strict = true` allows panic paths: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn refcell_read(c: &RefCell<u32>) -> u32 {
    *c.borrow()
}

/// The same under `strict = true, panic_macros = false`: the panic path is an error.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn refcell_read_strict(c: &RefCell<u32>) -> u32 {
    *c.borrow()
}

/// `RefCell::borrow_mut` under `strict = true, panic_macros = false`: an error.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn refmut_store_strict(c: &RefCell<u32>) {
    *c.borrow_mut() = 1;
}

/// `RefCell::try_borrow_mut`: no panic path, passes even under `panic_macros = false`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn refcell_try_store(c: &RefCell<u32>) -> bool {
    match c.try_borrow_mut() {
        Ok(mut r) => {
            *r = 2;
            true
        }
        Err(_) => false,
    }
}

/// A write through `UnsafeCell::get`: passes (whether another reference aliases the
/// cell is a question of undefined behaviour, for Verus, Miri and the `unsafe`
/// audit, not checked here).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn unsafecell_write(c: &core::cell::UnsafeCell<u32>) {
    // SAFETY: the caller guarantees no other reference to the cell's value is live.
    unsafe { *c.get() = 3 };
}

/// `Rc::new`: an allocation (error).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn rc_new(x: u32) -> Rc<u32> {
    Rc::new(x)
}

/// `Rc::get_mut`, a dynamic uniqueness check without allocation or panic: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn rc_unique_store(r: &mut Rc<u32>) -> bool {
    match Rc::get_mut(r) {
        Some(v) => {
            *v = 4;
            true
        }
        None => false,
    }
}

/// `Rc::clone`: no allocation; the count's overflow aborts (the `abort` intrinsic, a
/// panic path, allowed outside strict mode): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn rc_clone(r: &Rc<u32>) -> Rc<u32> {
    let s = Rc::clone(r);
    core::mem::forget(Rc::clone(&s));
    s
}
