// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Drops that are frees only if their drop glue deallocates (limits plan L12).
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
