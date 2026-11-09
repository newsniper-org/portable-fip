// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A user crate may implement a `core` trait for a primitive (`u8: Add<Local>`) or
//! for a fundamental type (`&Local: Index<u8>`), so the item path of a nested function
//! prints like a standard-library UB check
//! (`<u8 as core::ops::Add<Local>>::add::precondition_check`). These functions panic;
//! the strict roots must report the panic paths (UB checks are recognised by the
//! defining crate, never by the printed path).

#![allow(clippy::all)]

pub struct Local(pub u8);

impl core::ops::Add<Local> for u8 {
    type Output = u8;

    fn add(self, rhs: Local) -> u8 {
        fn precondition_check() {
            panic!("not a UB check");
        }
        precondition_check();
        self ^ rhs.0
    }
}

impl core::ops::Index<u8> for &Local {
    type Output = u8;

    fn index(&self, _: u8) -> &u8 {
        fn precondition_check() {
            panic!("not a UB check either");
        }
        precondition_check();
        &self.0
    }
}

#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn add_root(a: u8, b: u8) -> u8 {
    a + Local(b)
}

#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn index_root(l: &Local) -> u8 {
    (&l)[0]
}
