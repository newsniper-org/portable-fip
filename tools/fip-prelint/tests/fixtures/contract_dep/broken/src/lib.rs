// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! An exported dependency with a contracted trait method and an implementation that
//! breaks the contract: checked (and rejected) where this crate is compiled.
#![cfg_attr(fip_prelint, fip::export)]

pub trait Area {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
    fn area(&self) -> u32;
}

pub struct Boxed(pub u32);

/// Allocates: breaks the contract.
impl Area for Boxed {
    fn area(&self) -> u32 {
        *Box::leak(Box::new(self.0))
    }
}

pub struct Plain(pub u32);

/// Meets the contract.
impl Area for Plain {
    fn area(&self) -> u32 {
        self.0
    }
}
