// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Traits with contracts (`fip::mark` on the method declaration) and implementations
//! that meet them, in an exported workspace member.
#![cfg_attr(fip_prelint, fip::export)]

/// Every implementation of `area` is allocation-free (checked in the crate of the
/// implementation, and wherever a dynamic call relies on it).
pub trait Shape {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
    fn area(&self) -> u32;
}

/// Every implementation of `grow` allocates at most once.
pub trait Grow {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
    fn grow(&self) -> u32;
}

/// No contract: a dynamic call of `size` is `⊤`.
pub trait Plain {
    fn size(&self) -> u32;
}

/// A contract on a method with a default body: the default body is checked as a
/// root, and for every implementation that keeps it.
pub trait Scaled {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
    fn scaled(&self) -> u32 {
        3
    }
}

pub struct Square(pub u32);

/// Meets the contract: passes.
impl Shape for Square {
    fn area(&self) -> u32 {
        self.0.wrapping_mul(self.0)
    }
}

/// One allocation, never freed, within `n = 1`: passes.
impl Grow for Square {
    fn grow(&self) -> u32 {
        *Box::leak(Box::new(self.0))
    }
}

impl Plain for Square {
    fn size(&self) -> u32 {
        self.0
    }
}

/// Keeps the default body: checked for `Square`.
impl Scaled for Square {}
