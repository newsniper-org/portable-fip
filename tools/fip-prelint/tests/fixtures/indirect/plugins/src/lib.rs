// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A path dependency that declares `fip::export` but is not a workspace member: it is
//! compiled by the driver without roots, and its implementations of trait methods
//! with a contract are checked there (fixture `contract_dep`: one that breaks it).
#![cfg_attr(fip_prelint, fip::export)]

pub struct Doubled(pub u32);

/// Meets the contract of `Shape::area`.
impl shapes::Shape for Doubled {
    fn area(&self) -> u32 {
        self.0.wrapping_mul(2)
    }
}
