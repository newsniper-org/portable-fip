// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Roots calling into `dep_export` and `dep_plain`.

use dep_export::make as fresh;

/// `Box::new` directly: violation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn direct(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Through an exported callee: violation with the callee on the chain.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_export(x: u32) -> Box<u32> {
    dep_export::make(x)
}

/// The same callee in a crate without `fip::export`: unknown, reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_plain(x: u32) -> Box<u32> {
    dep_plain::make(x)
}

/// Allocation-free exported callee: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn pure_export(x: u32) -> u32 {
    dep_export::twice(x)
}

/// Allocation-free, but not exported: unknown, reported (never passed).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn pure_plain(x: u32) -> u32 {
    dep_plain::twice(x)
}

/// A `use` alias of the allocating function: violation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_alias(x: u32) -> Box<u32> {
    fresh(x)
}

/// The alias under `fip(1)`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
pub fn via_alias_one(x: u32) -> Box<u32> {
    fresh(x)
}
