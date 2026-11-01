// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Roots calling dependencies whose `fip::export` the text test did not see.

/// Allocation through `dep_multi` (exported): an error with the chain.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn make_multi(x: u32) -> Box<u32> {
    dep_multi::make(x)
}

/// Allocation-free through `dep_multi` (exported): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn twice_multi(x: u32) -> u32 {
    dep_multi::twice(x)
}

/// Allocation through `dep_comment_in` (exported): an error with the chain.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn make_comment_in(x: u32) -> Box<u32> {
    dep_comment_in::make(x)
}

/// Allocation-free through `dep_comment_in` (exported): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn twice_comment_in(x: u32) -> u32 {
    dep_comment_in::twice(x)
}

/// Allocation through `dep_nested` (exported): an error with the chain.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn make_nested(x: u32) -> Box<u32> {
    dep_nested::make(x)
}

/// Allocation-free through `dep_nested` (exported): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn twice_nested(x: u32) -> u32 {
    dep_nested::twice(x)
}
