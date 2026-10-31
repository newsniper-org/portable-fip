// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Roots calling into non-member dependencies.

/// Through the exported non-member: an allocation, with the callee on the chain.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_export(x: u32) -> Box<u32> {
    dep_export_nm::make(x)
}

/// Through the exported non-member, allocation-free: passes (not ⊤).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn pure_export(x: u32) -> u32 {
    dep_export_nm::twice(x)
}

/// Through the non-member without `fip::export`: unresolved, reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn pure_plain(x: u32) -> u32 {
    dep_plain_nm::twice(x)
}
