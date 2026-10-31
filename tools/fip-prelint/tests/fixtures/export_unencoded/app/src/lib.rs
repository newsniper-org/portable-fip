// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Calls into a dependency that claims `fip::export` without carrying MIR.
#![cfg_attr(fip_prelint, fip::export)]

/// Must not pass: the callee's body is missing although its crate opted in.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0))]
pub fn via_unencoded(x: u32) -> u32 {
    dep_unencoded::twice(x)
}
