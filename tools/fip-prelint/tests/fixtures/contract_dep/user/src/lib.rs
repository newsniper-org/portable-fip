// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Relies on the contract of `broken::Area::area` through a dynamic call.

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn total(a: &dyn broken::Area) -> u32 {
    a.area()
}
