// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A dependency declaring `fip::export`: the driver compiles it with its flags but
//! does not check it (`Role::ExportedDependency`), so `fip_fn!(prelint, ..)` must not
//! compile here even under the driver.
#![cfg_attr(fip_prelint, fip::export)]

use fip_strict::FipFn;

/// An honest driver-mode construction, still rejected: nothing would check it.
pub fn dep_value() -> u32 {
    let f = fip_macros::fip_fn!(prelint, 0, |x: u32| x + 1);
    f.call((1,))
}
