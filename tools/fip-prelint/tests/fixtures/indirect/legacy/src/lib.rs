// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A path dependency without `fip::export` (not a workspace member): its
//! implementation of a contracted trait cannot be checked.

pub struct Legacy(pub u32);

impl shapes::Shape for Legacy {
    fn area(&self) -> u32 {
        self.0
    }
}
