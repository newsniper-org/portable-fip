// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Does not declare `fip::export` in its source; the fixture's RUSTFLAGS inject it,
//! so the driver does not take part in compiling this crate and no MIR is encoded.

/// Non-generic, not `#[inline]`: no MIR without `-Zalways-encode-mir`.
pub fn twice(x: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < 2 {
        s += x;
        i += 1;
    }
    s
}
