// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `write!` of an integer into a fixed buffer: passes through the std summaries of
//! `core::fmt::write`, and is `⊤` when they are not used.

use core::fmt::{self, Write};

/// A fixed buffer; writing never allocates.
pub struct Buf {
    pub b: [u8; 16],
    pub n: usize,
}

impl Write for Buf {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for &c in s.as_bytes() {
            if self.n >= self.b.len() {
                return Err(fmt::Error);
            }
            self.b[self.n] = c;
            self.n = self.n.wrapping_add(1);
        }
        Ok(())
    }
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_number(b: &mut Buf, x: u32) -> fmt::Result {
    write!(b, "{x}")
}
