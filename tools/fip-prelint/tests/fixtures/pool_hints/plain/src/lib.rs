// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The same bump arena in a crate without `fip::export`, checked as a workspace
//! member: a hint too (its own roots use it; since 2026-11-04).

pub struct Bump {
    pub buf: [u8; 32],
    pub top: usize,
}

impl Bump {
    pub fn alloc(&mut self, n: usize) -> Option<&mut [u8]> {
        let start = self.top;
        let end = start.checked_add(n)?;
        if end > self.buf.len() {
            return None;
        }
        self.top = end;
        Some(&mut self.buf[start..end])
    }

    pub fn reset(&mut self) {
        self.top = 0;
    }
}

/// A root through the local arena: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn use_bump(b: &mut Bump) -> usize {
    b.alloc(4).map_or(0, |s| s.len())
}
