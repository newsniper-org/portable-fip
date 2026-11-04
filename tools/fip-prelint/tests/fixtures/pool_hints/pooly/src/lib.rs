// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Pool-like types in a crate that declares `fip::export`: two unmarked pools (hints
//! with `--pool-hints`), a marked one (no hint: already declared) and data structures
//! of a similar shape that are not pools (no hint).
#![cfg_attr(fip_prelint, fip::export)]

/// A slot pool with a free-list head: `alloc` writes a slot and the head and returns
/// the slot's index; `release` writes `None` back. Unmarked: a hint.
pub struct Pool {
    pub slots: [Option<u32>; 8],
    pub free: usize,
}

impl Pool {
    pub fn alloc(&mut self, v: u32) -> Option<usize> {
        let i = self.free;
        if i < self.slots.len() {
            self.slots[i] = Some(v);
            self.free = i + 1;
            Some(i)
        } else {
            None
        }
    }

    pub fn release(&mut self, i: usize) {
        if i < self.slots.len() {
            self.slots[i] = None;
        }
    }
}

/// A bump arena: `alloc` advances `top` and returns a borrow of `buf`; `reset`
/// rewinds `top`. Unmarked: a hint.
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

/// The same arena, marked: no hint.
pub struct MarkedBump {
    pub buf: [u8; 32],
    pub top: usize,
}

impl MarkedBump {
    #[cfg_attr(fip_prelint, fip::alloc_source)]
    pub fn alloc(&mut self, n: usize) -> Option<&mut [u8]> {
        let start = self.top;
        let end = start.checked_add(n)?;
        if end > self.buf.len() {
            return None;
        }
        self.top = end;
        Some(&mut self.buf[start..end])
    }

    #[cfg_attr(fip_prelint, fip::free_source)]
    pub fn reset(&mut self) {
        self.top = 0;
    }
}

/// A fixed-capacity stack: `pop` returns a value, not a borrow or an index (control).
pub struct Stack {
    pub items: [u32; 8],
    pub len: usize,
}

impl Stack {
    pub fn push(&mut self, v: u32) -> Result<(), u32> {
        if self.len < self.items.len() {
            self.items[self.len] = v;
            self.len += 1;
            Ok(())
        } else {
            Err(v)
        }
    }

    pub fn pop(&mut self) -> Option<u32> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        Some(self.items[self.len])
    }

    pub fn clear(&mut self) {
        self.len = 0;
    }
}

/// A parser cursor: `advance` returns a position but writes no slot (control).
pub struct Cursor {
    pub data: [u8; 16],
    pub pos: usize,
}

impl Cursor {
    pub fn advance(&mut self) -> Option<usize> {
        if self.pos < self.data.len() {
            let p = self.pos;
            self.pos += 1;
            Some(p)
        } else {
            None
        }
    }

    pub fn rewind(&mut self) {
        self.pos = 0;
    }
}

/// A root through the unmarked pool: passes with and without `--pool-hints` (the
/// declared assumption; the hint changes no verdict).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn use_pool(p: &mut Pool) -> Option<usize> {
    p.alloc(1)
}

/// A root through the marked arena: one allocation (with and without hints).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn use_marked(b: &mut MarkedBump) -> usize {
    b.alloc(4).map_or(0, |s| s.len())
}
