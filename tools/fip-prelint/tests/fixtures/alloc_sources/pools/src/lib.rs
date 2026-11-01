// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Pure-Rust allocators (no `alloc` in the hand-out paths, no `unsafe`) in a crate
//! that declares `fip::export`: the allocator probe of the limits plan (M2), with the
//! pools marked as allocation and free sources. `PlainArena` is the same arena
//! unmarked: the documented residue (whether "write into a buffer and advance an
//! index" allocates is intent, not semantics).
#![cfg_attr(fip_prelint, fip::export)]

/// Bump arena over an owned buffer.
pub struct Arena {
    pub buf: [u8; 64],
    pub top: usize,
}

impl Arena {
    /// Hands out `n` fresh bytes: an allocation from this arena.
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
    /// Releases everything: a free of every block.
    #[cfg_attr(fip_prelint, fip::free_source)]
    pub fn reset(&mut self) {
        self.top = 0;
    }
}

/// The same bump arena, not marked: its calls are analysed as ordinary code and are
/// allocation-free for the driver. A crate that declares `fip::export` and hands out
/// memory from its own pools must mark them.
pub struct PlainArena {
    pub buf: [u8; 64],
    pub top: usize,
}

impl PlainArena {
    /// Hands out `n` fresh bytes, unmarked.
    pub fn alloc(&mut self, n: usize) -> Option<&mut [u8]> {
        let start = self.top;
        let end = start.checked_add(n)?;
        if end > self.buf.len() {
            return None;
        }
        self.top = end;
        Some(&mut self.buf[start..end])
    }
}

/// Fixed-capacity slab with handles.
pub struct Slab {
    pub slots: [Option<u32>; 8],
}

impl Slab {
    /// Takes a free slot: an allocation.
    #[cfg_attr(fip_prelint, fip::alloc_source)]
    pub fn insert(&mut self, v: u32) -> Option<usize> {
        let mut i = 0;
        while i < self.slots.len() {
            if self.slots[i].is_none() {
                self.slots[i] = Some(v);
                return Some(i);
            }
            i += 1;
        }
        None
    }
    /// Returns a slot: a free.
    #[cfg_attr(fip_prelint, fip::free_source)]
    pub fn remove(&mut self, i: usize) -> Option<u32> {
        self.slots.get_mut(i)?.take()
    }
    /// Takes two slots per call.
    #[cfg_attr(fip_prelint, fip::alloc_source(n = 2))]
    pub fn insert_pair(&mut self, v: u32) -> Option<(usize, usize)> {
        let a = self.insert(v)?;
        let b = self.insert(v)?;
        Some((a, b))
    }
}

/// A pool whose `take` is declared a source on the trait: every implementation, and
/// a call on a generic `P: Pool`, counts one allocation.
pub trait Pool {
    #[cfg_attr(fip_prelint, fip::alloc_source)]
    fn take(&mut self) -> Option<u32>;
}

impl Pool for Slab {
    fn take(&mut self) -> Option<u32> {
        let i = self.insert(0)?;
        Some(i as u32)
    }
}

/// A source whose body allocates twice in a loop and recurses: outside FIP, so
/// callers count one allocation and nothing from the body is reported.
#[cfg_attr(fip_prelint, fip::alloc_source)]
pub fn refill(k: usize) -> usize {
    let mut v = Vec::new();
    for _ in 0..k {
        v.push(Box::new(1u8));
        v.push(Box::new(2u8));
    }
    let deeper = if k > 1 { refill(k - 1) } else { 0 };
    v.len() + deeper
}

/// Allocation-free control.
pub fn twice(x: u32) -> u32 {
    x.wrapping_mul(2)
}
