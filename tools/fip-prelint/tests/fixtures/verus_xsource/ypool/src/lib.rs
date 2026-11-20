// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Allocation sources of another crate (decision 2026-11-01-fip-prelint, amendments
//! 2026-11-19 and 2026-11-20): `yuser` takes Verus's bound through a source only if
//! this crate's sidecar lists the source with `encapsulates alloc(a, d)` equal to its
//! declaration (`take_counted`, `put`, `<Pages as Backend>::reserve`, the generic
//! `alloc_from`), not through `take` (`allocates 0`).

#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
#![cfg_attr(fip_prelint, fip::export)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Pool {
    pub next: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Pool {
    /// States its count.
    #[cfg_attr(fip_prelint, fip::alloc_source)]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        encapsulates alloc(1, 0)
    ))]
    pub fn take_counted(&mut self) -> usize {
        if self.next < 1000 {
            self.next = self.next + 1;
        }
        self.next
    }

    /// A free source that states its deallocation.
    #[cfg_attr(fip_prelint, fip::free_source)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        encapsulates alloc(0, 1)
    ))]
    pub fn put(&mut self, slot: usize) {
        if self.next > 0 && slot > 0 {
            self.next = self.next - 1;
        }
    }

    /// States 0.
    #[cfg_attr(fip_prelint, fip::alloc_source)]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        allocates 0
    ))]
    pub fn take(&mut self) -> usize {
        if self.next < 1000 {
            self.next = self.next + 1;
        }
        self.next
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Backend {
    #[cfg_attr(fip_prelint, fip::alloc_source)]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        allocates 1
    ))]
    fn reserve(&mut self) -> usize;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Pages {
    pub top: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Backend for Pages {
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        encapsulates alloc(1, 0)
    ))]
    fn reserve(&mut self) -> usize {
        if self.top < 1000 {
            self.top = self.top + 1;
        }
        self.top
    }
}

/// A generic source, as a slab's `alloc<B: PageBackend>`: declared one allocation.
#[cfg_attr(fip_prelint, fip::alloc_source)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    encapsulates alloc(1, 0)
))]
pub fn alloc_from<B: Backend>(b: &mut B) -> usize {
    b.reserve()
}
