// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Allocation bounds proved by Verus (`allocates`, `-V alloc-check`; decision
//! 2026-11-06-redesign-verus-allocates, phase 4). The sidecar records each listed
//! function's bound; the driver takes a literal bound in place of its own count only
//! where its count is not a finite number at most the bound, for a non-generic function
//! without `requires`. Frees, panics and recursion stay the driver's.

#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Proved 0, counted 0: passes either way.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == a / 2,
    allocates 0
))]
pub fn zero(a: u32) -> u32 {
    a / 2
}

/// Proved 1, counted 1: the driver's count is kept. Its box is freed: an error for
/// `#[fip]` (frees are never taken from Verus).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 1))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == 1,
    allocates 1
))]
pub fn one() -> u32 {
    let b = Box::new(1u32);
    *b
}

/// Two calls of `one` in a loop: the driver counts `∞` (a call in a loop), Verus
/// proves 2, so the count is 2 and `n = 2` holds; the frees stay reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == 2,
    allocates 2
))]
pub fn twice() -> u32 {
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            s == i,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        s = s + one();
        i = i + 1;
    }
    s
}

/// A bound linear in a parameter is recorded (`0+1*n`) but not evaluated: the
/// driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == n,
    allocates n as nat
))]
pub fn times(n: u32) -> u32 {
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= n,
            s == i,
            allocated() <= i as nat,
        decreases n - i,
    ))]
    while i < n {
        s = s + one();
        i = i + 1;
    }
    s
}

/// With a `requires`: the fork assumes the bound only under it, which a caller Verus
/// did not verify may break, so the driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        k <= 2,
    ensures
        r == k,
    allocates 2
))]
pub fn upto(k: u32) -> u32 {
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= k,
            k <= 2,
            s == i,
            allocated() <= i as nat,
        decreases k - i,
    ))]
    while i < k {
        s = s + one();
        i = i + 1;
    }
    s
}

/// Generic: the Verus premise `T: Copy` of the drop is not re-established per instance,
/// so the driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == 2,
    allocates 2
))]
pub fn twice_with<T: Copy>(x: T) -> u32 {
    let _keep = x;
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            s == i,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        s = s + one();
        i = i + 1;
    }
    s
}

/// A caller of `twice`: its count is `twice`'s, 2 (from the proof), with no proof of
/// its own.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
pub fn use_twice() -> u32 {
    twice()
}

/// A pool with its own interface (not a `core::alloc::Allocator`): its methods are
/// declared allocation sources whose bodies call no allocator, so Verus counts a
/// call only through the method's own clause, and the driver takes Verus's bounds
/// through a source only if that clause is `encapsulates alloc(a, d)` with the
/// declared counts (decision 2026-11-01-fip-prelint, amendments 2026-11-19 and
/// 2026-11-20).
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Pool {
    pub next: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Pool {
    /// A declared source without `encapsulates`: 0 to Verus, which does not count its
    /// calls.
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

    /// A declared source whose clause states its count: Verus charges every call 1.
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

    /// Declared 2, 1 to Verus: the two declarations differ, an error.
    #[cfg_attr(fip_prelint, fip::alloc_source(n = 2))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        encapsulates alloc(1, 0)
    ))]
    pub fn take_pair(&mut self) -> usize {
        if self.next < 999 {
            self.next = self.next + 2;
        }
        self.next
    }
}

/// `n` calls of a source Verus does not count: Verus proves 0, the driver's `∞`
/// stays (an error for `#[fip]`).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 0
))]
pub fn drain(p: &mut Pool, n: usize) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            allocated() == 0,
        decreases n - i,
    ))]
    while i < n {
        let _ = p.take();
        i = i + 1;
    }
}

/// A caller of `drain` with a proved bound of its own: it reaches the same source,
/// so its bound is not taken either.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 0
))]
pub fn drain_three(p: &mut Pool) {
    drain(p, 3);
}

/// Two calls, in a loop, of a source whose clause states its count: the driver counts
/// `∞`, Verus proves 2, so the count is 2 and `n = 2` holds.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn two_counted(p: &mut Pool) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        let _ = p.take_counted();
        i = i + 1;
    }
}

/// Two calls, in a loop, of a source declared 2 whose clause says 1: Verus proves 2
/// where the declarations give 4, so the driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn two_pairs(p: &mut Pool) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        let _ = p.take_pair();
        i = i + 1;
    }
}

/// A page backend: a source declared on a trait method, bounded by its declaration.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Backend {
    #[cfg_attr(fip_prelint, fip::alloc_source)]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        allocates 1
    ))]
    fn reserve(&mut self) -> usize;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Backend for Pool {
    /// States its clause: Verus charges every call 1, resolved or generic.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        encapsulates alloc(1, 0)
    ))]
    fn reserve(&mut self) -> usize {
        self.take_counted()
    }
}

/// A backend whose implementation states no clause of its own: the driver does not
/// take Verus's bounds through it (the sidecar records no bound for it).
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Bare {
    pub top: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Backend for Bare {
    fn reserve(&mut self) -> usize {
        if self.top < 1000 {
            self.top = self.top + 1;
        }
        self.top
    }
}

/// Two reservations, in a loop, through a type parameter.
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn reserve_two<B: Backend>(b: &mut B) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        let _ = b.reserve();
        i = i + 1;
    }
}

/// Through the generic helper with `Pool`, whose `reserve` states 1: the count is 2.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn pool_two(p: &mut Pool) {
    reserve_two(p);
}

/// Through the generic helper with `Bare`: the driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn bare_two(b: &mut Bare) {
    reserve_two(b);
}

/// Resolved calls of `Bare::reserve` in a loop: the driver's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 2))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates 2
))]
pub fn bare_two_direct(b: &mut Bare) {
    let mut i: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= 2,
            allocated() <= i as nat,
        decreases 2 - i,
    ))]
    while i < 2 {
        let _ = b.reserve();
        i = i + 1;
    }
}

/// `encapsulates` on a function that is not a declared source: Verus charges its
/// callers 0 and does not check its body, which allocates. The driver analyses the
/// body and takes no Verus bound from it or through it.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    encapsulates alloc(0, 0)
))]
pub fn sneak(n: usize) -> usize {
    let b = Box::new(n);
    *b
}

/// `n` calls of `sneak`: Verus proves 0, the driver's `∞` stays (an error).
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    allocates 0
))]
pub fn via_sneak(n: usize) -> usize {
    let mut i: usize = 0;
    let mut s: usize = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            allocated() == 0,
        decreases n - i,
    ))]
    while i < n {
        s = sneak(i);
        i = i + 1;
    }
    s
}
