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

    /// A free source of two deallocations whose clause says one: an error.
    #[cfg_attr(fip_prelint, fip::free_source(n = 2))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        encapsulates alloc(0, 1)
    ))]
    pub fn put_two(&mut self, slot: usize) {
        if self.next > 1 && slot > 0 {
            self.next = self.next - 2;
        }
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

/// Frees once if `c`.
#[cfg_attr(verus_keep_ghost, verus_spec(
    allocates (if c { 1int } else { 0int })
    deallocates (if c { 1int } else { 0int })
))]
pub fn cond(c: bool) {
    if c {
        let _b = Box::new(1u8);
    }
}

/// `n` calls that free nothing, as `deallocates 0`: the driver's `∞` (a call that may
/// free, in a loop) becomes Verus's 0.
#[cfg_attr(verus_keep_ghost, verus_spec(allocates 0 deallocates 0))]
pub fn calm(n: u8) {
    let mut i = 0u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            allocated() == 0,
            deallocated() == 0,
        decreases n - i,
    ))]
    while i < n {
        cond(false);
        i += 1;
    }
}

/// The same as `#[verifier::fip]`, which admits no `deallocates` clause: the sidecar
/// records `deallocates 0` for it (2026-11-23; it recorded none, and the `∞` stayed).
#[cfg_attr(verus_keep_ghost, verus_spec(ensures true))]
#[cfg_attr(verus_keep_ghost, verifier::fip)]
pub fn calm_fip(n: u8) {
    let mut i = 0u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            allocated() == 0,
        decreases n - i,
    ))]
    while i < n {
        cond(false);
        i += 1;
    }
}

/// Callers that Verus does not verify: both pass with 0 frees.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip", frees = 0))]
pub fn via_calm(n: u8) {
    calm(n);
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip", frees = 0))]
pub fn via_calm_fip(n: u8) {
    calm_fip(n);
}

/// A control: `cond(true)` in the loop is not `fip`, and its caller's `∞` stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip", frees = 0))]
pub fn via_cond(n: u8) {
    let mut i = 0u8;
    while i < n {
        cond(true);
        i += 1;
    }
}

/// A marker that differs between the builds, as `fip_strict::NoDeallocDrop` does:
/// vstd's trait under Verus, every type in the plain build.
#[cfg(verus_keep_ghost)]
pub use vstd::alloc_check::NoDeallocDrop;
#[cfg(not(verus_keep_ghost))]
pub trait NoDeallocDrop {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized> NoDeallocDrop for T {}

/// Drops a value whose drop Verus knows to free nothing, by the bound. In the plain
/// build the bound holds for a `Box` too, so the `deallocates 0` is not taken for this
/// function (a Verus bound is taken for a non-generic function only).
#[cfg_attr(verus_keep_ghost, verus_spec(deallocates 0))]
pub fn eat_marked<T: NoDeallocDrop>(t: T) {
    let _u = t;
}

/// The same as `#[verifier::fip]`.
#[cfg_attr(verus_keep_ghost, verus_spec(ensures true))]
#[cfg_attr(verus_keep_ghost, verifier::fip)]
pub fn eat_marked_fip<T: NoDeallocDrop>(t: T) {
    let _u = t;
}

/// Generic roots, not verified (no Verus attribute: Verus ignores them, so they need no
/// gate). In the plain build their `T` is any type, a `Box` too: none may pass with 0
/// frees. (A root passing a `Box` itself cannot be in this crate: Verus compiles the
/// crate and refuses `Box<u8>: NoDeallocDrop`; and a module of plain builds only is
/// more than the gate may hold, amendment 2026-11-25 (2).)
pub mod unmarked {
    #[cfg_attr(fip_prelint, fip::mark(kind = "fbip", frees = 0))]
    pub fn any<T: super::NoDeallocDrop>(t: T) {
        super::eat_marked(t);
    }

    #[cfg_attr(fip_prelint, fip::mark(kind = "fbip", frees = 0))]
    pub fn any_fip<T: super::NoDeallocDrop>(t: T) {
        super::eat_marked_fip(t);
    }
}

/// Proof blocks vanish in plain builds (as in fip-core).
#[cfg(not(verus_keep_ghost))]
macro_rules! proof {
    ($($t:tt)*) => {};
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Pick: Sized {
    #[cfg_attr(verus_keep_ghost, verus_spec(r => allocates 1 deallocates 0))]
    fn pick(self) -> Option<Box<u8>>;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Pick for u64 {
    #[cfg_attr(verus_keep_ghost, verus_spec(r => allocates 0 deallocates 0))]
    fn pick(self) -> Option<Box<u8>> {
        None
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Pick for i32 {
    #[cfg_attr(verus_keep_ghost, verus_spec(r => allocates 1 deallocates 0))]
    fn pick(self) -> Option<Box<u8>> {
        Some(Box::new(1u8))
    }
}

// (A function in which ghost code types a literal, `let n = 1; proof! { let g: u64 = n; }`,
// was here until the fork `6ae48cb`, which refuses it: `just verify-sidecar`, crate
// `ghosttyped`.)

/// A literal with its suffix: `n: u64` in every build, and Verus's 0 is taken.
#[cfg_attr(verus_keep_ghost, verus_spec(allocates 0 deallocates 0))]
pub fn suffix_typed(k: u8) {
    let mut i = 0u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            allocated() == 0,
            deallocated() == 0,
        decreases k - i,
    ))]
    while i < k {
        let n = 1_u64;
        if let Some(b) = n.pick() {
            core::mem::forget(b);
        }
        i += 1;
    }
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_suffix_typed(k: u8) {
    suffix_typed(k);
}

/// A literal that exec code types `i32` looks the same to the driver: refused too,
/// until it has its suffix (`a + 1_i32`).
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        a < 100,
    ensures
        r == a + 1,
))]
pub fn bump(a: i32) -> i32 {
    a + 1
}

// (A type with a `Drop` impl of plain builds only, and a function dropping it in a loop,
// were here: such an impl is more than the gate may hold, and the crate would list no
// function. `just verify-sidecar`, crate `twindrop`.)

/// A verified function that no sidecar lists (made by a macro: one item text for every
/// expansion), and a listed caller: its Verus results are not used either (the callee
/// this build runs must be a listed one).
macro_rules! make_noop {
    ($name:ident) => {
        #[cfg_attr(verus_keep_ghost, verus_spec(allocates 0 deallocates 0))]
        pub fn $name() {}
    };
}
make_noop!(made);

#[cfg_attr(verus_keep_ghost, verus_spec(allocates 0 deallocates 0))]
pub fn calls_made(k: u8) {
    let mut i = 0u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            allocated() == 0,
            deallocated() == 0,
        decreases k - i,
    ))]
    while i < k {
        made();
        if let Some(b) = cond_box(false) {
            core::mem::forget(b);
        }
        i += 1;
    }
}

/// Allocates if `c`.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    allocates (if c { 1int } else { 0int })
    deallocates 0
))]
pub fn cond_box(c: bool) -> Option<Box<u8>> {
    if c { Some(Box::new(1u8)) } else { None }
}

/// With the bound of `calls_made` this would pass (the driver counts `∞` for its loop).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn via_calls_made(k: u8) {
    calls_made(k);
}
