// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-testkit — allocation-count assertions for FIP-style code (tests only)
//!
//! `#[fip]` and friends from `fip-macros` are a syntactic lint. This crate is the
//! check that runs the code: it counts heap operations **on the current thread**
//! while a closure runs.
//!
//! ```ignore
//! fip_testkit::install!();              // once per test binary
//!
//! #[test]
//! fn reverse_is_fip() {
//!     let xs = build_list(1000);
//!     let r = fip_testkit::assert_fip!(reverse(xs));
//! }
//! ```
//!
//! ## Semantics
//!
//! | macro | passes when, during the expression |
//! |---|---|
//! | [`assert_fip!`] | 0 allocations, 0 reallocations, 0 frees |
//! | [`assert_fbip!`] | 0 allocations, 0 reallocations (frees allowed) |
//! | [`assert_fip_n!`] | at most `n` allocations + reallocations, 0 frees |
//!
//! These follow FP²: `fip` neither allocates nor frees, `fbip` may free, `fip(n)` may
//! allocate at most `n` cells. The value of the expression is returned, so it is
//! dropped by the caller, outside the measured region.
//!
//! ## Limits
//!
//! - The `assert_*` macros count per thread, which keeps parallel tests
//!   independent; work handed to other threads is not counted. To include it, use
//!   [`measure_all_threads`] (process-wide, needs tests not to run concurrently).
//! - A pass is evidence for the inputs tested, not a proof for all inputs.
//! - Only allocations through the Rust global allocator are seen.
//! - The macros panic if the counting allocator is not installed, so a missing
//!   `install!()` cannot produce a vacuous pass.

#![deny(unsafe_code)]

pub mod callgraph;
pub mod certs;
mod srcmodel;
pub mod summaries;
pub mod surface;

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

thread_local! {
    static COUNTS: Cell<AllocStats> = const { Cell::new(AllocStats::ZERO) };
}

/// Heap operations observed on one thread.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AllocStats {
    /// Calls to `alloc` / `alloc_zeroed`.
    pub allocs: u64,
    /// Calls to `realloc`.
    pub reallocs: u64,
    /// Calls to `dealloc`.
    pub frees: u64,
    /// Bytes requested by `alloc`, `alloc_zeroed` and the new size of `realloc`.
    pub bytes_requested: u64,
}

impl AllocStats {
    /// All counters zero.
    pub const ZERO: Self = Self {
        allocs: 0,
        reallocs: 0,
        frees: 0,
        bytes_requested: 0,
    };

    /// Counter-wise `self - earlier` (saturating).
    #[must_use]
    pub fn since(self, earlier: Self) -> Self {
        Self {
            allocs: self.allocs.saturating_sub(earlier.allocs),
            reallocs: self.reallocs.saturating_sub(earlier.reallocs),
            frees: self.frees.saturating_sub(earlier.frees),
            bytes_requested: self.bytes_requested.saturating_sub(earlier.bytes_requested),
        }
    }
}

/// Process-wide counters, for [`measure_all_threads`].
static GLOBAL: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];
/// Serialises [`measure_all_threads`] calls against each other.
static GLOBAL_SERIAL: Mutex<()> = Mutex::new(());

fn record(f: impl Fn(&mut AllocStats)) {
    // `try_with`: during thread teardown the slot may be gone; such events are not
    // inside any per-thread measured region, so dropping them there is correct.
    let _ = COUNTS.try_with(|c| {
        let mut s = c.get();
        f(&mut s);
        c.set(s);
    });
    let mut d = AllocStats::ZERO;
    f(&mut d);
    for (slot, v) in GLOBAL
        .iter()
        .zip([d.allocs, d.reallocs, d.frees, d.bytes_requested])
    {
        if v != 0 {
            slot.fetch_add(v, Ordering::Relaxed);
        }
    }
}

fn global() -> AllocStats {
    let [a, r, f, b] = &GLOBAL;
    AllocStats {
        allocs: a.load(Ordering::SeqCst),
        reallocs: r.load(Ordering::SeqCst),
        frees: f.load(Ordering::SeqCst),
        bytes_requested: b.load(Ordering::SeqCst),
    }
}

/// Like [`measure`], but counts heap operations of **every thread** of the process
/// while `f` runs, so work `f` hands to other threads is included.
///
/// Anything else running concurrently is counted too. Use it in a test binary
/// whose other tests do not run at the same time (`--test-threads 1`, or a
/// dedicated `tests/*.rs` file with one test). Calls to this function are
/// serialised against each other.
pub fn measure_all_threads<R>(f: impl FnOnce() -> R) -> (R, AllocStats) {
    let _guard = GLOBAL_SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let before = global();
    let r = f();
    let after = global();
    (r, after.since(before))
}

fn bytes(layout: Layout) -> u64 {
    u64::try_from(layout.size()).unwrap_or(u64::MAX)
}

/// Global allocator that forwards every call to [`System`] and counts it on the
/// calling thread. Install with [`install!`].
#[derive(Clone, Copy, Debug, Default)]
pub struct CountingAlloc;

// SAFETY: every method forwards its arguments unchanged to `System`, whose
// `GlobalAlloc` contract is the one we promise; the only addition is updating a
// thread-local `Cell`, which neither allocates nor unwinds. See
// docs/decisions/2026-10-31-testkit-counting-allocator.md.
#[allow(unsafe_code)]
unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record(|s| {
            s.allocs += 1;
            s.bytes_requested += bytes(layout);
        });
        // SAFETY: caller upholds `GlobalAlloc::alloc`'s contract; forwarded as is.
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record(|s| {
            s.allocs += 1;
            s.bytes_requested += bytes(layout);
        });
        // SAFETY: as for `alloc`.
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        record(|s| s.frees += 1);
        // SAFETY: `ptr`/`layout` come from this allocator, which got them from `System`.
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        record(|s| {
            s.reallocs += 1;
            s.bytes_requested += u64::try_from(new_size).unwrap_or(u64::MAX);
        });
        // SAFETY: as for `dealloc`; `new_size` is forwarded unchanged.
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

/// Installs [`CountingAlloc`] as the global allocator of the current binary.
/// Use once, at the top level of a test crate.
#[macro_export]
macro_rules! install {
    () => {
        #[global_allocator]
        static FIP_TESTKIT_GLOBAL_ALLOC: $crate::CountingAlloc = $crate::CountingAlloc;
    };
}

/// Counters of the current thread since it started.
#[must_use]
pub fn current() -> AllocStats {
    COUNTS.try_with(Cell::get).unwrap_or(AllocStats::ZERO)
}

/// Runs `f` and returns its result together with the heap operations it performed
/// on this thread. The result is returned, not dropped, so its destruction is not
/// counted.
pub fn measure<R>(f: impl FnOnce() -> R) -> (R, AllocStats) {
    let before = current();
    let r = f();
    let after = current();
    (r, after.since(before))
}

/// `true` if [`CountingAlloc`] is the global allocator of this binary.
#[must_use]
pub fn is_installed() -> bool {
    let ((), s) = measure(|| {
        drop(std::hint::black_box(Box::new(std::hint::black_box(0_u8))));
    });
    s.allocs == 1 && s.frees == 1
}

#[doc(hidden)]
pub fn __check(kind: &str, s: AllocStats, max_new: u64, frees_ok: bool, expr: &str) {
    assert!(
        is_installed(),
        "fip-testkit: CountingAlloc is not the global allocator; add `fip_testkit::install!();`"
    );
    let new = s.allocs + s.reallocs;
    assert!(
        new <= max_new && (frees_ok || s.frees == 0),
        "{kind} violated by `{expr}`: {s:?} (allowed: {max_new} allocations, frees {})",
        if frees_ok { "allowed" } else { "forbidden" }
    );
}

/// Evaluates the expression and asserts it performed no allocation, reallocation or
/// free on this thread. Returns the value.
#[macro_export]
macro_rules! assert_fip {
    ($e:expr $(,)?) => {{
        let (v, s) = $crate::measure(|| $e);
        $crate::__check("fip", s, 0, false, stringify!($e));
        v
    }};
}

/// Like [`assert_fip!`], but frees are allowed (FP² `fbip`).
#[macro_export]
macro_rules! assert_fbip {
    ($e:expr $(,)?) => {{
        let (v, s) = $crate::measure(|| $e);
        $crate::__check("fbip", s, 0, true, stringify!($e));
        v
    }};
}

/// Like [`assert_fip!`], but counted over all threads with [`measure_all_threads`].
#[macro_export]
macro_rules! assert_fip_all_threads {
    ($e:expr $(,)?) => {{
        let (v, s) = $crate::measure_all_threads(|| $e);
        $crate::__check("fip (all threads)", s, 0, false, stringify!($e));
        v
    }};
}

/// Like [`assert_fip!`], but at most `n` allocations (+ reallocations) are allowed
/// (FP² `fip(n)`).
#[macro_export]
macro_rules! assert_fip_n {
    ($n:expr, $e:expr $(,)?) => {{
        let (v, s) = $crate::measure(|| $e);
        $crate::__check("fip(n)", s, $n, false, stringify!($e));
        v
    }};
}
