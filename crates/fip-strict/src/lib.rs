// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-strict — allocation certificates for `#[fip(strict = true)]`
//!
//! A strict function may call only functions that carry a **certificate**: an upper
//! bound on the heap allocations one call performs, together with the promise that
//! the call frees nothing and does not recurse. Certificates are
//!
//! - [`Cert`] constants named `__fip_strict_<fn>`, placed next to a function, and
//! - [`FipBound`] implementations, for values called through [`FipFn`].
//!
//! `fip-macros` generates both from a checked body: `#[fip(strict = true)]` emits the
//! constant, `fip_fn!` emits the `FipBound` impl for a closure wrapper.
//!
//! ## Hand-written certificates are visible
//!
//! A certificate is a claim, so making one by hand needs `unsafe`:
//! [`Cert::assume`] is an `unsafe fn` and [`FipBound`] is an `unsafe trait`. In a crate
//! with `#![forbid(unsafe_code)]` neither can be written by hand at all, while the
//! code `fip-macros` generates still compiles (rustc does not apply `unsafe_code` to
//! proc-macro output). Everywhere else they stand out to review and to
//! `grep -n "Cert::assume\|unsafe impl.*FipBound"`. `fip_testkit::certs` lists them so a
//! test can pin the expected set.
//!
//! What remains possible without `unsafe`: re-exporting an existing certificate under
//! another function's name (`use a::__fip_strict_g as __fip_strict_f;`). That needs
//! the `__fip_strict_` identifier in source, which the same listing reports.
//!
//! `#![no_std]`, no `alloc`, no dependencies. `unsafe` appears only in the two
//! declarations above; there is no `unsafe` block or impl in this crate.
//!
//! ## Certificates for other portable-fip crates
//!
//! [`certs`] holds the hand-written certificates for functions of `fip-core` and
//! `fip-alloc`, which re-export them. Being in this crate, they are built without
//! `Cert::assume`, so those two crates keep `#![forbid(unsafe_code)]`. That makes
//! [`certs`] the one place where a certificate is made without `unsafe`; its
//! contents are pinned by a test and justified entry by entry.

#![no_std]
#![deny(unsafe_code)]

/// Certificate for one function: one call performs at most [`Cert::allocs`] heap
/// allocations, no deallocation, and no recursion (directly or through other
/// functions), counting everything it calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cert {
    allocs: u64,
}

impl Cert {
    /// Creates a certificate without checking anything.
    ///
    /// # Safety
    ///
    /// Not memory safety: the caller asserts the property above for the function the
    /// certificate is attached to. A false certificate makes `#[fip(strict = true)]`
    /// accept code that allocates, frees or recurses. Generated code calls this with a
    /// bound computed from a checked body and the callees' own certificates.
    #[allow(
        unsafe_code,
        reason = "certificate constructor; `unsafe` marks a trusted claim"
    )]
    #[must_use]
    pub const unsafe fn assume(allocs: u64) -> Self {
        Self { allocs }
    }

    /// The certified allocation bound.
    #[must_use]
    pub const fn allocs(self) -> u64 {
        self.allocs
    }
}

/// Certificate for a callable value: calling it through [`FipFn::call`] performs at
/// most `ALLOCS` heap allocations, no deallocation and no recursion.
///
/// Separate from [`FipFn`] so the bound does not depend on the argument types (and
/// their lifetimes). The associated constant also makes `dyn FipBound` impossible:
/// a strict function cannot call a value whose bound is unknown.
///
/// # Safety
///
/// Implementing it asserts the property above; see [`Cert::assume`].
#[allow(
    unsafe_code,
    reason = "certificate trait; `unsafe impl` marks a trusted claim"
)]
pub unsafe trait FipBound {
    /// Upper bound on allocations per call.
    const ALLOCS: u64;
}

/// A certified callable taking `Args` (a tuple, e.g. `(&T,)`).
///
/// Values come from `fip_macros::fip_fn!(|x| ..)`. Call with
/// `FipFn::call(&f, (x,))` or `f.call((x,))`; stable Rust does not allow
/// implementing the `Fn` traits, so `f(x)` is not available.
pub trait FipFn<Args>: FipBound {
    /// Return type.
    type Output;
    /// Calls the wrapped function.
    fn call(&self, args: Args) -> Self::Output;
}

/// Hand-written certificates for `fip-core` and `fip-alloc` functions, re-exported by
/// those crates next to the functions. Each entry states its justification.
#[doc(hidden)]
#[allow(non_upper_case_globals)]
pub mod certs {
    use super::Cert;

    /// `fip_core::swap`: `fip-core` does not link `alloc`, so it cannot allocate or
    /// free heap memory; `swap` drops no `T`, calls no user code, and Verus rejects
    /// recursion without `decreases`, which no `fip-core` function has.
    pub const __fip_strict_swap: Cert = Cert { allocs: 0 };

    /// `fip_core::replace`: same reasons as `__fip_strict_swap`.
    pub const __fip_strict_replace: Cert = Cert { allocs: 0 };

    /// `fip_alloc::refill`: the body calls only `core::mem::swap` (audited `core`
    /// table), moves the `Box` without dropping it, and does not recurse;
    /// allocation-free behaviour is also measured (`fip-alloc/tests/reuse.rs`).
    pub const __fip_strict_refill: Cert = Cert { allocs: 0 };
}
