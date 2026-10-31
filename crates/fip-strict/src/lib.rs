// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-strict — allocation certificates for `#[fip(strict = true)]`
//!
//! A strict function may call only functions that carry a **certificate**: an upper
//! bound on the heap allocations one call performs, together with the promise that
//! the call frees nothing and does not recurse. Certificates are
//!
//! - [`Cert`] constants named `__fip_strict_<fn>` (or `__fip_strict_<Type>__<m>`,
//!   `__fip_strict_<Type>__<Trait>__<m>` for methods), placed next to the function
//!   or the `impl` block, and
//! - [`FipBound`] implementations, for values called through [`FipFn`].
//!
//! `fip-macros` generates both from a checked body: `#[fip(strict = true)]` and
//! `#[fip_impl]` emit the constants, `fip_fn!` wraps a closure into [`Certified`].
//!
//! ## Certificates name their function
//!
//! A [`Cert`] carries the name it was made for (`"f"`, `"Type__m"`). A strict caller
//! of `f` reads the bound through [`Cert::allocs_for`]`("f")`, which fails constant
//! evaluation if the certificate names another function. So re-exporting one
//! function's certificate under another's name
//! (`use a::__fip_strict_g as __fip_strict_f;`) does not compile where it is used.
//! What remains possible without `unsafe`: importing the certificate of a
//! **same-named** function from another module (`use a::__fip_strict_f;` next to a
//! local `fn f`); the names match, the functions differ. `fip_testkit::certs` reports
//! that, since it needs the `__fip_strict_` identifier in source.
//!
//! ## Hand-written certificates are visible
//!
//! A certificate is a claim, so making one by hand needs `unsafe`:
//! [`Cert::assume`] and [`Certified::assume`] are `unsafe fn`s and [`FipBound`] is
//! an `unsafe trait`. In a crate with `#![forbid(unsafe_code)]` none can be written
//! by hand at all, while the code `fip-macros` generates still compiles (rustc does
//! not apply `unsafe_code` to proc-macro output). Everywhere else they stand out to
//! review and to `grep -n "Cert::assume\|unsafe impl.*FipBound"`. `fip_testkit::certs`
//! lists them so a test can pin the expected set.
//!
//! ## Verus
//!
//! Under the `verus` driver (`cfg(verus_keep_ghost)`) [`FipBound`], [`FipFn`] and
//! [`Certified`] are declared inside `verus! { }`: [`FipFn`] gains the spec functions
//! `pre` / `post`, and `call` requires `pre` and ensures `post`. For [`Certified`]
//! they are the wrapped closure's `requires` / `ensures`. Plain builds see the
//! dependency-free declarations; `tests/verus_drift.rs` checks that both declare the
//! same exec items. Verify with `just verify-strict` (exports the Verus metadata
//! `fip-core` imports).
//!
//! `#![no_std]`, no `alloc`, no dependencies.
//!
//! ## Certificates for other portable-fip crates
//!
//! [`certs`] holds the hand-written certificates for functions of `fip-core` and
//! `fip-alloc`, which re-export them. Being in this crate, they are built without
//! `Cert::assume`, so those two crates keep `#![forbid(unsafe_code)]`. That makes
//! [`certs`] the one place where a certificate is made without `unsafe`; its
//! contents are pinned by a test and justified entry by entry.

#![no_std]
#![cfg_attr(fip_prelint, fip::export)]
#![deny(unsafe_code)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Certificate for one function: one call performs at most [`Cert::allocs`] heap
/// allocations, no deallocation, and no recursion (directly or through other
/// functions), counting everything it calls. [`Cert::name`] is the function it was
/// made for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cert {
    name: &'static str,
    allocs: u64,
}

impl Cert {
    /// Creates a certificate for the function `name` without checking anything.
    ///
    /// `name` is the part of the certificate's identifier after `__fip_strict_`
    /// (`"f"` for `__fip_strict_f`, `"Type__m"` for a method).
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
    pub const unsafe fn assume(name: &'static str, allocs: u64) -> Self {
        Self { name, allocs }
    }

    /// The certified allocation bound.
    #[must_use]
    pub const fn allocs(self) -> u64 {
        self.allocs
    }

    /// The function this certificate was made for.
    #[must_use]
    pub const fn name(self) -> &'static str {
        self.name
    }

    /// The certified bound, after checking that the certificate was made for `name`.
    /// Strict callers read every callee's bound through this.
    ///
    /// # Panics
    ///
    /// Panics (a compile error in the constant evaluation of a strict caller) if the
    /// certificate names another function.
    #[must_use]
    pub const fn allocs_for(self, name: &str) -> u64 {
        assert!(
            str_eq(self.name, name),
            "fip_strict: the certificate names another function (a certificate re-exported under a different name)"
        );
        self.allocs
    }
}

const fn str_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

// ---- Plain declarations (every build except the `verus` driver). Keep the exec
// items identical to the `verus!` declarations below (`tests/verus_drift.rs`).

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
#[cfg(not(verus_keep_ghost))]
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
///
/// Under Verus the trait also has `spec fn pre(&self, args: Args) -> bool` and
/// `spec fn post(&self, args: Args, out: Self::Output) -> bool`; `call` requires
/// `pre` and ensures `post`.
#[cfg(not(verus_keep_ghost))]
pub trait FipFn<Args>: FipBound {
    /// Return type.
    type Output;
    /// Calls the wrapped function.
    fn call(&self, args: Args) -> Self::Output;
}

/// A closure `C` certified to perform at most `ALLOCS` allocations per call, no
/// deallocation and no recursion. Made by `fip_macros::fip_fn!`.
///
/// Fields are private and [`Certified::assume`] is `unsafe`: pairing a closure with
/// a bound is a claim.
#[cfg(not(verus_keep_ghost))]
pub struct Certified<const ALLOCS: u64, C> {
    f: C,
}

#[cfg(not(verus_keep_ghost))]
impl<const ALLOCS: u64, C> Certified<ALLOCS, C> {
    /// Wraps `f` without checking anything.
    ///
    /// # Safety
    ///
    /// Not memory safety: the caller asserts that every call of `f` performs at most
    /// `ALLOCS` allocations, no deallocation and no recursion. `fip_fn!` calls this
    /// with a bound computed from the checked closure body.
    #[allow(
        unsafe_code,
        reason = "certificate constructor; `unsafe` marks a trusted claim"
    )]
    #[doc(hidden)]
    #[must_use]
    pub const unsafe fn assume(f: C) -> Self {
        Certified { f }
    }
}

#[allow(
    unsafe_code,
    reason = "the bound was claimed by the `unsafe` constructor `Certified::assume`"
)]
#[cfg(not(verus_keep_ghost))]
unsafe impl<const ALLOCS: u64, C> FipBound for Certified<ALLOCS, C> {
    const ALLOCS: u64 = ALLOCS;
}

// ---- Verus declarations (only under the `verus` driver).

#[cfg(verus_keep_ghost)]
verus! {

/// Certificate for a callable value; see the plain declaration.
#[allow(unsafe_code, reason = "certificate trait; `unsafe impl` marks a trusted claim")]
pub unsafe trait FipBound {
    /// Upper bound on allocations per call.
    const ALLOCS: u64;
}

/// A certified callable taking `Args`, with a specification.
pub trait FipFn<Args>: FipBound {
    /// Return type.
    type Output;
    /// Precondition of a call with `args`.
    spec fn pre(&self, args: Args) -> bool;
    /// Postcondition of a call with `args` returning `out`.
    spec fn post(&self, args: Args, out: Self::Output) -> bool;
    /// Calls the wrapped function.
    fn call(&self, args: Args) -> (r: Self::Output)
        requires
            self.pre(args),
        ensures
            self.post(args, r),
    ;
}

/// A certified closure; see the plain declaration.
pub struct Certified<const ALLOCS: u64, C> {
    f: C,
}

impl<const ALLOCS: u64, C> Certified<ALLOCS, C> {
    /// Wraps `f` without checking anything; see the plain declaration.
    #[allow(unsafe_code, reason = "certificate constructor; `unsafe` marks a trusted claim")]
    #[doc(hidden)]
    pub const unsafe fn assume(f: C) -> (r: Self)
        ensures
            r.inner() == f,
    {
        Certified { f }
    }

    /// The wrapped closure.
    pub closed spec fn inner(&self) -> C {
        self.f
    }
}

#[allow(unsafe_code, reason = "the bound was claimed by the `unsafe` constructor `Certified::assume`")]
unsafe impl<const ALLOCS: u64, C> FipBound for Certified<ALLOCS, C> {
    const ALLOCS: u64 = ALLOCS;
}

} // verus!

/// `FipFn<(A0, ..)>` for `Certified<N, C>` with `C: Fn(A0, ..) -> R`: one source for
/// both declarations of the trait. Under Verus, `pre`/`post` are the closure's
/// `requires`/`ensures`.
macro_rules! certified_fip_fn {
    ($($A:ident $a:ident),*) => {
        #[cfg(not(verus_keep_ghost))]
        impl<const ALLOCS: u64, C, $($A,)* R> FipFn<($($A,)*)> for Certified<ALLOCS, C>
        where
            C: Fn($($A),*) -> R,
        {
            type Output = R;
            #[inline]
            fn call(&self, args: ($($A,)*)) -> R {
                let ($($a,)*) = args;
                (self.f)($($a),*)
            }
        }

        #[cfg(verus_keep_ghost)]
        verus! {
        impl<const ALLOCS: u64, C, $($A,)* R> FipFn<($($A,)*)> for Certified<ALLOCS, C>
        where
            C: Fn($($A),*) -> R,
        {
            type Output = R;
            open spec fn pre(&self, args: ($($A,)*)) -> bool {
                self.inner().requires(args)
            }
            open spec fn post(&self, args: ($($A,)*), out: R) -> bool {
                self.inner().ensures(args, out)
            }
            #[inline]
            fn call(&self, args: ($($A,)*)) -> (r: R) {
                let ($($a,)*) = args;
                (self.f)($($a),*)
            }
        }
        } // verus!
    };
}

certified_fip_fn!();
certified_fip_fn!(A0 a0);
certified_fip_fn!(A0 a0, A1 a1);
certified_fip_fn!(A0 a0, A1 a1, A2 a2);
certified_fip_fn!(A0 a0, A1 a1, A2 a2, A3 a3);

/// Largest closure arity `fip_fn!` supports (the number of `FipFn` impls above).
pub const MAX_ARITY: usize = 4;

/// Hand-written certificates for `fip-core` and `fip-alloc` functions, re-exported by
/// those crates next to the functions. Each entry states its justification.
#[doc(hidden)]
#[allow(non_upper_case_globals)]
pub mod certs {
    use super::Cert;

    /// `fip_core::swap`: `fip-core` does not link `alloc`, so it cannot allocate or
    /// free heap memory; `swap` drops no `T`, calls no user code, and Verus rejects
    /// recursion without `decreases`, which no `fip-core` function has.
    pub const __fip_strict_swap: Cert = Cert {
        name: "swap",
        allocs: 0,
    };

    /// `fip_core::replace`: same reasons as `__fip_strict_swap`.
    pub const __fip_strict_replace: Cert = Cert {
        name: "replace",
        allocs: 0,
    };

    /// `fip_alloc::refill`: the body calls only `core::mem::swap` (audited `core`
    /// table), moves the `Box` without dropping it, and does not recurse;
    /// allocation-free behaviour is also measured (`fip-alloc/tests/reuse.rs`).
    pub const __fip_strict_refill: Cert = Cert {
        name: "refill",
        allocs: 0,
    };
}
