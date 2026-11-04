// SPDX-License-Identifier: MIT OR Apache-2.0
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
//! Two `fip-macros` attributes turn a written claim into a certificate, and each
//! requires a visible `unsafe` from the user:
//!
//! - `#[fip_extern]` certifies foreign functions (`#[fip_cert(evidence = "..",
//!   allocs = N)]`) and requires an `unsafe extern` block, also in edition 2021
//!   where rustc accepts a plain `extern` block (`unsafe_code` lints `unsafe extern`,
//!   so a crate with `#![forbid(unsafe_code)]` cannot certify foreign functions;
//!   measured, rustc 1.99.1). A foreign function certified to free
//!   (`frees = true`, `kind = "fbip"`) gets no `Cert`: a `Cert` promises no
//!   deallocation.
//! - `#[fip_trait]` makes a strict contract of a trait method a `Cert` that strict
//!   callers pay for any implementation, so the trait must be an `unsafe trait`:
//!   each implementation is either an `unsafe impl` (the user's claim) or written
//!   under `#[fip_impl(contract)]`, which checks it against every contract and emits
//!   the `unsafe` itself. A crate with `#![forbid(unsafe_code)]` can implement such a
//!   trait that way but cannot declare one.
//!
//! ## Adapters
//!
//! [`Stateless`]`(f)` turns a one-argument callable into a state-passing step for
//! the `_st` combinators (`(s, x)` to `(s, f(x))`, bound `F::ALLOCS`);
//! [`Compose`]`(f, g)` calls `g(f(args))` for an `f` of any arity (it also maps a
//! callable's output; bound `F::ALLOCS + G::ALLOCS`, an overflow is a compile
//! error); [`Then`]`(f, g)` runs two state-passing steps one after the other (same
//! bound). They are tuple structs, so a strict body builds them as constructors, and
//! their `FipBound` impls are the audited claims (pinned by
//! `tests/hand_written_certs.rs`). Under Verus their `pre` / `post` are built from the
//! wrapped callables' (`verify/compose_state.rs`).
//!
//! ## Panic strictness
//!
//! [`FipBound::NO_PANIC_MACROS`] (default `false`) states that a callable's body was
//! checked with `panic_macros = false`, as [`Cert::no_panic_macros`] does for a
//! function. `fip_fn!(panic_macros = false, ..)` makes a `Certified<N, C, true>`
//! ([`Certified::assume_no_panic_macros`]); the adapters have it only if every part
//! has it; a strict callee declared `panic_macros = false` requires it of each
//! `param(..)` argument it calls.
//!
//! ## Verus
//!
//! Under the `verus` driver (`cfg(verus_keep_ghost)`) [`FipBound`], [`FipFn`] and
//! [`Certified`] are declared inside `verus! { }`: [`FipFn`] gains the spec functions
//! `pre` / `post`, and `call` requires `pre` and ensures `post`. For [`Certified`]
//! they are the wrapped closure's `requires` / `ensures`. Plain builds see the
//! dependency-free declarations; `tests/verus_drift.rs` checks that both declare the
//! same exec items. The constructors [`Certified::assume`] and
//! [`Certified::assume_no_panic_macros`] are single items for both builds, their
//! Verus `ensures` in `cfg_attr(verus_keep_ghost, verus_spec(..))`. Verify with `just verify-strict` (exports the Verus metadata
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
/// made for. [`Cert::no_panic_macros`] states that its body was also checked with
/// `panic_macros = false` (no panicking macro in it).
///
/// Every certificate is of kind `fip` (no deallocation): `#[fbip]` has no strict
/// mode, so there is no `fbip` certificate to compare.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cert {
    name: &'static str,
    allocs: u64,
    no_panic_macros: bool,
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
        Self {
            name,
            allocs,
            no_panic_macros: false,
        }
    }

    /// [`Cert::assume`] for a function whose body was also checked with
    /// `panic_macros = false` (`#[fip(strict = true, panic_macros = false)]`).
    ///
    /// # Safety
    ///
    /// As [`Cert::assume`], and the caller also asserts that the function's body uses
    /// none of the panicking macros `panic_macros = false` rejects.
    #[allow(
        unsafe_code,
        reason = "certificate constructor; `unsafe` marks a trusted claim"
    )]
    #[must_use]
    pub const unsafe fn assume_no_panic_macros(name: &'static str, allocs: u64) -> Self {
        Self {
            name,
            allocs,
            no_panic_macros: true,
        }
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

    /// `true` if the body was also checked with `panic_macros = false`.
    #[must_use]
    pub const fn no_panic_macros(self) -> bool {
        self.no_panic_macros
    }

    /// [`Cert::no_panic_macros`], after checking that the certificate was made for
    /// `name`, as [`Cert::allocs_for`] does.
    ///
    /// # Panics
    ///
    /// As [`Cert::allocs_for`].
    #[must_use]
    pub const fn no_panic_macros_for(self, name: &str) -> bool {
        assert!(
            str_eq(self.name, name),
            "fip_strict: the certificate names another function (a certificate re-exported under a different name)"
        );
        self.no_panic_macros
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

/// `true` if every name in `contracted` is in `implemented`: the check of
/// `#[fip_impl(contract)]` that every strict contract of the trait
/// (`<dyn Trait>::__FIP_CONTRACTED`, emitted by `#[fip_trait]`) is implemented by a
/// strict method of the block, whose certificate is compared with the contract.
#[doc(hidden)]
#[must_use]
pub const fn contracted_covered(contracted: &[&str], implemented: &[&str]) -> bool {
    let mut i = 0;
    while i < contracted.len() {
        let mut j = 0;
        let mut found = false;
        while j < implemented.len() {
            if str_eq(contracted[i], implemented[j]) {
                found = true;
            }
            j += 1;
        }
        if !found {
            return false;
        }
        i += 1;
    }
    true
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
#[diagnostic::on_unimplemented(
    message = "`{Self}` carries no allocation certificate (`fip_strict::FipBound`)",
    label = "not a certified callable",
    note = "a plain closure or function has no allocation bound: wrap it with `fip_macros::fip_fn!(|x: T| ..)` or, for a function with a certificate, `fip_macros::fip_fn!(path)`"
)]
pub unsafe trait FipBound {
    /// Upper bound on allocations per call.
    const ALLOCS: u64;
    /// `true` if the callable's body was checked with `panic_macros = false` (no
    /// panicking macro in it), as [`Cert::no_panic_macros`] for a function. A strict
    /// callee declared `panic_macros = false` requires it of every `param(..)`
    /// argument it calls.
    const NO_PANIC_MACROS: bool = false;
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
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a certified callable taking `{Args}` (`fip_strict::FipFn`)",
    label = "not a certified callable",
    note = "a plain closure or function has no allocation bound: wrap it with `fip_macros::fip_fn!(|x: T| ..)` or, for a function with a certificate, `fip_macros::fip_fn!(path)`",
    note = "a `fip_fn!` value takes `{Args}` only if its parameter types match; annotate them (`|v: &u8| ..`)"
)]
pub trait FipFn<Args>: FipBound {
    /// Return type.
    type Output;
    /// Calls the wrapped function.
    fn call(&self, args: Args) -> Self::Output;
}

/// A closure `C` certified to perform at most `ALLOCS` allocations per call, no
/// deallocation and no recursion. Made by `fip_macros::fip_fn!`. `NO_PANIC_MACROS`
/// (default `false`) states that its body was also checked with `panic_macros =
/// false` (`fip_fn!(panic_macros = false, ..)`); it is [`FipBound::NO_PANIC_MACROS`].
///
/// Fields are private and [`Certified::assume`] is `unsafe`: pairing a closure with
/// a bound is a claim.
#[cfg(not(verus_keep_ghost))]
pub struct Certified<const ALLOCS: u64, C, const NO_PANIC_MACROS: bool = false> {
    f: C,
}

#[allow(
    unsafe_code,
    reason = "the bound was claimed by the `unsafe` constructors `Certified::assume` / `assume_no_panic_macros`"
)]
#[cfg(not(verus_keep_ghost))]
unsafe impl<const ALLOCS: u64, C, const P: bool> FipBound for Certified<ALLOCS, C, P> {
    const ALLOCS: u64 = ALLOCS;
    const NO_PANIC_MACROS: bool = P;
}

/// Lifts a one-argument certified callable to a state-passing step for the `_st`
/// combinators: `Stateless(f)` called with `(s, x)` returns `(s, f(x))`, keeping the
/// state. Same bound as `f` (one call of `f`, nothing else).
///
/// Under Verus, `pre((s, x))` is `f.pre((x,))` and `post((s, x), (s2, y))` is
/// `s2 == s && f.post((x,), y)`.
#[cfg(not(verus_keep_ghost))]
pub struct Stateless<F>(pub F);

#[allow(
    unsafe_code,
    reason = "one call of `Stateless(f)` is one call of `f`, bounded by `F::ALLOCS`"
)]
#[cfg(not(verus_keep_ghost))]
unsafe impl<F: FipBound> FipBound for Stateless<F> {
    const ALLOCS: u64 = F::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS;
}

#[cfg(not(verus_keep_ghost))]
impl<S, A, B, F: FipFn<(A,), Output = B>> FipFn<(S, A)> for Stateless<F> {
    type Output = (S, B);
    #[inline]
    fn call(&self, args: (S, A)) -> (S, B) {
        let (s, x) = args;
        let y = self.0.call((x,));
        (s, y)
    }
}

/// `Compose(f, g)` called with `args` returns `g(f(args))`: `f` takes any number of
/// arguments (a `FipFn<Args>`), `g` takes `f`'s output. So it also maps the output
/// of a multi-argument callable. Its bound is `F::ALLOCS + G::ALLOCS` (one call of
/// each); an overflowing sum is a compile error in constant evaluation, not a
/// wrapped bound.
///
/// Under Verus, `pre(args)` is `f.pre(args)` and `g.pre` for every result `f.post`
/// allows; `post(args, z)` is: some `y` with `f.post(args, y)` and `g.post((y,), z)`.
#[cfg(not(verus_keep_ghost))]
pub struct Compose<F, G>(pub F, pub G);

#[allow(
    unsafe_code,
    reason = "one call of `Compose(f, g)` is one call of `f` and one of `g`"
)]
#[cfg(not(verus_keep_ghost))]
unsafe impl<F: FipBound, G: FipBound> FipBound for Compose<F, G> {
    const ALLOCS: u64 = F::ALLOCS + G::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS && G::NO_PANIC_MACROS;
}

#[cfg(not(verus_keep_ghost))]
impl<Args, B, C, F: FipFn<Args, Output = B>, G: FipFn<(B,), Output = C>> FipFn<Args>
    for Compose<F, G>
{
    type Output = C;
    #[inline]
    fn call(&self, args: Args) -> C {
        let y = self.0.call(args);
        self.1.call((y,))
    }
}

/// `Then(f, g)` runs two state-passing steps of the `_st` combinators one after the
/// other: called with `(s, x)`, `f` gives `(s1, y)` and `g` is called with
/// `(s1, y)`; the result is `g`'s. Bound `F::ALLOCS + G::ALLOCS`, as [`Compose`].
///
/// Under Verus, `pre((s, x))` is `f.pre((s, x))` and `g.pre(r)` for every result `r`
/// `f.post` allows; `post((s, x), out)` is: some `r` with `f.post((s, x), r)` and
/// `g.post(r, out)`.
#[cfg(not(verus_keep_ghost))]
pub struct Then<F, G>(pub F, pub G);

#[allow(
    unsafe_code,
    reason = "one call of `Then(f, g)` is one call of `f` and one of `g`"
)]
#[cfg(not(verus_keep_ghost))]
unsafe impl<F: FipBound, G: FipBound> FipBound for Then<F, G> {
    const ALLOCS: u64 = F::ALLOCS + G::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS && G::NO_PANIC_MACROS;
}

#[cfg(not(verus_keep_ghost))]
impl<S, A, B, C, F: FipFn<(S, A), Output = (S, B)>, G: FipFn<(S, B), Output = (S, C)>> FipFn<(S, A)>
    for Then<F, G>
{
    type Output = (S, C);
    #[inline]
    fn call(&self, args: (S, A)) -> (S, C) {
        let (s, y) = self.0.call(args);
        self.1.call((s, y))
    }
}

// ---- Verus declarations (only under the `verus` driver).

#[cfg(verus_keep_ghost)]
verus! {

/// Certificate for a callable value; see the plain declaration.
#[allow(unsafe_code, reason = "certificate trait; `unsafe impl` marks a trusted claim")]
#[diagnostic::on_unimplemented(
    message = "`{Self}` carries no allocation certificate (`fip_strict::FipBound`)",
    label = "not a certified callable",
    note = "a plain closure or function has no allocation bound: wrap it with `fip_macros::fip_fn!(|x: T| ..)` or, for a function with a certificate, `fip_macros::fip_fn!(path)`"
)]
pub unsafe trait FipBound {
    /// Upper bound on allocations per call.
    const ALLOCS: u64;
    /// `true` if the callable's body was checked with `panic_macros = false`.
    const NO_PANIC_MACROS: bool = false;
}

/// A certified callable taking `Args`, with a specification.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a certified callable taking `{Args}` (`fip_strict::FipFn`)",
    label = "not a certified callable",
    note = "a plain closure or function has no allocation bound: wrap it with `fip_macros::fip_fn!(|x: T| ..)` or, for a function with a certificate, `fip_macros::fip_fn!(path)`",
    note = "a `fip_fn!` value takes `{Args}` only if its parameter types match; annotate them (`|v: &u8| ..`)"
)]
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
pub struct Certified<const ALLOCS: u64, C, const NO_PANIC_MACROS: bool = false> {
    f: C,
}

impl<const ALLOCS: u64, C, const P: bool> Certified<ALLOCS, C, P> {
    /// The wrapped closure.
    pub closed spec fn inner(&self) -> C {
        self.f
    }
}

#[allow(unsafe_code, reason = "the bound was claimed by the `unsafe` constructors `Certified::assume` / `assume_no_panic_macros`")]
unsafe impl<const ALLOCS: u64, C, const P: bool> FipBound for Certified<ALLOCS, C, P> {
    const ALLOCS: u64 = ALLOCS;
    const NO_PANIC_MACROS: bool = P;
}

/// A state-keeping adapter; see the plain declaration.
pub struct Stateless<F>(pub F);

#[allow(unsafe_code, reason = "one call of `Stateless(f)` is one call of `f`, bounded by `F::ALLOCS`")]
unsafe impl<F: FipBound> FipBound for Stateless<F> {
    const ALLOCS: u64 = F::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS;
}

impl<S, A, B, F: FipFn<(A,), Output = B>> FipFn<(S, A)> for Stateless<F> {
    type Output = (S, B);
    open spec fn pre(&self, args: (S, A)) -> bool {
        self.0.pre((args.1,))
    }
    open spec fn post(&self, args: (S, A), out: (S, B)) -> bool {
        out.0 == args.0 && self.0.post((args.1,), out.1)
    }
    #[inline]
    fn call(&self, args: (S, A)) -> (r: (S, B)) {
        let (s, x) = args;
        let y = self.0.call((x,));
        (s, y)
    }
}

/// Composition; see the plain declaration.
pub struct Compose<F, G>(pub F, pub G);

#[allow(unsafe_code, reason = "one call of `Compose(f, g)` is one call of `f` and one of `g`")]
unsafe impl<F: FipBound, G: FipBound> FipBound for Compose<F, G> {
    const ALLOCS: u64 = F::ALLOCS + G::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS && G::NO_PANIC_MACROS;
}

impl<Args, B, C, F: FipFn<Args, Output = B>, G: FipFn<(B,), Output = C>> FipFn<Args> for Compose<F, G> {
    type Output = C;
    open spec fn pre(&self, args: Args) -> bool {
        &&& self.0.pre(args)
        &&& forall|y: B| #[trigger] self.0.post(args, y) ==> self.1.pre((y,))
    }
    open spec fn post(&self, args: Args, out: C) -> bool {
        exists|y: B| #[trigger] self.0.post(args, y) && self.1.post((y,), out)
    }
    #[inline]
    fn call(&self, args: Args) -> (r: C) {
        let y = self.0.call(args);
        self.1.call((y,))
    }
}

/// Two state-passing steps; see the plain declaration.
pub struct Then<F, G>(pub F, pub G);

#[allow(unsafe_code, reason = "one call of `Then(f, g)` is one call of `f` and one of `g`")]
unsafe impl<F: FipBound, G: FipBound> FipBound for Then<F, G> {
    const ALLOCS: u64 = F::ALLOCS + G::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS && G::NO_PANIC_MACROS;
}

impl<S, A, B, C, F: FipFn<(S, A), Output = (S, B)>, G: FipFn<(S, B), Output = (S, C)>> FipFn<(S, A)> for Then<F, G> {
    type Output = (S, C);
    open spec fn pre(&self, args: (S, A)) -> bool {
        &&& self.0.pre(args)
        &&& forall|r: (S, B)| #[trigger] self.0.post(args, r) ==> self.1.pre(r)
    }
    open spec fn post(&self, args: (S, A), out: (S, C)) -> bool {
        exists|r: (S, B)| #[trigger] self.0.post(args, r) && self.1.post(r, out)
    }
    #[inline]
    fn call(&self, args: (S, A)) -> (r: (S, C)) {
        let (s, y) = self.0.call(args);
        self.1.call((s, y))
    }
}

} // verus!

// ---- Shared items (both builds): one source, with the Verus specification in
// `cfg_attr(verus_keep_ghost, ..)`, so the Verus sidecar lists them by their text.
// Under Verus, `Certified` and `Certified::inner` are those of the `verus!` block.

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<const ALLOCS: u64, C> Certified<ALLOCS, C, false> {
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
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r.inner() == f,
    ))]
    pub const unsafe fn assume(f: C) -> Self {
        Certified { f }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<const ALLOCS: u64, C> Certified<ALLOCS, C, true> {
    /// [`Certified::assume`] for a closure whose body was also checked with
    /// `panic_macros = false`.
    ///
    /// # Safety
    ///
    /// As [`Certified::assume`], and the caller also asserts that the body of `f`
    /// uses none of the panicking macros `panic_macros = false` rejects.
    #[allow(
        unsafe_code,
        reason = "certificate constructor; `unsafe` marks a trusted claim"
    )]
    #[doc(hidden)]
    #[must_use]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r.inner() == f,
    ))]
    pub const unsafe fn assume_no_panic_macros(f: C) -> Self {
        Certified { f }
    }
}

/// `FipFn<(A0, ..)>` for `Certified<N, C>` with `C: Fn(A0, ..) -> R`: one source for
/// both declarations of the trait. Under Verus, `pre`/`post` are the closure's
/// `requires`/`ensures`.
macro_rules! certified_fip_fn {
    ($($A:ident $a:ident),*) => {
        #[cfg(not(verus_keep_ghost))]
        impl<const ALLOCS: u64, C, const P: bool, $($A,)* R> FipFn<($($A,)*)> for Certified<ALLOCS, C, P>
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
        impl<const ALLOCS: u64, C, const P: bool, $($A,)* R> FipFn<($($A,)*)> for Certified<ALLOCS, C, P>
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
        no_panic_macros: false,
    };

    /// `fip_core::replace`: same reasons as `__fip_strict_swap`.
    pub const __fip_strict_replace: Cert = Cert {
        name: "replace",
        allocs: 0,
        no_panic_macros: false,
    };

    /// `fip_alloc::refill`: the body calls only `core::mem::swap` (audited `core`
    /// table), moves the `Box` without dropping it, and does not recurse;
    /// allocation-free behaviour is also measured (`fip-alloc/tests/reuse.rs`).
    pub const __fip_strict_refill: Cert = Cert {
        name: "refill",
        allocs: 0,
        no_panic_macros: false,
    };
}
