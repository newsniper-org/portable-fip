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
//! [`Cert::assume`], [`Cert::assume_no_panic_macros`], [`Certified::assume`] and
//! [`Certified::assume_no_panic_macros`] are `unsafe fn`s and [`FipBound`] is an
//! `unsafe trait` (its four `unsafe impl`s in this crate, for [`Certified`] and the
//! adapters, are the audited ones). In a crate with `#![forbid(unsafe_code)]` none can be written
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
//! One source for both builds. The exec items ([`FipBound`], [`FipOut`], [`FipFn`],
//! [`Certified`], the adapters, every `call`) are plain Rust with their Verus
//! specification in `cfg_attr(verus_keep_ghost, ..)` attributes. What exists only under
//! the `verus` driver (`cfg(verus_keep_ghost)`) is specification: the trait [`FipSpec`]
//! with the spec functions `pre`, `post` and `allocs` (a `nat`) and its impls,
//! `Certified::inner`, and the impls of the drop markers. No exec item is declared per
//! build. (Until 2026-11-25 the traits, the structs and the impls were declared twice,
//! once in `verus! { }`: what the sidecar generator's rule on `verus_keep_ghost` refuses;
//! decision record `2026-11-01-fip-prelint`, amendment 2026-11-25 (3).)
//!
//! [`FipFn::call`] requires `pre`, ensures `post` and is `allocates self.allocs()`,
//! `deallocates 0` (the Verus fork's bounds, checked with `-V alloc-check`; decision
//! `2026-11-06-redesign-verus-allocates`, phase 3). For [`Certified`]`<ALLOCS, C>` they
//! are the wrapped closure's `requires` / `ensures`, with
//! `call_allocations(closure, args) <= ALLOCS` as a second conjunct of `pre` (and
//! `call_deallocations(closure, args) == 0` as a third), and `allocs()` is `ALLOCS`. So
//! the certificate number is checked by Verus wherever a verified caller calls the
//! value: a closure that may allocate more than `ALLOCS` (or has no `allocates` bound)
//! fails `pre`. For the adapters `allocs()` is the sum of the parts' (`Stateless`: the
//! part's). `allocs` is a `nat`, not an `int`: the fork clamps a trait declaration's
//! bound at 0, so with `int` a generic caller could not use it.
//!
//! Under Verus the adapters and `Certified<_, C: Copy>` also implement
//! `vstd::alloc_check::AllocFreeDrop` and `NoDeallocDrop` (`unsafe impl`s checked by the
//! fork, pinned by `tests/hand_written_certs.rs`). [`Compose`] has one [`FipFn`] impl
//! per arity `0..=`[`MAX_ARITY`], in both builds: the fork requires a bound on every
//! type parameter of a bounded function and vstd has no `AllocFreeDrop` for a generic
//! argument tuple, so the argument types are bounded one by one.
//! [`Certified::assume`] and [`Certified::assume_no_panic_macros`] require, under Verus,
//! that dropping the closure cannot allocate (`vstd::alloc_check::bound_drop_alloc_free`,
//! which the fork checks at each verified call for the closure passed).
//!
//! Unwinding (2026-11-28): [`FipFn::call`] is `no_unwind when !self.may_unwind(args)`.
//! For [`Certified`], `may_unwind(args)` is the closure's `call_unwinds(closure, args)`
//! (the fork's unwinding of function values); for the adapters, that a part may unwind
//! (the second on a result the first allows). The two constructors are `no_unwind`. So
//! a function that may not unwind (what `#[fip(total)]` generates) can build and call a
//! certified callable whose closure is `no_unwind`.
//! Verify with `just verify-strict` (exports the Verus metadata `fip-core` imports).
//!
//! `#![no_std]`, no `alloc`, no dependencies.
//!
//! ## Certificates for other portable-fip crates
//!
//! None is made here. Until phase 5 of decision 2026-11-06-redesign-verus-allocates a
//! module `certs` held hand-written certificates for `fip_core::swap`,
//! `fip_core::replace` and `fip_alloc::refill`; those functions are now declared
//! `#[fip_macros::fip(strict ..)]` / `#[fip_macros::fip(total)]`, which generates
//! their certificates (and, under Verus, their allocation contracts) like any other
//! strict function's. A test pins that no certificate is made in this crate without
//! `Cert::assume`.

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

// ---- Drop markers of the Verus allocation check (decision
// 2026-11-06-redesign-verus-allocates, D2/D3). Both builds name them; only Verus
// restricts them.

/// Types whose drop glue cannot allocate.
///
/// Under Verus (`cfg(verus_keep_ghost)`) this is `vstd::alloc_check::AllocFreeDrop`:
/// the fork's `-V alloc-check` requires every type parameter of a function with an
/// `allocates` bound to be `Copy` or `AllocFreeDrop`, also where values are only
/// moved. vstd implements it for the primitive types, references and its trusted std
/// types; a user type needs an `unsafe impl` that Verus checks (rejected if the type's
/// `Drop::drop` is not bounded by `allocates 0`).
///
/// In plain builds it is a marker implemented for every type, so the bounds
/// `T: AllocFreeDrop` of `fip-core` and `fip-alloc` restrict nothing and need no
/// `vstd`. Consequence for downstream crates: an `unsafe impl AllocFreeDrop for Node {}`
/// must be Verus-only, `#[cfg(verus_keep_ghost)]` (and `verus_keep_ghost` in the crate's
/// `check-cfg`); ungated it fails the plain build with E0119 (it conflicts with the
/// blanket impl) and E0199 (the plain trait is not `unsafe`). It also needs `unsafe`,
/// so a crate under `#![forbid(unsafe_code)]` cannot write it.
#[cfg(verus_keep_ghost)]
pub use vstd::alloc_check::AllocFreeDrop;
/// Plain builds: implemented for every type (see the Verus declaration's docs).
#[cfg(not(verus_keep_ghost))]
pub trait AllocFreeDrop {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized> AllocFreeDrop for T {}

/// Types whose drop cannot deallocate (the fork's deallocation counting, 2026-11-22).
///
/// Under Verus this is `vstd::alloc_check::NoDeallocDrop` (primitives, references,
/// `Option`/`Result`/tuples of such, and a certified callable whose closure is `Copy`):
/// the strict combinators of `fip-core` take their callable by value and drop it, and
/// state `deallocates 0`. In plain builds a marker implemented for every type, as
/// [`AllocFreeDrop`] is (and with the same consequence for a downstream `unsafe impl`).
#[cfg(verus_keep_ghost)]
pub use vstd::alloc_check::NoDeallocDrop;
/// Plain builds: implemented for every type (see the Verus declaration's docs).
#[cfg(not(verus_keep_ghost))]
pub trait NoDeallocDrop {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized> NoDeallocDrop for T {}

// ---- The certificate traits. One declaration for both builds; the Verus
// specification is in `cfg_attr(verus_keep_ghost, ..)` and in `FipSpec`.

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
#[diagnostic::on_unimplemented(
    message = "`{Self}` carries no allocation certificate (`fip_strict::FipBound`)",
    label = "not a certified callable",
    note = "a plain closure or function has no allocation bound: wrap it with `fip_macros::fip_fn!(|x: T| ..)` or, for a function with a certificate, `fip_macros::fip_fn!(path)`"
)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub unsafe trait FipBound {
    /// Upper bound on allocations per call.
    const ALLOCS: u64;
    /// `true` if the callable's body was checked with `panic_macros = false` (no
    /// panicking macro in it), as [`Cert::no_panic_macros`] for a function. A strict
    /// callee declared `panic_macros = false` requires it of every `param(..)`
    /// argument it calls.
    const NO_PANIC_MACROS: bool = false;
}

/// The return type of a certified callable taking `Args`: the `Output` of
/// [`FipFn`]`<Args>`, which has it as a supertrait (so `F: FipFn<(A,), Output = B>` and
/// `F::Output` read as before).
///
/// A trait of its own because the Verus specification of a call ([`FipSpec`]) names
/// the output type and is a supertrait of [`FipFn`] too. An implementation of
/// [`FipFn`] gives `Output` in an `impl FipOut<Args>`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait FipOut<Args> {
    /// Return type.
    type Output;
}

/// The Verus specification of a certified callable taking `Args`.
///
/// Under Verus (`cfg(verus_keep_ghost)`) a trait with the spec functions
/// `pre(&self, args: Args) -> bool`, `post(&self, args: Args, out: Self::Output) -> bool`
/// and `allocs(&self) -> nat`, which [`FipFn::call`] requires, ensures and is bounded
/// by, and `may_unwind(&self, args: Args) -> bool`: `call` is
/// `no_unwind when !self.may_unwind(args)` (since 2026-11-28). A type implements it in
/// a `#[cfg(verus_keep_ghost)] verus! { .. }` block.
///
/// In plain builds a marker implemented for every type, so the supertrait of
/// [`FipFn`] restricts nothing and needs no `vstd`.
#[cfg(not(verus_keep_ghost))]
pub trait FipSpec<Args> {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized, Args> FipSpec<Args> for T {}

/// A certified callable taking `Args` (a tuple, e.g. `(&T,)`).
///
/// Values come from `fip_macros::fip_fn!(|x| ..)`. Call with
/// `FipFn::call(&f, (x,))` or `f.call((x,))`; stable Rust does not allow
/// implementing the `Fn` traits, so `f(x)` is not available.
///
/// The return type is [`FipOut::Output`]. Under Verus, `call` requires
/// [`FipSpec`]'s `pre`, ensures `post` and allocates at most `allocs()`, with no
/// deallocation (Verus fork, `-V alloc-check`).
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a certified callable taking `{Args}` (`fip_strict::FipFn`)",
    label = "not a certified callable",
    note = "a plain closure or function has no allocation bound: wrap it with `fip_macros::fip_fn!(|x: T| ..)` or, for a function with a certificate, `fip_macros::fip_fn!(path)`",
    note = "a `fip_fn!` value takes `{Args}` only if its parameter types match; annotate them (`|v: &u8| ..`)"
)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait FipFn<Args>: FipBound + FipOut<Args> + FipSpec<Args> {
    /// Calls the wrapped function.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.pre(args),
        ensures
            self.post(args, r),
        no_unwind when !self.may_unwind(args)
        allocates self.allocs()
        deallocates 0
    ))]
    fn call(&self, args: Args) -> <Self as FipOut<Args>>::Output;
}

/// A closure `C` certified to perform at most `ALLOCS` allocations per call, no
/// deallocation and no recursion. Made by `fip_macros::fip_fn!`. `NO_PANIC_MACROS`
/// (default `false`) states that its body was also checked with `panic_macros =
/// false` (`fip_fn!(panic_macros = false, ..)`); it is [`FipBound::NO_PANIC_MACROS`].
///
/// Fields are private and [`Certified::assume`] is `unsafe`: pairing a closure with
/// a bound is a claim. Under Verus the claim is checked at each verified call:
/// `pre(args)` requires `call_allocations(closure, args) <= ALLOCS` and
/// `call_deallocations(closure, args) == 0` (since 2026-11-22: `FipFn::call` is
/// `deallocates 0`), and `allocs()` is `ALLOCS`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Certified<const ALLOCS: u64, C, const NO_PANIC_MACROS: bool = false> {
    f: C,
}

#[allow(
    unsafe_code,
    reason = "the bound was claimed by the `unsafe` constructors `Certified::assume` / `assume_no_panic_macros`"
)]
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
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Stateless<F>(pub F);

#[allow(
    unsafe_code,
    reason = "one call of `Stateless(f)` is one call of `f`, bounded by `F::ALLOCS`"
)]
unsafe impl<F: FipBound> FipBound for Stateless<F> {
    const ALLOCS: u64 = F::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<S, A, B, F: FipFn<(A,), Output = B>> FipOut<(S, A)> for Stateless<F> {
    type Output = (S, B);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<
    S: crate::AllocFreeDrop,
    A: crate::AllocFreeDrop,
    B: crate::AllocFreeDrop,
    F: FipFn<(A,), Output = B>,
> FipFn<(S, A)> for Stateless<F>
{
    #[inline]
    fn call(&self, args: (S, A)) -> (S, B) {
        let (s, x) = args;
        let y = self.0.call((x,));
        (s, y)
    }
}

/// `Compose(f, g)` called with `args` returns `g(f(args))`: `f` takes up to
/// [`MAX_ARITY`] arguments, `g` takes `f`'s output. So it also maps the output of a
/// multi-argument callable. Its bound is `F::ALLOCS + G::ALLOCS` (one call of
/// each); an overflowing sum is a compile error in constant evaluation, not a
/// wrapped bound.
///
/// Under Verus, `pre(args)` is `f.pre(args)` and `g.pre` for every result `f.post`
/// allows; `post(args, z)` is: some `y` with `f.post(args, y)` and `g.post((y,), z)`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Compose<F, G>(pub F, pub G);

#[allow(
    unsafe_code,
    reason = "one call of `Compose(f, g)` is one call of `f` and one of `g`"
)]
unsafe impl<F: FipBound, G: FipBound> FipBound for Compose<F, G> {
    const ALLOCS: u64 = F::ALLOCS + G::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS && G::NO_PANIC_MACROS;
}

/// `Then(f, g)` runs two state-passing steps of the `_st` combinators one after the
/// other: called with `(s, x)`, `f` gives `(s1, y)` and `g` is called with
/// `(s1, y)`; the result is `g`'s. Bound `F::ALLOCS + G::ALLOCS`, as [`Compose`].
///
/// Under Verus, `pre((s, x))` is `f.pre((s, x))` and `g.pre(r)` for every result `r`
/// `f.post` allows; `post((s, x), out)` is: some `r` with `f.post((s, x), r)` and
/// `g.post(r, out)`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Then<F, G>(pub F, pub G);

#[allow(
    unsafe_code,
    reason = "one call of `Then(f, g)` is one call of `f` and one of `g`"
)]
unsafe impl<F: FipBound, G: FipBound> FipBound for Then<F, G> {
    const ALLOCS: u64 = F::ALLOCS + G::ALLOCS;
    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS && G::NO_PANIC_MACROS;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<S, A, B, C, F: FipFn<(S, A), Output = (S, B)>, G: FipFn<(S, B), Output = (S, C)>>
    FipOut<(S, A)> for Then<F, G>
{
    type Output = (S, C);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<
    S: crate::AllocFreeDrop,
    A: crate::AllocFreeDrop,
    B: crate::AllocFreeDrop,
    C: crate::AllocFreeDrop,
    F: FipFn<(S, A), Output = (S, B)>,
    G: FipFn<(S, B), Output = (S, C)>,
> FipFn<(S, A)> for Then<F, G>
{
    #[inline]
    fn call(&self, args: (S, A)) -> (S, C) {
        let (s, y) = self.0.call(args);
        self.1.call((s, y))
    }
}

// ---- Specifications (only under the `verus` driver): no exec code.

#[cfg(verus_keep_ghost)]
verus! {

/// The specification of a certified callable taking `Args`; see the plain declaration.
pub trait FipSpec<Args>: FipOut<Args> {
    /// Precondition of a call with `args`.
    spec fn pre(&self, args: Args) -> bool;
    /// Postcondition of a call with `args` returning `out`.
    spec fn post(&self, args: Args, out: Self::Output) -> bool;
    /// Upper bound on the allocations of one call (Verus `allocates`).
    spec fn allocs(&self) -> nat;
    /// Whether a call with `args` may unwind (`call` is `no_unwind when !may_unwind(args)`).
    spec fn may_unwind(&self, args: Args) -> bool;
}

impl<const ALLOCS: u64, C, const P: bool> Certified<ALLOCS, C, P> {
    /// The wrapped closure.
    pub closed spec fn inner(&self) -> C {
        self.f
    }
}

impl<S, A, B, F: FipFn<(A,), Output = B>> FipSpec<(S, A)> for Stateless<F> {
    open spec fn pre(&self, args: (S, A)) -> bool {
        self.0.pre((args.1,))
    }
    open spec fn post(&self, args: (S, A), out: (S, B)) -> bool {
        out.0 == args.0 && self.0.post((args.1,), out.1)
    }
    open spec fn allocs(&self) -> nat {
        self.0.allocs()
    }
    open spec fn may_unwind(&self, args: (S, A)) -> bool {
        self.0.may_unwind((args.1,))
    }
}

impl<S, A, B, C, F: FipFn<(S, A), Output = (S, B)>, G: FipFn<(S, B), Output = (S, C)>> FipSpec<(S, A)> for Then<F, G> {
    open spec fn pre(&self, args: (S, A)) -> bool {
        &&& self.0.pre(args)
        &&& forall|r: (S, B)| #[trigger] self.0.post(args, r) ==> self.1.pre(r)
    }
    open spec fn post(&self, args: (S, A), out: (S, C)) -> bool {
        exists|r: (S, B)| #[trigger] self.0.post(args, r) && self.1.post(r, out)
    }
    open spec fn allocs(&self) -> nat {
        self.0.allocs() + self.1.allocs()
    }
    open spec fn may_unwind(&self, args: (S, A)) -> bool {
        self.0.may_unwind(args) || exists|r: (S, B)| #[trigger] self.0.post(args, r) && self.1.may_unwind(r)
    }
}

// Dropping a certified callable can neither allocate nor deallocate when the wrapped
// closure is `Copy` (its captures are), or when the adapters' parts cannot.
#[allow(unsafe_code, reason = "checked by Verus -V alloc-check (drop rule)")]
unsafe impl<const ALLOCS: u64, C: Copy, const P: bool> vstd::alloc_check::AllocFreeDrop for Certified<ALLOCS, C, P> {}
#[allow(unsafe_code, reason = "checked by Verus -V alloc-check (drop rule)")]
unsafe impl<const ALLOCS: u64, C: Copy, const P: bool> vstd::alloc_check::NoDeallocDrop for Certified<ALLOCS, C, P> {}
#[allow(unsafe_code, reason = "checked by Verus -V alloc-check (drop rule)")]
unsafe impl<F: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Stateless<F> {}
#[allow(unsafe_code, reason = "checked by Verus -V alloc-check (drop rule)")]
unsafe impl<F: vstd::alloc_check::NoDeallocDrop> vstd::alloc_check::NoDeallocDrop for Stateless<F> {}
#[allow(unsafe_code, reason = "checked by Verus -V alloc-check (drop rule)")]
unsafe impl<F: vstd::alloc_check::AllocFreeDrop, G: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Compose<F, G> {}
#[allow(unsafe_code, reason = "checked by Verus -V alloc-check (drop rule)")]
unsafe impl<F: vstd::alloc_check::NoDeallocDrop, G: vstd::alloc_check::NoDeallocDrop> vstd::alloc_check::NoDeallocDrop for Compose<F, G> {}
#[allow(unsafe_code, reason = "checked by Verus -V alloc-check (drop rule)")]
unsafe impl<F: vstd::alloc_check::AllocFreeDrop, G: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Then<F, G> {}
#[allow(unsafe_code, reason = "checked by Verus -V alloc-check (drop rule)")]
unsafe impl<F: vstd::alloc_check::NoDeallocDrop, G: vstd::alloc_check::NoDeallocDrop> vstd::alloc_check::NoDeallocDrop for Then<F, G> {}

} // verus!

// ---- The constructors.

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<const ALLOCS: u64, C> Certified<ALLOCS, C, false> {
    /// Wraps `f` without checking anything.
    ///
    /// Under Verus it requires that dropping a `C` cannot allocate
    /// (`vstd::alloc_check::bound_drop_alloc_free`): the fork checks it at each
    /// verified call, for the closure passed.
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
        requires
            vstd::alloc_check::bound_drop_alloc_free::<C>(),
        ensures
            r.inner() == f,
        no_unwind
        allocates 0
        deallocates 0
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
        requires
            vstd::alloc_check::bound_drop_alloc_free::<C>(),
        ensures
            r.inner() == f,
        no_unwind
        allocates 0
        deallocates 0
    ))]
    pub const unsafe fn assume_no_panic_macros(f: C) -> Self {
        Certified { f }
    }
}

/// `FipFn<(A0, ..)>` for `Certified<N, C>` with `C: Fn(A0, ..) -> R`. Under Verus,
/// `pre`/`post` are the closure's `requires`/`ensures`.
macro_rules! certified_fip_fn {
    ($($A:ident $a:ident),*) => {
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        impl<const ALLOCS: u64, C, const P: bool, $($A,)* R> FipOut<($($A,)*)> for Certified<ALLOCS, C, P>
        where
            C: Fn($($A),*) -> R,
        {
            type Output = R;
        }

        #[cfg(verus_keep_ghost)]
        verus! {
        impl<const ALLOCS: u64, C, const P: bool, $($A,)* R> FipSpec<($($A,)*)> for Certified<ALLOCS, C, P>
        where
            C: Fn($($A),*) -> R,
        {
            open spec fn pre(&self, args: ($($A,)*)) -> bool {
                &&& self.inner().requires(args)
                &&& call_allocations(self.inner(), args) <= ALLOCS as int
                &&& call_deallocations(self.inner(), args) == 0
            }
            open spec fn allocs(&self) -> nat {
                ALLOCS as nat
            }
            open spec fn post(&self, args: ($($A,)*), out: R) -> bool {
                self.inner().ensures(args, out)
            }
            open spec fn may_unwind(&self, args: ($($A,)*)) -> bool {
                call_unwinds(self.inner(), args)
            }
        }
        } // verus!

        #[cfg_attr(verus_keep_ghost, verus_verify)]
        impl<const ALLOCS: u64, C, const P: bool, $($A: crate::AllocFreeDrop,)* R: crate::AllocFreeDrop> FipFn<($($A,)*)> for Certified<ALLOCS, C, P>
        where
            C: Fn($($A),*) -> R,
        {
            #[inline]
            fn call(&self, args: ($($A,)*)) -> R {
                let ($($a,)*) = args;
                (self.f)($($a),*)
            }
        }
    };
}

certified_fip_fn!();
certified_fip_fn!(A0 a0);
certified_fip_fn!(A0 a0, A1 a1);
certified_fip_fn!(A0 a0, A1 a1, A2 a2);
certified_fip_fn!(A0 a0, A1 a1, A2 a2, A3 a3);

/// Largest closure arity `fip_fn!` supports (the number of `FipFn` impls above), and
/// the largest arity of the first callable of a [`Compose`].
pub const MAX_ARITY: usize = 4;

/// `FipFn` for `Compose`, one impl per arity `0..=MAX_ARITY` of `f`: the fork's
/// `-V alloc-check` requires every type parameter of a bounded function to be `Copy`
/// or `AllocFreeDrop`, and vstd has no `AllocFreeDrop` for a generic tuple `Args` (nor
/// for 1-tuples), so the argument types are bounded one by one. The same impls in
/// plain builds (until 2026-11-25 those had one impl generic over `Args`).
macro_rules! compose_fip_fn {
    ($($A:ident),*) => {
        #[cfg_attr(verus_keep_ghost, verus_verify)]
        impl<$($A,)* B, C, F: FipFn<($($A,)*), Output = B>, G: FipFn<(B,), Output = C>> FipOut<($($A,)*)> for Compose<F, G> {
            type Output = C;
        }

        #[cfg(verus_keep_ghost)]
        verus! {
        impl<$($A,)* B, C, F: FipFn<($($A,)*), Output = B>, G: FipFn<(B,), Output = C>> FipSpec<($($A,)*)> for Compose<F, G> {
            open spec fn pre(&self, args: ($($A,)*)) -> bool {
                &&& self.0.pre(args)
                &&& forall|y: B| #[trigger] self.0.post(args, y) ==> self.1.pre((y,))
            }
            open spec fn post(&self, args: ($($A,)*), out: C) -> bool {
                exists|y: B| #[trigger] self.0.post(args, y) && self.1.post((y,), out)
            }
            open spec fn allocs(&self) -> nat {
                self.0.allocs() + self.1.allocs()
            }
            open spec fn may_unwind(&self, args: ($($A,)*)) -> bool {
                self.0.may_unwind(args) || exists|y: B| #[trigger] self.0.post(args, y) && self.1.may_unwind((y,))
            }
        }
        } // verus!

        #[cfg_attr(verus_keep_ghost, verus_verify)]
        impl<$($A: crate::AllocFreeDrop,)* B: crate::AllocFreeDrop, C: crate::AllocFreeDrop, F: FipFn<($($A,)*), Output = B>, G: FipFn<(B,), Output = C>> FipFn<($($A,)*)> for Compose<F, G> {
            #[inline]
            fn call(&self, args: ($($A,)*)) -> C {
                let y = self.0.call(args);
                self.1.call((y,))
            }
        }
    };
}

compose_fip_fn!();
compose_fip_fn!(A0);
compose_fip_fn!(A0, A1);
compose_fip_fn!(A0, A1, A2);
compose_fip_fn!(A0, A1, A2, A3);
