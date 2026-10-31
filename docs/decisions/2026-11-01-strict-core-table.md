<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `#[fip(strict = true)]`: certificates and the audited `core` table

**Status:** ACCEPTED, 2026-11-01. Amended 2026-10-31 (named certificates,
`#[fip_impl]`, `Certified`, Verus specs for `FipFn`, `panic_macros = false`,
audit at rustc 1.97.1). Open items: `TODOs/strict-open-items.md`.

## Decision

A strict function may call only

1. functions in the `core` table below, named by a full path rooted at `core` or
   `std` (`core::mem::swap(..)`; `use` aliases are not recognised and are rejected), or
2. functions with a certificate: a `fip_strict::Cert` constant next to the function
   (or, for values called through `FipFn`, a `fip_strict::FipBound` impl):

   | callee as written | certificate read |
   |---|---|
   | `f(..)`, `a::f(..)` | `__fip_strict_f`, `a::__fip_strict_f` |
   | `Type::m(..)`, `a::Type::m(..)`, `<Type<..>>::m(..)`, `Self::m(..)` | `__fip_strict_Type__m` (module level) |
   | `<Type as Tr>::m(..)`, `<Self as Tr>::m(..)` | `__fip_strict_Type__Tr__m` (module level) |

`#[fip(strict = true)]`, `#[fip_impl]` (methods) and `fip_fn!` generate certificates
from a checked body. The certificate's bound is the body's own allocation sites plus
the callees' certificates, so the total is checked at compile time and recursion
through strict functions becomes a cycle in constant evaluation, which rustc rejects.

### Certificates name their function

`Cert::assume(name, allocs)`; generated certificates carry the part of their
identifier after `__fip_strict_` (`"f"`, `"Type__m"`, `"Type__Tr__m"`). A strict
caller reads a bound only through `Cert::allocs_for("<name>")`, which panics in
constant evaluation if the names differ. `use a::__fip_strict_g as __fip_strict_f;`
therefore fails where `f` is called (`compile_fail` example in `fip-macros`).
Still possible without `unsafe`: importing a **same-named** function's certificate
from another module (`use a::__fip_strict_f;` next to a local `fn f`). The token-level
caller cannot tell which `f` it calls; `fip_testkit::certs::hand_written` reports the
`__fip_strict_` identifier in source.

### Methods: `#[fip_impl]`

An associated constant needs inferable type arguments (`Type::<T>::C` cannot be
written with `T` unknown) and a trait impl cannot add items, so certificates of
methods are emitted at module level, before the `impl` block, by `#[fip_impl]`. The
name identifies one method only if no other impl can define the same name for the
same type name, so `#[fip_impl]` rejects:

- bounds on the impl's parameters and `where` clauses (a bounded impl leaves other
  instantiations to other impls);
- self types that are not `Name<exactly the impl's parameters>` (`impl Foo<u8>`,
  `impl<T> Tr for T`, `&Foo`);
- generic traits (`impl Tr<u8> for Foo`), and `<Type as Tr<..>>::m` in callers.

A trait method is reached only through `<Type as Tr>::m`: `Type::m` resolves to an
inherent method of that name first, and its certificate name is the inherent one.
A strict method with a `self` receiver outside `#[fip_impl]`, and `Self::m` outside
it, are compile errors. Residual: a type with **defaulted** parameters
(`struct Foo<T = u8>`) written as `impl Foo` covers only the default; the macro
cannot see the definition. Trait default methods get no certificate.

### Certified closures: `fip_strict::Certified`

`fip_fn!(|x: T| ..)` expands to
`unsafe { ::fip_strict::Certified::<{ checks; bound }, _>::assume(closure) }`: the
bound is a const argument of the type, and `Certified::assume` is the `unsafe`
claim. No item is declared, so the expression is accepted inside Verus-verified
bodies (Verus rejects item statements there; measured). `FipFn` is implemented for
closure arities 0–4. A `fip_fn!(..)` argument inside a strict body is not scanned
by the outer function (`fip_fn!` checks it; its calls are bounded by the receiving
function's `param(..)`).

### Verus specifications of `FipFn`

Under the `verus` driver `fip-strict` declares `FipBound`, `FipFn` and `Certified`
inside `verus! { }`; `FipFn` gains `spec fn pre(&self, args)` and
`spec fn post(&self, args, out)`, and `call` requires `pre` / ensures `post`. For
`Certified`, `pre`/`post` are the closure's `requires`/`ensures`. Plain builds keep
the dependency-free declarations; `fip-strict/tests/verus_drift.rs` compares the
exec items of both. Probed before implementing (Verus 0.2026.10.18.7d82994): `unsafe
trait` with an associated const, spec fns in traits, HRTB bounds
(`for<'a> FipFn<(&'a T,)>`), and the generic wrapper all verify; item statements in
verified bodies do not.

## The `core` table is audited, not proved

"Proved beforehand" holds only partly, and per property:

| property | evidence for every entry | strength |
|---|---|---|
| no heap allocation | `core` has no allocator API (crate boundary) | by construction |
| no deallocation | signature and body: no value of a caller-chosen type is dropped | audited (rustc 1.97.1 and 1.99.1 `core` sources) |
| no call into user code | no closure / trait-object / user-trait parameter is invoked | audited (same) |
| no recursion | implementation read | audited (same) |
| functional behaviour | `vstd` specification | only where marked below |

Line references are into `library/core/src` of the `rust-src` component; `vstd`
references into the `vstd` of the installed Verus (`/opt/verus/vstd`, 0.2026.10.18.7d82994).
A `vstd` specification is an `assume_specification`: trusted, and it states
functional behaviour only, not "no deallocation".

| entry | rustc 1.99.1 | rustc 1.97.1 | `vstd` spec | notes |
|---|---|---|---|---|
| `mem::swap` | `mem/mod.rs:830-834`: `intrinsics::typed_swap_nonoverlapping(x, y)` | `mem/mod.rs:785-789`, identical | yes (`std_specs/core.rs:129`) | drops nothing |
| `mem::replace` | `mem/mod.rs:961-979`: `read_via_copy` + `write_via_move`; "Nothing is dropped and nothing here can panic" (`:967`) | `mem/mod.rs:916-934`, identical | no | returns the old value |
| `mem::size_of` | `mem/mod.rs:375-384`: `<T as SizedTypeProperties>::SIZE` | `mem/mod.rs:373-375`, same body (1.99.1 adds a comment) | yes (`layout.rs:77`) | compile-time constant |
| `mem::align_of` | `mem/mod.rs:543-545`: `<T as SizedTypeProperties>::ALIGN` | `mem/mod.rs:528-530`, identical | yes (`layout.rs:85`) | compile-time constant |
| `hint::black_box` | `hint.rs:490-492`: `intrinsics::black_box(dummy)` | `hint.rs:490-492`, identical | no | returns its argument |
| `convert::identity` | `convert/mod.rs:106-108`: `x` | `convert/mod.rs:105-107`, identical | no | returns its argument |
| `slice::len` | `slice/mod.rs:116-118`: `ptr::metadata(self)` | same lines, identical | yes (`slice.rs:83`) | |
| `slice::is_empty` | `slice/mod.rs:136-138`: `self.len() == 0` | same lines, identical | yes (`slice.rs:95`) | |
| `slice::swap` | `slice/mod.rs:908-916`: bounds checks `&self[a]`, `&self[b]`, then `swap_unchecked` (`:947-…`: `ptr::swap(ptr.add(a), ptr.add(b))`) | `slice/mod.rs:906-918`: `&raw mut self[a]`, `&raw mut self[b]`, `ptr::swap(pa, pb)`; `ptr/mod.rs:1316-…` copies through a `MaybeUninit` | no | **differs** between the versions; both copy bytes, drop nothing, call no user code, may panic on an index |
| `slice::split_at` | `slice/mod.rs:1961-1966`: `split_at_checked`, `panic!("mid > len")` | `slice/mod.rs:1953-1958`, identical (`split_at_checked` `:2154-2162`, `split_at_unchecked` `:2039-2055`, identical) | yes (`std_specs/slice.rs:539`) | may panic |
| `slice::split_at_mut` | `slice/mod.rs:1995-2000` (`split_at_mut_checked` `:2201-2209`, `split_at_mut_unchecked` `:2101-2121`) | `slice/mod.rs:1987-1992` (`:2193-2201`, `:2093-2113`), identical | yes (`std_specs/slice.rs:549`) | may panic |

Excluded on purpose: `mem::take` (calls `Default::default`, user code),
`mem::drop` (runs drop glue, may free), `cmp::min`/`max` (call `Ord`, user code),
anything taking a closure.

The audit is tied to a toolchain. `fip_lint_rules::CORE_TABLE_AUDITED_AT` lists the
audited versions (`1.97.1`, `1.99.1`), and `fip-macros/tests/strict_toolchain.rs`
fails on any other compiling rustc (`fip-macros/build.rs` records it; measured to
fail on 1.96.0). When the toolchain changes, re-read the implementations above,
update the line references, and add the version.

## Hand-written certificates

A certificate is a claim. Writing one by hand needs `unsafe`
(`Cert::assume` and `Certified::assume` are `unsafe fn`s, `FipBound` an
`unsafe trait`):

- in a crate with `#![forbid(unsafe_code)]` it is impossible, while macro output still
  compiles (rustc does not apply `unsafe_code` to proc-macro output; measured
  2026-11-01 with a probe crate: generated `unsafe impl` accepted, hand-written one
  rejected; `compile_fail` examples for `Cert::assume`, `Certified::assume` and
  `unsafe impl FipBound`);
- elsewhere it is visible, and `fip_testkit::certs::hand_written` lists every
  occurrence (`Cert::assume` — which also matches `Certified::assume` —,
  `unsafe impl … FipBound`, and any `__fip_strict_` identifier in source).

The hand-written certificates in this repository live in `fip_strict::certs` and are
re-exported by `fip-core` and `fip-alloc` next to the functions, so those crates keep
`#![forbid(unsafe_code)]`. Being inside the crate that defines `Cert`, they are built
without `Cert::assume`; that module is the only place where this is possible, and a
test pins its exact contents, including that each names its function (plus the
re-exports in each crate):

| for | certificate (name) | justification |
|---|---|---|
| `fip_core::swap`, `fip_core::replace` | `__fip_strict_swap` (`"swap"`), `__fip_strict_replace` (`"replace"`) | `fip-core` links no `alloc`; drops nothing; calls no user code; Verus rejects recursion |
| `fip_alloc::refill` | `__fip_strict_refill` (`"refill"`) | body is `core::mem::swap` only; moves the `Box`; allocation-free behaviour measured |

`fip_core::strict::*` and the internal `swap_lt` carry generated certificates
(`#[fip(strict = true)]` in plain builds).

## What strict does not cover

Measured in `fip-macros/tests/strict_gaps.rs`; each is accepted with bound 0:

- **Implicit calls** (INHERENT for a token-level macro): `Drop` of locals (a strict
  function dropping its `Box` argument frees once), overloaded operators (`+` on a
  type whose `Add` allocates allocates once), `Deref`, `Index` on user types.
  `fip_testkit::assert_fip!` fails on both measured cases; closing the gap
  statically needs type information (a rustc driver), which is not dependency-free.
- **Panic paths** (MITIGATED): `panic_macros = false` rejects the panicking macros.
  A panicking strict function allocates on the `std` panic path (measured). Panics
  from indexing, overflow, division and callees remain.
- **Generic parameters** (INHERENT on stable): `FipFn` arguments are checked after
  monomorphisation. Measured with rustc 1.99.1: `--emit=metadata` (`cargo check`)
  accepts an argument exceeding its declared bound; a full build rejects it. A trait
  bound `ALLOCS <= K` needs `generic_const_exprs` (unstable).
- **`use` aliases** of table functions are rejected by design (the macro does not
  resolve names).

## What would reopen this

- A `vstd` (or other machine-checked) specification for the remaining table entries
  covering "no deallocation, no user code", which would turn audit into proof.
- rustc applying `unsafe_code` to proc-macro output (the forbid-crate story would
  need a different marker).
- Stable const-generic expressions (would let `Certified<N, _>: AtMost<K>` be checked
  by `cargo check`).
- Verus supporting item statements in verified bodies (not needed any more by
  `fip_fn!`, but by hand-written `FipBound` markers).
