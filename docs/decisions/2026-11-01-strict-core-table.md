<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `#[fip(strict = true)]`: certificates and the audited `core` table

**Status:** ACCEPTED, 2026-11-01.

## Decision

A strict function may call only

1. functions in the `core` table below, named by a full path rooted at `core` or
   `std` (`core::mem::swap(..)`; `use` aliases are not recognised and are rejected), or
2. functions with a certificate: a `fip_strict::Cert` constant `__fip_strict_<fn>`
   next to the function, or (for values called through `FipFn`) a
   `fip_strict::FipBound` impl.

`#[fip(strict = true)]` and `fip_fn!` generate certificates from a checked body.
The certificate's bound is the body's own allocation sites plus the callees'
certificates, so the total is checked at compile time and recursion through strict
functions becomes a cycle in constant evaluation, which rustc rejects.

## The `core` table is audited, not proved

"Proved beforehand" holds only partly, and per property:

| property | evidence for every entry | strength |
|---|---|---|
| no heap allocation | `core` has no allocator API (crate boundary) | by construction |
| no deallocation | signature: no value of a caller-chosen type is dropped | audited (rustc 1.99.1 `core` sources) |
| no call into user code | no closure / trait-object / user-trait parameter is invoked | audited (same) |
| no recursion | implementation read | audited (same) |
| functional behaviour | `vstd` specification | only where marked below |

| entry | implementation at rustc 1.99.1 | `vstd` spec | notes |
|---|---|---|---|
| `mem::swap` | `intrinsics::typed_swap_nonoverlapping(x, y)` (`core/src/mem/mod.rs:830-834`) | **yes** (`std_specs/core.rs:129`) | drops nothing |
| `mem::replace` | two copies through intrinsics (`mem/mod.rs:961-…`); "Nothing is dropped and nothing here can panic" | no | returns the old value, drops nothing |
| `mem::size_of`, `mem::align_of` | `const fn`, no value arguments | no | compile-time constant |
| `hint::black_box` | `intrinsics::black_box(dummy)` (`core/src/hint.rs:490`) | no | returns its argument |
| `convert::identity` | `x` (`core/src/convert/mod.rs:106`) | no | returns its argument |

Excluded on purpose: `mem::take` (calls `Default::default`, user code),
`mem::drop` (runs drop glue, may free), `cmp::min`/`max` (call `Ord`, user code),
anything taking a closure.

The audit is tied to a toolchain. When the pinned rustc changes, re-read the five
implementations and update the line references.

## Hand-written certificates

A certificate is a claim. Writing one by hand needs `unsafe`
(`Cert::assume` is an `unsafe fn`, `FipBound` an `unsafe trait`):

- in a crate with `#![forbid(unsafe_code)]` it is impossible, while macro output still
  compiles (rustc does not apply `unsafe_code` to proc-macro output; measured
  2026-11-01 with a probe crate: generated `unsafe impl` accepted, hand-written one
  rejected);
- elsewhere it is visible, and `fip_testkit::certs::hand_written` lists every
  occurrence (`Cert::assume`, `unsafe impl … FipBound`, and any `__fip_strict_`
  identifier in source, which also catches re-exporting one function's certificate
  under another's name).

The hand-written certificates in this repository live in `fip_strict::certs` and are
re-exported by `fip-core` and `fip-alloc` next to the functions, so those crates keep
`#![forbid(unsafe_code)]`. Being inside the crate that defines `Cert`, they are built
without `Cert::assume`; that module is the only place where this is possible, and a
test pins its exact contents (plus the re-exports in each crate):

| for | certificate | justification |
|---|---|---|
| `fip_core::swap`, `fip_core::replace` | `__fip_strict_swap`, `__fip_strict_replace` | `fip-core` links no `alloc`; drops nothing; calls no user code; Verus rejects recursion |
| `fip_alloc::refill` | `__fip_strict_refill` | body is `core::mem::swap` only; moves the `Box`; allocation-free behaviour measured |

## What strict does not cover

- Implicit calls: `Drop` of locals (may free), overloaded operators, `Deref`, `Index`
  on user types. A token-level macro cannot see them.
- Panic paths: the allowed `assert!`/`panic!` family may allocate while panicking.
- Generic parameters: `FipFn` arguments are checked after monomorphisation, i.e.
  when the instantiation is built (`cargo build`, not `cargo check`).
- Methods on generic types and trait-impl methods cannot carry certificates (an
  associated constant needs inferable type arguments, and trait impls cannot add
  items).

## What would reopen this

- A `vstd` (or other machine-checked) specification for the remaining table entries
  covering "no deallocation, no user code", which would turn audit into proof.
- rustc applying `unsafe_code` to proc-macro output (the forbid-crate story would
  need a different marker).
