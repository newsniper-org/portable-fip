<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# Verification layout: one source, attribute-syntax specs, no `vstd` dependency

**Status:** ACCEPTED, 2026-10-31.

## Decision

`fip-core` and `fip-alloc` are plain Rust with **no dependencies**. Their Verus
specifications are written in Verus's attribute syntax and are active only when
the `verus` driver compiles the crate:

```rust
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures *final(slot) == new, r == *old(slot),
))]
pub fn replace<T>(slot: &mut T, new: T) -> T { /* … */ }
```

- `verus_keep_ghost` is set only by `verus`. A plain `cargo` build drops every
  specification, loop invariant and `proof!` block, so neither Verus nor `vstd`
  is a build dependency.
- `vstd` and the attribute macros come from the `verus` installation at
  verification time (`verus --crate-type=lib --no-cheating crates/<c>/src/lib.rs`).
- `proof!` / `proof_decl!` are defined as no-op `macro_rules!` in plain builds.
- `#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]` is required:
  attribute macros on loops are unstable syntax, enabled only for the verifier.

## Why

The crates must be consumable by kernel crates that keep `[dependencies]` empty,
build on stable rustc, and may verify their own code with a different Verus build
(e.g. a fork) than the one used here. Two alternatives were examined:

| alternative | problem |
|---|---|
| exec code inside `verus! { }` with `vstd` as a dependency | `vstd` (and through it `verus_builtin`, `verus_builtin_macros`, `verus_state_machines_macros`) becomes a dependency of every downstream build, including kernel crates; a second `vstd` would sit beside the one of a consumer verifying with another Verus build |
| plain crate + a sibling proof crate restating the functions | two copies of each body; drift between them is exactly the class of bug the single-spec discipline exists to prevent |

The attribute syntax keeps one body, verified as written.

## Measured (2026-10-31)

- Verus 0.2026.10.18.7d82994 (upstream main), Singular 4.4.1: `fip-core` 8 verified,
  `fip-alloc` 1 verified, both with `--no-cheating`; 5 mutants rejected
  (`just verify-negative`).
- Plain builds: `x86_64-unknown-none` with rustc 1.97.1 and 1.94.0
  (`--ignore-rust-version`), and `cargo test --workspace` on both.

## Gaps this layout creates, and how they are closed

- **Unspecified functions are silently unverified.** Under the attribute syntax a
  function without `verus_spec` is external to Verus, and `--no-cheating` does not
  object. Closed by `tests/verified_surface.rs` in each verified crate: every `fn`
  outside `verus! { }` must carry a `verus_spec` attribute.
- **`vstd` coverage limits what can be used.** E.g. `core::mem::replace` and
  `<[T]>::swap` have no `vstd` specification; `fip-core` builds them from
  `core::mem::swap` and `split_at_mut`, which do. A trusted specification would
  disable `--no-cheating` for every crate that imports it.

## What would reopen this

- Verus dropping or changing the attribute syntax (`verus_spec`, `proof!`).
- Consumers accepting `vstd` as a build dependency and verifying with the same
  upstream Verus as this repository.
