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

### Amendment (2026-10-31): `fip-strict` is verified and imported by `fip-core`

`fip-core`'s strict variants take `fip_strict::FipFn` callables, whose `pre`/`post`
specifications exist only in `fip-strict`'s Verus declarations
(`#[cfg(verus_keep_ghost)] verus! { .. }`, plain declarations otherwise;
`fip-strict/tests/verus_drift.rs` compares them). So Verus checks the two crates
together:

- `just verify-strict`: `verus --crate-type=lib --crate-name fip_strict --no-cheating
  crates/fip-strict/src/lib.rs --export target/verus-strict/fip_strict.vir --compile
  --out-dir target/verus-strict`;
- `just verify-core` (depends on it): `verus --crate-type=lib --no-cheating
  crates/fip-core/src/lib.rs --import fip_strict=target/verus-strict/fip_strict.vir
  --extern fip_strict=target/verus-strict/libfip_strict.rlib`. The bare
  `verus crates/fip-core/src/lib.rs` no longer resolves `fip_strict`;
- `verify-negative` passes the same flags to every mutant, and `verify-compose`
  uses the Verus build of `fip_strict` (so `verify/compose_strict.rs` can verify a
  strict function with a `FipFn` parameter and a verified caller using `fip_fn!`).

`vstd` is still not a build dependency: the Verus declarations of `fip-strict` are
compiled only by the `verus` driver, which supplies `vstd`. `fip-core` gains the
workspace proc-macro `fip-macros` as a dependency (applied only in plain builds via
`cfg_attr(not(verus_keep_ghost), fip_macros::fip(..))`).

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

- Verus 0.2026.10.18.7d82994 (upstream main), Singular 4.4.1: `fip-core` 22 verified
  (including 7 pre-verification lemmas on the `dedup_by`/`compact_map` specs),
  `fip-alloc` 1 verified, both with `--no-cheating`; 10 Verus mutants and 2
  surface-gate mutants rejected (`just verify-negative`).
- Plain builds: `x86_64-unknown-none` with rustc 1.97.1 and 1.94.0
  (`--ignore-rust-version`), and `cargo test --workspace` on both.

## Measured (2026-10-31, after the amendment)

Same Verus and Singular: `fip-strict` 7 verified, `fip-core` 36 verified (including
the pre-verification lemmas of `compact_post` and the `FipFn` forms), `fip-alloc`
1 verified, `verify/compose.rs` 2 and `verify/compose_strict.rs` 4 verified, all with
`--no-cheating`. 17 Verus mutants rejected (the 10 above, 5 on `fip_core::strict`,
1 on the `FipFn` spec relation, 1 on `Certified::pre`); `verify-compose` rejects a
strict function claiming the negation of `FipFn::post`; the drift test rejects a
mutated `FipFn::call` declaration.

## Measured (2026-11-01, state-passing variants)

Same Verus and Singular: `fip-core` 51 verified (`map_in_place_st`, `compact_map_st`,
their strict forms, and the pre-verification lemmas of `spec::state`),
`verify/compose_state.rs` 4 verified (a counter threaded through `map_in_place_st`,
state 10 → elements `[11, 12, 13]`, final 13; an odd count through
`compact_map_st`); `fip-strict`, `fip-alloc`, `compose.rs`, `compose_strict.rs`
unchanged. 23 Verus mutants rejected (the 17 above, 5 that reverse the order or stop
threading the state, 1 that drops the state chain from `map_st_post`), and claiming
a wrong final state in either verified caller is rejected (`postcondition not
satisfied`).

Two findings constrain how the specs are written:

- **No ghost outputs under `--no-cheating`.** Attribute-mode `verus_spec(r => with
  -> trace: Ghost<..>)` verifies, but the macro also emits a copy of the function for
  unverified callers marked `external_body` with `requires false`
  (`builtin_macros/src/attr_rewrite.rs`, `rewrite_unverified_func`), and
  `--no-cheating` rejects every `external_body` outside `vstd`
  (`vir/src/well_formed.rs`). The trace is therefore existential, in named `*_post`
  predicates triggered on the elements, and callers `choose` it.
- **Per-module SMT context.** Verus gives each module's queries all of that module's
  definitions. With the new predicates added to `spec`, Z3 failed the existing
  `lemma_compact_map_spec_rejects_extra` deterministically (5 seeds); each wrapper
  alone did not. The new predicates live in the submodule `spec::state`, which leaves
  the context of `spec` as it was.

## Gaps this layout creates, and how they are closed

- **Unspecified functions are silently unverified.** Under the attribute syntax a
  function without `verus_spec` is external to Verus, and `--no-cheating` does not
  object. Closed by `tests/verified_surface.rs` in each verified crate (scanner in
  `fip_testkit::surface`): every `fn` outside `verus! { }` must carry a `verus_spec`
  attribute; a mutant with one attribute removed must fail the test.
- **`vstd` coverage limits what can be used.** E.g. `core::mem::replace` and
  `<[T]>::swap` have no `vstd` specification; `fip-core` builds them from
  `core::mem::swap` and `split_at_mut`, which do. A trusted specification would
  disable `--no-cheating` for every crate that imports it.

## What would reopen this

- Verus dropping or changing the attribute syntax (`verus_spec`, `proof!`).
- Consumers accepting `vstd` as a build dependency and verifying with the same
  upstream Verus as this repository.
