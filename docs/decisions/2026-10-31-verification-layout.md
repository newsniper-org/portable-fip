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
  (`vir/src/well_formed.rs`). The trace was therefore existential, in named `*_post`
  predicates triggered on the elements, and callers `choose` it (superseded by the
  named traces below).
- **Per-module SMT context.** Verus gives each module's queries all of that module's
  definitions. With the new predicates added to `spec`, Z3 failed the existing
  `lemma_compact_map_spec_rejects_extra` deterministically (5 seeds); each wrapper
  alone did not. The new predicates live in the submodule `spec::state`, which leaves
  the context of `spec` as it was.

## Measured (2026-11-01, state invariants and named traces)

Two open points of the state-passing variants: `f` had to accept every element with
any state, and callers had to `choose` the trace. Both Verus builds, `--no-cheating`:
upstream 0.2026.10.18.7d82994 and Y4's fork 0.2026.10.31.559ac52
(`VERUS=$HOME/Y4/verus-fork/source/target-verus/release/verus VERUS_Z3_PATH=/usr/bin/z3
just verify`), identical results: `fip-strict` 7, `fip-core` 56 (51 before),
`fip-alloc` 1, `verify/compose.rs` 2, `verify/compose_strict.rs` 4,
`verify/compose_state.rs` 9 (4 before) verified; `fip-core` also verifies with
`smt.random_seed` 1–7 on both. 33 Verus mutants (23 before) and 7 wrong claims of
verified callers (2 before) are rejected for their stated reason.

Encodings tried (probes outside the repository on both builds, except where marked):

| open point | encoding | result |
|---|---|---|
| invariant | ghost parameter `verus_spec(with Ghost(inv): Ghost<Inv>, ..)` | verifies without `--no-cheating`; rejected with it on both builds (`external_body/assume_specification not allowed with --no-cheating`): any `with` clause makes the macro emit the twin (`rewrite_verus_spec_on_fun_or_loop`, same code in `/opt/verus` and the fork) |
| invariant | trait `StInv<S>` with `spec fn inv(&self, k: int, s: S)`, passed as a value, with a `NoInv` default | verifies on both builds (probe, 4 verified). Not adopted: functions cannot have default type parameters, so it needs new functions, and the trait and every caller's invariant type must be declared twice (plain and `verus!`), as `FipFn` is |
| invariant | precondition over reachable states (`reachable(k, s) ==> f.requires(..)`) | not measured. As strong as the adopted form with `inv = reachable`, but each caller has to prove reachability by induction (a recursive lemma) |
| invariant | **adopted:** `requires map_st_by_ok(xs, f, s0)`: `f` accepts any state, or some `inv` satisfies `map_st_by_inv` (holds on `s0`; `f` accepts `xs[k]` with every state satisfying `inv(k, _)`; every call preserves it); `ensures`: every such `inv` holds along the trace | verifies on both builds; signatures unchanged; callers whose `f` has no precondition prove the first case as before; a caller states its invariant by proving `map_st_by_inv` for a concrete `inv` |
| trace | `with -> trace: Ghost<..>`, `with Tracked(out): Tracked<&mut Ghost<..>>` | rejected under `--no-cheating` on both builds (same twin) |
| trace | ghost field of the result type | not measured: the results are tuples; a struct would change the plain-build signature |
| trace | **adopted:** spec fn `map_st_by_trace(old, new, f, s0, s)` = `choose` of a trace satisfying the postcondition along which every invariant holds; the `ensures` states the postcondition for it (`compact_map_st_by_witnesses` returns `(ss, ys, ks, idx, pos)`) | verifies on both builds; callers bind it with `let`, no `choose` and no lemma call |
| strict caller | `fip_fn!(\|c: u32, x: u32\| tick_checked(c, x))` in place of the `Certified` value below | rejected (upstream): the closure has no `requires`, so its call of `tick_checked` fails "precondition not satisfied", and `map_st_fip_inv` is unprovable because the closure's `requires` / `ensures` are unspecified. `fip_fn!` accepts only `\|args\| body`, so no spec can be attached |
| strict caller | **adopted:** `unsafe { Certified::<{ __fip_strict_tick_checked.allocs_for("tick_checked") }, _>::assume(tick_checked) }` in `verify/compose_state.rs` | verifies on both builds; `pre` / `post` are the named function's `requires` / `ensures`; the bound is its generated certificate. `verify/` is outside every crate's `src`, so the certificate gate does not see it |

Findings:

- **`spec_fn` applications are not triggers.** A quantifier whose only candidate was
  `inv(k, s)` failed with "Could not automatically infer triggers". The invariant
  quantifiers trigger on `f.requires` / `f.ensures` (`pre` / `post`) and `ss[k]`.
- **Z3 session state.** With the new definitions, `compact_map`'s and
  `compact_map_st`'s proofs verified alone and on 7 seeds but failed whenever an
  earlier query of module `slice` had failed (mutants of `map_in_place_st`);
  `verifier::spinoff_prover` gives each its own Z3 process, after which those mutants
  fail only where intended.
- **Error budget of mutants.** A reversed `map_in_place_st` loop now first fails
  `f`'s indexed precondition; with Verus's default of 2 extra errors per function
  the state-chain invariant was not reported. Mutants run with `--multiple-errors 8`.

Still open: `fip_fn!` cannot wrap a closure with Verus `ensures`, so a strict verified
caller passes a named function through `Certified::assume` by hand.

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
