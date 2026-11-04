<!-- SPDX-License-Identifier: MIT OR Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# Evidence pack for a Verus GitHub Discussion

**Status:** WORKING MATERIAL, 2026-11-04. Not the Discussion text.

This file collects facts, measurements and pointers for a Discussion with the Verus
team. The Discussion text, PR descriptions and replies must be written by the human
contributor (Verus `CONTRIBUTING.md`, "Policy for AI-generated and AI-assisted code").
Code is contributed only after `portable-fip` is complete, by extracting the relevant
parts and having the human contributor rewrite them.

Versions used for every measurement below, unless stated otherwise:

- upstream Verus `0.2026.10.18.7d82994` (`/usr/bin/verus`), with Z3 4.16.0;
- a downstream fork rebased on the same release (`0.2026.10.31.559ac52`), used only
  to confirm that results match;
- rustc 1.99.1, the toolchain Verus pins in `rust-toolchain.toml`.

Source references to Verus are file:line at commit `7d82994`.

## 0. Contribution policy facts that shape the plan

- Opinionated changes should start with a GitHub Discussion (`CONTRIBUTING.md:30`).
- AI use must be disclosed in the PR. Tools are not listed as co-authors; use
  `Assisted-by: <tool>:<model>`. PR descriptions and discussion comments must be
  human-written (`CONTRIBUTING.md:32-38`).
- License: Verus is MIT. `portable-fip` is now dual MIT OR Apache-2.0 (relicensed in
  commit `9b18e50`, 2026-11-04; `docs/decisions/2026-11-04-dual-license.md`).
- Commit trailers in `portable-fip` (measured 2026-11-04 at `ee273e1`): 0 of 114
  commits on all local branches contain `Co-Authored-By` or `Claude`. The extracted contribution will add
  `Assisted-by:` trailers where they apply.

## 1. Findings about Verus itself (candidate issues or Discussion points)

### 1.1 `FnMut` closures: the post-call state is not modelled

Probes: `docs/notes/verus-fnmut/` (each file states how to run it), and the note
`docs/notes/verus-fnmut-monadic-workaround.md`.

| probe | what it does | result on upstream |
|---|---|---|
| `a_generic.rs` | `F: FnMut(u32) -> bool` called in a loop; the postcondition does not mention the results | 3 verified |
| `b_capture.rs` | a closure in verified code that mutates a captured local | rejected: "Verus does not currently support closures capturing a mutable reference for variables of any mode" |
| `c_state.rs` | after `let b = f(1)` with `f: F: FnMut`, `assert(f == f0)` where `f0` is the value before the call | **verifies** |

What `c_state.rs` shows: suppose a combinator that is generic over `FnMut` has been
verified. Its proof covers only closures without state. If unverified code passes a
closure that has state, the proof relies on a false fact.

Workaround, measured: pass the state explicitly as `Fn(S, X) -> (S, Y)` and carry the
trace in the postcondition.
- `e_monadic.rs`: 5 verified, including a caller that proves the final state is 3.
- `e_negative.rs`: claims 4 and is rejected.
- Both builds give the same results.

Questions for the team:
- Is this the intended semantics?
- Would a guide section on the state-passing pattern be welcome?

### 1.2 Attribute mode: any `with` clause makes `--no-cheating` reject the function

What happens:
- In attribute mode (`#[verus_spec(..)]`), a `with` clause makes the macro emit a copy of
  the function for unverified callers (`rewrite_unverified_func`,
  `source/builtin_macros/src/attr_rewrite.rs:1222`).
- That copy is `external_body` with `requires false`.
- `--no-cheating` rejects every `external_body` outside vstd:
  `external_body/assume_specification not allowed with --no-cheating`,
  `source/vir/src/well_formed.rs:1597`.

Measured on both builds:
- These forms verify without `--no-cheating` and are rejected with it:
  - `with -> trace: Ghost<..>` (ghost output);
  - `with Ghost(inv): Ghost<..>` (ghost input);
  - `with Tracked(out): Tracked<&mut Ghost<..>>`.
- The 06c99ac-era probe verified 38 functions without the flag.

Consequence for a crate verified with `--no-cheating`: attribute-mode code cannot use
ghost inputs or outputs at all. `portable-fip` works around it with existential
postconditions plus spec functions defined by `choose` (commits `06c99ac`, `6fe289b`).

Question for the team: could a macro-generated copy be exempt from `--no-cheating`
(its `requires false` makes it uncallable from verified code), or not be generated
under an option?

### 1.3 No machine-readable list of verified functions

`portable-fip` needs to know which functions Verus verified (commit `1c89ac1`, a
"verified bodies" sidecar consumed by a separate MIR checker). Measured:
- **Text output:** gives counts only.
- **`--output-json`** (`source/rust_verify/src/config.rs:324`): its function details
  include imported specs and vstd items, so they cannot tell a verified body from an
  imported spec.
- **VIR log (`--log vir`):** has one record per function, with span, mode,
  `is_external_body`, body span and `requires`. This is what the generator uses.
  - Impl methods appear as `impl&%N` and cannot be mapped back to rustc paths without
    extra work.
  - Functions outside `verus!` without any Verus attribute are absent.

Question for the team: would an output listing verified items, with rustc def-path,
span, and verification status, be acceptable? It could be a JSON field or a separate
flag.

### 1.4 Proc macros cannot tell that they run under Verus

- The driver adds `--cfg verus_keep_ghost` through its driver API
  (`source/rust_verify/src/driver.rs:177`, `:290-291`;
  `source/rust_verify/src/cargo_verus.rs:221`). A proc macro never sees the crate's
  `--cfg` set, however it is passed, so it cannot tell that it runs under Verus. A
  macro that therefore emits `#[cfg(verus_keep_ghost)]` items in every build makes
  downstream crates without that `check-cfg` warn, and `#[allow(unexpected_cfgs)]` on
  the emitted items does not silence the warning (measured).
- Workaround in `portable-fip` (commit `f573d62`): detect `argv[0] == rust_verify`
  in the proc macro.

Question for the team: could the driver expose a stable signal, such as an environment
variable, to proc macros?

### 1.5 Smaller observations

- Applications of a `spec_fn` cannot be triggers: "Could not automatically infer
  triggers" (`6fe289b`).
- Z3 session sensitivity: `compact_map` verified alone and on seeds 1-7, but failed
  after an earlier query in the same module failed. `verifier::spinoff_prover` was
  used as a workaround (`6fe289b`), and removed in `612a2b5`: without it the
  unmodified crate verified on all 20 runs (seeds 1-10, both builds), but in mutant
  runs of the module `compact_map` and `compact_map_st` each failed their final
  postcondition assertion, even right after asserting the identical loop invariant.
  Assembling the postcondition in two small lemmas whose `requires` are the loop
  invariants at exit fixed it.
- The default of 2 extra errors per function hid a later failure in a mutant run.
  `--multiple-errors 8` was needed (`6fe289b`).
- Attribute mode on closures:
  - `cfg_attr(verus_keep_ghost, verus_spec(..))` on a closure, including a capturing
    one, verifies;
  - coercing a closure to a function pointer is rejected;
  - a projected output type (`G: FipFn<(F::Output,)>`) hits E0275, while explicit type
    parameters work;
  - `saturating_add` in a trait const is rejected, while `+` works
  (`docs/notes/fip-fn-ergonomics-brainstorm.md`, commits `80eda41`, `da394d5`).

## 2. What `portable-fip` could offer (after completion and extraction)

| part | what it is | verified (upstream, `--no-cheating`) | fit (our guess, to ask) |
|---|---|---|---|
| state-passing pattern | guide text plus the probes of 1.1 | yes (5 / control fails) | guide chapter |
| in-place slice combinators (`compact`, `dedup_by`, `compact_map`, `map_in_place`, `update`, `replace`, `swap`, `_st` variants) | specs: permutation, filter, order, state trace, state invariants | `fip-core` 58 verified; 35 functional mutants and 1 recursive mutant rejected; 14 caller controls | vstd extension or example |
| allocation-bound certificates (`fip-strict`: `FipFn`, `Certified`, `Cert`, `Stateless`, `Compose`, `Then`) | type-level allocation bounds for callables | `fip-strict` 19 verified; 1 mutant rejected | open; depends on interest in FIP |
| `#[fip]` family macros | token-level checks, strict mode with certificates | n/a (proc macro) | open; perhaps under `contrib/` like `auto_spec`, `exec_spec` |
| tooling from 1.3 / 1.4 | verified-items output, driver signal | n/a | general Verus features |

Kept outside any contribution (independent repository): `fip-prelint` (a MIR checker,
not a proof), `fip-testkit` (counting allocator, call-graph scans) and `fip-arch`
(prefetch asm, cache-line constants).

## 3. Possible order (for the Discussion, to be confirmed with the team)

1. Guide section on state passing (1.1). Smallest, no code in Verus.
2. Issue or Discussion on 1.2 (`with` vs `--no-cheating`).
3. Tooling: 1.3 and 1.4, as small general PRs from a branch based on upstream `main`,
   not on any fork branch.
4. Only if the team is interested: the combinators, then certificates and macros, in
   small reviewable PRs.

## 4. How to reproduce

- Probes of 1.1: `verus <file>.rs` in `docs/notes/verus-fnmut/`.
- Proofs of `portable-fip`: `just verify` (upstream). For the fork:
  `VERUS=<fork verus> VERUS_Z3_PATH=/usr/bin/z3 just verify`.
- Commits named above: `06c99ac` and `6fe289b` are on `main` (pushed up to `d06a115`);
  the others are on the `prelint/*` branches, not yet merged or pushed as of 2026-11-04.
