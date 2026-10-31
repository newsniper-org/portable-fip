<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `fip-prelint`: a MIR-level checker as a rustc driver

**Status:** ACCEPTED, 2026-11-01. Background and first probes: `TODOs/fip-prelint.md`. Probe sources: `tools/fip-prelint/probes/`.

## Decision

1. **Form.** A rustc driver, `fip-prelint`, plus a cargo subcommand
   `cargo-fip-prelint`. It lives in `tools/fip-prelint/`, a separate cargo project
   **excluded from the workspace**, so `cargo build/test --workspace` on stable and on
   the MSRV is unaffected. It is a host-only `std` tool. Its only non-workspace
   "dependencies" are the compiler's own `rustc_private` crates. It may depend on
   `fip-lint-rules` by path.
2. **Toolchain.** Pinned to rustc **1.99.1**, the toolchain of the installed Verus,
   with the `rustc-dev` component. The driver is built with `RUSTC_BOOTSTRAP=1`, and
   so are the crates it compiles. A different rustc cannot read the MIR (measured:
   `E0514`), so every crate of one analysis is compiled by the same driver.
3. **API.** `rustc_public` for items, bodies and tool attributes. `rustc_middle`
   (through `run_driver!(.., with_tcx)`) only where `rustc_public` has no
   equivalent; measured: crate-root attributes.
4. **Invocation.** `cargo fip-prelint` runs `cargo check` into its own target
   directory, with `RUSTC_WORKSPACE_WRAPPER` set to the driver. For every workspace
   crate the driver adds
   `-Zalways-encode-mir -Copt-level=0 --cfg fip_prelint`,
   `-Zcrate-attr=feature(register_tool)`,
   `-Zcrate-attr=feature(custom_inner_attributes)` and
   `-Zcrate-attr=register_tool(fip)`. It then analyses the crate after type
   checking and reports verdicts as compiler diagnostics.
5. **Contract attributes**, invisible to plain builds:
   - `#![cfg_attr(fip_prelint, fip::export)]` at the crate root: use this crate's MIR
     for verdicts in downstream crates. MIR of a crate without it is not used, even
     where rustc encoded it anyway (small functions at `-O2`), and its functions
     are ⊤.
   - `#[cfg_attr(fip_prelint, fip::mark(..))]` on functions, emitted by `fip-macros`
     for `#[fip]`, `#[fip(N)]`, `#[fbip]`, `param(..)` and `strict`. These are the
     roots and declared bounds.
   - The driver rejects any other name under `fip::`. rustc accepts unknown names
     under a registered tool silently (measured).
6. **Analysis.** The `fip_testkit::summaries` design (lattice {0..N, ∞, ⊤}, SCCs with
   widening, symbolic parameter terms, witnesses, unresolved = ⊤ and reported) on
   MIR:
   - resolved call targets (`Instance` resolution with the caller's generic
     arguments where known);
   - allocator entry points (`alloc::alloc::{alloc, alloc_zeroed, realloc,
     exchange_malloc}` and the `__rust_alloc*` symbols) count as allocations;
   - `Drop` terminators on types with drop glue and calls to deallocation entry
     points count as possible frees;
   - `Assert` terminators and calls into `core::panicking` count as panic paths;
   - a callee's MIR is used if it is local, in a crate declaring `fip::export`, or
     (for `core`/`alloc`/`std`) available because it is generic or inline. Intrinsics
     and other bodies without MIR come from `fip_lint_rules` tables, else ⊤.
7. **Cross-toolchain consumers** (e.g. Y4 on rustc 1.95): per-function summary
   sidecars stamped with crate hash, driver version and rustc version. Deferred. A
   sidecar is a claim, used only where the MIR cannot be read.

## Measured (2026-11-01, rustc 1.99.1, `/tmp/mirprobe`)

| question | result |
|---|---|
| downstream `rustc_middle::optimized_mir` of a non-generic, non-inline function | readable only with `-Zalways-encode-mir` on the dependency; control fails at -O0/2/3 for a large function; small functions are encoded anyway at -O2/-O3 |
| same through `rustc_public` (`FnDef::has_body`/`body`) | with the flag: bodies present (6 and 2 blocks); without: `has_body = false`, `body = None` |
| works when the dependency is built with `--emit=metadata` (what `cargo check` does) | yes, identical results |
| function-level tool attribute `fip::mark(..)`, local and in a dependency, via `rustc_public` `all_tool_attrs` | read in both |
| crate-root tool attribute `fip::export`, local and in a dependency, via `tcx.get_all_attrs` | read in both |
| different rustc reading the dependency | `E0514` |

## Corrections found while implementing (2026-11-01)

Implementation: `tools/fip-prelint`; results and open items: `TODOs/fip-prelint.md`.

1. **Item 3 (API).** `rustc_public`'s `Instance::resolve` and `Instance::body` work
   only in a fully monomorphized typing environment (the bridge's
   `resolve_instance` uses `TypingEnv::fully_monomorphized()`), so generic roots such
   as `fip_core::strict::compact<T, F>` cannot be analysed through them. The
   analysis therefore uses `rustc_middle` (`Instance::try_resolve` in
   `TypingEnv::post_analysis(root)`, `instance_mir`); `rustc_public` finds the roots
   and reads their `fip::mark` (`local_crate().fn_defs()`, `all_tool_attrs()`). The
   driver has its own `Callbacks` with `rustc_internal::run` instead of
   `run_driver!`, because compilation must continue after the analysis so that
   `cargo check` writes the `.rmeta` the dependants need.
2. **Item 4 (flags).** Also `--check-cfg cfg(fip_prelint)` (fixture workspaces have no
   `check-cfg`) and `-Aunused_features` (`custom_inner_attributes` is unused in
   crates without `#![fip::export]`). `cargo fip-prelint` runs
   `cargo check --workspace --all-targets --keep-going` into `target/fip-prelint`.
3. **Item 5 (`fip::mark`).** `fip-macros` emits the `cfg_attr` only when the expanding
   compiler is the driver (it sets `FIP_PRELINT_DRIVER=1` in its own process before
   expansion). Measured: emitted unconditionally, it makes every downstream crate
   without `check-cfg = ["cfg(fip_prelint)"]` warn `unexpected_cfgs`. Syntax:
   `fip::mark(kind = "fip"|"fbip", n = N, strict = .., panic_macros = .., param(g = K, ..))`.
4. **Item 6 (entry points).** The `std`/`alloc` MIR shipped with 1.99.1 is optimized
   MIR with inlining: `alloc::alloc::alloc` is inlined into
   `alloc::alloc::Global::alloc_impl_runtime`, which calls the symbols
   `__rust_alloc` / `__rust_alloc_zeroed` directly (after the empty marker
   `__rust_no_alloc_shim_is_unstable_v2`). `Box::new` reaches it through
   `alloc::boxed::box_new_uninit`, not `exchange_malloc`; `Vec::with_capacity`,
   `String::from` and `vec![]` through `RawVecInner::try_allocate_in` /
   `box_new_uninit`; `Vec::push` reaches `__rust_realloc`; dropping a `Box` reaches
   `__rust_dealloc`; `format!` reaches `alloc::fmt::format::format_inner`, which has
   no MIR (⊤). The tables (`fip_lint_rules::mir`) list the symbols and keep the
   `alloc::alloc::*` paths for direct calls.
5. **Item 6 (panics).** Diverging `core`/`alloc`/`std` functions (`-> !`, e.g.
   `alloc::alloc::handle_alloc_error`, `alloc::raw_vec::handle_error`) count as panic
   paths and are not looked into. Skipped: `Assert`s whose condition is a constant that
   cannot fail (opt-level 0 keeps the shift check of `x >> 1`), the null/misaligned
   pointer UB checks, and `core`'s `precondition_check` functions (they fire only
   when an `unsafe` contract is already broken).

## Not covered, and why

- Crates outside the workspace (crates.io) are compiled by plain rustc under
  `RUSTC_WORKSPACE_WRAPPER` and cannot declare `fip::export`, so they are ⊤.
- Function pointers, closures and trait objects whose target is not determined in
  the analysed MIR are ⊤.
- It is still a check, not a proof. Proofs remain with Verus.

## What would reopen this

- `rustc_public` covering crate-root attributes (drop the `rustc_middle` use).
- A Verus toolchain change (re-pin, re-run the probes).
- A stable way to encode MIR for all functions without `-Z` flags.
