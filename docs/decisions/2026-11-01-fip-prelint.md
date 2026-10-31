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
