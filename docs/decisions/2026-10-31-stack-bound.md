<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# Bounded stack: acyclic call graphs

**Status:** ACCEPTED, 2026-10-31.

## Decision

FP²'s `fip` includes constant stack space. Rust has no tail-call guarantee and no
stack-size analysis on stable, so this repository bounds the stack **structurally**:
a function that takes part in no recursion, and whose frames have fixed size (true
of Rust without `alloca`), uses stack bounded by its longest call chain.

| code | mechanism | strength |
|---|---|---|
| verified crates (`fip-core`, `fip-alloc`) | Verus rejects any recursion (direct or mutual) among verified functions that lacks a `decreases` clause. `tests/verified_surface.rs` forbids function-level `decreases` and requires every function to be verified. | proof: the call graph among the crate's functions is acyclic |
| user code marked `#[fip]` | the macro rejects direct self-recursion; `fip_testkit::callgraph::fip_cycles` (one crate) / `fip_cycles_multi` (several crates by name) lexes the sources and reports every cycle reachable from a `#[fip]` function, also one marked through `cfg_attr`. The graph has functions keyed by crate, module path and `impl` owner, path calls resolved through modules, `use` imports and `pub use` re-exports, method calls to every scanned `self` method of that name, defined functions used as values, calls in `macro_rules!` bodies of the scanned sources, `include!` files and `#[path]` modules; in a `#[fip]` function a call through an expression, a local or a callable parameter reaches every function used as a value and every closure passed as an argument | **check, not proof**: may over-report (method calls and unresolvable paths match by name); misses macros and functions outside the scanned crates, pointers and closures created outside them, and indirect calls in unmarked functions. It gives no stack bound for unverified code |

## Measured (2026-10-31)

- Probe: two mutually recursive functions with `verus_spec` and no `decreases` are
  rejected with "recursive function must have a decreases clause".
- `just verify-negative`: a mutant of `fip_core::swap` that calls itself is rejected
  by Verus; a mutant adding a function-level `decreases` is rejected by the surface
  gate.
- `fip-testkit` unit tests: mutual recursion through an unmarked function, path and
  turbofish calls, method calls through `self`, a function passed as a value
  (`iter.map(f)`, `let g: fn() = f`), and qualifiers between the attribute and `fn`
  are detected; strings, comments, Verus ghost code, `core`/`std`/`alloc`
  paths and method calls on non-`self` functions are not reported.
- Added 2026-10-31 (`TODOs/callgraph-limitations.md`, all items with tests):
  `cfg_attr(.., fip)` roots, cycles through local `macro_rules!` bodies, `include!`
  and `#[path]` files (also read from disk), calls through expressions / locals /
  parameters in `#[fip]` functions, cycles across two crates, same-named functions in
  different modules no longer merged, `T::f()` for a generic `T` not linked to free
  functions.
- Workspace: `crates/fip-macros/tests` with `fip_core`, `fip_alloc`, `fip_strict`
  (39 marked functions, including the six `cfg_attr`-marked strict functions of
  `fip-core`): no cycle (`no_indirect_recursion`, `checker_agreement`). All eleven
  source and test directories at once: 40 reported cycles, all false positives of
  by-name method resolution and of parameter calls reaching the checker's own
  closures (measured, see the TODO).

## Allocation through callees (related, not a stack bound)

`fip_testkit::summaries::fip_violations` uses the same graph to bound allocations
per call through callees (`#[fip]` 0, `#[fip(N)]` ≤ N, `#[fbip]` 0), with symbolic
terms for closure parameters and `⊤` for anything it cannot resolve; recursion of a
`#[fip]`/`#[fip(N)]` root is reported there with a chain from the root. It is a
check as well: implicit calls (drop glue, operators, `Deref`, `Index`), panic paths
and implementations outside the scanned sources are not seen
(`TODOs/callgraph-fip-summaries.md`).

## Not covered

- Closures and functions passed in by the caller (`keep`, `same`, `f`): their stack
  use is the caller's. The cycle check follows them only when they are created in
  the scanned sources (closure literals, `fip_fn!`, named functions used as values).
- A byte count. The bound is the absence of recursion, not a number.

## What would reopen this

- A stable way to obtain per-function stack sizes (e.g. `-Z emit-stack-sizes`
  stabilised), which would allow a numeric bound.
- Verus accepting recursion without `decreases` (it would break the first row).
