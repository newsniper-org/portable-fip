<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# TODO: open items of `#[fip(strict = true)]` and `FipFn`

**Status:** OPEN. **Recorded:** 2026-11-01.
Design and limits: `docs/decisions/2026-11-01-strict-core-table.md`.

| # | item | kind | note |
|---|---|---|---|
| 1 | Verus specifications for `FipFn` | missing | `FipFn::call` has no spec. Verified higher-order code (`fip-core`'s `compact`, `compact_map`, …) uses Verus' built-in closure specs on `Fn`. A strict, verified variant needs `FipFn` with spec functions (pre/post) that `call` ensures. Probe before designing. |
| 2 | strict variants of `fip-core`'s higher-order functions | missing | `compact`, `dedup_by`, `compact_map`, `map_in_place`, `update` take `Fn` closures and have no certificate. Depends on 1. |
| 3 | certificates for methods of generic types | limitation | `Type::<T>::__fip_strict_m` cannot be named without inferable type arguments; strict callers cannot call such methods. |
| 4 | trait-impl methods | limitation | a trait impl cannot gain the associated certificate constant. |
| 5 | implicit calls | not covered | `Drop` glue (may free), overloaded operators, `Deref`, `Index` on user types. Only Verus-verified code is free of this gap. |
| 6 | panic paths | not covered | `assert!`/`panic!` family is allowed; the panic machinery may allocate. |
| 7 | generic checks under `cargo check` | limitation | `FipFn` argument bounds are checked after monomorphisation, i.e. at build. |
| 8 | `core` table is audited, not proved | limitation | Re-audit on every toolchain bump; only `mem::swap` has a `vstd` spec. |
| 9 | certificate re-export without `unsafe` | detected, not prevented | `use a::__fip_strict_g as __fip_strict_f;` compiles; `fip_testkit::certs::hand_written` reports it. |
| 10 | `use` aliases of table functions | rejected | conservative by design; listed so it is not mistaken for a bug. |
