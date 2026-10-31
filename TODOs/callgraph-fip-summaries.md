<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# TODO: interprocedural `#[fip]` / `#[fip(N)]` checking over the call graph

**Status:** PROPOSED, not started. **Recorded:** 2026-10-31.
**Depends on:** `TODOs/callgraph-limitations.md` items 6, 7, 10 (lexer bugs and
regression tests) first; the check is only as exhaustive as the extracted graph.

## Proposal (user, 2026-10-31)

Encode caller–callee relations as a finite-state machine and check exhaustively
whether a `#[fip]` or `#[fip(N)]` violation is reachable through indirect calls.

## Assessment

- **Recursion alone:** a cycle reachable from a `#[fip]` root in a finite graph is
  what the current DFS already finds exhaustively. Re-expressing it as an FSM adds
  nothing for this property.
- **Where it adds value:** allocation reached through callees. Today `#[fip]` only
  sees allocation sites in its own body, so calling a function that does `Box::new`
  passes.
- **Counting is over the call tree, not one path.** Allocations before and after a
  call all happen in one execution, so a path-wise FSM does not count them. The
  exact model with matched call/return is a pushdown system / recursive state
  machine.
- **Calls inside loops** multiply by an unknown count. A callee that may allocate,
  called in a loop, gives ∞, which violates `fip(N)`.
- **Explicit-state FSM** (function × count 0..N × stack) explodes. Summaries
  computed to a fixpoint give the same verdicts in polynomial time.

## Design

1. Condense the call graph into strongly connected components. A non-trivial SCC
   (or a self-loop) reachable from a `#[fip]` / `#[fip(N)]` root is a recursion
   violation, as now.
2. Visit SCCs in reverse topological order and compute, per function `f`, a summary:
   - `alloc(f)` ∈ {0, 1, …, N_max, ∞}:
     `alloc(f) = local_sites(f) + Σ_{call sites c} w(c)`, where
     `w(c) = alloc(callee)` outside loops, and `w(c) = ∞` inside a loop if
     `alloc(callee) > 0`.
   - `may_free(f)`: syntactic only (explicit `drop`, `mem::drop`); implicit drops
     stay invisible.
   - `in_loop` flag per call site, taken from the same loop detection `fip-macros`
     uses.
3. Verdicts: `#[fip]` requires `alloc = 0` and no recursion; `#[fip(N)]` requires
   `alloc ≤ N` and no recursion; `#[fbip]` requires `alloc = 0`.
4. On a violation, report a witness: the call chain from the root to the
   allocation site, with loop markers
   (`a → b (in loop) → c: Box::new at file:line`).

## Prerequisites and constraints

- **One rule set.** Allocation-site rules currently live in `fip-macros`. The checker
  must use the same list. Move it to a small dependency-free crate
  (`fip-lint-rules`) used by both, so the rule set cannot drift between them.
- **Graph soundness first.** Fix `callgraph-limitations.md` 6 and 7 (lexer bugs),
  then 1–3 (missed sources of edges and roots). Name merging (8, 9) only adds false
  positives.
- **Still a check, not a proof.** Implicit drops, macro-generated calls and
  externally supplied function pointers remain invisible. A proof of allocation
  bounds is available only for Verus-verified code (an allocation ledger ensured by
  exec functions). Unverified code gets no guarantee from this check.

## Acceptance

- Unit tests with expected results:
  - `#[fip]` → helper with `Box::new`: violation, witness `a → helper`;
  - `#[fip(1)]` → helper with one `Box::new`: pass;
  - `#[fip(1)]` calling that helper twice: violation (2 > 1);
  - `#[fip(N)]` calling an allocating helper inside a loop: violation (∞);
  - helper allocation only under `#[fbip]` callers: unaffected;
  - every case from `callgraph-limitations.md` keeps its current or fixed result.
- `fip-macros` and the checker agree on every `compile_fail` / accept example
  (shared rule crate).
- Runs on `crates/fip-macros/tests` with no reported violation.

## Order

1. `callgraph-limitations.md` 6, 7, 10.
2. `fip-lint-rules` shared crate.
3. Summary fixpoint (`fip_violations`) with witnesses.
4. `callgraph-limitations.md` 1–3.
