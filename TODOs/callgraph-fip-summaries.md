<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# TODO: interprocedural `#[fip]` / `#[fip(N)]` checking over the call graph

**Status:** IMPLEMENTED 2026-10-31 as `fip_testkit::summaries` (`fip_violations`,
`fip_violations_dir`, `fip_violations_in`, `fip_violations_in_crates`); see
"Implementation" at the end for what was built, deviations and what is not covered.
**Recorded:** 2026-10-31.
**Depends on:** `TODOs/callgraph-limitations.md` (items 1–3, 6–10 fixed, 4–5 partly);
the check is only as exhaustive as the extracted graph.

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
   - `alloc(f)` ∈ {0, 1, …, N_max, ∞, ⊤} (⊤ = unknown; see below):
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

### Unresolved callees: ⊤, never 0

Today the graph silently drops calls to names it does not define (`dfs` skips
them). Summarising those as 0 would let every higher-order `#[fip]` function pass.
`fip-core`'s own `compact` (`keep(&xs[r])`) and `compact_map` (`f(item)`) call
their closure parameters exactly like that, and the result would no longer be
equivalent to exhaustive FSM exploration. Rules:

- **`⊤` absorbs:** any sum involving `⊤` is `⊤`. A `#[fip]`/`#[fip(N)]`/`#[fbip]`
  root whose summary is `⊤` is **reported** ("cannot check: unresolved call to
  `name` at file:line"), never passed.
- **Unresolved callees are `⊤`:** names not defined in the scanned sources, trait
  methods without a unique local impl, calls through expressions (`(h.f)()`),
  calls into other crates.
- **Known external functions:** an explicit table in `fip-lint-rules` gives
  summaries for external functions (e.g. `core::mem::swap` = 0, `<[T]>::len` = 0,
  `Box::new` = 1), each with a reason. Anything not in the table stays `⊤`.
- **Parameters (FP²'s second-order functions):** a call to a function parameter
  `g` (closure or `fn` pointer) contributes a **symbolic term** `alloc(g)`. A
  summary is then `c + Σ kᵢ·alloc(gᵢ)`, with `kᵢ = ∞` for calls inside loops.
  At each call site the caller instantiates `gᵢ` with the argument's summary: a
  named function's summary, a closure's body summary, or `⊤` if unknown. The
  obligation moves to the caller, as in FP², where functions passed from Σ are
  checked where they are defined. A root that is itself higher-order (parameters
  not instantiated) is reported as "fip relative to its parameters" with the
  symbolic summary, never as an unconditional pass.

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
  - `#[fip]` calling an undefined function not in the table: reported unknown
    (`⊤`), not passed;
  - higher-order `#[fip]` calling its closure parameter in a loop: summary
    `∞·alloc(g)`; with an allocation-free closure it passes, with
    `|x| Box::new(x)` it is a violation;
  - every case from `callgraph-limitations.md` keeps its current or fixed result.
- `fip-macros` and the checker agree on every `compile_fail` / accept example
  (shared rule crate).
- Runs on `crates/fip-macros/tests` with no reported violation.

## Order

1. `callgraph-limitations.md` 6, 7 (done 2026-11-01), 10 (done 2026-10-31).
2. `fip-lint-rules` shared crate (done).
3. Summary fixpoint (`fip_violations`) with witnesses (done 2026-10-31).
4. `callgraph-limitations.md` 1–3 (done 2026-10-31).

## Implementation (2026-10-31)

Code: `crates/fip-testkit/src/summaries.rs` (lattice, fixpoint, verdicts, witnesses),
on the front end `crates/fip-testkit/src/srcmodel/` shared with `callgraph`. Unit
tests: `crates/fip-testkit/src/summaries/tests.rs` (27 tests). Agreement with
`fip-macros`: `crates/fip-macros/tests/checker_agreement.rs`.

### What was built

- **Lattice** `Bound = Finite(n) | Infinite | Unknown` (`0 … N, ∞, ⊤`); `⊤` absorbs in
  sums and products, `0·x = 0` (so `∞·0 = 0`), `∞·⊤ = ⊤`.
- **Summaries** `c + Σ kᵢ·alloc(gᵢ)` per function and per closure literal, computed
  per strongly connected component (Tarjan) in reverse topological order; recursive
  components iterate, and from the third round every component that still grows is
  widened to `∞` (a safety cap sets a component still changing after 64 rounds
  to `⊤`).
- **Events and costs** as listed in the module documentation: allocation sites from
  `HEAP_TYPES`×`HEAP_CONSTRUCTORS`, `ALLOC_MACROS`, `ALLOC_METHODS` (1 each; a method
  site is the maximum of 1 and the scanned methods of that name), `CORE_TABLE` via
  `in_core_table` (0), `GHOST_MACROS` skipped, `ALLOC_FREE_METHODS` (0 when no scanned
  method of that name exists), everything unknown `⊤`. In loop bodies and `while`
  conditions a cost is multiplied by `∞`.
- **Parameters:** a parameter is callable if its type is `impl`/`dyn` of a trait in
  `FN_TRAITS` (`Fn`, `FnMut`, `FnOnce`, `FipFn`), a `fn(..)` pointer, or a generic
  bounded by one of them (in `<..>` or `where`). Calls `g(..)`, `(g)(..)`, `g.call(..)`,
  `g.call_mut/once(..)`, `FipFn::call(&g, ..)` are the term `alloc(g)`. At a call site
  the term is instantiated with the argument: a closure literal or `fip_fn!(..)` /
  `fip_macros::fip_fn!(..)` (directly or through a `let`), a named function without
  parameter terms, or the caller's own callable parameter (the term moves to the
  caller); anything else is `⊤`. `param(g = K)` instantiates `g` with `K` for the
  root's verdict.
- **Verdicts:** `#[fip]` bound 0 and no cycle, `#[fip(N)]` bound ≤ N and no cycle,
  `#[fbip]` bound 0. A root with parameter terms left is reported in
  `Report::conditional` with its symbolic summary (e.g. `∞·alloc(g)`), never passed.
  `Report::roots` lists every marked function with its bound and `may_free`.
- **Witnesses:** one per violation, e.g. ``a -> b (in loop) -> c: allocation site
  `Box::new` at x.rs:5``; through closure arguments
  ``bad -> each -> {closure@x.rs:13} (argument for `g`) (in loop): …``; for `⊤` every
  distinct unresolved leaf is a violation of its own (``a -> b: unresolved call `m1`
  at x.rs:3``); for recursion the chain from the root into the cycle
  (`a -> b -> c -> b`).
- **Crates:** several crates at once keyed by crate name; `crate_name::f` follows the
  module tree and `pub use` re-exports of that crate, else matches by name within
  that crate.

### Deviations from the design, and additions

- **Name-only matches are `⊤`.** When a path cannot be resolved (external crate,
  `use ext::f`), the call graph still links every same-named function (conservative
  for cycles), but the summary of such a call is `⊤`
  (`name_only_matches_are_unknown_for_bounds`). A name match inside another *scanned*
  crate (`crate_name::f`) counts as that function, as specified.
- **Method calls** use the maximum over all scanned methods of that name (as the task
  specified), not "`⊤` unless there is a unique local impl"; `T::f()` for a generic
  `T` uses the unique scanned `impl`/`trait` member if there is exactly one, `⊤` if
  there are several. Both miss implementations outside the scanned sources.
- **Escaping closures** cost nothing where they escape: a closure stored or passed to
  a non-callable parameter can only be called later through an expression, a local
  or a parameter, and those calls are `⊤` or instantiated where they happen.
- **`while` conditions** count as in-loop (`fip-macros` counts only loop bodies);
  **`for` loops** over anything but a range literal add the implicit `.into_iter()` and
  in-loop `.next()` calls, resolved like method calls (`for x in xs` is `⊤`).
- **`?`** is `⊤` (it calls `From::from` on the error path); external macros outside
  `ALLOC_FREE_MACROS` / `PANIC_MACROS` are `⊤`; capitalised callees that are not defined
  functions are constructors (0) — an assumption from Rust naming, not checked.
- **`may_free`** is computed (explicit `drop` / `mem::drop` reachable, through
  `DROP_FUNCTIONS`) and reported per root, but is not part of any verdict, as in the
  design's verdict list.
- **Addition:** every call of a function with `param(g = K)` is checked: an argument
  whose bound is not ≤ K (including `⊤`) is a violation
  `ArgumentExceedsDeclared` (`arguments_are_checked_against_declared_bounds`).
- **New `fip-lint-rules` tables:** `ALLOC_FREE_MACROS`, `PANIC_MACROS` (same list as the
  strict mode's macro allowlist, which still has its own copy in
  `fip-macros/src/strict.rs`), `FN_TRAITS`, `DROP_FUNCTIONS` with `is_drop_function`.

### Acceptance, measured 2026-10-31

| acceptance item | result | test |
|---|---|---|
| `#[fip]` → helper with `Box::new` | violation, witness ``a -> helper: allocation site `Box::new` at x.rs:2`` | `allocation_in_a_callee_violates_fip` |
| `#[fip(1)]` → helper with one `Box::new` | pass, bound 1 | `fip_one_with_one_allocating_call_passes` |
| `#[fip(1)]` calling it twice | violation, bound 2 > 1 | `fip_one_with_two_allocating_calls_is_two` |
| `#[fip(N)]` calling it in a loop | violation, bound ∞ | `allocating_call_in_a_loop_is_unbounded`, `witness_marks_the_loop_on_the_chain` |
| helper allocation under `#[fbip]` callers only | `#[fip]` root unaffected (bound 0); the `#[fbip]` caller is reported (bound ∞ after widening its recursion) | `allocation_under_fbip_callers_only_does_not_affect_fip_roots` |
| `#[fip]` calling an undefined function | `⊤`, reported with `file:line`, not passed | `undefined_function_is_unknown_not_zero`, `every_unresolved_leaf_is_listed` |
| higher-order `#[fip]` calling its parameter in a loop | conditional `∞·alloc(g)`; with `\|x\| x + 1` pass, with a `Box::new` closure violation ∞ | `higher_order_root_is_conditional`, `closure_arguments_instantiate_the_parameter` |
| `callgraph-limitations.md` cases | current or fixed result | `callgraph::tests` (34 tests) |
| `fip-macros` and the checker agree | the 7 non-strict behaviour `compile_fail` examples of `fip-macros/src/lib.rs` (allocation sites, `vec!`, `.to_vec()`, direct recursion, `fip(1)` loop, two sites over `fip(1)`, `fbip` with `format!`) are violations, each asserted verbatim in `src/lib.rs`; `tests/accept.rs` (8 roots) has no violation | `checker_agreement.rs`: `snippets_are_the_ones_in_the_crate_docs`, `rejected_examples_are_violations`, `accepted_examples_are_not_violations` |
| runs on `crates/fip-macros/tests` | together with `fip_core`, `fip_alloc`, `fip_strict`: 39 roots, 0 violations, 0 conditional (every higher-order root there declares `param(..)`) | `tests_and_called_crates_have_no_violation` |

The strict-mode `compile_fail` examples (certificates, `param`, `?`, macros) are not
part of the agreement test: they are about the strict mode's certificate rules, not
about behaviour the checker models.

Scanning all eleven source and test directories of the workspace at once (0.31 s):
41 roots, 718 violations in 16 roots, all from by-name method resolution and from
item 4 edges into the checker's own sources (see `callgraph-limitations.md`). Scan the
crates a root calls.

### Not covered (still a check, not a proof)

- implicit calls: drop glue (and so implicit frees), overloaded operators, `Deref`,
  `Index` on user types (the conversion behind `?` is reported as `⊤`);
- panic paths (`PANIC_MACROS`, indexing, overflow) and their allocations;
- methods and trait implementations outside the scanned sources when a scanned
  method of the same name exists; receiver types in general;
- functions generated by macros, macros defined outside the scanned sources (`⊤`);
- function pointers and closures created outside the scanned sources;
- a numeric stack bound.

