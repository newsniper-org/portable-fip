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
   directory, with `RUSTC_WRAPPER` set to the driver, so every crate goes through it
   (amended 2026-11-01, see below). Per crate the driver chooses a role:
   - **primary** (`CARGO_PRIMARY_PACKAGE`, i.e. the workspace members): flags,
     attribute validation, analysis;
   - **exported dependency** (any other crate whose root source contains
     `#![cfg_attr(fip_prelint, fip::export)]` or `#![fip::export]`): flags only, so
     its MIR and marks are encoded for downstream crates; no verdicts;
   - **pass-through** (everything else, and version probes): the real rustc,
     unchanged.

   The flags it adds
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
   - **A crate declaring `fip::export` must carry MIR.** The attribute stays readable
     when the bodies are missing (measured: the control crate reports `fip::export`
     with `has_body = false` everywhere). So a dependency with `fip::export` that has a
     function with a body in source but no MIR in its metadata (built without
     `-Zalways-encode-mir`, i.e. not by the driver) is a **hard error** naming the
     crate and one such function, whether or not a root calls it. A call into it is
     also reported as unresolved. It is never 0 and never silently ⊤. Fixture:
     `tests/fixtures/export_unencoded` (a non-member dependency built by plain rustc
     with the tool flags from RUSTFLAGS).
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

- Dependencies whose source does not declare `fip::export` (e.g. crates.io crates)
  are passed through to the real rustc, so they are ⊤.

## Amendment 2026-11-01: `RUSTC_WRAPPER` instead of `RUSTC_WORKSPACE_WRAPPER`

With `RUSTC_WORKSPACE_WRAPPER` only workspace members went through the driver. A
project that consumes portable-fip as a git or path dependency (Y4, rIC3) therefore
got `fip-core`/`fip-strict` compiled without `--cfg fip_prelint` and without
`-Zalways-encode-mir`. Their `fip::export` was inactive and every call into them was
⊤. Measured with a consumer workspace (`/tmp/consumer`) depending on `fip-core`,
`fip-macros` and `fip-strict` by path:

| wrapper | 3 `#[fip]` roots calling `fip_core::swap`, `fip_core::replace`, `fip_core::strict::compact` with `fip_fn!` |
|---|---|
| `RUSTC_WORKSPACE_WRAPPER` (before) | 1 passed, 4 errors, all ⊤ ("crate `fip_core` does not declare `fip::export`") |
| `RUSTC_WRAPPER` with roles (after) | 3 passed, 0 errors |

Fixture `nonmember_export` keeps this tested.

- Function pointers, closures and trait objects whose target is not determined in
  the analysed MIR are ⊤.
- It is still a check, not a proof. Proofs remain with Verus.

## Amendment 2026-11-01: declared parameter bounds at call sites

Item 6 gains a rule, the port of `fip_testkit::summaries`' `ArgumentExceedsDeclared`
(before, `param(g = K)` was used only for the declaring function's own verdict, and a
caller passing an argument above `K` was reported only if it was a root whose own
budget the argument broke; reproducer and measurements: `TODOs/fip-prelint.md`,
"Resolved 2026-11-01: declared parameter bounds at call sites").

- **Rule.** At a call whose resolved callee carries `fip::mark(.., param(g = K))`,
  the argument for `g` is the actual type `T` of `g`'s generic type parameter `F`.
  Its bound is the bound of one call: the callable methods of `F`'s bounds
  (`FipFn::call`, `Fn::call`, `FnMut::call_mut`, `FnOnce::call_once`, from the
  callee's `param_env`) resolved for `T` and analysed like any callee, maximum over
  them. For `fip_fn!` values (`Certified<N, C>`) this is the computed bound of the
  closure, not the claimed `N`. A `T` that is a generic parameter of the analysed
  function is the term `alloc(h)`, instantiated by that function's own
  `param(h = K')`. Error at the call site when the bound is `⊤`, or has no terms left
  and exceeds `K`; terms left are not reported (checked where the caller is
  instantiated). A `g` whose type is not a generic parameter is `⊤`.
- **Scope.** Call sites in every body that a root's analysis explores in the local
  crate or a crate declaring `fip::export` (with the root's instantiation; the error
  counts against that root), and in every other local function, method and closure
  (identity arguments; only the arguments' entry points are explored). Each violation
  is reported once.
- **Rendering.** Calls made in sources outside the analysed workspace (absolute
  paths, e.g. a path dependency on `fip-strict`) are shown in witness chains without
  their machine-dependent location.

Fixture `param_bounds`; on this workspace 16 call sites are checked, none violates.

## Amendment 2026-11-01: value analysis for `Assert` terminators

Item 6 ("`Assert` terminators ... count as panic paths") gains an exception: an
`Assert` that an intraprocedural value analysis of its body proves unable to fire on
every path reaching it is not a panic path (`tools/fip-prelint/src/value.rs`).
Domain: difference bounds between integer locals, slice lengths, checked-operation
results and `Range<integer>`/`Option<integer>` parts, refined by `SwitchInt` on
comparisons and by successful checks, widened at loop heads; `Range::next` and
`into_iter` are modelled from their `core` contract. Locals whose address is taken
are never tracked (shared borrows of places without interior mutability, and a
`Range` borrowed only by `next`, excepted); calls forget only their destination;
anything unknown keeps the assert. Measured on this workspace: 64 → 40 notes (48 →
24 overflow/bounds notes; the rest are unguarded arithmetic or behind `swap_lt`'s
caller precondition). Fixture `guards`; details `TODOs/fip-prelint.md`, "Resolved
2026-11-01: path-insensitive panics".

## Amendment 2026-11-02: allocation and free sources (limits plan L7)

What counts as an allocation changes (plan `docs/decisions/2026-11-02-fip-prelint-limits-plan.md`,
L7; user principle: allocation inside an allocator is outside FIP). Before, only the
`fip_lint_rules::mir` entry points (`__rust_alloc*`, `alloc::alloc::*`) allocated and
every other function with MIR was descended into, so a pure-Rust arena or slab in an
exported crate, and a direct call of a pure-Rust `GlobalAlloc::alloc`, passed `#[fip]`
(5 false passes measured, M2).

- **Sources.** An allocation or free source is a function declared
  `#[cfg_attr(fip_prelint, fip::alloc_source)]` (`fip::alloc_source(n = N)`, `N ≥ 1`)
  or `fip::free_source` (both: a reallocation), on a function, a method, a trait
  method declaration (then every implementation, and a call on a generic parameter
  or through `dyn`, is the source) or a foreign function; every method of a
  `GlobalAlloc` or `Allocator` implementation (by trait `DefId`, table
  `ALLOCATOR_TRAIT_METHODS`); and a foreign C allocation function (`malloc`, `calloc`,
  `aligned_alloc`, `posix_memalign`, `memalign`, `free`, `realloc`, `reallocarray`;
  foreign items only; table `FOREIGN_ALLOC_SYMBOLS`).
- **Opaque boundary.** A source is checked before any table and before MIR: a leaf
  with exactly its declared events. Its body (bookkeeping, a backing allocator, loops,
  recursion, panics, `⊤`) is never analysed. Costs at call sites follow the existing
  path, loop and recursion rules (a source in a loop is `∞`).
- **Checks.** `n = 0`, unknown keys and a misplaced source mark are errors; a FIP mark
  on a source (including `GlobalAlloc`/`Allocator` methods) is an error, the root is
  not analysed. Source marks are trusted declarations: the per-crate summary note
  ends with "N declared sources" when the crate declares any, and
  `FIP_PRELINT_DUMP=1` lists every source a root uses with its location.
- **Residue.** An unmarked pure-Rust pool is ordinary code (no MIR property separates
  "hand out a slice of a buffer" from buffer use). The `fip::export` contract now
  reads: a crate that declares `fip::export` and hands out memory from its own pools
  must mark them.

Measured: fixture `alloc_sources` (the M2 probe, marked) turns all 5 M2 false passes
into errors; the self-check is unchanged (`selfcheck.expected` byte-identical, same
note counts). Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-02: allocation and
free sources".

## Amendment 2026-11-02: sites on infeasible paths (limits plan L11)

The value analysis (amendment "value analysis for `Assert` terminators") now returns,
per block, whether any feasible path reaches its terminator, and it also runs on
bodies without an `Assert` that branch (`SwitchInt`) on a comparison; the locals of
those comparisons are tracked too (if that exceeds the size limits, the analysis is
retried with the assert locals only, as before). Every site in a block that no
feasible path reaches is dropped: calls (with their allocations, frees, panics and
`⊤`), drops, asserts, inline assembly, and the block's outgoing edges. Before, only
`Assert` terminators were dropped. Soundness: the same proof as for asserts (no
execution reaches the block). Fixture `guards`: a `panic!` and a `Box::new` under
`i < n && i >= n` pass, feasible controls are reported; the self-check is unchanged.
Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-02: sites on infeasible paths".

## Amendment 2026-11-02: drops through their glue (limits plan L12 + L5)

Item 6 ("`Drop` terminators ... count as possible frees") changes. Before, every drop
of a type with drop glue pushed a free at the drop site and also descended into the
glue, and a drop of a type mentioning a generic parameter was a term
(`drop(Option<T>)`, `drop(Vec<T>)`), with no analysis of its glue.

- A `Drop` terminator is a call of the drop glue (`drop_glue::<T>` resolved in the
  root's typing environment), analysed like any callee. A drop frees exactly when
  its glue reaches a deallocation entry point, a free source (L7, including
  `Allocator::deallocate`) or `⊤`. `RefMut`, `MutexGuard`-like guards and user
  guards without heap are no longer frees; `Box`, `Vec`, `Rc`, `String` still are.
- Glue of a type that mentions a generic parameter is built for the polymorphic
  type and analysed field by field. Only the drop of a bare type parameter
  (`Drop` of a `T`, `drop_glue::<T>` reached from `drop_in_place::<T>`) is the term
  `drop(T)`; `param(g = K)` still instantiates `drop(F)` with 0. So `drop(Vec<T>)`
  is "may free" plus `∞·drop(T)`, `drop(Option<T>)` is `drop(T)` only.
- Witness chains of frees run through the glue (`drop glue of Box<u8>`) to the
  deallocation instead of ending at "drop of `T`".

Measured: fixture `cells` (new: `RefMut` store and a user guard pass, `Rc` may free),
fixture `generics` (`drop(Vec<T>)`, `drop(Box<T>)` errors; `drop(Option<T>)`,
`drop(T)` warnings); self-check: same verdicts and counts, two witness texts changed.
Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-02: drops through their glue".

## Amendment 2026-11-02: drop shims rustc cannot build (hardening of L5)

A polymorphic drop shim is built by rustc in the typing environment of
`drop_in_place`, which lacks the root's bounds and the types of its const parameters.
For a field `[Vec<T>; N]` of a const-generic struct this ends in an internal compiler
error, which aborted the driver. The driver now requests the MIR of a drop shim whose
type mentions a generic parameter under `catch_unwind` (panic hook suspended); a panic
makes that drop `⊤`, reported with the type. rustc still prints the caught internal
error and counts it as an error (the crate fails, also under `--warn-only`). Fixture
`generics` (`drop_rows`, `drop_rows_again`); details: `TODOs/fip-prelint.md`,
"Resolved 2026-11-02: drop shims rustc cannot build are `⊤`".

## Amendment 2026-11-02: values returned by calls (limits plan L2)

The value analysis (amendment "value analysis for `Assert` terminators") is no longer
blind to calls. A callee with MIR (in `core`/`alloc`/`std` or an analysed crate, not
a source) whose result is an integer, a `bool`, a slice pointer or a tuple with slice
pointer fields gets a return summary: the same analysis of its body, projected at its
reachable `return`s onto the result and its unchanged parameters. The domain gains
access paths through shared references to `Freeze` types (`(*p).f`, the rule already
used for shared borrows), raw-pointer and tuple-field slice metadata, unsizing of
`&[T; N]`, and unchecked arithmetic. Intrinsics use the audited table
`fip_lint_rules::mir::INTRINSIC_RESULT_BOUNDS`, each entry with a differential test.
Soundness: a summary is computed by the same analysis (a fact holds at every return);
an unknown callee keeps the old behaviour. Fixture `guards` (5 passes, 7 controls);
self-check unchanged. Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-02: values
returned by calls".

## Amendment 2026-11-02: caller contexts and declared preconditions (limits plan L1)

The analysis is no longer intraprocedural for facts. A callee whose body can use the
caller's state (an `Assert`, a branch on a comparison, a declared precondition) is
analysed in the context of each call site (the caller's state projected onto its
parameters), up to 3 nested contexts; return summaries are computed per context too.
A new contract attribute, `#[cfg_attr(fip_prelint, fip::requires(..))]` (written by
`fip-macros` from `#[fip(.., requires(..))]`, grammar `fip_lint_rules::requires`): a
root is analysed under it; every analysed call site must establish it (else a panic
path at the call, and the callee is analysed without it there); a function with a
precondition used as a function value is a panic path. `fip-macros` cannot read the
Verus `requires` (measured: an attribute macro does not see a following
`cfg_attr(verus_keep_ghost, ..)` when the cfg is off), so the precondition is written
by hand and checked against the Verus one where both are visible (the macro under
Verus, and a source gate for `fip-core`). Self-check: 46 → 23 notes (the 23
`swap_lt` notes). Fixture `preconditions`. Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-02: caller contexts and declared preconditions".

## Amendment 2026-11-02: iterator contracts (limits plan L3)

The value analysis models more `for` loops: `RangeInclusive<int>`, `Rev<Range<int>>`,
`slice::Iter{,Mut}`, `Enumerate` of a slice iterator and `Zip` of two, each by a
contract of `next` (trusted models of `core`, matched by lang item or defining path,
each with a differential test against the real iterator). Constants are evaluated
with the analysed instance's arguments, which removes the `size_of::<T>()` assert
behind `Iterator::zip` for a sized `T` (the cause of M3's `zip` report). The
`Enumerate` contract covers `Enumerate::next`'s inherited overflow check. Measured:
fixture `guards` (4 passes, 3 controls), M3 probe 12 → 7 errors, self-check
unchanged. The differential test showed that `RangeInclusive`'s `start` wraps after
the last item on rustc 1.99.1; the contract does not use it. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-02: iterator contracts".

## Amendment 2026-11-02: function pointers, trait objects and contracts (limits plan L4)

Indirect calls are no longer `⊤` by construction. A function pointer or `&dyn`
receiver whose value comes, on every path of its body, from one reified function or
closure or one unsized concrete type is resolved to it (a must-analysis over the
body's assignments). `param(g = K)` is accepted for function-pointer and
`&dyn Fn*`/`&dyn FipFn` parameters: a call through `g` counts `K` and what the
function's mark allows, and every analysed call site must pass a function known
there that meets them (else `⊤` at the call site). A `fip::mark` on a trait method
declaration is a contract: a `dyn` call costs it, every implementation is checked
against it in its own crate (the driver now also checks the implementations of an
exported dependency it compiles), and one in a crate without `fip::export` is `⊤`.
No closed-world candidate sets. Measured: fixtures `param_bounds` (3 → 7 passed,
30 → 23 errors on the extended fixture), `indirect` and `contract_dep` (new), M3
probe unchanged as written and 8 → 5 errors with the declarations added; self-check
unchanged. Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-02: function pointers,
trait objects and trait method contracts".

## Amendment 2026-11-02: generated std summaries (limits plan L6 + L10e)

Standard-library functions without MIR in the shipped `std` are no longer `⊤` when
the committed sidecar `tools/fip-prelint/std-summaries/<release>-<target>.txt`
covers them. It is generated by the driver itself (`cargo fip-prelint
--std-summaries`, `just prelint-std-summaries`) from a `-Zbuild-std` build with the
release settings of the shipped `std`; open calls through `fmt` parameters are terms
resolved at each call site from bindings of the node's parameters (output type,
formatting functions). The stamp (format, rustc version string, target) must match
exactly, else the file is not used and such functions stay `⊤`. The file is committed
(generation measured 94–131 s cold, reproducible byte for byte), not generated in CI.
Measured: `write!` into a buffer passes, `format!` is a violation without `⊤`
(fixture `std_summaries`, and `std_summaries_stale` for the refused stamp); self-check
unchanged. Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-02: generated std
summaries".

## Amendment 2026-11-02: repin, targets, export detection, `compile_fail` examples (limits plan L10a–d)

The pin to 1.99.1 stays. A repin is scripted (`just prelint-repin <version>`,
`tools/fip-prelint/repin.sh`): toolchain, driver build, the probes of "Measured"
(now runnable, sysroot from `PROBE_SYSROOT`), the allocator entry-point dump, the std
summaries (regenerated; byte-identical for the pinned version), every driver test,
then the pin sites and the trusted tables to re-audit by hand. Measured: identity
repin passes in 80 s; 1.97.1 fails to build the driver (41 `rustc_private` errors).
`just prelint` now checks the workspace for every target installed in the driver's
toolchain (11 here; the 10 `std` targets equal the host self-check,
`x86_64-unknown-none` checks the `no_std` libraries). Item 4's **exported dependency**
role is decided from the crate root's inner attributes as `rustc_parse` parses them
(`#![fip::export]`, or inside `cfg_attr`, nested, with the predicate evaluated
three-valued, unknown counting as declared), no longer from the file's text; the text
test is only the fallback for an unparsable file (fixture `export_detection`: three
`cfg_attr` forms the text test missed are analysed, the attribute's text in comments
and a raw string no longer gives the driver's flags). `fip-macros` has a mark-only
mode (`FIP_MACROS_MARK_ONLY=1`, honoured only inside the driver) in which `#[fip]` and
`#[fbip]` skip their token-level behaviour checks; the 15 rejected behaviour examples
of its documentation run through the driver (`tests/compile_fail.rs`): all rejected,
14 for the documented reason, `HashMap::new` as `⊤`. Details: `TODOs/fip-prelint.md`,
"Resolved 2026-11-02: repin, targets, export detection, `compile_fail` examples".

## Amendment 2026-11-02: stack bounds for one build (limits plan L9)

`cargo fip-prelint --stack` is a separate build mode: `cargo build --workspace --lib`
with the driver adding `-Zemit-stack-sizes -Zshare-generics=no` and keeping the
profile's opt-level, and giving no FIP verdicts. The driver writes, next to each rlib
it compiles, the roots' symbols and every codegened function (mono item) with the
reason it cannot be bounded (call through a function pointer, dynamic call, unresolved
call, inline assembly, unsized local) and the diverging standard-library functions it
calls (panic paths, excluded). `cargo-fip-prelint` reads the rlibs' ELF objects
without dependencies and reports per root the longest path over the build's direct
calls (relocations) of `.stack_sizes` frames plus 8 bytes of return address each, or
`⊤` with the reason. The graph is the machine code's, every function on it mapped to
its MIR instance, not the MIR call graph: measured, opt-level-0 code calls
`precondition_check` functions the MIR analysis does not explore, and `memcpy`.
Fixture `stack` (dev and release builds, expected bounds, cross-checked with
`llvm-readobj` where present). Summing MIR local sizes stays rejected. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-02: stack bounds for one build".

## Amendment 2026-11-02: uniqueness and interior mutability are out of scope (limits plan L8)

`fip-prelint` checks no uniqueness, aliasing or interior-mutability property, and
will not. Reasons: (1) uniqueness of owned values and of `&mut` is what Rust's
ownership and borrow checking already give, statically; the reuse primitive
`fip_alloc::refill` takes its `Box` by value. (2) Where uniqueness is dynamic (`Rc`,
`Arc`, `RefCell`), its FIP-relevant effects are already observed by the analysis as it
is: creating an `Rc` allocates, dropping the last one may free (its glue reaches the
deallocation), a failed dynamic borrow is a panic path (`panic_already_borrowed`,
`panic_already_mutably_borrowed`), and `Rc::get_mut`/`try_borrow_mut` neither allocate
nor panic. (3) Whether an `UnsafeCell` or raw pointer aliases is a question of
undefined behaviour, which belongs to Verus, Miri and the `unsafe` audit
(`fip_strict::certs`); no MIR heuristic decides it. Interior mutability matters to the
driver only for the soundness of its value analysis: places behind an `UnsafeCell` are
never tracked through shared references (`Freeze` access paths only). Fixture `cells`
pins the behaviour: 15 roots, 10 passed, 5 errors (`Rc::new`, a last `Rc` dropped, a
`Box` taken out of a `Cell` and dropped, `borrow`/`borrow_mut` under `strict = true,
panic_macros = false`); `Cell`, aliasing `&Cell`s, an `UnsafeCell` write,
`try_borrow_mut`, `Rc::get_mut`, `Rc::clone` and a `RefMut` store pass. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-02: uniqueness and interior mutability".

## Amendment 2026-11-02: `#[fip]` on trait method declarations (contracts)

The L4 contracts were written by hand (`fip-macros` rejected a bodiless item).
`#[fip]`, `#[fip(N)]` and `#[fbip]` now accept a trait method declaration, bodiless
or with a default body. On a bodiless one the macro checks nothing (it sees only the
declaration) and emits the item with a `# FIP` section and, under the driver, the same
`fip::mark(kind = .., n = .., strict = false, panic_macros = true)` as on a function;
a default body gets the usual token-level checks. Rejected on a declaration, with a
compile error: `param(..)` (the driver rejects it in a contract too), `strict = true`
(a certificate belongs to one body; nothing could make every implementation carry
one; a strict contract stays hand-written) and `requires(..)`. `strict = true` on a
default body does not compile either (with a receiver: the existing "needs
`#[fip_impl]`" error; without one, the certificate's `pub(self)` is rejected in a
trait, E0449). The macro cannot tell a trait method declaration from a foreign
function; on the latter the driver reports the mark as `⊤`.

Driver changes, from the consistency check of item (4) and a hole found while adding
it: an implementation is checked against a contract **without** its own
`fip::requires(..)` (a `dyn` call does not establish it; before, an implementation of
a strict contract whose precondition made `xs[i]` safe passed, and a `dyn` caller
with `strict = true, panic_macros = false` passed while the call could panic,
measured); `fip::requires(..)` in a contract is rejected like `param(..)`; an
implementation's own `fip::mark` weaker than the contract (more allocations, `fbip`
for a `fip` contract, less strict) is an error at the implementation.

Measured: fixtures `indirect` and `contract_dep` with their contracts converted to
`#[fip]` (one hand-written contract kept, `shapes::Grow::grow`): output identical,
line for line, to the hand-written version (and the old driver reads the macro's
marks identically). With the new cases in `indirect/app` (`Tight`, `Loose`, `Pick`
/ `Indexed`, `pick_dyn`, `Bounded`): old driver 21 roots, 13 passed, 12 errors; new
driver 21 roots, 11 passed, 15 errors (the weaker mark, the panic path of `Indexed`
under the contract, `requires` in a contract). Details: `TODOs/fip-prelint.md`,
"Resolved 2026-11-02: `#[fip]` on trait method declarations".

## Amendment 2026-11-02: Contracts for calls on `Self` and type parameters inside generic bodies

A call of a contracted trait method on `Self` or a type parameter inside a generic body
(e.g. a default method body calling `self.area()`, or `fn f<S: Shape>(s: &S) { s.area() }`)
was previously reported as a warning ("only relative to its generic parameters") because
it was treated as a term instead of using the contract. Soundness is identical to `dyn`
calls: every implementation is checked against the contract in its crate.

The driver now uses the contract for unresolved generic calls (`self.node_contract`),
creating a leaf node with the contract's declared events. Instantiated analysis where
the concrete instance is known is kept (no precision lost when the callee can be
resolved). Calls of non-contracted trait methods continue to produce the warning/term,
and implementations violating the contract continue to be reported at the implementation.

Measured:
- `indirect/shapes`: 5 roots (was 4), all 5 passed, 0 errors, 0 warnings, 0 notes.
- `indirect/app`: 27 roots (was 21), 14 passed (was 11), 19 errors (was 15), 1 warning
  (was 0: the uncontracted `generic_plain`). Warnings removed on contracted generic
  calls (`generic_area`, `generic_scaled`, default body `Shape::twice` in `accept.rs`).

## Amendment 2026-11-02: Strict contracts without hand-written marks (`#[fip_trait]`)

Previously `strict = true` on a trait method declaration was rejected by `fip-macros`
and required a hand-written `#[cfg_attr(fip_prelint, fip::mark(.., strict = true, ..))]`,
and strict callers could not call contracted methods through `dyn` or generic receivers
because no certificate was available.

Measurements on compiler and macro constraints:
- An attribute macro on a trait item can expand to multiple trait items, but putting an
  associated const inside a trait makes the trait not dyn-compatible (E0038).
- Functions in traits cannot be const (E0379), and generic const items are experimental (E0658).
- An attribute on a trait item cannot emit items outside the trait at module level.
- Inherent impls on `dyn Trait` (`impl dyn Trait { pub const __fip_strict_<m>: Cert = ...; }`)
  keep the trait 100% dyn-compatible and are accessible across module boundaries wherever
  the trait is in scope.

Design:
- `#[fip(strict = true)]` and `#[fip(N, strict = true)]` are supported on trait method declarations
  under `#[fip_trait]`, emitting the driver mark and certificates `<dyn Trait>::__fip_strict_<m>` and `<vis> const __fip_strict_<Trait>__<m>`.
- `strict = true` on a declaration without `#[fip_trait]` is rejected with a clear compile error.
- Generic traits and generic trait methods under `#[fip_trait]` are rejected clearly at compile time.
- Strict callers support `x.m()` (for `x: &dyn Tr` or `T: Tr`), `Tr::m(x)`, `<dyn Tr>::m(x)` and `<T as Tr>::m(x)`.
- Implementations under `#[fip_impl]` are checked against the contract at compile time via a typed const assertion
  (`Cert::allocs_for(__fip_strict_Self__Tr__m, ..) <= Cert::allocs_for(<dyn Tr>::__fip_strict_m, ..)`, failing with E0080 if weaker, impossible to forge without `unsafe`).
- Hand-written mark case (`Grow::grow` in `indirect/shapes`) kept as equivalence check.
## What would reopen this

- `rustc_public` covering crate-root attributes (drop the `rustc_middle` use).
- A Verus toolchain change (re-pin, re-run the probes).
- A stable way to encode MIR for all functions without `-Z` flags.
