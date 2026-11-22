<!-- SPDX-License-Identifier: MIT OR Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `fip-prelint`: a MIR-level checker as a rustc driver

**Status:** ACCEPTED, 2026-11-01, amended 2026-11-01 through 2026-11-04 (sections "Amendment .."
below; the 2026-11-04 Verus sidecar amendment is a trust change accepted by the user). Background and first probes: `TODOs/fip-prelint.md`. Probe sources: `tools/fip-prelint/probes/`.

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
7. **Cross-toolchain consumers** (e.g. a downstream project on rustc 1.95): per-function summary
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
   when an `unsafe` contract is already broken; since 2026-11-04 matched exactly, on
   standard-library items only, see the amendment "soundness audit of the driver").

## Not covered, and why

- Dependencies whose source does not declare `fip::export` (e.g. crates.io crates)
  are passed through to the real rustc, so they are ⊤.

## Amendment 2026-11-01: `RUSTC_WRAPPER` instead of `RUSTC_WORKSPACE_WRAPPER`

With `RUSTC_WORKSPACE_WRAPPER` only workspace members went through the driver. A
project that consumes portable-fip as a git or path dependency therefore
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

## Amendment 2026-11-02: FFI functions (certified XOR excluded XOR error)

Every foreign function (`extern` block item) reachable from a FIP-checked function must be in exactly one of:
- (a) **certified**: carries `#[fip_cert(evidence = "..", allocs = N)]` (or `#[fip(..., evidence = "..")]`) under `#[fip_extern]` on the `extern` block. Requires non-empty `evidence = ".."`. Emits `<vis> const __fip_strict_<name>: Cert = unsafe { Cert::assume(..) }` at module level for strict callers and driver mark `fip::cert` for `fip-prelint`. Counted and listed in the crate summary note (`N certified foreign functions`).
- (b) **excluded**: `#[fip_exclude]` (standalone or inside `#[fip_extern]`, optional `reason = ".."`). Calls contribute no events to FIP aggregation. User assumption; counted and listed in crate summary note (`N excluded foreign functions`) and in `FIP_PRELINT_DUMP`. No certificate emitted; strict callers cannot call it (E0425).
- (c) **otherwise**: specific error `foreign function <x> is neither certified nor excluded` (not a generic ⊤).

Both (a) and (b) on one function is an error. Direct `#[fip]` on a foreign function without `evidence` is rejected at compile time under `#[fip_extern]` and by the driver always. Allocator FFI (`alloc_source`/`free_source` and `FOREIGN_ALLOC_SYMBOLS`) is treated as allocator certificates and counted under declared sources (no double counting).

Measured:
- `tools/fip-prelint/tests/fixtures/ffi`: 7 roots, 4 passed, 4 errors, 3 certified foreign functions, 1 excluded foreign functions.
- `tools/fip-prelint/tests/fixtures/alloc_sources`: `mystery` updated from generic ⊤ to specific error `foreign function mystery is neither certified nor excluded`.
- `compile-fail-reasons`: 72/72 passed (+6 FFI compile_fail examples).

## Amendment 2026-11-02: foreign marks match by link symbol and ABI

The previous amendment keyed `fip::cert`/`fip::exclude` by the declaration's
`DefId`: a call through a declaration in `std`, `libc` or another dependency could be
neither certified nor excluded (the user cannot mark another crate's items), and a
declaration of the same symbol in the user's crate did **not** cover it (a call
reaches the dependency's `DefId`). Marks are now keyed by the **link symbol**
(`tcx.symbol_name` of the foreign item: its `#[link_name]`, else its name; foreign
items are not mangled), from the local crate and from crates declaring `fip::export`,
and apply to every foreign declaration of that symbol a root reaches. Rules: (1)
certified on one declaration and excluded on another (or the same) is an error at the
later local declaration and at every call; (2) two certificates of one symbol whose
counted properties differ (`kind`, `n`, `frees`; the evidence is not compared) are an
error likewise; (3) a marked declaration whose ABI (as rustc prints it, e.g. `"C"` vs
`"C-unwind"`) differs from the called declaration's is an error at the call, not a
match: the same symbol under another calling convention is another contract, and an
error keeps it visible. Every match through another declaration is a note line
`foreign function <callee> (symbol .., extern ..) certified (or excluded) by symbol:
<declaration> (<where>)` and a count in the crate summary. `#[fip_extern]` puts
`#[allow(dead_code)]` on marked items (a declaration may exist only to carry the
mark). Strict callers are unchanged: the certificate `__fip_strict_<name>` is found
through the marked declaration's path only. Measured: `tests/fixtures/ffi`, see
`TODOs/fip-prelint.md`, "Resolved 2026-11-02: foreign marks by link symbol".

## Amendment 2026-11-02: the macro reads an item's enclosing block for two rejections

Two statements of the trait-contract amendment change (no driver rule changes): "the
macro cannot tell a trait method declaration from a foreign function" and "`strict =
true` on a default body without receiver: E0449". `fip-macros` now rejects `#[fip]`
on a bodiless function whose tokens show a foreign function (a visibility, `safe`, a
variadic `...`, none valid on a trait method declaration), and reads the enclosing
block from the item's source file (`Span::local_file`/`line`/`column`; used only when
that position holds the item's own `fn <name>` and the header is exactly `trait ..`
or `extern ..`) to reject a plain `fn f();` in an `extern` block and `strict = true`
on a trait default body (with or without receiver) with specific messages. Both are
rejections of code that is rejected anyway (by the driver, or by rustc's E0449), so
a position that cannot be read leaves the earlier behaviour in place. `#[fip_trait]`
gives the default-body message without the file. Details: `TODOs/fip-prelint.md`,
"Resolved 2026-11-02: foreign functions and strict default bodies at expansion".

## Amendment 2026-11-02: constructor spellings normalised for the token checkers

No driver rule changes; the token-level checkers that run before it change.
`#[fip]`, strict mode and `fip_testkit::srcmodel` read every callee path through
`fip_lint_rules::callee` (turbofish, qualified self `<T>`/`<T as Tr>`, leading `::`
reduced to type, trait and function). Allocating spellings are allocation sites in all
three; audited non-allocating constructors are accepted in every spelling (strict mode
before rejected the turbofish and qualified ones); an allocating method called by path
on a heap type, slice, `str` or std trait (`Vec::clone(&v)`, `Clone::clone(&v)`) is an
allocation site like the method-call form; a constructor-like trait function without a
type (`Default::default()`) is rejected in strict mode and left to the driver in
non-strict mode (fixture `ctor_spellings`: the driver rejects the allocating ones).
Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-02: one normaliser for constructor
spellings (token rule)".

## Amendment 2026-11-03: the profile's overflow checks and debug assertions (top plan T14.1)

Item 4's `-Copt-level=0` no longer changes the analysed semantics. The driver reads the
debug-assertion and overflow-check settings the crate's own arguments imply (the last
explicit `-C debug-assertions` / `-C overflow-checks`, else rustc's defaults for the
original opt-level) and appends them explicitly after `-Copt-level=0`. The analysed MIR
has exactly the checks of the profile's build: under `overflow-checks = false` an
arithmetic overflow wraps and is not a panic path; a `debug_assert!` counts only where
debug assertions are on. Dev-profile runs are unchanged (measured: identical
self-check). The self-check gains a `--release` expectation; fixture `profiles`. The
one extra `--release` note before this change (`fip_core::strict::dedup_by`, a bounds
check) came from the host unit of `fip_core` that cargo builds for the proc macro with
the `build-override` profile (no overflow checks): without the `w - 1` overflow assert
the analysis cannot prove `w >= 1`, a Verus invariant. Details: `TODOs/fip-prelint.md`,
"Resolved 2026-11-03: the profile's overflow checks and debug assertions".

## Amendment 2026-11-03: function pointers from constants, immutable statics and local aggregates (top plan T1.1–T1.3)

The must-origin of a function pointer also follows constants and loads from immutable
data. A constant of function pointer type is the function it evaluates to. A load below
a constant reference (a `static` or constant memory) reads the evaluated initializer:
the static must not be `static mut`, thread-local or foreign, its type must be
`Freeze` and its allocation immutable; struct and tuple fields and array or slice
elements are followed, an unknown index takes every element, and the candidates are
alternatives of one call site (their maximum counts, every one is checked like a
direct callee). A field of a local aggregate assigned only as a whole, never borrowed
mutably or written in part, has the origin of the aggregate's operand. Everything else
loaded from memory stays `⊤`. Fixture `indirect_data`. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-03: function pointers from constants,
immutable statics and local aggregates".

## Amendment 2026-11-03: callable bindings across calls (top plan B)

A node's parameters may also be bound to what a callable argument holds at the call
sites that reach it: the function(s) of a function pointer (reified, constant, or the
candidates of immutable data), the concrete type of a `&dyn Fn*`, or a caller's
parameter declared `param(g = K)`. A call through a bound parameter resolves to that
binding before the callee's own declaration; call-site checks inside a bound node use
it too. Bindings are must-facts at the call sites (nodes are keyed by them) and nest up
to 3 callees; roots and local functions checked on their own are analysed unbound, as
before. Fixture `callable_binds`. Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-03: callable bindings across calls".

## Amendment 2026-11-03: the `Fn` shim of a function pointer and `Box<dyn Fn*>` (top plan T3 + T2)

Callable bindings also bind references to function pointers and `Box<dyn Fn*>` /
`&Box<dyn Fn*>` arguments. The `Fn*` shim of a function pointer calls through its
`self`, which is resolved through that binding; the `Box` impl of `Fn*` calls the trait
object its `&Box` parameter owns (the projection `(*self).0` with its deref casts, only
for `Box`), resolved through the binding of that parameter. At call sites, a generic
`G` instantiated with a function pointer is checked through its shims bound to the
argument, and `param(g = K)` on a `&Box<dyn Fn*>` parameter is checked like on a `&dyn
Fn*`. `Rc<dyn Fn*>` and `FnMut`-bound function pointers stay `⊤`. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-03: the `Fn` shim of a function pointer and
`Box<dyn Fn*>`".

## Amendment 2026-11-03: private functions checked at their call sites (top plan T4.3)

The "declared parameter bounds" amendment keeps its rule for exported functions: a
parameter without `param(..)` passed on is reported where it is passed. A local
function that is not exported by name, not a trait method or implementation, has no
external symbol and is never used as a value (only called by name) is instead checked
at each of its call sites in the crate, with what that call passes (callable
bindings); an unknown argument reports the `⊤` there. Details: `TODOs/fip-prelint.md`,
"Resolved 2026-11-03: private functions checked at their call sites".

## Amendment 2026-11-03: floats, 128-bit integers, float math and `std`'s dependencies (top plan T7c/d/e/h)

The std summaries' seed covers float and 128-bit integer formatting and the radix and
exponent formats of every integer type (165 summarised functions). The audited
intrinsic table lists the `f32`/`f64` math intrinsics: they lower to instructions or
to the C math library's function of the same name, whose allocation freedom is a
trusted claim about the C library (C standard 7.12), stated with each entry; and the
integer/bitwise SIMD lane intrinsics. The crates the standard library depends on
(`hashbrown`, ..: loaded only through a standard-library crate) are analysed like
`core`/`alloc`/`std`; foreign functions in them still follow the FFI rule. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-03: floats, 128-bit integers, float math and
`std`'s dependencies".

## Amendment 2026-11-03: derived `Debug`, the debug builders and `PadAdapter` (top plan T7a/b)

Bindings now also describe places below a parameter (a closure's captures, a
`core::fmt` builder's formatter, a `PadAdapter`'s buffer) and `&dyn Debug`/`&dyn
Display` values (the concrete type at the call site). A path is a must-origin only if
it cannot change between entry and read: fields of the parameter's own value, of
`Freeze` memory behind a shared reference, or `core` fields audited never to be
reassigned. Four readings of the 1.99.1 `core` sources are trusted (builder
constructors, builder methods returning `self`, `PadAdapter::wrap`, the audited
fields); a repin reopens them. Std summaries gain the term `§dyn` and the output
`pad`. Derived `Debug` (1–5 fields), slices, `Option`, `Result`, tuples and the
list/set/map builders, with `{:?}` and `{:#?}`, are checked into a buffer. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-03: derived `Debug`, the debug builders and
`PadAdapter`".

## Amendment 2026-11-03: thread locals through their `static` key (top plan T7g)

A shared reference to immutable data that holds function pointers (`&'static
LocalKey`) is bound at the call site to its reference constant, and a pointer loaded
below the parameter is read from the evaluated initializer under the T1.2 rules
(immutable memory only). `LocalKey::with` on a `const` thread local is checked.
`HashMap::new` and lazily initialised thread locals stay `⊤`: they reach foreign
functions inside `std` (the random source, paths that print to stderr),
which std summaries record as `⊤`. Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-03: thread locals through their `static` key".

## Amendment 2026-11-03: contracts with `param(..)` (top plan T5)

A trait method contract may declare `param(g = K)` for a parameter of function-pointer
or callable trait-object type (before: rejected by the driver and by `fip-macros`).
Every implementation is checked with `g` costing `K` (the bound follows the position
to the implementation's own parameter name; its own tighter `param` is an error, as a
weaker mark), and every call through the contract, dynamic or on a type parameter,
checks its argument against `K` and the contract's permissions, like any call site of
a function declaring `param(..)`. `#[fip(param(g = K))]` is accepted on a declaration
without `strict = true` (the name and the type are checked); with `strict = true` it
stays rejected, since a `#[fip_trait]` certificate carries no parameter bounds. This
supersedes "`param(..)` (the driver rejects it in a contract too)" of the amendment
"`#[fip]` on trait method declarations". Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-03: contracts with `param(..)`".

## Amendment 2026-11-03: element paths and access-path preconditions (top plan T13.1, T13.2)

The value analysis's access paths below a shared reference to a `Freeze` type also
step into array and slice elements at a constant index (`xs[0]`: a `ConstantIndex`, or
an index local holding one constant in the whole body), so a guard on `xs[0]` decides
a later use of it. `fip::requires(..)` accepts access paths below a `&T` parameter
with `T: Freeze` (`w.n`, `w.0`, `xs[0]`, `w.b.len()`; fields and literal indices, not
through a further reference); a root assumes them and every analysed call site must
establish them, as for the other terms. Relational nonlinear guards, variable indices
and interior mutability stay reported. Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-03: element paths and access-path preconditions".

## Amendment 2026-11-03: foreign calls inside std summaries (top plan item 8b)

A foreign call inside a summarised `std` function is stored as the term `§ffi <symbol>
<abi>` (sidecar format 2; format-1 files and drivers refuse each other) and resolved
at the use site with the analysed crate's FFI marks, by symbol and ABI, as a direct
call: certified, excluded (both listed), else the FFI error naming the std function.
The seed adds `HashMap::new` and a lazily initialised thread local; both still reach
function pointers from mutable data (`⊤`). Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-03: foreign calls inside std summaries".

## Amendment 2026-11-03: the analysis cache follows the std summaries' content

`cargo fip-prelint` passes a content hash of the std summaries files
(`FIP_PRELINT_INPUTS_ID`) and the driver records it, with `FIP_PRELINT_SYSROOT`, in the
dep-info, so cargo re-checks a crate when a sidecar's content changes, not only when
its modification time moves. Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-03:
the analysis cache follows the std summaries' content".

## Amendment 2026-11-03: std summaries for every installed `std` target (top plan T7j)

The sidecar is generated and committed for every installed target with `std` (10),
not only the host; `repin.sh` regenerates or compares all of them. A target without a
sidecar keeps the `⊤` of "std summaries not used". The wasm32 results equal the
host's for formatting and differ where `std::sys` differs. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-03: std summaries for every installed `std`
target".

## Amendment 2026-11-03: stack mode gaps (top plan T8)

Stack mode adds `-Zcross-crate-inline-threshold=never`, reads AArch64 ELF objects
(return address 0) besides x86_64, bounds a generic root per instance the build
codegens, reads the objects of bins and tests when they are selected (`-Csave-temps`),
and with `--build-std` builds and bounds the standard library with the profile's
settings. The crate attribute `fip::stack_leaf(sym = B, evidence = "..")` declares the
stack use of a symbol the build has no frame for (a trusted declaration, listed in the
summary, used only for that crate's roots). Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-03: stack mode gaps".

## Amendment 2026-11-03: certified function pointers (top plan T1.4)

A call through the pointer held in a `fip_strict::Certified<N, fn(..)>` costs `N`
allocations and a possible panic (no free, no recursion). Every analysed
`Certified::assume` is checked against `N` like a `param(f = N)` argument; a pointer of
unknown origin or a generic callable type is `⊤` there. Constructions in crates the
driver does not analyse are trusted (`assume` is `unsafe`). Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-03: certified function pointers".

## Amendment 2026-11-03: allocation failure label (top plan T14.3)

Under a mark that permits allocations, the panic path of a failed allocation
(`alloc::alloc::handle_alloc_error`) is labelled "allocation failure path (diverges)";
the verdict is unchanged (a note, an error under `panic_macros = false`). Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-03: allocation failure label".

## Amendment 2026-11-03: opt-in pool hints (top plan T17)

`cargo fip-prelint --pool-hints` prints notes labelled "heuristic" for unmarked
methods of crates declaring `fip::export` (since 2026-11-04 also of every package the
driver checks, with or without it) that look like pool allocators (hand out a
borrow of or an index into their own buffer, with a sibling release method). Off by
default; never a verdict, a count or an exit status. Unmarked pools remain the
declared assumption. Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-03: opt-in
pool hints".

## Amendment 2026-11-04: Verus as an oracle for panic freedom (top plan T13.4)

**A trust change, accepted by the user on 2026-11-04.** The driver now also trusts
Verus, for one kind of fact: a body-local `Assert` panic site (overflow, bounds,
division, remainder, negation checks) of a function that a `--no-cheating` Verus run
of its whole crate verified is discharged under that function's Verus `requires`.

- **What is trusted.** Verus 0.2026.10.18.7d82994 (commit `7d829946231d`) with Z3
  4.16.0, pinned in `tools/fip-prelint/verus-trusted.txt` (compiled into the driver;
  changing it is a trust decision), and the sidecar's provenance: the generator
  `cargo fip-prelint --verus-sidecar`, which accepts only a successful run over the
  entire crate with `--no-cheating` and lists the exec functions of the crate's VIR
  log that have a body and are not `external_body`.
  **Repinned 2026-11-06** (user decision D5 of
  `2026-11-06-redesign-verus-allocates.md`): the trusted build is the Verus fork `fip`
  at `0.2026.11.05.ca33b04` (`ca33b0438c36`), Z3 4.16.0; sidecars record
  `-V alloc-check` in `flags`, and VIR path namespace marks (`t%`) are dropped
  (`TODOs/fip-prelint.md`, "Resolved 2026-11-06").
- **Where.** A package opts in in its manifest (`[package.metadata.fip-prelint]
  verus-sidecar = ".."`); the sidecar is committed next to it
  (`crates/fip-core/verus-verified.txt`). `just verify-core` regenerates it and fails
  if it differs; a stale sidecar is refused by the driver, which changes the
  self-check.
- **When it is used.** Only if the stamp equals the pin, every source file of the run
  (the crate and the imported Verus crates) has its recorded SHA-256, the function's
  path is listed for its file and the SHA-256 of its item text (outer attributes and
  doc comments through the body, so the `verus_spec` too) matches, and the site lies
  in that text outside any macro expansion. Otherwise the site stays reported, with
  the reason; a refused sidecar is named in the crate summary.
- **What does not change.** Calls, allocations, frees, recursion, `⊤`, `assert!` and
  `panic!` calls, and the sites of closures and of functions not listed. A caller that
  Verus did not verify (or a call Verus did not check directly: through a pointer, a
  trait method, a `param(..)` argument, a cycle) carries the callee's Verus `requires`
  as a panic path ("precondition .. verified by Verus only for Verus callers"); a
  Verus caller passes it on under its own `requires`.
- **Visible.** The crate summary ends with "N panic sites discharged by Verus (sidecar
  of `<crate>`: Verus <version> (<commit>), Z3 <version>, --no-cheating)".
  `cargo fip-prelint --no-verus` gives the analysis without the trust.

Measured: `fip-core` 17 functions listed (both the upstream and the fork Verus build
give the same list and hashes; only the stamp differs, and the fork's is refused); the
self-check is unchanged in dev (0 sites to discharge) and under `--release` has 15
instead of 16 notes (the `strict::dedup_by` bounds check discharged; `pipeline`'s note
becomes the precondition note). Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-04: Verus as an oracle for panic freedom".

## Amendment 2026-11-04: proc-macro crates are never listed

A dependency loaded only for its macros (`crate_dep_kind == MacrosOnly`, a proc-macro
crate) is never treated as encoded, also in std-summary generation mode, which treats
every other dependency as encoded. Listing its functions was an ICE in
`rustc_metadata` (generation mode of any crate depending on `fip-macros`). Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-04: generation mode with a proc-macro
dependency (ICE)".

## Amendment 2026-11-04: closures generic through the enclosing function

`Certified::assume` with a closure or function item type that has type parameters
(built inside a generic function) is analysed through its body, like a monomorphic
closure; `⊤` stays for a type that may be a function pointer. At the check function
of a driver-mode `fip_fn!` (`__fip_prelint_checked`), an undeclared term left in the
generic body is `⊤` (the certificate claims its bound for every instantiation).
Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-04: `fip_fn!` closures in generic
functions".

## Amendment 2026-11-04: function-pointer residue (top plan T1–T3)

Also resolved: an element of a local array of function pointers assigned only as a
whole (every element a candidate, or the one at a constant index); a pointer behind a
shared reference stored in immutable data, when the memory it points to is immutable
and of a `Freeze` type; a function pointer through an `FnMut` bound (a `&mut g` used
only as the receiver of `call_mut`, whose function-pointer shim never writes `*self`,
keeps `g` stable); `&Rc<dyn Fn*>` / `&Arc<dyn Fn*>` parameters like `&Box<dyn Fn*>`
(`param(g = K)`, bound to the concrete type at the call site). Everything else stays
`⊤`. Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-04: function-pointer residue".

## Amendment 2026-11-04: elements at a variable index

An access path may step to the element at the index held in a local `k` whose
address is never taken, tracked while `k` is unchanged (every assignment to `k`
forgets it); an index temporary copied from `k` right before its use (same block, or
the bounds check's only successor) stands for `k`. Such paths stay inside one body
(never in a summary or a precondition). Details: `TODOs/fip-prelint.md`, "Resolved
2026-11-04: an element at a variable index read twice".

## Amendment 2026-11-04: T4.3 reports at the caller

A call site inside a private function checked at its call sites (T4.3) is reported
at the call of that function in the caller whose binding found it, for that caller
(and, for an unknown pointer, naming the caller's parameter), once per such call.
Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-04: T4.3 reports at the caller".

## Amendment 2026-11-04: stack mode on ELF32 (i386, ARM)

Stack mode reads ELF32 i386 and ARM objects (`REL` relocations): return address 4
bytes on i386, plus 4 for a function without callees (a PC-reading `call` below the
frame, measured), and 0 on ARM (the saved `lr` is inside the measured frame). Thumb
branch relocations make the object unreadable (`⊤`). Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-04: stack mode on ELF32 (i386, ARM) and
the allocator shim's name".

## Amendment 2026-11-04: Verus sidecars list impl methods, by location

Sidecar format 2. Every entry records the 1-based line where its item text starts
(`fn <path> <file>:<line> <hash> <requires>`), and every impl block in a path is
written `{impl}`. An impl method is identified by that path, its file and the line,
never by the impl number: Verus's `impl&%N` and rustc's `{impl#N}` are both the
`DefPath` disambiguator, but of two different builds, and `cfg(verus_keep_ghost)`
changes the impl blocks a build has (measured: `fip-strict`'s Verus `impl&%8` is
rustc's `{impl#1}`; in the fixture `verus_sidecar`, Verus `impl&%0` is rustc
`{impl#1}`). The generator skips methods inside an item marked exactly
`#[cfg(verus_keep_ghost)]` (no plain twin at that place) and functions whose span
comes from a macro expansion (one text for every expansion). The driver does not use
an impl method whose impl block's header (its attributes through the self type)
mentions `verus_keep_ghost`, as for the item text. `fip-strict` and `fip-alloc`
declare sidecars (0 and 1 functions listed; `fip-strict` lists 2 since its
`Certified` constructors became single items, `TODOs/fip-prelint.md`, "Resolved
2026-11-04: `fip-strict`'s Verus-only constructors merged into single items"). `FIP_PRELINT_VERUS_ID` also covers the
sidecars of path dependencies outside the workspace, transitively. Details:
`TODOs/fip-prelint.md`, "Resolved 2026-11-04: Verus sidecars for impl methods,
`fip-strict` and `fip-alloc`".

## Amendment 2026-11-04: `ffi(dep::sym = local::sym)` mappings checked by symbol and ABI (top plan T10.2)

`#[fip(strict = true, ffi(dep::sym = local::sym, ..))]` lets strict calls of a
dependency's foreign function `dep::sym` read the certificate of a `#[fip_extern]`
declaration `local::sym` (before: E0425 on `dep::__fip_strict_sym`). Under the driver
the attribute emits, at the start of the strict body, one hidden function per pair
carrying `fip::ffi_map` whose body names both functions
(`let _ = (dep::sym as *const (), local::sym as *const ());`). The driver reads the
two functions from the HIR of each `fip::ffi_map` function and reports, at the pair,
a side that is not a foreign function, or two declarations whose link symbols
(`tcx.symbol_name`) or ABIs differ: the same rule as marks matched by symbol, applied
to the certificate the macro chose. `fip::ffi_map` is a known tool attribute, accepted
on functions with a body only. Trust without the driver: the mapping is unchecked,
except that `Cert::allocs_for` checks the certificate's name against `sym` of the
local path. Measured: `tests/fixtures/ffi` cases 15–17, see `TODOs/fip-prelint.md`,
"Resolved 2026-11-04: FFI certificate mapping for strict callers".

## Amendment 2026-11-04: soundness audit of the driver

Rules tightened after an audit whose probes passed code that allocates, frees,
recurses or panics:

- **Tail calls.** A body with a reachable `become` (`TailCall`) gets no return summary
  (its callers learn nothing about the result). Before, a body without `Return` was
  summarised "never returns", which made the rest of every caller dead.
- **Contracts and recursion.** While an implementation is checked against its trait
  method's contract (`run_contract`, `run_default`), a dynamic call of a contracted
  method also carries a possible recursion (for `fip`; `fbip` allows it anyway): the
  contract is assumed for that implementation too, so a cycle through `dyn` calls was
  assumed away on both sides. Allocation counts stay sound by induction and are
  unchanged.
- **Path tables name standard-library items only.** Every path-table test
  (allocation, deallocation and reallocation entry points, panic prefixes, UB checks,
  the `core::fmt` paths of the formatting analysis) reads `std_path`, empty for a
  crate that is not `core`/`alloc`/`std` or one of their dependencies: a local
  `mod core { mod panicking { .. } }` prints as `core::panicking::..`. UB checks are
  matched exactly (`fip_lint_rules::mir::is_ub_check`: last segment
  `precondition_check` under `core::`/`alloc::`/`std::`, or
  `core::hint::unreachable_unchecked`), not by substring.
- **Foreign functions by link symbol.** The allocation tables (`__rust_alloc`,
  `malloc`, `free`, ..) classify a foreign declaration by its link symbol
  (`#[link_name]`), as the marks do (`foreign_table_name`); declarations inside the
  standard library keep their item name, because `#[rustc_std_internal_symbol]`
  mangles the runtime symbols.
- **Std summaries.** The stamp's `settings` must equal the generator's
  (`stdsum::SETTINGS`), every entry has exactly one `alloc` line, and summaries are
  not used when the crate's `core` is not the sysroot's (a user `-Zbuild-std` build
  compiles `std` with the profile's settings).

Details and measurements: `TODOs/fip-prelint.md`, "Resolved 2026-11-04: soundness
audit of the driver".

## Amendment 2026-11-04: Verus sidecars bound to the build configuration and to verified imports

**A narrowing of the Verus trust (amendment "Verus as an oracle for panic freedom").**
Two audit probes had sites discharged in code Verus never compiled, and a third
imported a crate verified with cheating:

- **Configuration.** Verus compiles a crate without `--cfg fip_prelint`, the cargo
  features, `cfg(test)` and the profile's settings; the driver with them. An item
  whose text holds any `cfg(..)`/`cfg!(..)`/`cfg_attr(..)` other than
  `cfg_attr(verus_keep_ghost, verus_spec(..)|verus_verify|verifier::..)`,
  `cfg_attr(not(verus_keep_ghost), fip_macros::..)` and `cfg_attr(fip_prelint, fip::..)`
  is not listed by the generator and not used by the driver
  (`verus::cfg_conflict`; `cfg_attr(verus_keep_ghost, cfg(any()))` deleted a bounds
  check for Verus only). A crate whose sources test any cfg but `verus_keep_ghost`
  and `feature` outside those forms gets no sidecar and an existing one is refused
  (`verus::crate_cfg_conflict`: a `#[cfg(test)]` constant or inherent method changes
  a listed item without changing its text). The stamp records the run's target and
  features (sidecar format 3, line `cfg`); the driver uses a sidecar only for a build
  with both equal. Consequence, measured: on the ten other installed targets (nine with `std`, and `x86_64-unknown-none`) the
  self-check names the refused sidecars; no verdict changes (no site was discharged in
  dev).
- **Imports.** The generator accepts `--import <name>=<vir>` only with
  `--import-sidecar <name>=<committed sidecar>`: that sidecar must have the trusted
  stamp with `--no-cheating` and unchanged sources, and the VIR file must carry the
  record (`<vir>.fip-run`: crate, `--no-cheating`, SHA-256 of the file) that a
  generator run writes for its `--export`. A VIR file from a plain Verus run (which
  may have used `assume`) is refused.
- **Cache.** The analysis cache key (`FIP_PRELINT_VERUS_ID`) and the dep-info of a
  crate with a sidecar include the current content of every `source` file the sidecar
  lists, so a Verus-only module (`#[cfg(verus_keep_ghost)] mod spec;`) edited after a
  run re-checks the crate.

Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-04: Verus sidecar trust after the
audit".

## Amendment 2026-11-04: Verus sidecars after the re-audit (sidecar format 4)

The re-audit found three ways to get sites discharged in code Verus never compiled,
each measured with the fixture crate `vside` (generator, then driver):

- **N3, macros.** The cfg scan was textual: `gate!(cfg, fip_prelint)` with
  `macro_rules! gate { ($c:ident, $p:ident) => { $c!($p) } }`, and
  `option_env!("CARGO_PKG_NAME")` (cargo sets it for the driver's rustc, not for the
  direct Verus run), were listed and their division sites discharged ("14 roots, 14
  passed, 7 panic sites discharged"). Decided: refuse, not reproduce the driver's
  configuration for Verus. Running Verus with the driver's cfgs and cargo's
  environment would need every variable cargo sets (and `cfg(test)`, the profile's
  cfgs, `fip_prelint`) to be reproduced per build, and would still not cover a
  dependency macro; the refusal is checkable on the text. `verus::macro_conflict`
  (generator and driver, crate scan and item texts) refuses `env!`, `option_env!`,
  `include!`, `include_str!`, `include_bytes!` (an included file is not among the
  hashed sources), a macro named by a metavariable (`$c!`), a bare `cfg`,
  `cfg_attr`, `env`, `option_env` or `include*` token in a macro's arguments, and,
  crate-wide, any macro that is neither a `macro_rules!` of the crate's sources
  (whose body the scan reads) nor one of a short list of `core`/`std` macros whose
  expansion tests no cfg (not `debug_assert!`), Verus's and `fip_fn!`. Measured on
  the repository: `fip-core`, `fip-strict`, `fip-alloc` and `vside` use only local
  macros (`proof!`, `proof_decl!`, `certified_fip_fn!`), `assert!`, `seq!`, `verus!`
  and `fip_macros::fip_fn!`; no sidecar changes. After: the generator refuses both
  probes ("`$c!(..)` (a macro named by a metavariable ..)", "`option_env!(..)` .."),
  and the driver refuses an existing sidecar of such a crate (0 sites discharged).
- **N4, sources outside `src/`.** The generator scanned `src/` and the driver skipped
  every listed source starting with `../` (assumed imported): a
  `#[path = "../../shared.rs"] mod shared;` whose `on()` returns `cfg!(fip_prelint)`
  with `ensures !r` escaped both ("13 passed, 6 discharged"). Now both scan every
  listed source. An imported crate's sources are scanned too rather than told apart by
  import: they passed the same scan in the imported crate's own run, so this refuses
  nothing more, and needs no record of which source came from which import. After:
  the generator refuses the crate ("../shared.rs: `cfg!(fip_prelint)` tests
  `fip_prelint`"), the driver an existing sidecar.
- **N4, callers of a skipped function.** A function skipped because its code differs
  between the builds (a cfg form in its text such as `cfg_attr(verus_keep_ghost,
  cfg(any()))`, or Verus-only) still gave its `ensures` to verified callers, which
  were listed. Measured: `on()` deleting `return true;` for Verus only, `ensures !r`,
  and `probe_taint` dividing under `if on()`: listed, division discharged (6 sites).
  Now the generator reads every function a VIR record names (`(Fun :path ..)`: call
  targets, resolved trait methods, functions in specifications), taints every
  function naming a tainted one to a fixpoint (through unlisted verified functions
  too), and skips the listed ones ("relies on the specification of `vside::on`, whose
  code may differ in the driver's build"); an `--import-sidecar`'s skips of these
  kinds taint the importing run's callers. After: `probe_taint` skipped, its division
  reported (5 sites discharged).

The sidecar lines are unchanged; the format number is 4 so that the driver refuses
sidecars written by the earlier generator. Trust boundary, not checked: attribute
and derive macros of dependencies and a glob import from a dependency shadowing a
known macro name are assumed to expand alike in both builds; a call through a trait
method names the trait's method, so an implementation skipped for a cfg (impl paths
compared as `{impl}`) taints only callers whose VIR names it.
*(Closed 2026-11-06 by the amendment "cfg twins and proved allocation bounds": callers
of a method of a trait with a divergent implementation are skipped, and the driver
refuses trait calls into implementations no sidecar lists.)*

## Amendment 2026-11-06: cfg twins and proved allocation bounds (sidecar format 5)

Phase 4 of `2026-11-06-redesign-verus-allocates.md` (section 2.4). Two changes, both
fail closed.

**The cfg-twin hole (the re-audit's open trust boundary "a call through a trait method
names the trait's method").** Reproduced with a probe (fork `ca33b04`,
`--no-cheating -V alloc-check`): trait `Step` declared in `verus!` under
`#[cfg(verus_keep_ghost)]` with `fn step(&self) -> (r: u32) ensures r > 0, allocates 0`
(Verus impl returns 1), a plain twin declaration and a plain-only `impl Step for S`
returning 0 after a `Box::new`; `run<T: Step>` (`a / t.step()`), `run_s` (`run(&S, a)`)
and `direct` (`a / S.step()`), each `allocates 0`, 4 verified. Before: the three were
listed and both divisions discharged ("2 panic sites discharged by Verus"); the VIR
records of all three, also of the concrete `direct`, name only `hole::Step::step`, so the
taint of the Verus-only impl never reached them. Now:

- **Generator.** `verus::divergent_traits` finds every trait implementation and
  declaration inside an item gated by a cfg naming `verus_keep_ghost` (`#[cfg(P)]` with
  it in `P`, `#[cfg_attr(P, .. cfg(..))]`; also inside `macro_rules!` bodies) in every
  source of the run; the sidecar records them (`divergent <trait> <file>:<line>`), and
  every function whose VIR record names a method of such a trait, or of one an
  `--import-sidecar` records, is skipped with its callers ("relies on the specification
  of `vside::Step::step`, a method of trait `Step`, which has an implementation or
  declaration in only one of the builds"). Matched by trait name (two traits of one name
  are both divergent). After: the probe lists nothing.
- **Driver.** Independently of the generator, the Verus results of a listed function are
  not used for an analysed instance that calls a trait method (not `Fn*`: a closure's
  specification reaches the body only through its own `requires`) resolved, in this
  build, to a function that no sidecar lists, outside the standard library (vstd's
  specifications are trusted). This covers the twins and an unverified implementation in
  a downstream crate reached through a type parameter. After: with the probe's old
  listing (forged to format 5) both divisions stay ("it calls the trait method
  `Step::step`, implemented in this build by `<S as Step>::step`, which no Verus sidecar
  lists"; a generic root: "whose implementation in this build is not resolved").
- **Unification of `fip-strict`'s twins into one attribute-mode source: not done.**
  `Compose` has one plain impl generic over `Args` and one Verus impl per arity (vstd has
  no `AllocFreeDrop` for a generic tuple); the Verus impls carry `AllocFreeDrop` bounds
  and spec functions the plain build cannot name; the marker traits are blanket impls in
  the plain build. Exclusion is the general rule and also covers downstream twins.
- **Measured consequences.** `fip-strict`'s sidecar records 28 divergent places (`FipFn`
  10, `FipBound` 10, `AllocFreeDrop` 6, `DropFreeFn` 2); `fip-core`'s 7
  `fip_core::strict::*` functions are no longer listed (10 listed, 7 skipped); in the
  release self-check the `strict::dedup_by` bounds check, the one site discharged, is
  reported again (`fip_core` 0 → 1 notes). On the other installed targets the summaries
  also name `fip-strict`'s sidecar as refused (it is consulted now for the resolved
  `FipFn` implementations); no verdict changes.

**Proved `allocates` bounds.** Every `fn` line carries a sixth word, the bound the run
proved, read from the fork's VIR field `:allocates`: `-` (none), a literal, a
parameter-linear form `c+k*p..` (constants, unsigned or `nat` parameters, `+` and constant
`*` over `int`/`nat`), or `opaque:<sha256>` of the expression without spans and ids. The
generator refuses a run without `-V alloc-check`, the driver a sidecar whose `flags` lack
it. A **literal** bound `K` replaces the driver's count of the function's body only if the
function is not generic (a bounded parameter's Verus premise, `T: AllocFreeDrop`, holds
for every type in the plain build), has no `requires` (the fork assumes a callee's bound
only under its precondition), its instance passes the trait check above, and every panic
path of its summary is an allocation failure (the fork bounds normally returning
executions only; an allocation failure diverges inside the allocation). Then a finite
count `m <= K` is kept, a finite `m > K` is kept and is an error at every root reaching
the function ("the proof's trust boundary is violated (or the driver's count is
imprecise)"), any other count (`∞`, open terms) becomes `K`. Frees, panics, recursion
and unresolved events stay the driver's; parameter-linear and opaque bounds are not
evaluated. Fixture `verus_alloc` (crate `valloc`): `twice` (a loop of two `one()`
calls, proved `allocates 2`) and its plain caller get 2 instead of `∞` and pass `n = 2`
(9 errors, against 11 with `--no-verus` or a stamp without `-V alloc-check`); `zero`
(0/0) and `one` (1/1) keep the driver's counts; the linear `times`, `upto` (with
`requires`) and the generic `twice_with` keep `∞`; `one`'s bound forged to 0 gives the
violation error at all 7 roots reaching it. No workspace verdict changes: every listed
workspace function is generic or has a `requires`.

Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-06: cfg twins and proved allocation
bounds (redesign phase 4)".

## Amendment 2026-11-09: re-pin to rustc 1.100.0-beta.10 and the fork audit's gate rules

The Verus fork moves to `0.2026.11.08.6f6975a` (`6f6975af2411…`, toolchain
`beta-2026-11-05`, rustc 1.100.0-beta.10); `fip-prelint` follows (`rust-toolchain.toml`).
The workspace MSRV stays 1.99.1 (`just msrv` passes; nothing needs 1.100).

- **Driver API.** `rustc_session::config::CrateType` is now `rustc_structures::CrateType`;
  `try_to_leaf`/`try_to_target_usize` need `rustc_middle::ty::consts::ConstExt` in scope.
- **Trusted tables re-read against the 1.100 sources** (`rust-src` of the toolchain;
  files unchanged against 1.99.1 re-checked by diff, changed ones read): entry points,
  `__rust_no_alloc_shim_is_unstable_v2`, `GlobalAlloc`/`Allocator` methods (unchanged;
  `Allocator` is stable since 1.100), panic prefixes, UB check markers, intrinsics,
  `NON_ALLOCATING_CONSTRUCTORS`, `CORE_TABLE` (audited-at markers gain 1.100.0-beta.10),
  the iterator contracts, `drop_glue`, `Formatter::buf`. Changes: `Ord::min`/`max` of
  integers are the intrinsics `integer_min`/`integer_max` (allocation-free, and a value
  summary `INTRINSIC_MIN_MAX`; without it every `Vec` growth path was `⊤`); the float
  math intrinsics are generic (`sin`, `cos`, `exp`, `exp2`, `log`, `log10`, `log2`);
  `precondition_check` items of trait methods print as qualified paths
  (`<usize as core::slice::index::SliceIndex<[T]>>::..`) and are recognised by the
  crate defining the item (see below).
- **Allocator entry points** (`FIP_PRELINT_DUMP=1`, step 4 of `repin.sh`): the leaves of
  all seven probes are the same as on 1.99.1.
- **Std summaries** regenerated for 11 targets (`wasm32-wasip3` new). Against 1.99.1,
  per function: no change of allocation, free or term lines except renamed symbols
  (`Big32x40` → `Big64x20`, new `Big*::from_u64` on 32-bit targets, wasip crate hashes
  in `§ffi` terms); panic witnesses differ in paths only.
- **Cargo 1.100 build-dir layout.** The stack mode ignores build scripts (cargo now
  lists the driver-compiled file, without kept objects) and finds an uplifted
  executable's original under `build/<package>/<hash>/out/`; the justfile locates
  artifacts with `one_artifact` (exactly one candidate, else a failure).
- **Fixture diffs accepted:** rustc version strings (`-stale`), the allocator shim's
  mangled symbol (`stack -tests`), one fewer panic path in `std_summaries`
  (`Chunks::next`'s `split_at` is now proved in bounds through `integer_min`), the new
  target section `wasm32-wasip3`.
- **Gate rules (the fork audit).** The driver refuses a Verus sidecar whose `flags`
  lack `--no-cheating` or record anything besides `--no-cheating -V alloc-check`
  (`--is-vstd`, `--is-core`, `--is-stdlib-outside-of-core` named); the generator refuses
  those flags. Verus can prove false facts about memory of an allocator whose methods
  touch its state, in the crate using it: a sidecar whose listed sources implement
  `Allocator`, `GlobalAlloc`, `GlobalAllocator`, `StaticAllocator` or `AllocatorClone`
  is refused whole, and an entry is not used for a function whose MIR (locals,
  callees' generic arguments) has a non-std type implementing `Allocator`/`GlobalAlloc`,
  a type parameter bounded by one or a trait object of one (any type parameter if such
  an implementation is blanket). Fixture `verus_alloc` variants `-cheat`, `-isvstd`,
  `-allocimpl`, `-allocuse`.
- **UB checks by defining crate.** `is_ub_check` takes the crate of the item's `DefId`
  (`core`/`alloc`/`std`), not its printed path: a user impl of a `core` trait for `u8`
  or `&Local` can nest a `fn precondition_check` whose path prints alike (fixture
  `ub_lookalike`: both panics reported).


**Later the same day:** re-pinned to the fork `0.2026.11.09.1b27c11` (`1b27c1101…`, same
toolchain `beta-2026-11-05`). Between the two pins the fork added the hand-out rule for
user allocators (`hand_out`/`reclaim`), block size and alignment postconditions, trusted
(`external_body`-only) user `grow`/`shrink`, cross-crate `fip(strict)`, and
`deallocates_when(0, false)` on the slice and `Vec` views; portable-fip still refuses
allocator impls (surface gate, driver), so none of its claims depend on those rules.
Measured: `just verify` gives the same counts; the Verus sidecars and the `targets`
fixture differ only in the stamp (version and commit). Re-pinned again 2026-11-10 to
`0.2026.11.09.c716c2b` (`c716c2bfd…`, same toolchain): the fork's strict check accepts
std calls marked as dropping nothing with a non-`Copy` `T`, so `total` emits
`#[verifier::fip(strict)]` (redesign record 7.6).

## What would reopen this

- `rustc_public` covering crate-root attributes (drop the `rustc_middle` use).
- A Verus toolchain change (re-pin, re-run the probes); a Verus or Z3 update (re-pin
  `verus-trusted.txt`, regenerate the Verus sidecars, review their diff).
- A stable way to encode MIR for all functions without `-Z` flags.

## Amendment 2026-11-17: re-pin to stable rustc 1.100.0; recorded and installed target sets

The Verus fork moved to stable Rust 1.100.0 (`0.2026.11.17.1c37a96`, branch `fip`);
`fip-prelint` follows (`rust-toolchain.toml`: `beta-2026-11-05` → `1.100.0`).

**Measured** (`just prelint-repin 1.100.0`, x86_64 Linux host, 2026-11-17):

- the driver builds unchanged against 1.100.0 (no `rustc_private` API change);
- the probes pass (MIR of a non-inline function only with `-Zalways-encode-mir`,
  `fip::export` / `fip::mark` readable from a dependency, E0514 across compilers);
- the allocator entry-point leaves are the ones recorded for 1.100.0-beta.10;
- the `library/` tree of the `rust-src` component is byte-identical to that of
  `beta-2026-11-05` (`diff -rq`, 3658 files). The trusted tables were therefore not
  re-read; `NON_ALLOCATING_CONSTRUCTORS_AUDITED_AT` and `CORE_TABLE_AUDITED_AT` gain
  `1.100.0` on that ground, stated at the constants;
- the std summaries were regenerated for the 11 recorded `std` targets. Against the
  1.100.0-beta.10 files they differ in the stamp (`rustc`, and `std-src`, whose hash
  covers the absolute paths of the sources and so changes with the toolchain
  directory) and, on the three WASI targets, in the crate-hash part of mangled FFI
  symbol names (2 or 3 lines each). The beta files are removed;
- fixtures: three expected files change, only in the rustc version string (35
  occurrences) and one mangled allocator-shim symbol.

**Target sets.** The toolchain on the maintainer's host now has far more targets
installed (86 with `std`) than are recorded (11 `std`, 1 `no_std`). Until now
`tests/targets.rs` built every installed target and failed on an unrecorded one, and
`repin.sh` generated summaries for every installed `std` target, so the gate's result
and its cost depended on what happened to be installed. Now:

- **recorded** (default; `FIP_PRELINT_TARGETS=recorded`, `just prelint-targets`,
  `just prelint-std-summaries-recorded`, `repin.sh` step 5, and what `just ci`
  runs): the targets with a section in `tests/targets.expected`. An installed target
  without a section is named in a note and not built. A recorded target that is not
  installed still fails under `FIP_PRELINT_REQUIRE_TARGETS=1`; a `targets.expected`
  that records nothing, or none of whose targets is installed, fails.
- **all** (`FIP_PRELINT_TARGETS=all`, `just prelint-targets-all`,
  `just prelint-std-summaries-all`, `TARGETS=all` for `repin.sh`): every installed
  target; an unrecorded one fails until its output is reviewed and recorded.

Consequence: an unrecorded installed target no longer fails `just ci`. Widening the
recorded set is a deliberate step (`prelint-targets-all` with `FIP_PRELINT_BLESS=1`
after review, plus the std summaries of the new targets).

**MSRV and the lint gate (same day, user decision).** The workspace MSRV moves from
1.99.1 to 1.100.0 (`rust-version`), and a `rust-toolchain.toml` at the repository
root pins 1.100.0 (with `rustfmt` and `clippy`) for every gate the justfile runs
with a plain `cargo`. Before, those gates ran on whatever toolchain was the host's
default (1.99.1 on the maintainer's host), so `just lint` did not see the lints of
the compiler the proofs and `fip-prelint` use: clippy 1.100.0 reports ten
`map(_).unwrap_or_default()` sites (`fip-macros`, `fip-testkit`, three test files)
that clippy 1.99.1 accepts. They are rewritten to `map_or_default`, which is why
the MSRV cannot stay below 1.100.0 once they are. A consumer on an older compiler
keeps working only with a revision from before this change.

One gate still builds on an older compiler: the upstream strip gate
(`just verify-upstream`) builds `fip-macros` with the toolchain of the pinned
upstream Verus (1.99.1; upstream `main` was still on 1.99.1 on 2026-11-17), because
that compiler loads the proc-macro. The build passes `--ignore-rust-version`
(measured: `fip-macros` at this revision compiles on 1.99.1). So the declared MSRV
is 1.100.0 while `fip-macros` is in fact kept compiling on 1.99.1 by that gate, for
as long as upstream Verus stays there.

`fip-testkit` no longer needs 64-bit atomics (a `Mutex<[u64; 4]>` where
`target_has_atomic = "64"` is false), found by `just prelint-targets-all`: four
installed targets did not build.

## Amendment 2026-11-18: re-pin to the fork a330057 (same rustc)

The fork's `fip` branch gained two commits after `1c37a9697` (notice of the fork to
this repository, 2026-11-18): `4ea38e93f` (`<[T]>::to_vec` and `Box<[T]>: From<&[T]>`
specifications, `Clone` markers) and `a33005760` (`x.into()` through std's blanket
impl is checked as the resolved `from`; `From`/`Into` markers). 18 files, +894/-24.
The pin moves to `0.2026.11.18.a330057`; the rustc toolchain (1.100.0) does not
change, so `repin.sh` was not needed and the std summaries are untouched.

**Measured** (x86_64 Linux host, 2026-11-18):

- `just verus-pin` accepts the new build (Z3 4.16.0, toolchain 1.100.0);
- `just ci` exits 0 with the new pin: 951 tests pass, 20 Verus result lines, each
  with 0 errors and with the same verified counts as under `1c37a96`;
- the six regenerated sidecars differ from the committed ones in the stamp line and
  in the `requires opaque:` hash of `fip_core::slice::{compact, compact_map,
  map_in_place}`, nothing else;
- cause of the three hashes: `a33005760` adds a field `into_forward` to VIR's
  `CallTargetAttrs`, so every call node prints ` :into_forward None`. `fip-core` was
  run under both builds with `--log vir`: of its 22 non-`None` `:allocates` fields,
  10 have identical text and 12 differ, and the differing tokens are only the added
  `:into_forward None` (and, in one vstd function, two numeric ids, which the
  generator drops). The other nine differing fields change no sidecar line: seven
  belong to the functions of `fip_core::strict`, which the sidecar skips (seven
  `skip` lines), one to the imported `fip_strict::FipFn::call` (no body) and one to
  vstd. The fourth opaque bound of the sidecar (`fip_core::slot::update`) kept its
  hash. This is the same situation as on 2026-11-09 (`trusted_call`).

**Trust added by the fork** (as listed in its notice; not audited here): the
specifications of `to_vec`, `Box<[T]>::from(&[T])` and a `deallocates_when(0, false)`
on `<[T]>::into_vec` and on the reflexive `From::from`; marker impls of
`FbipClone`/`FipClone`/`FipStrictClone` for the primitive types and of
`AllocFreeDrop`/`NoDeallocDrop` for `f32`/`f64`; the blanket `FbipInto` and the
reflexive `From<T> for T` markers; the axioms `axiom_clone_is_fip`,
`axiom_fbip_clone`, `axiom_fbip_from`, `axiom_fbip_into`. In MIR strict checking a
blanket `Into::into` call drops nothing if the resolved `From` impl drops nothing,
and a strict function cannot call `clone_from` through a `Clone` marker.

**`src.into()` in the driver** (measured 2026-11-18, a probe crate outside the
repository, `src: &[u32]`, every function `#[fip(1)]`, the macros active): the
driver passes all six of `src.to_vec()`, `Box::<[u32]>::from(src).into_vec()`,
`let b: Box<[u32]> = src.into(); b.into_vec()`, `src.into()` to a `Box<[u32]>`,
`src.into()` to a `Vec<u32>` and `Box::from(src)` (6 roots, 6 passed). The control,
`Vec::with_capacity` followed by `push` in a loop, is rejected by the macro, and with
`FIP_MACROS_MARK_ONLY=1` by the driver ("may allocate ∞ time(s)", "may free").

The consumer's shape is generic (Verigrad's `copy_on_shared<T: Copy + ..>(src: &[T])
-> Vec<T>`, a helper without a certificate reached from `#[fip(1)]` roots), so the
probe was extended the same day:

- a generic helper `fn h<T: Copy>(src: &[T]) -> Vec<T>` with each of the three bodies
  (`to_vec`, `Box::from` + `into_vec`, `.into()` + `into_vec`), called from concrete
  `#[fip(1)]` roots over `i32` and `f64`: 5 roots, 5 passed;
- a generic `#[fip(1)]` root `<T: Copy>` with any of the bodies, or a generic root
  calling the helper: no error, one warning each (7), "is #[fip(1)] only relative to
  its generic parameters", with the open call `<T as ConvertVec>::to_vec` (for
  `to_vec` and `.into()` to a `Vec<T>`) or `<T as CopySpec>::clone_slice` (for the
  `Box<[T]>` forms). The `.into()` forms get the same bound and the same open call as
  their `From::from` spelling;
- `#[fip(1, strict = true)]`: the macro rejects all of them. Method calls must be
  written by path; by path, `<[T]>::to_vec` is refused ("an allocating method called
  by path may call user code (e.g. the element type's `Clone`)") and
  `<[T]>::into_vec` is "not in the audited `core` table". With
  `FIP_MACROS_MARK_ONLY=1` the driver itself reports no error for the strict
  functions, only notes (allocation-failure and panic paths) and the generic warning.
  So a function that copies a slice this way cannot carry the macro's strict
  certificate today; Verigrad's strict grade for `copy_on_shared` is Verus's
  `#[verifier::fip(strict)]`, and its roots are plain `#[fip(1)]`.

On Verigrad itself (a copy of the tracked files of its `main` `7e24b90`; the original
checkout was not modified; the driver binary of its own build directory, which trusts
`0.2026.11.17.1c37a96`, and `tools/fip-prelint/src` did not change from `42d6f5c`
to Verigrad's pin `1d08a0c`): unchanged, the library gives the recorded 169 roots,
167 passed, 4 errors. With the body of `copy_on_shared` replaced by `src.to_vec()`, by
`Box::<[T]>::from(src).into_vec()` or by `let b: Box<[T]> = src.into(); b.into_vec()`,
no error names `reuse::` any more; `reuse::reuse_or_copy::<T, K>` and
`reuse::consume_and_apply::<T, K>` each get the warning "only relative to its generic
parameters" instead (both roots are generic; open call `<T as ConvertVec>::to_vec`, or
`<T as CopySpec>::clone_slice` for the two `Box` forms). So the 4 errors become 2
warnings, not 0 diagnostics. Those runs also print 40 errors on the eight
`#[fip(total)]` roots, all citing the Verus sidecar as unused because `src/reuse.rs`
changed: an artefact of editing the source without re-running Verus, which was not
done here (it needs Verigrad's changed bounds and the fork a330057).

**The warning is correct, and `Copy` does not close it.** (A first reading here
assumed that every `Copy` type takes std's bitwise path. That was not checked and is
false; what follows was read in the sources named and measured.)

*std* (`rust-src` of 1.100.0). `<[T]>::to_vec` is `to_vec_in(Global)`, which calls
`<T as ConvertVec>::to_vec` (`alloc/src/slice.rs`); `Vec<T>: From<&[T]>` is
`s.to_vec()`. `Box<[T]>: From<&[T]>` is `Box::clone_from_ref`, which allocates once
and calls `<[T] as CloneToUninit>::clone_to_uninit`, that is
`<T as CopySpec>::clone_slice` (`alloc/src/boxed/convert.rs`, `alloc/src/boxed.rs`,
`core/src/clone.rs`, `core/src/clone/uninit.rs`). The blanket `Into::into` is `U::from(self)`. Both private
traits have an `impl<T: Clone>` whose methods are `default` and call `clone()` once
per element, and an `impl<T: TrivialClone>` that copies the bytes.

*`TrivialClone`* (`core/src/clone.rs`) is an unstable `unsafe` marker ("the `Clone`
implementation is identical to copying the value"). `Copy` has `Clone` as its only
supertrait and there is no blanket implementation for `T: Copy`. It is implemented

- in `core`, type by type: the integer and float types, `bool`, `char`, `!`, raw
  pointers, `&T`, `[T; N]` and `Option<T>` for `T: TrivialClone`, `PhantomData`,
  `MaybeUninit`, `NonNull`, `NonZero`, `Discriminant` and a few more;
- by the compiler (`rustc_trait_selection`, `assemble_builtin_copy_clone_candidate`
  and `copy_clone_conditions`; the next solver has the same table): tuples, closures,
  coroutine closures and pattern types of `TrivialClone` components, function items
  and pointers. A type parameter gets no built-in candidate;
- by `#[derive(Clone)]` (`rustc_builtin_macros/src/deriving/clone.rs`): only when the
  same `#[derive(..)]` also lists `Copy` and the type has no type parameter, or for a
  union.

Compiled with `#![feature(trivial_clone)]`: `fn g<T: Copy>() { needs_trivial::<T>() }`
is E0277 ("the trait bound `T: TrivialClone` is not satisfied"), while `T: Copy`
gives `T: Clone`. Each of the following types is `Copy`, and
`TrivialClone` holds for `u32`, `f64`, `bool`, `(u32, f64)`, `[u32; 4]`,
`Option<u32>`, `&u8`, `fn(u32) -> u32`, a `#[derive(Clone, Copy)]` struct, enum or
union (either order, also with a lifetime or const parameter), `Duration`,
`Ipv4Addr`, `Ordering`; it does not hold for a type with `#[derive(Clone)]` and
`#[derive(Copy)]` as two attributes, `#[derive(Clone, Copy)] struct G<T>(T)` at
`G<u32>`, `#[derive(Clone)]` with a hand-written `impl Copy`, a hand-written `Clone`,
a tuple, array or `Option` of such a type, or `core::num::Wrapping<u32>`.

*rustc* (`rustc-src` of the toolchain, commit `0ef1bc386`,
`rustc_ty_utils/src/instance.rs`). `resolve_associated_item` selects the impl
(`codegen_select_candidate`; a candidate whose nested obligations fail is dropped, so
under `T: Copy` the `TrivialClone` impl is), takes the leaf definition of the method
and returns `Ok(None)` if that is not final (a `default` method) and the trait
reference is `still_further_specializable()` (a type parameter, placeholder or
inference variable is left), also in `TypingMode::PostAnalysis`.

Measured with a small `rustc_private` program on 1.100.0 (it walks the MIR from a
function to these calls and prints `codegen_select_candidate` and
`Instance::try_resolve` in `TypingEnv::post_analysis` of that function;
`next_trait_solver_globally()` is false):

| caller | selected impl | `try_resolve` |
|---|---|---|
| `fn f<T: Copy>(s: &[T])`, `s.to_vec()` | `impl<T: Clone> ConvertVec` (`slice.rs:408`) | `Ok(None)` |
| the same, `Box::from(s)` | `impl<T: Clone> CopySpec` (`uninit.rs:12`) | `Ok(None)` |
| `&[i32]`, `to_vec` / `Box::from` | the `TrivialClone` impls (`slice.rs:444`, `uninit.rs:55`) | the bitwise methods |
| `&[Hand]` (`Copy`, hand-written `Clone`) | the `Clone` impls (`slice.rs:408`, `uninit.rs:12`) | the `default` methods, which call `clone()` |

*The driver* (`analysis.rs`) analyses a root in `TypingEnv::post_analysis(root)`;
`resolve` turns `Ok(None)` into `unresolved`, which for a trait method on a type
parameter without a contract is the term `<T as Trait>::m`; `report.rs` prints a
root with terms left as this warning.

*Measured* (a counting allocator, opt-level 0 and 3, an 8-element slice, through
`fn f<T: Copy>(s: &[T]) -> Vec<T>`):

| element type | `to_vec` / `Box::from` / `.into()` |
|---|---|
| `u32` | 1 allocation, 0 `clone()` calls |
| `#[derive(Clone, Copy)]` struct | 1 allocation, 0 `clone()` calls |
| `#[derive(Copy)]` struct with a hand-written `Clone` that allocates | 9 allocations, 8 `clone()` calls |

So these bodies call `clone()` for a `Copy` type that is not `TrivialClone`, which the
present loop of `copy_on_shared` (`out.push(src[i])`, a copy) never does. A driver
rule "`T: Copy` takes the `TrivialClone` implementation" would be unsound and is
rejected.

*This was known where the request came from.* Verigrad's request names it as its
first ground (vstd's `slice_to_vec` comment: "since Rust 1.93, `to_vec` copies
bitwise only for `TrivialClone` types and calls `Clone::clone` for a `Copy` type with
a hand-written `Clone`"), and the fork's reply says that `T: Copy` alone is not
enough, for the same reason. The
fork's specification of `to_vec` charges `seq_clone_allocates` and the bound holds
through `T: FbipClone`. Run here with the fork a330057 (`--no-cheating -V
alloc-check`): the one-line `src.to_vec()` verifies with
`T: Copy + AllocFreeDrop + FipStrictClone`; with `T: Copy + AllocFreeDrop` alone its
`allocates` bound fails; `unsafe impl FbipClone` for a type whose `clone` is
`allocates 1`, or derived, is rejected ("must be checked by Verus and bounded by
`allocates 0`").

*In the plain build nothing says this.* `fip_core::AllocFreeDrop` is implemented for
every type there (`fip-strict`), and this repository has no `Clone` marker. In
Verigrad (`7e24b90`) every `InPlaceKernel` implementation is for `i32` (36) or `f64`
(78), and every call of `copy_on_shared`, `reuse_or_copy` and `consume_and_apply`
from outside `reuse.rs` was read: the buffer is `[i32]` at 4 of the 7 calls in
`verigrad-core/src/main.rs` and `verigrad-py` and at 9 of the 16 in
`tests/fip_runtime.rs`, `[f64]` at the others. Both are `TrivialClone`, so every
instantiation that exists takes the bitwise path; the warning is about the two
generic roots as such.

*Copies that do not go through `clone()`* (probe, `#[fip(1)]`, driver only): for a
generic `T: Copy`, `src.iter().copied().collect()`, `Vec::from_iter(..copied())`,
`with_capacity` + `extend_from_slice` and `with_capacity` + `extend(..copied())` are
errors ("cannot check ..: unresolved": `SpecFromIter::from_iter` or
`SpecExtend::spec_extend`, "not resolvable to one function"); for `i32`,
`src.iter().copied().collect()` is "may allocate 2 time(s)", "may free". None passes.

To reopen: a stable bound that implies `TrivialClone`, or a certified clone marker
that the driver can read in the plain build and use for std's two private traits.

Not covered: Verigrad with a regenerated sidecar, and targets other than the host.
No fixture was added.

**Not checked**: the fork's own test figures (vstd 2179 verified, 5400
`rust_verify_test` tests) were not re-run here.

## Amendment 2026-11-19: re-pin to the fork d13a91f; declared sources and Verus's count

The fork's `fip` branch gained six commits after `a33005760` (notices of the fork to
this repository, 2026-11-18 and 2026-11-19): `b30a4196c` (specifications of
`Vec<T>: From<&[T]>`/`From<&mut [T]>`/`From<&[T; N]>`, derived `clone` checked field by
field), `43cf335fa` and `85396985c` (allocators are the runtime: a bound counts the
program's calls to an allocator, one each, and not what the allocator does;
`BoundedAllocator`, `FipAllocator`, `allocator_max_cost` and `vstd::alloc_heap` are
gone), `587093164` (`deallocates_when` conditions on trait method declarations,
`call_deallocates`, `#[verifier::fip]` closures), `a53bcbae3` and `d13a91fed`
(messages for fip closures in strict functions). The pin moves to
`0.2026.11.19.d13a91f` (`d13a91fed6dc…`); the rustc toolchain (1.100.0) does not change.

**Measured** (x86_64 Linux host, 2026-11-19; the fork built from a clean worktree of
`d13a91fed`, `--features singular`, vstd 2166 verified):

- the fork's own suite (`vargo test --release -p rust_verify_test`): 5372 passing, 63
  ignored (two cvc5 tests need the fork's cvc5 1.3.4, `VERUS_CVC5_PATH`);
- the six regenerated sidecars of this repository differ from the committed ones in
  the stamp line only (no opaque hash changed);
- `just ci` with the new pin and the changes below exits 0: 952 tests pass (951 before,
  plus `verus_xsource_bounds`), 22 Verus result lines, each with 0 errors; against the
  dry run of the pin alone (20 lines) only `valloc` differs (10 → 28 verified, the new
  cases), and the two new lines are `ypool` (4) and `yuser` (8); the upstream strip gate
  passes.

**Allocation model.** The fork now counts what this driver has always counted: a call
of an allocator method or of a declared source is one allocation, and the source's
body is not analysed (README, "Allocation is detected at the allocator entry
points"). This is also FP²'s model (Lorenzen, Leijen and Swierstra, ICFP 2023): its
store holds constructor bindings and reuse credits, its size is the sum of their
sizes (§2.3, Definition 2), allocation is the primitive `alloc k` that adds a credit
(§5, Figure 9), and `fip(n)` allows "at most a constant n constructors" (§1.3); no
memory manager appears in the calculus. The same principle was recorded as the
user's decision in this repository's request to the fork of 2026-11-04
(`2026-11-04-exec-allocation-count-tracking.md`: what happens inside an allocator is
not FIP's concern). The fork's previous model (`a330057` and before) also charged an
allocator's own allocations.

Measured with a probe workspace (an allocator `Twice` in its own crate, whose
`allocate` calls `Global.allocate` twice; a function `hidden` that calls a helper
calling `Twice::allocate`, twice): the driver alone passes `hidden` at `#[fip(2)]` and
rejects it at `#[fip(1)]` ("may allocate 2 time(s)", the chain ending at
`<tw::Twice as core::alloc::Allocator>::allocate`); Verus `d13a91f` proves
`allocates 2` (with the calls in a loop; `a330057` rejects the same source). A
counting `#[global_allocator]` sees 4 global allocations: `fip-testkit` counts the
global allocator, not allocator calls, which README already states ("`fip-testkit`
sees only the Rust global allocator").

**Defect found and fixed: declared sources were not counted by Verus.** A function
declared `fip::alloc_source` (a pool with its own interface, not an `Allocator`, as
in a project that implements its own allocators) is opaque to the driver and one
allocation per call; to Verus it is an ordinary function, and a body that calls no
allocator proves `allocates 0`. Measured before the fix (with the drivers of both
pins, `a330057` and `d13a91f`): a `#[fip]` function calling such a source in a loop
was rejected by the driver alone ("may allocate ∞ time(s) … declared source") and
passed with the crate's Verus sidecar, which gave it `allocates 0`.

Now a source leaf carries the event `VerusUncounted` unless Verus charges at least the
declared count for a call of it, and no function reaching that event takes a Verus
bound (the crate summary lists them: "Verus allocation bounds not taken"). Verus
charges at least `n`:

- for a method of an allocator trait (one call is one allocation to the fork) with
  `n <= 1`;
- for a declared source, when a sidecar lists the function itself with a literal
  `allocates k`, `k >= n`. Verus charges a caller the callee's clause whatever its body
  does (measured: a pool method that allocates nothing, with `allocates 1`, verifies;
  two calls of it verify at `allocates 2` and fail at `allocates 1`, "postcondition not
  satisfied");
- for a source declared on a trait method, the same, on the implementation. Measured
  on the fork: a call Verus resolves to the implementation is charged the
  implementation's own clause, else the declaration's (an implementation may state
  `allocates 0` under a declaration's `allocates 1`, and two resolved calls then verify
  at `allocates 0`); a call through a type parameter is charged the declaration's
  clause, and an implementation's clause above the declaration's is rejected ("this
  `allocates` bound may exceed the trait method's `allocates` bound"); a declaration
  without a clause is not charged 0 (a generic call of it fails `allocates 0`). So an
  implementation that states `k >= n` itself suffices for both kinds of call; one that
  states nothing is listed with `-` and does not count;
- never for a foreign function or a call without MIR here (a dynamic call of a trait
  method), which no sidecar lists.

Fixture `verus_alloc` (crate `valloc`, sidecar regenerated with `d13a91f`; besides the
stamp, only new entries): `Pool::take` (`allocates 0`), `take_counted` (1),
`take_pair` (declared `n = 2`, clause 1), a trait `Backend` with a declared source
`reserve` (`allocates 1`) implemented by `Pool` (stating 1) and `Bare` (stating
nothing); roots `drain` and `drain_three` (through `take`), `two_pairs`, `bare_two`
(through a generic helper) and `bare_two_direct` keep the driver's `∞` and are errors;
`two_counted` and `pool_two` (through the generic helper `reserve_two::<Pool>`) take
Verus's 2 and pass. The other seven expected files change by the new roots only.

Fixture `verus_xsource` (two crates; `just verify-sidecar` exports and compiles `ypool`
by its generator run and verifies `yuser` with `--import ypool`): a source stating 1, a
trait-declared source whose implementation states 1, and a generic source stating 1
(as a slab's `alloc<B: PageBackend>`), each called twice in a loop from `yuser`, give
Verus's 2 (pass); the source stating 0 does not (`drain`, `∞`). Verus charges an
imported callee's clause as a local one: the three roots fail at `allocates 1`
("postcondition not satisfied", measured). Variant `-nodep` (no sidecar for `ypool`):
no bound of `yuser` is taken. The summary groups the bounds not taken by source.

**The allocator trust boundary stays** (sidecars whose sources implement an allocator
trait are not used, nor entries of functions whose MIR names a non-std allocator).
It was added for false facts about memory proved through user allocators (requests to
the fork of 2026-11-08 and 2026-11-09). Re-run with `d13a91f` (the probes with
`BoundedAllocator` removed, `--no-cheating -V alloc-check --compile`): `r4/scribble.rs`
(the allocator keeps the permission of a block it handed out) is rejected by the
hand-out rule; `r5/short.rs` (a block shorter than the layout) by the postcondition
`allocator_block_fits`; `r5/grow_short.rs` and `r5/grow_nocopy.rs` by "`grow` of a
user's `Allocator` must move the old contents"; `r5/freeA.rs` by the precondition of
`raw_ptr::deallocate`; `r2/uaf.rs` and `r2/uaf_grow.rs` because `deallocate` and
`grow` may be called only in a `trusted_call` block; the control `r5/oneslot_run.rs`
verifies and makes 3 allocations and 3 frees. Whether the boundary can be lifted was
asked of the fork (request of 2026-11-19, with the measurements above); until it
answers, a project that uses its own allocators gets Verus bounds through declared
sources that state their clause, and not through `Allocator` implementations.

To reopen: the fork's answer on which facts about a user `Allocator` Verus assumes
(lift or narrow the boundary), and on whether charging a callee's clause, whatever its
body does, is a guaranteed meaning (measured within a crate and across `--import`).

**Not checked**: declared free sources (`fip::free_source`) and Verus's `#[verifier::fip]` (a verified
function without the attribute may deallocate to the fork, so a fip function cannot
call it; not used by the driver, which takes no frees from Verus).

## Amendment 2026-11-20: re-pin to the fork 83fd42f; `encapsulates`, sidecar format 6

**Status:** done on the branch `update/verus-83fd42f` (pin, rename, sidecar format 6, the
`encapsulates` rule, `internal` refused by the generator and the surface gate, a first
stage of deallocation counts in the driver). Open: the finite count through summaries
(below).

The fork's `fip` branch moved by eleven commits: `e93729c25` (`encapsulates alloc(a, d)`),
then `b358424cd` .. `83fd42f3b` (the internal attribute removed, deallocation counting).
Pin: `0.2026.11.20.83fd42f` (`83fd42f3ba97…`), rustc toolchain unchanged (1.100.0).

Checked before the move (clean worktree of `83fd42f3b`, built with `--features singular`,
vstd 2175 verified):

- The diff `d13a91fed..e93729c25` and the diff `e93729c25..83fd42f3b` were read in full.
- The fork's test suite (`vargo test --release -p rust_verify_test`): 5427 passed, 0
  failed, 63 ignored (the fork reports the same numbers); the binaries were rebuilt with
  `--features singular` afterwards and the probes below run on that build.
- Deallocation counting, probes of this repository's own (outside the tree): 15 functions
  with tight `deallocates` bounds (drops of `Box`, nested `Box`, `Option<Box>`, `Vec`
  growth, a discarded `pop`, a tail temporary, overwrites, `String` growth, a
  conditionally initialised local, a field assignment, shadowing, `Rc`, a `return` in a
  loop, two `match` arms) verify, and all 15 fail with each bound lowered by one. A
  counting `#[global_allocator]` measured, per function, exactly the proved number of
  frees. 22 functions that free and state `deallocates 0` (struct and `Drop` values,
  closures, temporaries in arguments, tuples, struct literals, `match` scrutinees, arrays,
  blocks, `mem::replace`, moved-from parameters, partial moves, ..): none verifies.
- Found there, reported to the fork: a function with a `deallocates` bound whose only
  counted drop is the old value of an assignment through `&mut` or to a field
  (`*r = Box::new(1)`, even `*r = 1` for `r: &mut u64`) makes the verifier panic
  ("unknown function … drop_deallocations", `vir/src/poly.rs`); it verifies when the
  crate has another counted drop. A crash, not a wrong result. `core::mem::drop` has no
  specification.
- The hole found at `e93729c25` (a hand-written `#[verus::internal(encapsulates_alloc)]`
  made a recursive function a leaf of `#[verifier::fip(strict)]`) is closed: the
  attribute is "unrecognized" at `83fd42f3b`.

What changed here:

- **Rename.** `call_allocates(f, args)` is now a `bool` ("may allocate"); the count is
  `call_allocations(f, args)`. The specifications of `fip-core`, `fip-strict` and
  `verify/`, the mutation recipes and `verify/strip_alloc.py` use the new name. No
  function of this repository states `deallocates` yet.
- **Sidecar format 6.** A `fn` line ends with the function's `deallocates` bound (the
  spellings of `allocates`) and `encapsulates` or `-`. Format 5 could not tell a
  function with `encapsulates alloc(0, 0)` from one with a proved `allocates 0`
  (measured at `e93729c25`: the generator wrote `- 0` for both), so format 5 sidecars
  are refused.
- **The rule for declared sources** (replaces the rule of 2026-11-19, a literal
  `allocates k >= n` on the source). `encapsulates alloc(a, d)` is the fork's
  declaration for an allocator that does not implement `core::alloc::Allocator`: a
  verified caller is charged `a` and `d`, within the crate and through `--import`, and
  the body is not checked against them. The driver takes a Verus bound through a declared
  source only if a sidecar lists the source with `encapsulates`, `a` the literal
  `n` of `fip::alloc_source(n = ..)` (0 for a pure `fip::free_source`), and `d` the
  literal `n` of `fip::free_source(n = ..)` (0 without the attribute). For a source declared on a
  trait method the implementation carries the clause (the fork rejects `encapsulates`
  on a declaration and checks `a` and `d` against the declaration's bounds). A source
  whose clause states other counts is an **error** on the source: two trusted
  declarations of one function disagree. A source without the clause stays as before:
  no bound is taken through it, and the summary says so.
- **`encapsulates` on a function that is not a declared source.** Verus charges its
  callers the stated counts and does not check the body; the driver analyses the body.
  Its stated count is never taken, and no function reaching it takes a Verus bound.
  Fixture: `valloc::sneak` (`encapsulates alloc(0, 0)`, allocates) called in a loop by
  `via_sneak` (`allocates 0`, verified): the driver keeps `∞`.
- **`verus::internal` refused.** The generator writes no sidecar for a crate whose
  sources have the identifier `internal` anywhere in code, and the surface gate of
  `fip-testkit` rejects it in this repository's verified sources (two mutants in
  `just ci`). The identifier, not the path: `#[verus::r#internal(..)]` and a macro's
  `#[$t::$i(..)]` called with `m!(verus, internal)` reach Verus as the same attribute
  (measured on `83fd42f3b`: "unrecognized internal attribute" for all three spellings),
  the rule `trusted_call` already has. Independent of the fork's fix: those attributes
  are the verifier's input from its own macros, and a hand-written one states what no
  clause was checked for. Not covered: an attribute a dependency's procedural macro
  writes.

Fixtures: `verus_alloc` (`take_counted`, `<Pool as Backend>::reserve`: `encapsulates
alloc(1, 0)`; `take_pair`: declared 2, clause 1, the error; `sneak`, `via_sneak`),
`verus_xsource` (`ypool`: `encapsulates` on its sources, the free source `put` with
`alloc(0, 1)`; `yuser::take_put_twice` takes Verus's 2 through both).

**Deallocation counts, first stage.** The fork proves `deallocates` bounds; the driver
knew a free only as "may free" (`#[fip]` forbids it, `#[fbip]` allows any number).
Added, as an extension of FP² (whose `fbip` bounds allocation only):

- `fip::free_source(n = N)`: `N` deallocations per call (1 without `n`; `n = 0` is
  rejected as `alloc_source(n = 0)` is).
- A count beside the allocation count (`Summary::frees`), on the longest path. One
  deallocation each: a call of a free source, of a deallocating method of an allocator
  trait (`deallocate`; `realloc`, `grow`, `shrink` also allocate one), of a foreign
  `free`/`realloc`. So dropping a `Box` is 1 (its drop glue is analysed down to
  `Global`'s `deallocate`). Any number (`∞`): a free in a loop or in a recursive
  component, a free known only as a witness (a std summary, the summary of an exported
  crate, `fip::cert(frees = true)`, a contract or `param(..)` of an `fbip` function), a
  call of a parameter or a drop of a value of a type parameter.
- The literal `deallocates k` of a sidecar replaces an `∞` count under the conditions
  of `allocates` (non-generic, no `requires`, no `encapsulates`, every panic path an
  allocation failure, nothing reached that Verus counts otherwise); a finite count above
  `k` is kept and reported, as for allocations. The summary counts the bounds taken.
- `fip::mark(kind = "fbip", frees = M)`, written `#[fbip(frees = M)]` with
  `fip-macros`: more than `M` is an error naming the count. Without `frees` nothing
  changes. `frees` on `kind = "fip"` is malformed. An implementation whose mark allows
  more deallocations than its trait method's contract is weaker than the contract.

Fixtures: `alloc_sources` (`free_three` 3 of 3; `free_three_over` 3 of 2; `free_branch`
the longer branch; `free_loop` `∞`; `free_box` 1; `free_box_over` 1 of 0; `free_vec`
`∞`; `frees` on `fip`; `free_source(n = 0)`), `verus_xsource` (`yuser::put_twice`: a
loop the driver counts `∞`, Verus proves `deallocates 2`, taken; `put_twice_over`: 2 of
1), `verus_alloc` (`put_two`: declared 2, clause 1, the error), `clean` (`#[fbip(frees =
1)]` through `fip-macros`).

Open, not done in this change:

- **A finite count through summaries.** Std summaries, exported summaries, certificates
  and contracts carry "may free", not a number, so a function freeing through them is
  `∞` unless Verus proved its bound. A number there changes the summary format (every
  recorded target regenerated), `fip::cert` and the contract language. `fip-macros`
  does not yet generate a Verus `deallocates M` from `#[fbip(frees = M)]`.
- The allocator boundary (`custom_allocator`, the refusal of sidecars of crates
  implementing an allocator trait) is unchanged; the fork's reply of 2026-11-19 says its
  checks now cover such code. To be narrowed with the trusted allocators reported.

## Amendment 2026-11-22: re-pin to the fork 4383ece; the drop of a trait object

**Status:** done on the branch `update/verus-83fd42f`.

**Pin.** `0.2026.11.22.4383ece` (`4383ecedb9e4…`), one commit after `83fd42f3b`: the fork's
fix of the two defects reported on 2026-11-20 (the verifier panic on a function whose
only counted drop is an overwritten value; no specification for `core::mem::drop`).
Sidecars regenerated: stamps only. Checked before the move (clean worktree, `--features
singular`, vstd 2175 verified): the diff `83fd42f3b..4383ecedb` read in full (224 lines);
the fork's tests, 5437 passed, 0 failed, 63 ignored (the fork reports the same); the
reported repro files (`c1`, `c3`, `c7`, `c8`, `d1` verify; `c6`, `v[0] = ..`, is rejected
with "cannot count this drop", as the reply says); the 52 functions that free under
`deallocates 0` or a bound one too low, none verifies; the 15 tight bounds verify and
all fail lowered by one. All on the binaries rebuilt with `singular` after the test run.

**A defect of the driver, found by the same probes: the drop of a trait object.**
rustc's drop shim for `dyn Trait` has no statement (codegen emits the call of the
concrete type's drop glue through the vtable). The driver read that MIR and found
nothing. Measured with the driver of `590ba1c` (the commit before the fix) on the
fixture's new cases: `#[fbip] fn f(b: Box<dyn Obj>) {}` passed although the concrete
type's `Drop` allocates; `#[fbip(frees = 1)] fn f(o: Option<Box<dyn Obj>>) {}` passed
(the box's own deallocation, nothing for the object, whose type may free any number of
times); `#[fbip(frees = 0)] fn f(p: *mut dyn T) { drop_in_place(p) }` passed. Under
`#[fip]` the last one was an error, by accident: the empty shim reads as a call of
itself ("recurses"), which `fbip` allows. The code that reads the shim is older than the
deallocation count (not changed by it); earlier pins were not re-run. Fixed: the drop glue of a `dyn`
type is an unresolved event (`⊤`), as a dynamic call of a method without a contract is.
Fixture `audit_probes` (`drop_boxed_obj`, `drop_obj_in_place`, `drop_opt_obj` are errors,
`borrow_obj` passes). The std summaries of all 11 recorded targets regenerate
unchanged (`just prelint-std-summaries-recorded`). A function that drops a boxed trait object can therefore not be `#[fip]` or
`#[fbip]` for now; Verus rejects the same drop under `allocates` ("the drop of a `dyn`
value cannot be bounded yet").

**What a deallocation bound counts.** As `#[fip]` does for frees, `frees = M` counts
executions that return: a value dropped while a panic unwinds is not counted (measured:
`let r = may_panic(x); forget(b); r` passes `frees = 0`). `strict = true, panic_macros =
false` rejects the panic path itself.

**Limits of the fork measured on this pin** (reported to the fork 2026-11-22; none makes
a wrong result, each rejects code that is fine):

- No `for` loop in a function with a `deallocates` bound or `#[verifier::fip]`
  (`Iterator::next` has no bound), also over a range or a slice. `while` works.
- A closure passed to `Option::map`, `unwrap_or_else`, `ok_or_else`, `and_then`,
  `Result::map` in such a function: the specification counts the drop of the closure,
  which is not defined for a closure type, also one that captures nothing. A lemma over
  `F: Copy` proves it for a closure bound to a local; an inline closure cannot be used.
- `a.min(b)`, `a.max(b)`, `a.clamp(..)` on integers are rejected (also under `allocates
  0`); `core::cmp::min(a, b)` verifies.
- `if let Some(x) = v.pop() { .. }` and `match v.pop() { .. }` with a value that may
  deallocate are rejected ("a temporary value that is moved on some paths only"); binding
  the value first (`let o = v.pop();`) verifies.
- A function that only moves a `Box<dyn Trait>` (returns its argument) is rejected under
  `allocates`.

## Amendment 2026-11-22 (2): re-pin to the fork ac9642e; the edition of a Verus run

**Status:** done on the branch `update/verus-83fd42f`.

**Pin.** `0.2026.11.22.ac9642e` (`ac9642eeb51d…`), six commits after `4383ecedb`. The fork
lifted the five limits reported that morning (`for` loops over ranges, slices and
borrowing iterators, with the counter in the loop invariant; closures without drop glue
handed to `Option::map` and its like; `min`/`max`/`clamp` of integers; the scrutinee of
`if let`/`match`; a `Box<dyn Trait>` that is only moved), and closed two soundness holes
it found on the way, both present at `4383ecedb`, the pin of a few hours: the drop of a
closure's environment by the `FnOnce` shim (a `#[verifier::fip]` function handing a
closure that owns a `Box` to `Option::map` verified), and the compiled body of a
`#[verus_spec(with ..)]` function, which was not compared with the counted drops. This
repository's verified sources have no `verus_spec(with ..)` (searched) and verify
unchanged on the new pin, which rejects the first shape.

Checked before the move (clean worktree, `--features singular`, vstd 2175 verified): the
diff `4383ecedb..ac9642eeb` read in full (3035 lines); the fork's tests, 5454 passed, 0
failed, 63 ignored (the fork reports the same); the 18 repro files of the request (as
the reply says: `a1`–`a4` need the counter in the invariant, `c3` needs `b <= c`); 84
functions that free more than they state (the 52 of before and 32 new ones around the
two holes: closures owning a box through `map`, `then`, a generic `FnOnce` or `Fn`
consumer, a direct call, a closure only dropped; loops; scrutinees with a part left;
`dyn` values dropped on some paths, in a `Vec`, in a closure, by `Option::is_some`):
none verifies. All on the binaries rebuilt with `singular` after the test run.

The same class in the driver: probed and absent. A closure that owns a `Box`, handed to
`Option::map`, `bool::then`, `unwrap_or_else` or a local generic `FnOnce` consumer, or
called by reference and dropped at the end of the scope, counts its one deallocation
(`#[fip]` rejects it, `#[fbip(frees = 0)]` names 1): the driver reads the MIR of the shim
and of the std function.

**The edition of a Verus run (a defect here, found by a review of the reply).** The
workspace's crates are edition 2024. No Verus run of the justfile passed `--edition`,
and Verus's default is an older one (measured: `let gen = 1;` verifies without the flag
and is a syntax error with `--edition 2024`). So Verus verified the sources as written
for another edition than cargo and the driver compile them for. Editions differ in what
a method call resolves to (`into_iter` on a boxed slice) and in where temporaries are
dropped (the tail expression of a block, the scrutinee of `if let`), which the fork's
deallocation count compares with the compiled program. The sidecar recorded neither.
Nothing in the verified sources was found to depend on it (they verify unchanged with
the flag; the sidecars differ in their stamp lines only), but nothing checked it either.

- Every Verus run passes `--edition 2024` (`verus_flags`, the upstream runs);
  `verify/no_cheating_flags.py` requires it, with two mutants.
- Sidecar format 7: the `cfg` line ends with the run's edition. The generator refuses a
  run without `--edition`. The driver uses a sidecar only for a crate compiled for that
  edition: its own session's for the crate being compiled; for a dependency the one its
  package's manifest gives cargo (`[lib] edition`, `[package] edition`, the workspace's
  for `edition.workspace = true`, 2015 without the key), since rustc has no query for
  another crate's edition (a span of another crate reports the edition of the crate
  being compiled). Not found: the sidecar is not used. Format 6 is refused.
- An importing run trusts the imported crate's specifications as verified for that
  crate's edition. The sidecar has an `imported <source> <edition>` line for each
  source of an imported crate (the edition of that crate's own sidecar), and the driver
  uses the sidecar only if each such source's package is compiled for that edition.
- Found on the way: a sidecar listed a source of an imported crate only if a span of
  the run named it. `fip-alloc` imports `fip-strict` and listed none of its sources, so
  a change of `fip-strict` left `fip-alloc`'s sidecar in use although its proofs rest
  on `fip-strict`'s specifications. The generator now lists every source of every
  `--import-sidecar` (hash and edition).
- Fixtures: `verus_sidecar` (`-edition`: the sidecar says 2021), `verus_xsource`
  (`-depedition`: the dependency's manifest says 2021; its sidecar is used neither in
  its own build nor in the dependent's, and the dependent's own sidecar, which imported
  it, is not used either).

**A mutant and the resource limit.** `dedup-no-swap` (`--rlimit 1000`) reports the
intended error, the broken loop invariant, on both pins; on `ac9642e` Verus's search for
a second error then exceeds the limit (also at 2000), which the gate counts as a
failure of the mutant. The mutant now runs with `--multiple-errors 1`. The unmutated
proofs verify within their limits as before. At `--rlimit 2000` the verifier panics after
the two errors ("unexpected output from solver: … expected rlimit-count in smt
statistics", three runs of three); reported to the fork.

**Limits of the fork measured on this pin with `--edition 2024`** (reported 2026-11-22;
each rejects code that is fine, none verifies a wrong bound: the six too-low bounds of
the same shapes fail in both editions):

- A temporary in the tail expression of a function or branch (`peek(&mk())` as the last
  expression) is rejected ("cannot count this drop"): edition 2024 drops it before the
  locals. Binding the result (`let r = peek(&mk()); r`) verifies.
- `if let Some((x, true)) = v.pop() { .. } else { }`, with a part of the scrutinee left
  and an `else`: rejected (the fork's reply predicted it).

## Amendment 2026-11-22 (3): re-pin to the fork f2998b7

**Status:** done on the branch `update/verus-83fd42f`.

**Pin.** `0.2026.11.22.f2998b7` (`f2998b743dde…`), three commits after `ac9642eeb`: the
fork counts the drops of temporaries where Rust 2024 drops them (the tail expression of a
block, the scrutinee of `if let` and `while let`), which lifts the two limits reported
for edition 2024, and warns when `-V alloc-check` runs without `--edition`. vstd is
unchanged; sidecars: stamps only.

Checked before the move (clean worktree, `--features singular`, vstd 2175 verified): the
diff `ac9642eeb..f2998b743` read in full (649 lines); the fork's tests, 5461 passed, 0
failed, 63 ignored (the fork reports the same); the 7 repro files (as the reply says, in
both editions); 102 functions that free more than they state, each with `--edition
2021` and with `--edition 2024` (the 84 of before and 18 new ones around the new scopes:
tail temporaries in a function, a nested block, a `match` arm, a loop body and a closure;
`if let` with a part of the scrutinee left, with and without `else`, as a value, in an
`else if` chain, with `ref`; `while let` with a part left): none verifies in either
edition. The 15 tight bounds verify in both and all fail lowered by one. All on the
binaries rebuilt with `singular` after the test run.

**The mutant and the resource limit, measured on three pins** (`--multiple-errors 8`):
`4383ece` reports two broken invariants at `--rlimit 1000` and at 2000; `ac9642e` and
`f2998b7` report the first and then exceed the limit, and at 2000 the verifier panics
("expected rlimit-count in smt statistics"). A script that reproduces it from this
repository's commit `a124af1` was sent to the fork. The mutant stays at
`--multiple-errors 1`.

**Limits of the fork that remain** (its reply; not re-measured here): a temporary in an
operand of `&&` or `||`; a temporary a `let` keeps alive because its initialiser borrows
it (`let r = &f();`, also through a block's tail, a branch, a field of a literal); a loop
over an owning iterator (`for x in v`) and over iterator adapters; a closure that owns a
value whose drop may deallocate, handed over by value.

## Amendment 2026-11-22 (4): re-pin to the fork 0fa89d0

**Status:** done on the branch `update/verus-83fd42f`.

**Pin.** `0.2026.11.22.0fa89d0` (`0fa89d09bd54…`), one commit after `f2998b743`: the
verifier read Z3's cumulative `rlimit-count` as an integer and panicked once Z3 printed it
as a decimal (past 2^32), the panic the mutant `dedup-no-swap` showed at `--rlimit 2000`.
Resource accounting only; vstd is unchanged; sidecars: stamps only.

Checked before the move (clean worktree, `--features singular`, vstd 2175 verified): the
diff read in full (55 lines, `air/src/smt_verify.rs` and its test); the fork's tests,
5461 passed, 0 failed, 63 ignored, and AIR's, 146 passed (the fork reports the same); the
script sent to the fork: at `--rlimit 2000` the two errors and no panic, at 1000 the same
two errors, with `--multiple-errors 1` the intended error alone; the 102 too-low bounds
in both editions, none verifies; the 15 tight bounds as before.

The fork's finding on the second error's resource limit: the function alone finds both
broken invariants at once; in a run of the whole module the earlier functions leave Z3 in
a state where the search is longer. Nothing to fix there. The mutant stays at
`--multiple-errors 1`.
