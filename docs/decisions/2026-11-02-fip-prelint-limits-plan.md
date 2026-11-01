<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `fip-prelint`: a plan for every remaining limit

**Status:** PROPOSED, 2026-11-02. Nothing here is implemented. The user approves this
plan before any implementation starts. Builds on
`docs/decisions/2026-11-01-fip-prelint.md` (ACCEPTED) and `TODOs/fip-prelint.md`
(open items 2 and 4–8). Code references are to commit `06c99ac`.

## What "complete" means here

Every known limit gets a **decided treatment**: implement, declare (a source-level
contract the driver checks or trusts visibly), or keep as a reported limit with a
reason. It does **not** mean every property becomes decidable. Reachability of a
panic, a function pointer's target in general, or whether an unmarked function "is an
allocator" cannot be decided from MIR. For every such residue the plan says how it
stays visible: `⊤` (an error), a term (a warning), a panic path (a note or an error),
or a statement in the guarantee table. **No item prunes unsoundly.** A fact is used only
if it is proved by the analysis, or if it is a declared contract that is checked at
every analysed use or listed as trusted.

## Governing principle (user, 2026-11-02)

> "Allocation inside the allocator itself is entirely out of scope for the FIP principle."

Consequences used throughout (mainly in L7):

- A function declared as an allocation or free source is an **opaque boundary**. A
  call to it counts as one allocation (or free) at the call site. The driver does not
  descend into its body. Bookkeeping, slab refills, calls to a backing allocator
  (including `__rust_alloc`), loops, recursion, panics and `⊤` inside it are never
  reported against FIP roots, and FIP does not check them.
- The same holds for the global-allocator path. `__rust_alloc*` and an
  `impl GlobalAlloc` reached through it are the allocation. The allocator's own body
  is out of scope. This is already the case for `__rust_alloc*`: they are foreign
  leaves and are never descended into (`tools/fip-prelint/src/analysis.rs:913-931`).
- Allocator internals are not checked for FIP properties. Other mechanisms can cover
  them outside FIP: Verus for verified allocators, Miri and `fip-testkit` counting for
  tested ones. This plan does not extend `fip-prelint` there.

## Measurements behind this plan (2026-11-01, rustc 1.99.1, x86_64 Linux)

The driver was built from `06c99ac` into `/tmp/pd-prelint-target`
(`RUSTC_BOOTSTRAP=1 cargo +1.99.1 build --target-dir /tmp/pd-prelint-target` in
`tools/fip-prelint`). All runs used `FIP_PRELINT_TARGET_DIR` under `/tmp`. Nothing was
written to the repository's `target/`.

**M1. Self-check, notes classified** (`cargo fip-prelint --warn-only --message-format
short` on the workspace). The per-crate summaries are identical to
`tools/fip-prelint/tests/selfcheck.expected`: 43 roots, 3 errors, 1 warning, 44 notes.
The notes break down as follows:

| notes | cause |
|---|---|
| 12 | bounds checks `a[i]`, `b[0]` in `fip_core::slice::swap_lt` (directly and through `compact`, `dedup_by`, `compact_map`, `compact_map_st`, `swap`, and test callers) |
| 11 | `core::panicking::panic_fmt` inside `<[T]>::split_at_mut`, called from `swap_lt` |
| 14 | overflow checks on unguarded arithmetic (real) |
| 6 | `alloc::alloc::handle_alloc_error` (diverges) behind `Box::new` (real) |
| 1 | `assert!(x > 0)` in `strict_gaps::checked_dec` (real) |

The 23 `swap_lt` notes are safe only under the precondition `i < j < xs.len()`. That
precondition is written as a Verus `requires` (`crates/fip-core/src/slice.rs:20-25`),
which the driver never sees. The `TODOs/fip-prelint.md` self-check table still says
"10 bounds / 9 panic_fmt". Those are the counts from before the state-passing
variants; that file's update at lines 248-253 already records 40 → 44.

`FIP_PRELINT_DUMP=1` on `fip-core` shows that the shipped (optimized) MIR of
`split_at_mut` is a body with two calls: `split_at_mut_unchecked` and
`core::panicking::panic_fmt`. Its assert is a branch to a panic call, not an `Assert`
terminator.

**M2. Allocator probe** (`/tmp/pd-allocprobe`, sources in the appendix). Crate `slab`
declares `fip::export` and implements, without `alloc` or `unsafe`, a bump arena
(`Arena::alloc`, `Arena::reset`) and a fixed slab (`Slab::insert`, `Slab::remove`).
Crate `galloc` implements a pure-Rust `GlobalAlloc` over a static buffer and installs
it as `#[global_allocator]`. All roots use plain `fip::mark(kind = "fip")`, except
`arena_loop`, which uses `n = 3`.

| root | intended | driver today |
|---|---|---|
| `arena_once`: `a.alloc(16)` | 1 allocation → error | **passed (false pass)** |
| `arena_loop`: `a.alloc(1)` in `for _ in 0..k`, `fip(3)` | ∞ → error | **passed (false pass)** |
| `arena_reset`: `a.reset()` | free → error | **passed (false pass)** |
| `slab_cycle`: `insert` then `remove` | 1 allocation + free → errors | **passed (false pass)** |
| `control`: `slab::twice` | pass | passed |
| `ffi_malloc`: `extern "C" fn malloc` | allocation | `⊤`: "foreign function `malloc`" (error, never passed) |
| `galloc::boxed`: `Box::new` under the custom global allocator | 1 → error | 1 allocation (`__rust_alloc_zeroed`) → error |
| `galloc::direct_global_alloc`: `BUMP.alloc(layout)` | 1 → error | **passed (false pass)**: the pure-Rust `GlobalAlloc::alloc` body is analysed as allocation-free |
| `galloc::direct_system_alloc`: `System.alloc(layout)` | 1 → error | `⊤` through `libc::unix::{malloc, calloc, posix_memalign}` (3 errors) |

Summary lines: `app` 6 roots, 5 passed; `galloc` 3 roots, 1 passed. That makes five
false passes in all.

**M3. Limits probe** (crate `limits` in the same workspace). Roots use
`strict = true, panic_macros = false` where panics are in question.

| case | driver today |
|---|---|
| `xs[usize::from(i)]`, `xs: &[u8; 256]`, `i: u8` | bounds check reported (call result unknown) |
| `if i < w.len() { w.get()[i] }` through a wrapper's methods | bounds check reported |
| `for i in (0..xs.len()).rev() { xs[i] }` | bounds check reported |
| `for i in 0..=xs.len() - 1` after `is_empty()` | overflow check on `- 1` and bounds check reported |
| `for (i, x) in xs.iter().enumerate() { ys[i] }` with `ys.len() >= xs.len()` | bounds check, and overflow check in `Enumerate::next`, reported |
| `xs.iter().zip(ys)` | `core::panicking::panic` inside `Iterator::zip` reported (cause not yet located) |
| `g: fn(u8) -> u8; g(1)` | `⊤`: "call through a function pointer" |
| `s: &dyn Shape; s.area()` | `⊤`: "dynamic call ... (trait object)" |
| `drop(v)` for `v: Vec<T>` | warning: term `drop(Vec<T>)` |
| `format!("{x}")` | 1 allocation, plus `⊤`: `format_inner` has no MIR |
| `Cell::set(get().wrapping_add(1))` | passed |
| `*c.borrow_mut() = 1` on `RefCell` | panic path `panic_already_borrowed`, plus **"may free: drop of `RefMut<'_, u32>`"**. The free is spurious: `RefMut`'s drop deallocates nothing |
| `rc_drop(r: Rc<u32>)` | may free (real: the last reference frees) |

**M4. `-Zbuild-std`** (`RUSTFLAGS=-Zalways-encode-mir`,
`-Zbuild-std=core,alloc,std,panic_unwind,panic_abort --target x86_64-unknown-linux-gnu`,
same `limits` crate). Took 55.9 s cold, including checking `core`/`alloc`/`std`.

- `format!` becomes 2 allocations plus "may free" (`__rust_realloc`).
- The `⊤` moves deeper: `<dyn core::fmt::Write>::write_str` (virtual) and
  `core::fmt::rt::Argument::fmt` (a function pointer).
- New panic paths appear that are absent from the shipped `std`, for example an
  overflow check in `<BorrowRefMut as Drop>::drop`. The cause: `std` rebuilt in the
  dev profile has overflow checks, so what is analysed is not the `std` that ships.
- `limits`: 21 errors instead of 15.

**M5. Stack sizes.** `rustc +1.99.1 -Zemit-stack-sizes --emit=obj` works, and
`llvm-readobj --stack-sizes` reads the section. For a 3-function test file:

| function | opt-level 0 | opt-level 2 |
|---|---|---|
| `leaf` | 296 B | 0 B |
| `mid` | 104 B | 8 B |
| `top` | 8 B | 8 B |

Frame sizes depend on the build, and `cargo check` emits no objects.

**M6. Other target.** `cargo fip-prelint --target wasm32-unknown-unknown` on the
workspace took 1.80 s. Its per-crate summaries are identical to x86_64 (43 roots,
3 errors, 1 warning, 44 notes). Installed targets for 1.99.1:
`x86_64-unknown-linux-gnu` and `wasm32-unknown-unknown`.

## The limits, one by one

Effort: **S** ≤ 0.5 day, **M** 1–3 days, **L** 3–5 days, for one agent. These are
estimates (unmeasured).

### L1. Facts that hold only through a caller's guard or a callee's contract

**Current.**

- The value analysis is intraprocedural. Its entry state holds type bounds only
  (`tools/fip-prelint/src/value.rs:680-697`).
- A call forgets its destination (`value.rs:1512-1514`). The only exception is the
  `Range` contract (`value.rs:1459-1511`).
- The analysis runs only on bodies with an `Assert` (`value.rs:524-535`).
- Its result covers `Assert` blocks only (`value.rs:1623-1644`), so a panic *call* on an
  infeasible branch (the `split_at_mut` case, M1) is never dropped.
- Verus `requires` are stripped in driver builds: `verus_keep_ghost` is never set
  (`tools/fip-prelint/src/main.rs:53-65`).
- Measured cost: 23 of 44 notes (M1).

**Proposal.** Three parts, applied in this order.

1. **Feasibility of every block** (prerequisite, see L11). The value analysis returns,
   per block, whether any feasible path reaches it. `scan_body` drops every site in an
   infeasible block: calls, panics and allocations alike.
2. **Context-sensitive callee analysis.** At a call, project the caller's state at
   the call site onto the callee's parameters: integer arguments, slice lengths,
   constants. Analyse the callee's body with that projected state as its entry state.
   - Nodes become `(Instance, Context)`, where `Context` is a canonical closed
     difference-bound matrix over the parameters.
   - Results are memoized per `(Instance, Context)`.
   - Depth limit: 3 nested contexts. Then the empty context, which is today's
     behaviour.
   - Recursive components always get the empty context, so the fixpoint stays as it is.
   - Contexts are applied only to callees with MIR. This covers `split_at_mut` (M1):
     with `j < len`, its panic branch is infeasible.
3. **Declared preconditions.** A new mark,
   `#[cfg_attr(fip_prelint, fip::requires(i < j, j < xs.len()))]`. Its grammar is a
   conjunction of linear comparisons between integer parameters, `p.len()` of slice
   parameters, and constants. Anything else is a parse error, never silently dropped.
   - **Assume:** the conjuncts are added to the function's entry state.
   - **Guarantee:** at every analysed call site, the caller's state must entail them.
     If it does not, the call site gets a panic path "precondition `i < j` of
     `swap_lt` not established". It is a note, or an error under
     `panic_macros = false`.
   - **Reifying** a function with `fip::requires` into a function pointer, or passing
     it as a closure value, is a panic path at the reification. Indirect callers
     cannot be checked.
   - **Emission.** `fip-macros` (`#[fip]` sits above `verus_spec`, see
     `crates/fip-macros/src/lib.rs:33-35`) translates the subset of the sibling
     `verus_spec(requires ..)` that fits the grammar. `old(xs)@.len()` maps to
     `xs.len()`, chained `a < b < c` splits into conjuncts, and everything else is
     left out. Leaving a conjunct out means assuming less, which is sound.
   - **Unmeasured:** whether the attribute macro receives the following
     `#[cfg_attr(verus_keep_ghost, ..)]` tokens unexpanded when the cfg is off. This is
     the first probe of the item. If it does not, the mark is written by hand, and
     `fip-macros` checks that each `fip::requires` conjunct appears textually in the
     Verus `requires` (drift guard).

**Alternatives considered.**

- Reading the Verus `requires` from the source text in the driver: rejected. The
  attribute is gone from HIR, and a Verus-syntax text parser is fragile.
- `debug_assert!` as a precondition: rejected. At opt-level 0 it is itself a panic
  path, so it would only trade one panic for another.
- `core::hint::assert_unchecked(c)` as a fact: accepted as a small extension, on the
  same footing as `UB_CHECK_MARKERS`: it is UB if false, and an `unsafe` contract.
  It is unusable in `forbid(unsafe_code)` crates.
- Full inlining: rejected. The graph would blow up, and contexts give the same facts.

**Soundness.**

- Contexts only add facts that hold at the call site.
- Preconditions are assume-guarantee. Every analysed call site carries the
  obligation, and indirect uses are reported.
- A root with `fip::requires` is checked under its precondition. Its verdict text
  says "under `fip::requires(..)`", and the README row changes accordingly.
- Callers in crates not analysed by the driver are not checked. That matches
  Verus's model and is stated.

**Never fully solved.** Nonlinear, quantified or heap-dependent preconditions, and
guards the zone domain cannot express. Those panic paths stay reported.

**Tests.**

- New fixture `preconditions`:
  - a private callee whose guarded caller passes and whose unguarded caller is
    reported at the call site;
  - a pub callee with `fip::requires`;
  - a reified function with `requires`, reported;
  - a malformed `requires`, an error;
  - a `split_at_mut` call under `j < len`, which passes, and without the guard,
    which is reported.
- Unit tests for context canonicalisation.
- `selfcheck.expected` and the M1 table are updated with before/after counts. The
  prediction (unmeasured) is that most of the 23 `swap_lt` notes go. `rotate3`'s
  `swap(&mut xs, 0, 2)` on `[u8; 3]` additionally needs the length of an unsized
  array reference (`Unsize` coercion → constant `len`), which is added here.

**Effort.** L (4–5 days). Depends on L11 and L2.

### L2. Values returned by calls are unknown

**Current.** A call forgets its destination (`value.rs:1512-1514`). Only
`Range::into_iter`/`next` are modelled. Measured in M3: `usize::from(i)`,
`w.len()`/`w.get()`, `is_empty()`.

**Proposal.** **Return summaries** in the value domain, computed bottom-up from the
callee's MIR when it is available, with a small audited table as fallback.

- A summary relates the return value (or `len` of a returned slice, or of fields of a
  returned tuple) to parameters and to **stable access paths**.
- An access path `(*p).f.g` through a shared reference `p: &T` is a tracked value
  only when `T: Freeze`, meaning no `UnsafeCell` (`Ty::is_freeze`). The pointee then
  cannot change while the borrow is live. This is the same rule the value analysis
  already applies to shared borrows (`value.rs:29-33`).
- Needed transfer functions:
  - `Rvalue::Aggregate(RawPtr, [data, meta])` gives `len = meta`
    (`from_raw_parts{,_mut}`, `split_at_mut_unchecked`);
  - tuple fields of slice pointers;
  - `IntToInt` casts that widen (`usize::from(u8)`).
- **Table vs MIR.** MIR first, because it is not trusted. The table only for
  functions without MIR and intrinsics. Each entry cites the `core` documentation and
  has a differential unit test that runs the real function on boundary inputs.

**Soundness.**

- A summary is computed by the same sound analysis.
- Table entries are trusted claims listed in `fip_lint_rules::mir`, like the
  intrinsic table today.
- An unknown callee keeps today's behaviour: the destination is forgotten.

**Never fully solved.** Results that depend on mutable heap state, interior
mutability, nonlinear arithmetic, or callees without MIR and outside the table. Those
stay unknown, and their asserts stay.

**Tests.**

- Fixture `guards` gains three passes (`usize::from`, wrapper `len`/`get`,
  `!is_empty()` before `len() - 1`) and controls: a `Cell`-backed `len` must stay
  reported.
- Unit tests for every table entry.

**Effort.** L (3–4 days). Depends on L11.

### L3. Iterator adapters are not modelled

**Current.** Only `Range<integer>` through `into_iter`/`next` (`value.rs:1459-1511`).
Measured in M3: `rev()`, `0..=n`, `enumerate`, `zip` are all reported.

**Proposal.** **Iterator contracts** in the value analysis, each with an abstract
"remaining" value `rem(it)`:

| iterator | `next` contract |
|---|---|
| `RangeInclusive<int>` | `start`, `end`, `exhausted`; yields values in `start..=end` |
| `Rev<Range<int>>` | `next_back`: yields `end - 1`, decrements `end` while `start < end` |
| `slice::Iter{,Mut}` | `rem = len(xs)` at creation; `next` yields while `rem > 0` and decrements it |
| `Enumerate<I>` | `count + rem(I) = rem₀(I)`; yields `count < rem₀(I)` with the item |
| `Zip<A, B>` | `rem = min(rem(A), rem(B))`, two difference constraints |
| `StepBy`, `Take`, `Skip` | added only if a fixture needs them |

The `core::panicking::panic` inside `Iterator::zip` (M3) is investigated with the dump
before the contract is written. If it is a reachable `std` panic, it stays.

**Soundness.** Contracts are trusted models of `core` code, identified by lang item or
by resolved path, never by name alone. Each has a differential test that iterates the
real adapter and checks the contract's invariants. Unknown iterators keep today's
behaviour.

**Never fully solved.** User iterators, data-dependent adapters (`filter`,
`take_while`), and iterators over shared mutable state. Their asserts stay.

**Tests.** Fixture `guards` gains `rev`, `0..=n-1` (guarded), `enumerate` over a
longer slice, `zip`; each also has a reported off-by-one control.

**Effort.** M (2–3 days). Depends on L2 (the contract table and test harness).

### L4. Function pointers and `dyn` calls are `⊤`

**Current.**

- Virtual calls are `⊤` (`analysis.rs:828-831`), and so are function-pointer calls
  (`analysis.rs:1195-1197`).
- A `param(g = K)` whose `g` is not a generic type is `⊤` at every call site
  (`analysis.rs:1306-1312`).
- Measured in M3. Fixture `param_bounds` covers `fn_pointer`.

**Proposal**, in increasing reach.

1. **Intraprocedural devirtualisation.** A function pointer that is a local
   assigned, on every path, from a `ReifyFnPointer`/`ClosureFnPointer` cast of one
   `FnDef` resolves to that function. A `&dyn Trait` local that comes on every path
   from an `Unsize` coercion of one concrete type resolves the method for that type.
   This is a sound must-analysis: one origin on all paths, otherwise `⊤`.
2. **Declared bounds on function-pointer and `dyn Fn*` parameters.** `param(g = K)`
   accepted for `g: fn(..)`, `g: &dyn Fn*(..)`, `g: &dyn FipFn<..>`. Inside, the
   call is the term `alloc(g)`, instantiated with `K` as for generic parameters. At
   each call site, the argument must be resolvable by (1), else `⊤` at the call site.
   This moves the `⊤` to where the value is created, as for generic parameters
   (2026-11-01 amendment).
3. **Contracts on trait methods** (`fip::mark` on a trait method declaration, for
   example `fn area(&self) -> u32;`). A `dyn` call of a marked method costs the
   declared bound, a trusted value at the call site. Every impl of the method is
   checked against the contract as a root, in the crate that contains the impl.
   - Closing the world: in every primary crate the driver enumerates
     `tcx.all_impls(trait)` over the whole crate graph.
   - An impl in a crate without usable MIR (pass-through) is `⊤`, reported at the
     crate summary ("impl of a contracted trait in an unanalysed crate").
   - Unmarked trait methods stay `⊤` on `dyn` calls.

**Alternative rejected: closed-world candidate sets without contracts** (all
address-taken functions of a matching signature, all impls in analysed crates). Such a
set is complete only if every crate in the graph is analysed, and reifications in
pass-through crates and in `std` (for example `fmt::Argument`'s function pointer, M4)
are invisible. It is unsound in a library context.

**Soundness.**

- (1) is a must-analysis.
- (2) and (3) are assume-guarantee, with the guarantee checked at every analysed
  creation site or impl.
- Unanalysed impls and unresolvable creation sites stay `⊤`.

**Never fully solved.** Function pointers loaded from data (tables, struct fields,
statics, FFI), and `dyn` values from unanalysed crates without a contract. They stay
`⊤` (an error).

**Tests.**

- Fixture `param_bounds`: `fn_pointer` gains a declared-bound variant that passes and
  a data-loaded pointer that stays `⊤`.
- New fixture `indirect`: local reify (pass), local `dyn` coercion (pass), a
  contracted trait with a good and a bad impl, and an impl in a pass-through
  dependency (`⊤`).

**Effort.** L (3–4 days). No dependency; before L6.

### L5. Drops of generic values are terms or warnings

**Current.**

- A `Drop` of a type that mentions a generic parameter is a term `drop(..)`
  (`analysis.rs:1005-1017`).
- Drop glue of a generic type called directly is `⊤` (`analysis.rs:833-836`).
- Terms are warnings (`report.rs:313-342`).
- Measured: `drop(Vec<T>)` is a warning (M3). The self-check's warning is
  `Slot::<T>::put_twice` (`drop(T)`).

**Proposal.**

- Analyse the drop glue of a generic type **structurally** in the root's typing
  environment. The glue shim's calls (`<Vec<T> as Drop>::drop`, `<RawVec<T> as Drop>::drop`)
  are resolvable with `T` as a parameter, and are analysed like any callee.
- Only the drop of a bare parameter, `drop_in_place::<T>` or `[T]`, stays the term
  `drop(T)`.
- So `drop(Vec<T>)` becomes "may free" (deallocation reached) plus `drop(T)`. `Option<T>`
  stays `drop(T)` only.
- A shim that cannot be built for the polymorphic type stays `⊤`.

**Soundness.** The glue is the code that runs. Terms remain where the instantiation
decides, and `param(g = K)` keeps instantiating `drop(F)` with 0 (`analysis.rs:183-213`).

**Never fully solved.** `drop(T)` for a bare `T`: whether it frees depends on the
instantiation. It stays a warning at the generic root and is checked at each
instantiation (as now).

**Tests.**

- Fixture `generics` gains `drop(Vec<T>)` (error: may free), `drop(Option<T>)`
  (warning), and `Box<T>` (error).
- `selfcheck.expected` should keep `put_twice` as a warning (unmeasured).

**Effort.** M (1.5–2 days), together with L12. Depends on L7.

### L6. `format!` and other `std` functions without MIR are `⊤`

**Current.** A `std` function that is neither generic nor `#[inline]` has no MIR, and
is `⊤` (`analysis.rs:944-950`). Measured in M3 (`format_inner`) and M4.

**Options.**

| option | result |
|---|---|
| (a) hand-written summary table | trusted, version-specific, error-prone for `fmt` (it calls user `Display` impls through function pointers) |
| (b) `-Zbuild-std` at analysis time | measured in M4: 55.9 s cold. It analyses a dev-profile `std` that is **not** the one that ships (extra overflow-check panics), and it moves the `⊤` to `dyn Write` and function pointers (L4) rather than removing it |
| (c) `-Zalways-encode-mir` for the shipped `std` | impossible: the shipped `std` is prebuilt |

**Decision.**

- **Generated `std` summaries.** A maintainer-run mode, `cargo fip-prelint --std-summaries`,
  analyses a `-Zbuild-std` build with the **release profile settings of the shipped
  `std`** (`-Copt-level=3`, no overflow checks, no debug assertions). The build is
  pinned to the driver's toolchain.
- It writes one summary per non-generic, non-inline public `std`/`alloc`/`core`
  function reached from the fixtures and the workspace: bound, free, panic, `⊤`
  leaves, and **open indirect calls** expressed as terms over the call site's
  arguments. Example: `core::fmt::write(out, args)` becomes
  `∞·alloc(<dyn Write>::write_str of out) + Σ alloc(<Tᵢ as Display>::fmt)`, resolved
  in the caller from the `Argument::new_display::<Tᵢ>` constructions in its MIR, or
  `⊤` if not resolvable.
- The file (`tools/fip-prelint/std-summaries/<rustc-version>.txt`, plain text, no
  dependencies) is a sidecar in the sense of L10e. It carries the rustc version and
  the `std` source hash, and is used only where MIR is missing. A version mismatch
  means it is not used (`⊤`).
- Option (a) is rejected. Option (b) at analysis time is rejected, because of cost
  and because it analyses a different `std`.

**Soundness.** Summaries are produced by the same analysis on the same source and
settings, so they are claims with provenance. `⊤` leaves inside them propagate.

**Never fully solved.** Formatting through user impls that are `⊤` themselves, and any
`std` function not covered by the generated file. Both stay `⊤`. `format!` always
allocates (a `String`), so FIP roots cannot use it whatever the summary says.

**Tests.**

- Fixture `std_summaries`: `write!` into a fixed buffer through a local `Write` impl
  passes; `format!` is a violation without `⊤`; a stale-version file is ignored (`⊤`).
- Unit test: the file's parser.

**Effort.** L (3–4 days). Depends on L4 (indirect calls) and L10e (format).

### L7. User-declared allocation and free sources

**Current.**

- Allocation means only the entry points in `fip_lint_rules::mir`
  (`crates/fip-lint-rules/src/lib.rs:190-208`), matched in `analysis.rs:892-931`.
- Every other function with MIR is descended into.
- The only names allowed under `fip::` are `export` and `mark`
  (`tools/fip-prelint/src/marks.rs:18`).
- Exported crates contribute only `fip::mark` (`analysis.rs:417-423`).
- Measured (M2): **five false passes**. A pure-Rust arena or slab in an exported
  crate, and a direct call of a pure-Rust `GlobalAlloc::alloc`.
- Foreign `malloc`, and `System.alloc` through `libc`, are `⊤`: errors, never passes.

**Proposal.**

1. **Marks.**
   - `#[cfg_attr(fip_prelint, fip::alloc_source)]`: 1 allocation per call.
   - `fip::alloc_source(n = N)`: `N ≥ 1` per call. `n = 0` is an error, because it
     would be an escape hatch that claims "allocation-free".
   - `#[cfg_attr(fip_prelint, fip::free_source)]`: a possible free.
   - Both on one function means reallocation: one allocation plus a free, like
     `REALLOC_ENTRY_POINTS`.
   - Allowed on functions, inherent and trait-impl methods, **trait method
     declarations** (they then apply to every impl, and an unresolved
     `<T as Trait>::m` on a generic parameter becomes the declared event instead of
     a term), and **foreign function declarations** in `extern` blocks.
   - Rejected anywhere else, and with any other key. Validation is in
     `validate_tool_attrs` (`report.rs:175`).
2. **Opaque boundary** (user principle). `classify_item` checks for a source before
   any table lookup and before using MIR. A marked instance is a `Leaf` with exactly
   the declared events: no descent, no panic, no `⊤`, no recursion, no `param(..)`
   call sites from inside it. Marks are read from the local crate and from every
   crate declaring `fip::export`. `Crates::new` reads them next to `fip::mark`. In
   pass-through crates the `cfg_attr` is inactive, so there are no marks there: those
   crates are `⊤` anyway.
3. **Sources by trait, without marks.**
   - Every method of an impl of `core::alloc::GlobalAlloc` is a source: `alloc` and
     `alloc_zeroed` allocate, `dealloc` frees, `realloc` does both.
   - Likewise the unstable `core::alloc::Allocator`: `allocate` and
     `allocate_zeroed` allocate, `deallocate` frees, `grow`, `grow_zeroed` and
     `shrink` do both.
   - Resolved instances are matched by trait `DefId` (`trait_of_assoc` of the impl
     item), never by name.
   - This fixes `direct_global_alloc` and `direct_system_alloc` (M2), and is the
     principle applied to `impl GlobalAlloc`.
   - The `Vec` path, `<Global as Allocator>::allocate` and then `__rust_alloc*`,
     counts 1 either way. That `selfcheck.expected` is unchanged is a prediction,
     verified in the change.
4. **Foreign allocation table.** A new table, `FOREIGN_ALLOC_SYMBOLS`, of C symbols:
   `malloc`, `calloc`, `aligned_alloc`, `posix_memalign` and `memalign` allocate;
   `free` frees; `realloc` and `reallocarray` do both. It applies **only to foreign
   items** (`tcx.is_foreign_item`), so that a Rust function named `malloc` is not
   matched. Other foreign functions stay `⊤` unless marked (item 1).
5. **`#[fip]` (any `fip::mark`) on a source is an error.** Decision: reject, do not
   ignore.
   - Under the principle the body is out of scope, so a verdict on it is either
     vacuous (body skipped) or contradictory. Callers count the function as N
     allocations while its own `#[fip]` would claim 0.
   - Ignoring the mark would let `fip-macros` print a `# FIP` doc section for a check
     that never ran.
   - The same error applies to `fip::mark` on `GlobalAlloc` and `Allocator` impl
     methods.
   - Plain builds are unaffected. `fip-macros` keeps its own token-level rules.
6. **Transparency.** Source marks are trusted declarations: marking a non-allocator
   hides its body. The per-crate summary note gains "N declared sources", and
   `FIP_PRELINT_DUMP=1` lists every source used by a root, with its location.
7. **Optional, later: sources in crates.io dependencies.** These are pass-through
   and `⊤` today. A primary crate may declare
   `#![cfg_attr(fip_prelint, fip::extern_source(alloc = "bumpalo::Bump::alloc"))]`
   by resolved path. Since the body would not be analysed anyway, this only turns a
   `⊤` into a declared event. It is gated on a real use case.

**Soundness**, under the principle.

- A source mark only **adds** events at call sites (allocation ≥ 1, free) and
  **removes descent** into a body the principle puts out of scope.
- Costs at call sites go through the existing path, loop and SCC rules, so a source
  in a loop is `∞`.
- Nothing in scope is lost: what is dropped (events inside the allocator) is exactly
  what the principle excludes.
- The trait rule and the foreign table make fixed, audited boundaries, not user
  claims.
- `__rust_alloc*` stays a leaf as today. Reaching an `impl GlobalAlloc` through it is
  impossible in MIR, because the shim is a foreign symbol.

**Never fully solved.**

- An **unmarked** pure-Rust allocator. Whether "write into a buffer and advance an
  index" is an allocation is a question of intent, not of semantics. No MIR property
  separates it from ordinary buffer use, so no `⊤` or warning can be raised soundly
  without flooding.
- It stays a **declared assumption**. The README guarantee row and the
  `fip::export` contract change to: "allocation = global-allocator entry points,
  `GlobalAlloc`/`Allocator` impl methods, foreign allocation symbols, and functions
  declared `fip::alloc_source`/`fip::free_source`. A crate that declares
  `fip::export` and hands out memory from its own pools must mark them."
- The five M2 cases become a fixture, so the documented residue is pinned. The
  unmarked arena stays an expected "passed", with a comment saying why.

**Tests.** New fixture `alloc_sources`, built from the M2 probe:

- marked arena:
  - `arena_once`: error, 1 allocation;
  - `arena_loop`: `∞`;
  - `arena_reset`: may free;
- slab:
  - `slab_cycle`: 1 allocation plus free;
  - the same under `fbip`: free allowed, allocation not;
- unmarked arena: pinned pass, with the documented limit;
- a source whose body calls `Box::new` twice in a loop and recurses: callers count 1,
  and nothing from the body is reported;
- `direct_global_alloc` and `direct_system_alloc`: 1 allocation each;
- `ffi_malloc`: 1 allocation;
- an unknown foreign function: `⊤`;
- a marked foreign function: counted;
- a trait-declared source called on a generic parameter: counted, not a term;
- `#[fip]` on a source: error;
- `alloc_source(n = 0)`: error;
- an unknown key: error.

Unit tests for the mark parser.

**Effort.** M (2 days). No dependency. **First in the order**, because it is the only
measured false pass.

### L8. Uniqueness and interior mutability (`Cell`, `RefCell`, `UnsafeCell`)

The label "F4" does not occur in the repository (searched all `*.md` and `*.rs`). It
is read here as FP²'s uniqueness condition: an owned constructor is unique, so its
cell may be reused in place.

**Current.** `fip-prelint` checks no uniqueness or aliasing property. Interior
mutability matters to it only for soundness of the value analysis: places with
`UnsafeCell` are never tracked through shared borrows (`value.rs:29-33`). Measured in
M3:

- `Cell` code passes;
- `RefCell::borrow_mut` is a reported panic path (`panic_already_borrowed`);
- dropping an `Rc` is a "may free" (real);
- dropping a `RefMut` is a spurious "may free". This is a precision bug, handled in
  L12, not a uniqueness question.

**Decision: out of scope for `fip-prelint`.**

1. Rust's ownership and borrow checking already give uniqueness of owned values and
   `&mut` statically. The reuse primitive `fip_alloc::refill` takes its `Box` by
   value (`crates/fip-alloc/src/lib.rs:49-54`).
2. Where uniqueness is dynamic (`Rc`/`Arc`, `RefCell`), its FIP-relevant effects are
   already observed:
   - `Rc::new` is an allocation;
   - the last drop is a possible free;
   - a failed dynamic borrow is a panic path.
3. `UnsafeCell` aliasing is a question of undefined behaviour, which belongs to Verus,
   Miri and the `unsafe` audit (`fip_strict::certs`). A MIR heuristic cannot decide it.

**Tests.** The M3 cell cases become fixture `cells`, so that today's behaviour stays
pinned. The `RefMut` case flips to "passed" when L12 lands.

**Effort.** S (0.5 day, fixture and README sentence).

### L9. Stack: no byte bound, only acyclicity

**Current.**

- The driver reports recursion: SCC witness at `analysis.rs:1621-1626`, error for
  `fip` at `report.rs:281-286`. `fbip` allows it.
- No size is claimed (`README.md:46`, `docs/decisions/2026-10-31-stack-bound.md`).

**Proposal: a separate build mode, `cargo fip-prelint --stack`.**

- It runs `cargo build` (not `check`) with the user's profile plus
  `-Zemit-stack-sizes` into its own target directory. The driver codegens there and
  records `tcx.symbol_name(instance)` for every explored instance.
- After the build, a dependency-free ELF reader in the tool parses `.stack_sizes`
  from the objects.
- The bound of a root is the longest path over its acyclic instance graph, summing
  frame sizes:
  - An instance without an emitted symbol (inlined everywhere) counts 0. Its frame is
    part of its callers' frames, and its own callees remain edges in the graph, so
    this over-approximates.
  - A symbol emitted in several codegen units counts its maximum.
  - `dyn`/function-pointer edges are `⊤` (L4).
  - Non-generic precompiled `std` functions have no `.stack_sizes`, so they are `⊤`
    unless L6's `std` build is reused.
  - Codegen-introduced calls (`memcpy`, `memset`, `__rust_probestack`,
    `compiler_builtins`) need a table of leaf runtime functions with sizes measured
    the same way.
  - Panic and unwind paths are excluded, and the claim says so.
- The result is reported per root as "stack ≤ B bytes for this build (target,
  profile)" or "⊤".

**Alternative rejected: summing MIR local sizes per frame.** Not a bound: spill slots,
argument areas and alignment are added by LLVM.

**Soundness and claim level.** It is a measured bound **for the built artefact**, not
a proof. It trusts LLVM's frame-size report, which is static. Rust on stable has no
dynamic `alloca`, and crates enabling `unsized_fn_params`/`unsized_locals` are
rejected. M5 shows that the number is meaningless for any other opt-level or target,
so it is never reused across builds.

**Never fully solved.** `⊤` edges, precompiled code without stack sizes, signal or
interrupt context, panic machinery. All are reported as `⊤`, or excluded by statement.

**Tests.**

- Fixture `stack`: a 3-level chain with known arrays; the bound is ≥ the sum of the
  `llvm-readobj` sizes, checked in the test with the system `llvm-readobj` if present
  (skipped otherwise, never faked).
- A recursive root gives no bound.

**Effort.** L (4–5 days). Depends on L4, and on L6 for `std` frames.

### L10. Toolchain, platform and process limits

The current state of each:

- the driver is pinned to 1.99.1 and `rustc_private`
  (`tools/fip-prelint/rust-toolchain.toml`, `src/bin/cargo-fip-prelint.rs:18`);
- measured only on x86_64 Linux (`TODOs/fip-prelint.md:281-282`);
- export is detected by crate-root text (`main.rs:193-199`), over the whole file,
  comments included;
- the 7 behaviour `compile_fail` examples are not run through the driver
  (`TODOs/fip-prelint.md:283-285`);
- sidecars are deferred (decision record, item 7).

Treatments:

- **a. Pinning.** Kept by decision: MIR and `rustc_private` are unstable, and Verus
  fixes the toolchain.
  - Add a `just prelint-repin <version>` checklist recipe that reruns the decision
    record's probes, the entry-point dump, and every fixture.
  - "What would reopen this" stays the trigger.
  - Never fully solved: no stable MIR export exists.
  - Effort S.
- **b. Platforms and targets.**
  - Measured: `wasm32-unknown-unknown` gives identical summaries (M6).
  - Add a `just prelint` step that checks the workspace for every installed 1.99.1
    target, so that `cfg(target_arch)` code (`fip-arch`) is analysed per target.
  - Run on an aarch64 Linux and a macOS host when available, and record the results.
    Until then the README keeps "measured on x86_64 Linux".
  - `LD_LIBRARY_PATH` is Linux-specific. The rpath (`build.rs:19`) covers ELF; macOS
    needs `DYLD_FALLBACK_LIBRARY_PATH`, which is unmeasured.
  - Effort S, plus host access.
- **c. Export detection.**
  - Failure modes, from the code:
    - text in a comment means driver flags without an active attribute, so the crate
      is not exported: `⊤` downstream with a misleading "does not declare" message;
    - an attribute produced by a macro or `include!` is not detected: pass-through,
      `⊤`.
  - Both are sound: `⊤`, or the `export_unencoded` hard error.
  - Fix: parse only the crate root's inner attributes with `rustc_parse` in the
    driver process. The parser is already linked, and comments are excluded.
  - Keep the text test only as a fallback if parsing fails. Add a fixture with
    `fip::export` in a comment.
  - Macro-generated crate attributes stay undetectable before expansion. They are
    documented, and they lead to `⊤`.
  - Effort S.
- **d. `compile_fail` behaviour cases through the driver.**
  - `fip-macros` gains `FIP_MACROS_MARK_ONLY=1`, honoured only together with
    `FIP_PRELINT_DRIVER=1`. In that mode it emits `fip::mark` and skips its own
    token-level `compile_error!`.
  - A new test extracts the 7 examples into a generated fixture workspace and
    expects a driver error for each one.
  - Plain builds and the token-level checks are unchanged.
  - Effort M (1–2 days).
- **e. Cross-toolchain sidecars.**
  - Format (plain text): per function, the bound, free, panic, recursion and `⊤`
    leaves.
  - Stamped with the crate's SVH, the driver identity (`FIP_PRELINT_DRIVER_ID`) and
    the rustc version.
  - Used only where MIR is unreadable. Any mismatch means not used (`⊤`).
  - The first producer is L6's `std` summaries. Consumer crates on other toolchains
    (Y4 on 1.95) are served only if their code cannot be checked by the 1.99.1
    driver at all; today it can (`cargo fip-prelint` uses its own toolchain).
  - Effort M, inside L6.

### L11. (Found) Sites on infeasible paths still count

**Current.** The value analysis computes block entry states, but returns results only
for `Assert` blocks (`value.rs:1623-1644`), and runs only when the body has an
`Assert` (`value.rs:524-535`). So a panic call, allocation or `⊤` on a branch the
analysis proves infeasible is still counted. This is the reason `split_at_mut`'s
`panic_fmt` cannot be dropped even with facts (L1).

**Proposal.**

- Return per-block feasibility.
- Run the analysis on bodies with a `SwitchInt` on a tracked comparison, not only on
  bodies with an `Assert`.
- `scan_body` drops all sites in infeasible blocks.

**Soundness.** It uses the same proof as for asserts. Infeasible means no execution
reaches the block.

**Tests.** Fixture `guards`: `if i < n { if i >= n { panic!() } }` passes, and the
same with `Box::new` under `fip` passes. A feasible control is reported.

**Effort.** S (0.5 day). The first prerequisite of L1 and L2.

### L12. (Found) Every drop of a type with drop glue is a "possible free"

**Current.** `analysis.rs:1019-1027` pushes `Ev::Free` for every drop of a
`needs_drop` type, and also descends into the glue. Measured (M3): `RefMut<'_, u32>`
is reported as a free.

**Proposal.**

- Remove the syntactic `Ev::Free` at the drop site. A drop frees exactly when its glue
  (analysed anyway) reaches a deallocation entry point, a `free_source` (L7), a
  `GlobalAlloc`/`Allocator` free method, or `⊤`.
- `Box`, `Vec`, `Rc` and `String` keep "may free"; `RefMut`, `MutexGuard` without heap,
  and user guards lose it.
- Witness chains then end at `__rust_dealloc` instead of "drop of `T`". The first
  step names the dropped type.

**Soundness.** Frees are detected by the same mechanism as allocations. A glue whose
`Drop` impl is in a non-exported crate is `⊤` (reported), as today for calls.

**Tests.** Fixture `cells`: `RefMut` passes. Fixture `implicit`: `consume(Box<u8>)`
still frees. `selfcheck.expected`: the three `strict_gaps` errors are predicted
unchanged (`Box`-backed), and this is verified in the change.

**Effort.** Part of L5's M.

### Other limits found and kept

These are sound and reported, and need no change:

- `MAX_NODES = 20_000` instances per root gives `⊤` "analysis limit"
  (`analysis.rs:62`, `812-818`);
- the value analysis gives up above `MAX_VARS = 128` values or `MAX_CELLS` entries,
  or when its iteration budget runs out, and the asserts stay (`value.rs:59-62`,
  `1580-1584`);
- cleanup (unwind) blocks are not counted, by design (`analysis.rs:976-978`).

## Order of implementation

| # | item | depends on | effort | expected measurable change |
|---|---|---|---|---|
| 1 | L7 sources (marks, opaque boundary, trait rule, foreign table, reject `#[fip]` on sources) | — | M (2 d) | the 5 M2 false passes become errors; `selfcheck.expected` predicted unchanged |
| 2 | L11 feasibility of all sites | — | S (0.5 d) | `guards` gains passes; self-check unchanged (predicted) |
| 3 | L12 + L5 drop precision and generic drop glue | 1 | M (1.5–2 d) | the `RefMut` free disappears; `drop(Vec<T>)` becomes "may free" |
| 4 | L2 return summaries (Freeze access paths, raw-pointer metadata, table) | 2 | L (3–4 d) | M3's `usize::from`, wrapper `len`, `is_empty` cases pass |
| 5 | L1 contexts + `fip::requires` (+ `fip-macros` translation after its probe) | 2, 4 | L (4–5 d) | the 23 `swap_lt` notes, measured before and after |
| 6 | L3 iterator contracts | 4 | M (2–3 d) | M3's `rev`, inclusive, `enumerate`, `zip` cases |
| 7 | L4 devirtualisation, `param` on function pointers and `dyn`, trait contracts | — | L (3–4 d) | `param_bounds::fn_pointer` variants; new `indirect` fixture |
| 8 | L6 generated `std` summaries + L10e sidecar format | 7, 1 | L (3–4 d) | `format!` without `⊤`; `write!` into a buffer checkable |
| 9 | L10a–d repin recipe, per-target runs, parsed export detection, `compile_fail` through the driver | — | S–M (≈3 d) | new fixtures; per-target summaries recorded |
| 10 | L9 `--stack` mode | 7, 8 | L (4–5 d) | per-root byte bounds for one build, or `⊤` |
| 11 | L8 out-of-scope record + `cells` fixture | (3 for the flip) | S (0.5 d) | pinned behaviour |

The total is about 27–33 agent-days (an estimate). Items 1, 2, 7 and 9 have no
dependencies and can start in any order. Item 1 comes first because it is the only
measured false pass. Each item lands as its own commit with:

- its fixtures;
- a `TODOs/fip-prelint.md` section ("Resolved: ..") with before/after numbers;
- an amendment to `docs/decisions/2026-11-01-fip-prelint.md`;
- the README guarantee row adjusted. In particular, item 1 changes what "allocation"
  means there.

`just ci` must pass, including the self-check.

## What would reopen this

- A stable MIR or `rustc_public` API covering what the plan uses (contexts, symbol
  names, crate attributes).
- A Verus toolchain change (repin, L10a).
- A use case for sources in crates.io dependencies (L7 item 7) or for sidecars outside
  `std` (L10e).
- A change of the user principle on allocator internals.

## Appendix: probe sources (`/tmp/pd-allocprobe`, M2/M3)

`slab/src/lib.rs` (abridged; full file in the probe directory):

```rust
#![cfg_attr(fip_prelint, fip::export)]
#![no_std]
pub struct Arena { pub buf: [u8; 64], pub top: usize }
impl Arena {
    pub fn alloc(&mut self, n: usize) -> Option<&mut [u8]> {
        let start = self.top;
        let end = start.checked_add(n)?;
        if end > self.buf.len() { return None; }
        self.top = end;
        Some(&mut self.buf[start..end])
    }
    pub fn reset(&mut self) { self.top = 0; }
}
pub struct Slab { pub slots: [Option<u32>; 8] }
impl Slab {
    pub fn insert(&mut self, v: u32) -> Option<usize> {
        let mut i = 0;
        while i < self.slots.len() {
            if self.slots[i].is_none() { self.slots[i] = Some(v); return Some(i); }
            i += 1;
        }
        None
    }
    pub fn remove(&mut self, i: usize) -> Option<u32> { self.slots.get_mut(i)?.take() }
}
```

`app/src/lib.rs` roots (each `#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]`,
except `arena_loop` with `n = 3`): `arena_once` (`a.alloc(16)`), `arena_loop`
(`a.alloc(1)` in `for _ in 0..k`), `arena_reset`, `slab_cycle` (`insert` then
`remove`), `control` (`slab::twice`), `ffi_malloc` (`unsafe extern "C" { fn
malloc(n: usize) -> *mut u8; }`).

`galloc/src/lib.rs`: `unsafe impl GlobalAlloc for Bump` (`fetch_add` on an
`AtomicUsize` into a static `UnsafeCell<[u8; 4096]>`, `dealloc` empty),
`#[global_allocator] static BUMP`. Roots: `boxed` (`Box::new(1)`),
`direct_global_alloc` (`BUMP.alloc(Layout::new::<u64>())`), `direct_system_alloc`
(`std::alloc::System.alloc(..)`).

`limits/src/lib.rs`: one root per row of the M3 table.
