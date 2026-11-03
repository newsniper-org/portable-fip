<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `fip-prelint`: a plan for every case still reported as `⊤`, a warning or a note

**Status:** ACCEPTED by the user, 2026-11-03, for items 1–15 of "Recommended order";
implemented on branch `prelint/top-plan`, one commit per item. Item 16 (Verus
panic-freedom sidecar, a trust change) awaits a separate user decision; the "stay" and
"only on demand" items are not executed.
Builds on `docs/decisions/2026-11-02-fip-prelint-limits-plan.md` (ACCEPTED,
implemented: L1–L12) and its "Other limits found and kept", on the amendments of
`docs/decisions/2026-11-01-fip-prelint.md`, and on `TODOs/fip-prelint.md` and
`TODOs/strict-open-items.md`. Code references are to commit `3ef3759`. The driver
sources are unchanged since `d127bc4`, which is the commit the driver was built from.

## Scope and rules

This plan covers every case in which the driver gives no plain pass/fail verdict:

- **`⊤`**: an error, "cannot check .. unresolved", or a call site whose argument is
  unresolved;
- **warnings**: "only relative to its generic parameters";
- **notes**: reachable panic paths under marks that allow them, and informational
  notes.

The rules are the limits plan's. A fact is used only if the analysis proves it, or if
it is a declared contract that is either checked at every analysed use or listed as
trusted. Whatever stays undecidable stays visible, as `⊤`, a term, a note or a
statement in the guarantee table. **No item prunes unsoundly.**

## Measurements (2026-11-02, rustc 1.99.1, x86_64 Linux)

The driver was built into `/tmp/tp-prelint-target`
(`RUSTC_BOOTSTRAP=1 cargo +1.99.1 build --target-dir /tmp/tp-prelint-target` in
`tools/fip-prelint`). Every run used `FIP_PRELINT_TARGET_DIR` under `/tmp`, and the
repository's `target/` was not touched. Probe sources are in the appendix; the full
files are under `/tmp/tp-m3`.

**N1. Self-check** (`cargo fip-prelint --warn-only --message-format short`). It
reports 79 roots, 76 passed, 3 errors (the deliberate `strict_gaps`), 1 warning and
26 notes. The per-crate summaries are identical to
`tools/fip-prelint/tests/selfcheck.expected`. There is no `⊤`. The notes, classified:

| notes | cause | where |
|---|---|---|
| 15 | arithmetic overflow check (`+`, `*` without a guard): 12 in strict test functions, 3 inside `fip_fn!` closures of `strict_behaviour::pipeline` (`v + 1`, `v * 2`, `v + 10`) | `strict_accept`, `strict_impl`, `strict_gaps`, `strict_behaviour` |
| 8 | `alloc::alloc::handle_alloc_error` (diverges) behind `Box::new`, in roots that allow the allocation | `strict_accept`, `strict_impl`, `strict_crate_path`, `strict_gaps` |
| 2 | "dynamic call of `Step::step`: its contract `#[fip(strict = true)]` allows panic paths" (`step_dyn`, `step_gen`) | `strict_impl` |
| 1 | `assert!(x > 0)` (`core::panicking::panic_fmt`) in `strict_gaps::checked_dec` | `strict_gaps` |

The warning is `shapes::Slot::<T>::put_twice`, with term `alloc(drop(T))`. The README
row (`README.md:48`) still says "67 roots .. 23 panic-path notes". It is stale, and
`selfcheck.expected` is the current record.

**N2. Every fixture** (19 workspaces under `tools/fip-prelint/tests/fixtures`, default
run). Most of these cases are deliberate controls. The distinct reasons, with counts:

| class | reason | count | fixtures |
|---|---|---|---|
| `⊤` | call through a function pointer not resolved to one function | 4 | `indirect` 2, `param_bounds` 1, M3 1 |
| `⊤` | `dyn` call of a method without a contract | 2 | `indirect`, M3 |
| `⊤` | callee in a crate without `fip::export` | 4 | `cross_crate` 2, `nonmember_export`, `export_detection` |
| `⊤` | exported crate built without `-Zalways-encode-mir` | 1 | `export_unencoded` |
| `⊤` | `std` function without MIR, not in the std summaries | 2 | `ffi` (`set_functions_inner`), `std_summaries` (`debug_struct_field2_finish`) |
| `⊤` | drop shim that rustc cannot build for the generic type | 2 | `generics` |
| `⊤` (call site) | argument for a `param` not known (pointer from data; parameter without `param`; `fn` pointer through the `Fn` shim) | 3 | `param_bounds` |
| `⊤` | implementation of a contracted method in a crate without `fip::export` | 1 | `contract_dep` |
| error (FFI) | neither certified nor excluded / both / conflicting / across ABIs | 8 | `ffi`, `alloc_sources` |
| warning | `only relative to its generic parameters` (`drop(T)` ×3, `∞·drop(T)` ×2, `<T as Make>::make`, `<P as Plain>::size`, `∞·alloc(g)`) | 8 | `generics` 6, `indirect`, M3 |
| note | precondition not established at a call / not checked where a reified function is called | 2 | `preconditions` |
| note | `index out of bounds` (controls) | 2 | `implicit`, `preconditions` |
| note | FFI mark matched by symbol; contract implementation counts (informational) | 4 | `ffi` 3, `contract_dep` |

**N3. M3 limits probe, rerun** (the appendix of the limits plan, copied to
`/tmp/tp-m3`). `limits` reports 13 roots, 7 passed, 7 errors and 1 warning. The only
remaining `⊤` are `via_fn_ptr` and `via_dyn`. Both are undeclared on purpose: with
`param(g = 0)` or a contract they pass (limits plan L4). In the allocator probe,
`app` reports 6 roots and 5 passed. The four unmarked arena and slab roots still
pass, as documented (L7, "declared assumption").

**N4. New probe for this plan** (crates `top` and `tok`, appendix). Driver results:

| case | driver today |
|---|---|
| `(o.f)(1)` with `o: &Ops`; and with a local `let o = Ops { f: plus1 }` | `⊤` both ("call through a function pointer") |
| `TABLE[i](3)` with `static TABLE: [fn(u8) -> u8; 2]` | `⊤` |
| `ONE(x)` with `static ONE: fn(u8) -> u8 = plus1` | `⊤` |
| `CONE(x)` with `const CONE: fn(u8) -> u8 = plus1` | `⊤` (constants are not origins, `analysis.rs:4052-4058`) |
| `pick(b)(1)` (a pointer returned by a call) | `⊤` |
| `b.area()` on `&Box<dyn Shape>` or `Box<dyn Shape>`, or on each element of `&[Box<dyn Shape>]`, with a contracted `area` | passed (autoderef makes it a direct virtual call) |
| `g(1)` with `g: &Box<dyn Fn(u8) -> u8>` declared `param(g = 0)` | `⊤` through `<Box<dyn Fn> as Fn>::call` |
| `g(1)` with `g: &dyn Fn(u8) -> u8` declared `param(g = 0)` | passed |
| `apply(plus1)`, `apply<G: Fn>` declaring `param(g = 0)` | passed |
| `apply(p)` with `p: fn(u8) -> u8` a local reified from `plus1`, an undeclared parameter, or a parameter **declared** `param(p = 0)` | `⊤` all three, root and call site (`<fn(u8) -> u8 as Fn>::call (shim)`) |
| `mid(q) { apply_ptr(q) }` without `param(q = ..)` | `⊤` at `mid`'s call site; with `param(q = 0)` passes |
| `mid_generic(h) { apply(h) }`, generic, instantiated with `plus1` | passed |
| trait method declaration with `param(g = 0)` | error "`param(..)` is not supported in the contract of a trait method" (`report.rs:805-809`) |
| `write!(b, "{p:?}")` / `"{p:#?}"` on `#[derive(Debug)]`, `"{s:?}"` on `&[u8]`, `"{o:?}"` on `Option<u8>` | `⊤`: `debug_struct_field2_finish`, `debug_list`/`DebugList::entry`/`finish`, `debug_tuple_field1_finish` not in the summaries |
| `write!(b, "{x}")` for `f64` and for `u128` | `⊤`: `<f64 as Display>::fmt`, `<u128 as Display>::fmt` not in the summaries |
| `println!("{x}")` | `⊤`: `std::io::stdio::_print` not in the summaries |
| `std::io::Write::write_all` into `&mut [u8]` | passed |
| `x.sqrt() + x.sin()` | `⊤`: intrinsics `sqrtf64`, `sinf64` not in `ALLOC_FREE_INTRINSICS` |
| `TL.with(|c| c.get())` (`thread_local!`, `const` init) | `⊤`: `LocalKey::try_with` calls through a function pointer field |
| `HashMap::<u8, u8>::new()` | `⊤`: the `LocalKey` pointer (`RandomState::new`), and `hashbrown::RawTable::drop` ("crate `hashbrown` does not declare `fip::export`") |
| `if a < 100 && b < 100 { xs[a * b] }`, `xs: &[u8; 10000]` | passed |
| `if a < n && b < m && n·m ≤ len { xs[a * m + b] }` (relational, nonlinear) | overflow (Mul, Add) and bounds reported |
| `if xs[0] < ys.len() { ys[xs[0]] }` (slice element) | bounds reported |
| `if c.get() < ys.len() { ys[c.get()] }` (`Cell`) | bounds reported (correct: interior mutability) |
| `if i < w.n && w.n <= w.b.len() { w.b[i] }` (fields behind `&T`, `T: Freeze`) | passed |
| `a + b` under `strict = true` / `strict = true, panic_macros = false` | note / error |
| `Pool::alloc` (unmarked, hands out slots) | passed (declared assumption) |
| `#[fip]` with `type V = Vec<u8>; V::with_capacity(4)`; with `use Vec as Seq`; generic `T::default()` instantiated with `Box<u8>` | the macro accepts all three; the driver reports the allocation (generic: a warning, and an error at the `Box` instantiation) |
| strict caller of `cdep2::labs` where `labs` is certified on a local declaration | macro: E0425 "cannot find value `__fip_strict_labs` in crate `cdep2`"; driver (non-strict root): passes, "certified by symbol" |
| strict function containing `Certified::<{ Cert::allocs_for(__fip_strict_tick, "tick") }, _>::assume(tick)` | macro: "generic arguments in a callee path cannot be resolved" |
| `Certified::<0, _>::assume(boxy)` (wrong hand-written bound on a named function) passed for `param(g = 0)` | driver: error, the argument allocates once (the driver analyses the body, not the claimed `N`) |

**N5. Stack mode** (fixture `stack`). In the dev profile, 11 roots: 3 bounded, 8 `⊤`
(recursion, `dyn`, function pointer, `labs`, `std::process::id`, generic root,
`memcpy`, `__rust_alloc`). In the release profile, 4 bounded and 7 `⊤`: `indexed` and
`copy_big` have no symbol of their own. With
`RUSTFLAGS=-Zcross-crate-inline-threshold=never --release`, 5 are bounded: `indexed`
gets 16 bytes, and `copy_big` moves to the `memcpy` `⊤`. Object formats for
`-Zemit-stack-sizes` (`rustc +1.99.1 --emit=obj`, read with `llvm-readobj
--stack-sizes`):

| target | object | frame entries |
|---|---|---|
| `aarch64-unknown-linux-gnu` | ELF | present |
| `aarch64-apple-darwin` | Mach-O | none |
| `x86_64-pc-windows-gnullvm` | COFF | none |
| `wasm32-unknown-unknown` | WASM | none |

The reader accepts only x86_64 ELF (`stackbound.rs:152-158`). Stack mode builds
libraries only (`stack.rs:156`, `cargo-fip-prelint.rs:256`).

**N6. Profile.** `cargo fip-prelint --release` on the workspace still reports the 15
overflow notes, and adds one note: a bounds check in `fip_core::strict::dedup_by` at
`strict.rs:324`. The cause of that note was not located. The driver appends
`-Copt-level=0` (`main.rs:73-74`). Measured with a 3-line program: for rustc 1.99.1,
`-Copt-level=3 -Copt-level=0` turns on both `debug_assertions` and overflow checks,
while `-Copt-level=3` alone turns both off. Cargo passes `-C debug-assertions` /
`-C overflow-checks` only when they differ from the opt-level's default. So for a
release-profile crate the driver analyses MIR **with** overflow checks and debug
assertions, which the shipped build does not have. That is sound (it adds panic
paths) but imprecise. For a profile with `overflow-checks = false`, the overflow notes
describe code that does not ship.

**N7. Non-host targets.** `std_summaries` with `--target wasm32-unknown-unknown`
reports 5 roots, 0 passed, all `⊤`: "std summaries not used". The host reports
2 passed. The sidecar exists for `x86_64-unknown-linux-gnu` only
(`tools/fip-prelint/std-summaries/`).

**N8. Sidecar content.** 60 summarised functions. The seed
(`tools/fip-prelint/std-summaries/seed/src/lib.rs`) covers integer `Display`/radix
formats, `str`/`char`/`bool`, `DebugStruct` and `format!`. Three summaries keep a
`top` line: `<dyn Write>::write_str` reached from `Formatter::write_str` and from the
`DebugStruct::field` closure (the `PadAdapter` path of `{:#?}`), and
`<dyn Debug>::fmt` in that closure.

## The items

Effort: **S** ≤ 0.5 day, **M** 1–3 days, **L** 3–5 days, for one agent. These are
estimates (unmeasured). "Stays" marks a residue that remains a reported limit.

### T1. Function pointers loaded from memory

**Current.** `origin_of` (`analysis.rs:3783-3794`, `4052-4127`) is a must-analysis over
whole locals. It gives up on projections, on `Operand::Constant`, on call results and
on loads. Calls whose origin is unknown are `⊤` (`analysis.rs:2264-2273`). Measured
(N4): field of a parameter, field of a local aggregate, static table, static, `const`,
call result. All are `⊤`.

**Candidates.**

1. **Constants** (S). An `Operand::Constant` of `fn` pointer type evaluates to a
   pointer into `GlobalAlloc::Function(instance)`. Resolve it to that instance.
   - *Soundness:* a constant has one value. This is the same must-origin as a local
     reify.
2. **Immutable statics, including tables** (M). A load whose place is `*&STATIC` plus
   projections (fields, `Index`, `ConstantIndex`), where `STATIC` is not `static mut`
   and its type is `Freeze`. Evaluate the initializer (`eval_static_initializer`),
   collect every function pointer in the projected sub-value, and use the candidate
   set: the cost is the maximum over the candidates, the union of their events, and a
   loop if any candidate loops.
   - *Soundness:* the memory is immutable after initialisation (writing through a
     shared static without `UnsafeCell` is undefined behaviour), so a load yields one
     of the collected pointers.
   - An `Index` by an unknown `i` takes all elements, which is still complete.
   - `static mut`, `UnsafeCell`/atomics, and pointers to mutable memory stay `⊤`.
3. **Field-sensitive local origins** (M). `o.f` where `o` is a local written exactly
   once, as a whole, by an `Aggregate` whose field operand has a known origin, and
   never mutably borrowed or partially written. This uses the same "unstable local"
   rule as today (`analysis.rs:3760-3781`).
4. **Pointers in parameters and heap: a certified function-pointer type** (M; also
   idea 5 of `docs/notes/fip-fn-ergonomics-brainstorm.md`). Use
   `fip_strict::Certified<N, fn(A) -> R>` as the field type. It already compiles (a
   plain probe; `Certified` is generic over `C`).
   - Values come from `fip_fn!(f)` / `Certified::assume` and a safe `erase` from
     `Certified<N, FnDef>`.
   - The driver checks every analysed construction from a resolved origin (the
     function's bound ≤ `N`, as for `param(g = K)` arguments). At calls it uses `N`.
   - A construction it cannot resolve is `⊤` there (assume-guarantee, as limits plan
     L4.2).
   - *Trust:* `Certified::assume` in unanalysed crates. It is already `unsafe` and
     greppable (`crates/fip-strict/src/lib.rs:243-260`).
5. **Rejected: whole-program candidate sets** (all address-taken functions of the
   signature). These are unsound in a library context (limits plan L4).

**Stays.** Pointers from FFI, from mutable memory, from call results of unanalysed
code, and from `Freeze`-violating statics stay `⊤` (an error).

**Implemented** (item 2, candidates 1–3). Constants and loads below a reference
constant (a `static` or constant memory, read from the evaluated initializer;
`ConstValue::Indirect` for `const` slices) resolve to the function pointers found
there; an index local assigned one constant selects one element. Several candidates
are one call site `Item::Alt` costing their maximum. Fields of local aggregates
resolve through the aggregate's operand. Fixture `indirect_data`: 22 roots, 13 passed
(1 before, `apply_ptr`; the rest `⊤`). N4: `fnptr_const`, `fnptr_static`, `fnptr_local_struct` pass.
**Deviation:** `fnptr_static_table` is no longer `⊤`, but stays an error: the bounds
check of `TABLE[(i & 1) as usize]` is not proved (`BitAnd` is outside the value
domain). A static whose type is not `Freeze` stays `⊤` even for a field outside its
`UnsafeCell` (its allocation is mutable; conservative).

**Tests.** A new fixture `indirect_data` with the N4 cases:

- `const` and `static` pass, and the table passes with the max over its elements;
- a local aggregate passes;
- `static` with `Cell<fn>` stays `⊤`, and `AtomicPtr` stays `⊤`;
- a field of type `Certified<0, fn>` passes, and a construction with an allocating
  function is an error at the construction.

**Dependencies.** None for 1–3. 4 depends on B (below) only for the construction check
across calls.

### B. Shared mechanism: callable bindings across calls (prerequisite of T2–T4)

Today a node's parameters can carry bindings for formatting values only
(`Bind::Dyn`/`Bind::Formatter`, `analysis.rs:2356-2434`). **Proposal:** add
`Bind::Callable(origin)` for arguments of type `fn(..)`, `&dyn Fn*`, `Box<dyn Fn*>` or
a generic `F` instantiated with a `fn` pointer. The origin is one of:

- `Fn(FnDef/closure)`;
- `Declared(K, mark)`, a caller parameter with `param(p = K)`;
- `Certified(N)`, from T1.4.

`call_binds` computes these with `origin_of` at the call. In the callee,
`pointer_target`/`devirtualize` consult `bind_of(l)` before giving up. Nodes are
already keyed by instance and bindings.

- *Soundness:* a binding is a must-fact at the call site, carried into a
  context-specific node. That is the same argument as the L1 contexts.
- The depth is limited like contexts (3), and then the node falls back to no binding,
  which is today's `⊤`.

Effort M (2 days).

**Implemented** (item 3). `Bind::Callable` with `Callable::Fns` (instances: a reified
function or closure, a constant, the candidates of immutable data), `Pointee` (the
concrete type of a `&dyn Fn*`) and `Declared(fn, g)`; arguments of function-pointer
and `&dyn Fn*` type are bound (`Box<dyn Fn*>` and generic `F` come with item 4).
`Certified(N)` waits for T1.4. Depth: at most 3 nodes with callable bindings on the
first-caller chain. **Deviation:** the prediction "no verdict change alone" did not
hold. Measured: `top::through_mid` passes (its exploration no longer carries `mid`'s
unbound call-site `⊤`; `mid`'s standalone report stays); `param_bounds::fip_through_fbip`
reports the bound `frees` (may free) and no longer "recurses"; `indirect_data::pass_mixed`
also reports its root allocation through `apply_ptr`; new fixture `callable_binds`
8 roots, 0 → 5 passed.

### T2. `Box<dyn ..>` receivers and parameters

**Current.** Measured (N4): `Box<dyn Trait>` receivers of **contracted** methods pass
(autoderef gives a direct virtual call). This corrects the limits plan's "`Box<dyn ..>`
receivers are not followed", which holds only for callable trait objects behind smart
pointers. `g: &Box<dyn Fn(u8) -> u8>` declared `param(g = 0)` is `⊤`: the call goes
through `<Box<F, A> as Fn<Args>>::call`, whose `(**self).call(args)` is a virtual call
on a projection.

**Candidates.**

1. **Recommended.** With B, bind the Box `Fn*` impl's `self` to the declared parameter.
   Extend `origin_of` with the one projection chain `Box` deref uses
   (`(*((*_1).0.0.0))`), restricted to `alloc::boxed::Box`, identified by lang item /
   `DefId`. The same applies to `Rc<dyn Fn>` / `Arc<dyn Fn>` only through their
   `Deref`, which is an ordinary call and so needs no special case.
   - *Soundness:* the projection reads the pointer `Box` owns. The bound is the
     parameter's declared one.
2. Accept `param(g = K)` on `Box<dyn Fn*>` parameters and treat
   `<Box<dyn Fn*> as Fn*>::call*` as a trusted forwarder (S). This is smaller, but it
   adds a trusted model of `alloc` code. Rejected unless 1 proves hard.

**Stays.** Owned `Box<dyn Fn>` dropped in the root is a real "may free" (correct).
`dyn` values of unknown origin without a contract stay `⊤`.

**Tests.** `indirect`: `box_dyn_fn` with `param` passes. `Box<dyn Fn>` without `param`
stays `⊤`. `Rc<dyn Fn>` is a control.

**Effort.** S after B.

**Implemented** (item 4, candidate 1). `Origin::BoxPtr(l)`: `(*_1).0` of a `&Box`
parameter, through its `BoxDerefTransmute` cast and reborrow (the 1.99.1 shape of
`<Box<F, A> as Fn<Args>>::call`, not the plan's `(*((*_1).0.0.0))`), restricted by
`is_box()`; the `&Box` parameter is bound (B) to the caller's declared parameter or to
the type the box was unsized from (`Origin::Ref` for `&b`). `callable_dyn` accepts
`Box<dyn Fn*>` and references to it, so `param(g = K)` on `&Box<dyn Fn*>` is checked at
call sites. Fixture `indirect`: `box_dyn_fn` passes, `box_dyn_fn_undeclared` and
`rc_dyn_fn` stay `⊤`, `box_dyn_caller_alloc` is reported at the call site. N4
`box_dyn_fn` passes. **Deviation:** `Rc<dyn Fn>` is not followed through `Deref` (a
call result), so it stays `⊤`, unlike the plan's "needs no special case".

### T3. Generic `F` instantiated with a function pointer (the `Fn` shim)

**Current.** `apply::<fn(u8) -> u8>(p)` reaches `<fn(u8) -> u8 as Fn<(u8,)>>::call
(shim)`, which calls through its `self`. That is `⊤` for a local reify, for an
undeclared parameter, and also for a parameter **declared** `param(p = 0)` (N4,
`gen_declared`). The same leaf makes the call-site check `⊤`
(`param_bounds::fn_pointer`).

**Candidate.** With B, the shim's parameter 0 is bound from the caller's argument
origin: a reified function resolves to that function, and a declared parameter costs
`K` with its mark's permissions. The call-site check uses the same resolution.

- *Soundness:* as B.

**Stays.** A `fn` pointer of unknown origin stays `⊤` at the call site, as today.

**Tests.** `param_bounds`: `generic_with_fnptr_local` passes, `gen_declared` passes,
and `generic_with_fnptr_param` (undeclared) stays `⊤`.

**Effort.** S after B. **Dependencies:** B.

**Implemented** (item 4). `Origin::DerefArg(l)` (`*_1` of a reference parameter) and
`Origin::Ref(l)` (`&l`): the shim's `&fn` parameter is bound to what the argument
holds; `argument_items` binds the shim nodes of a function-pointer `G` at the call
site. Fixture `param_bounds`: `generic_with_fnptr_local` and `gen_declared` pass (root
and call site), `generic_with_fnptr_local_alloc` is reported with its allocation,
`fn_pointer` (undeclared) stays `⊤` at its call site. N4: `gen_declared`,
`generic_with_fnptr_local` pass; `generic_with_fnptr_param` keeps its call-site `⊤`
and its root now passes (the shim costs `apply`'s declaration, like any declared
callee). `FnMut` bounds are not covered (`&mut g` makes `g` unstable).

### T4. Origins passed through functions without `param`, and call results

**Current.** `mid(q) { apply_ptr(q) }` is reported at `mid`'s call site because `q`
has no `param` (`analysis.rs:2948-2952`). That happens even when every caller of `mid`
passes a known function. Since the call-site check runs in every local function, `mid`
is checked standalone. A pointer returned by a call (`pick(b)(1)`) is `⊤`.

**Candidates.**

1. **Keep the message.** The fix is already available: `param(q = K)` on `mid`
   (measured: passes). No change.
2. **Context-sensitive resolution through B for roots** (included in B). From
   `through_mid`, `mid`'s node has `q` bound to `plus1`, so the root's verdict is
   precise. `mid`'s standalone check still reports.
3. **Inferred parameter bounds for private, never-reified functions** (M). If `mid` is
   not `pub`, is never reified or coerced to a pointer, and every call site in the
   crate binds `q` (B), then the standalone report at `mid` is replaced by the checks
   at its callers.
   - *Soundness:* such a function is callable only from analysed code in this crate,
     so all its uses are seen. `pub`, `pub(crate)` with macros exporting it, and
     reified functions keep today's report.
4. **Return summaries for function pointers** (M). Extend L2's summaries with "returns
   a pointer whose origin set is S", computed by T1's candidate sets over the callee's
   returns. This is sound only if the callee's MIR is analysed. Otherwise `⊤`.

**Recommendation.** 2 (with B) and 3. 4 is gated on a use case.

**Stays.** A `pub` function's parameter without `param` stays reported at its call
sites inside it. That is the documented contract (2026-11-01 amendment "declared
parameter bounds").

**Tests.** `param_bounds`: private `mid` with bound callers has no report; `pub mid`
is reported; a reified private `mid` is reported.

**Effort.** M (3 after B). **Dependencies:** B.

### T5. Contracts with `param(..)`

**Current.** Rejected: `report.rs:805-809`, and `fip-macros` on declarations (2026-11-01
amendment, "`#[fip]` on trait method declarations"). Measured (N4).

**Candidate.** Allow `param(g = K)` in a contract when `g` is a callable parameter of a
dyn-compatible method (`g: &dyn Fn*`, `fn` pointer). A trait method with its own type
parameter is not dyn-compatible, so generic calls resolve per instance and need no
contract parameter.

- Every **implementation** is checked with `g` costing `K` (assume). Every **call**
  through the contract (`dyn` and generic-unresolved, `self.node_contract`) checks its
  argument for `g` against `K` and the mark's permissions (guarantee), exactly like an
  ordinary call site.
- *Soundness:* assume-guarantee. Both sides are in analysed code. An implementation in
  a crate without `fip::export` is already `⊤` (`contract_dep`).

**Stays.** Calls from unanalysed crates are not checked (as for `requires`, L1).

**Tests.** `indirect`: a contract `visit(&self, g: &dyn Fn(u8) -> u8)` with
`param(g = 0)`. A good implementation passes; a caller passing an allocating closure
is an error at the `dyn` call; an implementation that calls `g` twice in a loop under
`fip` still passes (cost `0`); one that allocates itself fails.

**Effort.** M (1.5 days). Mark validation in `fip-macros` and in the driver.

### T6. `dyn` calls without a contract, and implementations in non-exported crates

**Current.** `⊤` (`analysis.rs:1557-1573`; `contract_dep`). This is the deliberate
residue of L4.

**Decision. Stays** a reported limit. The only sound ways out are a contract (exists)
or analysing the implementing crate (`fip::export`, exists). Both are user actions,
and the messages already name them.

### T7. Standard-library sidecar gaps

**Current.** A `std` function without MIR that is not in the sidecar is `⊤`
(`analysis.rs:1788-1803`). Coverage is what the seed reaches (limits plan L6,
"Implemented"). Measured gaps (N4, N7, N8):

| gap | cause | candidate | soundness | stays |
|---|---|---|---|---|
| a. `{:?}` via `debug_struct_fieldN_finish`, `debug_tuple_field1_finish`, `debug_list`/`DebugList::entry`/`finish`, `DebugMap`, `DebugSet` | not seeded; their user values arrive as `&dyn Debug` | seed derived `Debug` for structs with 1–5 fields and tuples, slices, `Option`, `Result`; add a summary term `§dyn <i> <method>`, resolved at the call site through `origin_of` of argument `i` (an `Unsize` of a concrete `&T`, which the derived code always builds); for `entries(iter)` (generic, MIR) the term resolves per instance | same as `§out` terms today (`analysis.rs:2366-2390`): a term is resolved from a must-origin or is `⊤` | a `&dyn Debug` from data, `debug_struct_fields_finish` with a slice of `&dyn Debug` (array elements: resolved only through T1.3-style element origins) |
| b. `{:#?}` (`PadAdapter`, `Formatter::wrap_buf`) | the alternate path swaps the formatter's `buf` for `&mut PadAdapter as &mut dyn Write`; `PadAdapter::write_str` writes to the inner `dyn Write`; this is the 3 `top` lines of N8 | model `buf` as `Out::Ty(PadAdapter)` at the swap (a known unsize in the summarised MIR), and `PadAdapter`'s inner buffer as the outer `Out` (one field binding) | must-origin inside one summarised body | user code that builds its own `Formatter` over a `dyn Write` from data |
| c. float `Display`/`Debug`/`LowerExp` | `float_to_decimal_common_*` not seeded | seed `f32`/`f64` with the formats `{}`, `{:.N}`, `{:e}`, `{:?}` | generated, like every summary | none expected; the panics found by generation are reported |
| d. float math (`sqrt`, `sin`, ..) | intrinsics not in `ALLOC_FREE_INTRINSICS` | add the `f32`/`f64` math intrinsics to the audited table: no events; those that lower to libm calls (`sinf64`, ..) are listed with that note | trusted table entry, as the existing intrinsics; libm's `sin` is a C function, and its allocation-freedom is a claim about the C library | — |
| e. `u128`/`i128` and other non-seeded integer formats | not seeded | seed them | generated | — |
| f. `println!`/`eprint!`/`std::io` (`_print`, `Stdout::lock`, `LineWriter`) | not seeded | seed `_print`; expected (unmeasured) result: an allocation on the lazy buffer path, `⊤` through `OUTPUT_CAPTURE` (a thread local, see g) and `dyn Write` | generated | `println!` is not a FIP operation; the useful outcome is a precise violation instead of `⊤` |
| g. `thread_local!` (`LocalKey::with`/`try_with`) and through it `RandomState::new`/`HashMap::new` | `LocalKey { inner: fn }` is called through a field of `&'static LocalKey` | with B plus T1.2: the receiver is a reference to a `static`/promoted constant, so the field load is resolved from the evaluated initializer (`Bind::Const(place)`) | immutable static data, as T1.2 | the lazy-initialisation path of non-`const` thread locals, if it registers a destructor through a pointer from data (unmeasured) |
| h. `std`'s private dependencies (`hashbrown`, ..) | `is_std_crate` is `core`/`alloc`/`std` only (`analysis.rs:986-988`) | treat crates loaded from the sysroot (`tcx.used_crate_source` under the sysroot, or `tcx.is_private_dep` of a std crate) as std-like: analysed where they have MIR, summarised where not | the code is the shipped `std`'s; foreign calls inside them still go through the FFI rule | — |
| i. functions the seed does not reach (generally) | coverage is seed-driven by design | (1) a maintainer recipe `just prelint-std-coverage` that runs the fixtures and the workspace with `FIP_PRELINT_DUMP=1` and lists every "not in the std summaries" leaf; (2) seed new roots on demand; (3) **rejected:** summarising every public non-generic `std` function: generation time and sidecar size, and most of `std` is out of FIP scope (I/O, threads, processes) | — | anything not seeded stays `⊤` with its name, as now |
| j. non-host targets | the sidecar is per target; generation is measured for the host only | generate for every installed `std` target that `just prelint` checks (`tests/targets.rs`): 10 `std` targets; `-Zbuild-std` cross-builds need no target runtime | each file stamped with its target (exists) | targets without `rust-src` support for `-Zbuild-std` |

**Effort.**

- a+b: L (3 days);
- c+e: S (seed only; one regeneration, measured at 94–131 s cold);
- d: S;
- f: S, plus g;
- g: M (after B and T1.2);
- h: S;
- i: S;
- j: M (generation per target, about 2 min each, plus repin recipe changes).

**Tests.** Fixture `std_summaries`:

- derived `Debug` passes with a user `Write` buffer;
- `{:#?}` passes;
- `f64`/`u128` pass;
- `println!` is a violation, not `⊤`;
- `HashMap::new` gets a verdict; this one is a prediction;
- `--target wasm32-unknown-unknown` matches the host for the fixture.

**Dependencies.** g needs B and T1.2.

### T8. Stack mode gaps

**Current.** See N5 and limits plan L9 "Implemented".

| gap | candidate | soundness / claim | stays |
|---|---|---|---|
| a. non-x86_64 ELF | add AArch64 ELF (`R_AARCH64_CALL26`/`JUMP26` relocations, return address 0 because LR is a register; a frame record pushed by the callee is inside its `.stack_sizes` value), i686 and ARMv7 ELF; the objects exist for installed targets (measured: AArch64 ELF objects carry `.stack_sizes`) | per-target relocation and return-address rules, each with a fixture expectation computed from `llvm-readobj` | Mach-O, COFF, WASM: LLVM emits no frame sizes there (N5), so they **stay** `⊤` ("format without `.stack_sizes`") |
| b. runtime functions (`memcpy`, `memset`, `memmove`, `__rust_probestack`) | a declared crate attribute `fip::stack_leaf(memcpy = B, ..)` with `evidence = ".."`, counted and listed in the summary like FFI certificates; no built-in table, because the implementation linked at run time (glibc asm vs `compiler_builtins`) is not in the objects | a trusted declaration, visible | undeclared ones stay `⊤` |
| c. precompiled `std` frames | `--stack --build-std`: build the user's libraries **against a `-Zbuild-std` std with the profile's settings**; then the frames are those of the artefact actually built | measured bound for that artefact (not for one linked against the shipped `std`, and the report says so) | stack mode against the shipped `std` stays `⊤` at `std` calls; cold cost ≈ 2 min (L6 measurement) |
| d. roots without a symbol (inlined / cross-crate-inline only) | add `-Zcross-crate-inline-threshold=never` to the stack flags (`main.rs:106`); measured: `indexed` gets a bound at opt-level 3 | the claim is already "this build"; the build changes (as with `-Zshare-generics=no`), and the report states the flag | a root that LLVM inlines into every caller within its own crate still has no symbol: `⊤` |
| e. generic roots | bound every mono instance of the root that the build contains (with `-Zshare-generics=no` each user crate codegens its own); report "`f::<u8>` uses at most B" per instance; with f (below) the tests supply instances | per-instance measured bound | a generic root with no instance in the build stays `⊤` (`fip_core`: 8 roots, 0 instances in its libraries) |
| f. bins and tests | for bins and test targets, add `--emit=obj` for the primary crates in stack mode and read the `.o` files next to the executables (the final executable has relocations resolved, so the call graph needs the objects) | same reader | unmeasured whether `cargo test --no-run` keeps the objects; if not, `-Csave-temps` |

**Effort.** a: M; b: S; c: M; d: S; e: M; f: M. **Dependencies.** e benefits from f.
c reuses L6's build-std driver path.

### T9. Macro-generated crate attributes in export detection

**Current.** Not detectable before expansion: such a crate is passed through, so `⊤`
downstream (`export.rs:24-27`). It is sound.

**Candidates.**

1. **Stays** (recommended). Document it, which is done in the README row.
2. A second pass: build the crate with the driver's flags whenever the crate root
   contains any inner attribute macro invocation, then read `fip::export` from the
   expanded HIR. This doubles compile time for such crates, and the flags decision
   would be made after the fact. Rejected.
3. A cargo metadata key (`[package.metadata.fip] export = true`) as an alternative
   declaration, read from `cargo metadata` before compiling. It is unambiguous and
   needs no parsing, but it is a second spelling of one fact, so the parsed attribute
   would have to agree with it (both read, mismatch is an error). Effort S. Only if a
   user needs macro-generated crate attributes.

### T10. Strict callers reach an FFI certificate only through the marked declaration's path

**Current.** The driver matches marks by link symbol and ABI (2026-11-01 amendment,
"foreign marks match by link symbol and ABI"). The macro finds `__fip_strict_<name>`
next to the called path only (same amendment, last sentences). Measured (N4): a strict
call of `cdep2::labs` gives E0425, while a non-strict root passes "certified by
symbol".

**Candidates.**

1. **Stays, documented** (recommended): call through the certified declaration, which
   needs no code change.
2. `#[fip(strict = true, ffi(cdep2::labs = ffi::labs))]`: the macro reads the
   certificate of `ffi::labs` for calls of `cdep2::labs`, and emits a driver mark so
   the driver checks that both declarations have the same symbol and ABI (error
   otherwise).
   - *Trust:* without the driver, the mapping is unchecked, while `Cert::allocs_for`
     still checks the name.
   - Effort S–M. Gated on a use case.

### T11. Non-strict implementations of strict contracts (driver-only)

**Current.** `#[fip_impl]` cannot see whether a trait method has a contract, so `#[fbip]`
or unmarked implementations compile. The driver checks them
(`TODOs/fip-prelint.md`, "`#[fip_impl]` compares panic strictness .." table:
`#[fbip]` impl gets a driver error, an unmarked one is checked against the contract).

**Decision. Stays driver-only.** Every compile-time probe measured fails for traits
without `#[fip_trait]` or for traits that are not dyn-compatible (same section). An
autoref-specialisation probe cannot name a certificate that may not exist. Revisit
only if Rust gains a stable way to test for an associated item.

### T12. Type aliases, `use` renames and generic `T::default()` in the token rule (driver-only)

**Current.** The token rule sees names, not types (`TODOs/strict-open-items.md`,
items 5 and 10). Measured (N4): `#[fip]` accepts `V::with_capacity` with
`type V = Vec<u8>`, `Seq::with_capacity` with `use Vec as Seq`, and `T::default()`.
The driver reports all three (error, error, and a warning plus an error at the
allocating instantiation). Strict mode rejects inferred constructors
(`TODOs/fip-prelint.md`, "one normaliser for constructor spellings").

**Candidates.**

1. **Stays driver-only** (recommended).
2. `fip_testkit::srcmodel` could resolve module-level `type` and `use` aliases of
   heap types (it already resolves module-aware paths for the call graph). That would
   close the alias and rename cases for the token checker in tests, but not for
   `#[fip]` at expansion.
   - Effort S–M.
   - It still leaves `T::default()` to the driver, which is decidable only per
     instantiation.

### T13. Preconditions: nonlinear, heap-dependent, reified

**Current.** The domain is difference bounds (`value.rs:9-24`). `fip::requires` takes
linear comparisons over integer parameters, `p.len()` and constants (limits plan L1).
Measured (N4):

- interval-expressible products pass;
- relational nonlinear guards are reported;
- slice-element guards are reported;
- `Cell` guards are reported (correctly);
- fields behind `&T: Freeze` pass;
- a reified function with `requires` gets a note "precondition is not checked where
  it is called" (`preconditions`).

**Candidates.**

1. **Constant-index element access paths** (S–M): `(*p)[c]` for a constant `c` behind
   a shared reference to a `Freeze` slice, guarded by a proved `c < len(p)`. These are
   tracked like field paths.
   - *Soundness:* same as L2's access paths.
   - It covers `xs[0] < ys.len()`.
2. **Extend `fip::requires` to access paths** (`w.n`, `xs[0]`) of parameters behind
   `&T: Freeze` (S). Same assume-guarantee. Call sites must entail them.
3. **Products with a constant factor and bounded variables** (M): add a "product
   cell" `x·y ≤ c` only when both factors have interval bounds, which are then
   difference-bound facts on a fresh variable. A relational nonlinear guard
   (`a·m + b < n·m`) needs a polyhedral or nonlinear domain. Rejected: cost and the
   termination risk of widening.
4. **Verus as an oracle for panic freedom** (L, trust change). `just verify-*` runs
   with `--no-cheating`, and Verus proves the absence of arithmetic overflow and
   out-of-bounds indexing in verified exec bodies under their `requires`.
   - A verification run could emit a stamped sidecar ("verified bodies": path,
     source hash of the item, Verus version). The driver would then drop **only the
     body-local** overflow and bounds panic sites of a listed function whose hash
     matches.
   - Call sites outside Verus-verified callers still carry the precondition
     obligation. They remain notes ("precondition verified by Verus only for Verus
     callers") unless the linear subset of `fip::requires` covers it.
   - *Trust:* Verus, plus the sidecar's provenance (hash mismatch: not used).
   - Effort L.
   - It resolves `fip-core`'s verified functions, but not the test crates' notes,
     which are unverified.

**Stays.** Nonlinear relational guards, quantified preconditions, and facts about
mutable heap or interior mutability. They stay reported as panic paths (notes or
errors by mark). Reified functions with `requires` keep their note.

**Tests.** `preconditions`:

- the `xs[0] < ys.len()` pass (1);
- an access-path `requires` (2);
- a `Cell` control stays reported;
- the relational control stays reported;
- for 4, a sidecar for one verified function, and a stale-hash control.

### T14. The remaining self-check notes, and the profile the driver analyses

**Current.** N1: 15 overflow, 8 `handle_alloc_error`, 2 contract-allows-panic,
1 `assert!`. N6: under `--release` the driver analyses debug assertions and overflow
checks that the profile does not have.

**Candidates.**

1. **Analyse the profile's arithmetic and assertion semantics** (S, recommended
   first). When the driver replaces the opt-level with `-Copt-level=0`
   (`main.rs:73-74`), it adds `-Cdebug-assertions=<v>` and `-Coverflow-checks=<v>`
   with the values the original arguments implied: an explicit flag if cargo passed
   one, else the defaults of the original opt-level.
   - *Soundness:* the analysed MIR then has exactly the checks of the profile's
     build.
   - Under `overflow-checks = false`, overflow becomes wrapping (no panic, so not a
     FIP issue).
   - A note's text then states the profile.
   - Also locate the extra `dedup_by` note under `--release` (N6) before landing.
   - Dev-profile runs (`just prelint`) are unchanged.
   - **Implemented** (item 1): as proposed. The `dedup_by` note came from the host
     unit of `fip_core` built for the proc macro with cargo's `build-override` profile
     (no overflow checks): without the `w - 1` overflow assert the value analysis cannot
     prove `w >= 1` (a Verus invariant). It now appears for the target unit too.
     `--release` self-check: 13 notes (0 overflow, 2 `dedup_by`). **Deviation:** note
     texts do not state the profile (a check's note exists only when the profile has
     the check). Details: `TODOs/fip-prelint.md`, "Resolved 2026-11-03: the profile's
     overflow checks and debug assertions".
2. **Overflow notes (15).** All measured cases are real unguarded `+`/`*` in tests and
   in `fip_fn!` closures. **Stay** as notes (non-strict marks allow panics; under
   `panic_macros = false` they are errors, as N4's `add_err` shows). No suppression.
3. **`handle_alloc_error` (8).** Real: an allocation can fail. Report these under a
   distinct label, "allocation failure path (diverges)", in roots that permit
   allocation (`n ≥ 1`), so the reader can tell them from logic panics (S).
   Verdicts are unchanged: still a note, and an error under `panic_macros = false`.
   **Stays** reported.
4. **Contract allows panics (2).** Correct. The user-level fix is
   `#[fip(strict = true, panic_macros = false)]` on the contract. **Stays.**
5. **`assert!` (1).** Real, in the deliberate `strict_gaps` test. **Stays.**

**Tests.**

- A fixture `profiles` with `a + b` under the release profile:
  - with `overflow-checks = false`: no note;
  - with `[profile.release] overflow-checks = true`: a note;
  - a `debug_assert!` that appears only in dev.
- The self-check gains a `--release` variant expectation.

### T15. Generic warnings ("only relative to its generic parameters")

**Current.** A bare `drop(T)`, an uncontracted `<T as Trait>::m`, and calls of an
unbounded callable parameter are terms, which are warnings (`report.rs:640`;
limits plan L5). Each instantiation is checked where it is analysed.

**Decision. Stays.** The value depends on the instantiation, and the instantiation is
checked. The existing user-level fixes:

- `param(g = K)`, which instantiates terms (`Cost::instantiate`, `analysis.rs:220-224`);
- contracts on trait methods (exist);
- `fip::alloc_source` on trait declarations.

Optional (S): a `T: FipDrop`-style marker would let a generic body claim `drop(T)` is
free-free. Rejected: it is a trait the user must implement for every type, and it is
unverifiable without the driver.

### T16. Drop shims rustc cannot build

**Current.** `⊤` (`analysis.rs:1596-1603`; `generics` `drop_rows`). **Stays.** It is a
rustc limitation (an internal compiler error caught). Revisit on repin
(`just prelint-repin`).

### T17. Unmarked pure-Rust allocators (declared assumption)

**Current.** A pool that hands out slots of its own buffer passes (N3: four unmarked
roots; N4: `Pool::alloc`). The README row states the assumption, and `fip::export`
crates must mark their pools (limits plan L7, "Never fully solved").

**Decision.** Keep the declared assumption. Add **one** optional mitigation, clearly
labelled heuristic:

- `cargo fip-prelint --pool-hints` (off by default; never changes a verdict, the exit
  status or the summary counts) prints `note: fip-prelint: heuristic: ..` for
  candidate pool APIs in crates that declare `fip::export`. A candidate is a method
  `&mut self -> Option<&mut [T]> | Option<&mut T> | Option<usize> | Result<..>` whose
  body writes an integer field of `self` (bump index or free-list head) and returns a
  borrow of, or an index into, an array/slice field of `self`, and whose type has a
  method that resets that field, or writes `None`/`take()` into a slot.
- *Why opt-in:* the property is about intent (L7). Ring buffers, stack-allocated
  vectors and parsers match the same shape, so a default warning would flood.
- *Measurement before landing:* hits on fixture `alloc_sources` (unmarked arena and
  slab: expected hits), on the workspace (expected 0), and on `/tmp/tp-m3` (expected
  `Arena`, `Slab`, `Pool`). Report precision as measured.
- Effort M (1.5 days). Low priority.

**Rejected.** A default warning or `⊤` for pool-shaped code: unsound to rely on, and
noisy. Treating any `&mut self` method returning a borrow of `self`'s buffer as an
allocation: it changes the meaning of FIP for ordinary data structures.

### T18. Kept as they are

These are unchanged from the limits plan, sound and reported:

- `MAX_NODES` "analysis limit" `⊤`;
- the value analysis giving up above `MAX_VARS`/`MAX_CELLS` or its budget (asserts
  stay);
- unwind blocks not counted;
- crates without `fip::export`, and exported crates built without MIR (N2), which are
  user configuration with a specific message;
- FFI "neither / both / conflict / ABI" errors, which are verdicts by design
  (2026-11-01 amendments).

## Items that should stay reported limits

1. Function pointers from FFI, mutable memory or unanalysed call results (T1).
2. `dyn` calls without a contract, and implementations in crates without
   `fip::export` (T6).
3. Formatting through `dyn` values of unknown origin, and any `std` function not
   seeded (T7a/i).
4. Stack frames on Mach-O/COFF/WASM, undeclared runtime functions, roots inlined
   everywhere, and generic roots with no instance (T8).
5. Macro-generated crate attributes (T9).
6. Non-strict implementations of strict contracts and the token rule's alias,
   rename and `T::default()` cases: checked by the driver only (T11, T12).
7. Nonlinear relational, quantified and heap-dependent preconditions (T13).
8. Real panic paths: overflow, allocation failure, `assert!`, and contracts that
   allow panics (T14).
9. Generic terms (`drop(T)`, uncontracted `<T as Trait>::m`) at the generic root
   (T15).
10. rustc drop-shim internal compiler errors (T16).
11. Unmarked pure-Rust allocators (T17), as a declared assumption.

## Recommended order

| # | item | depends on | effort | expected measurable change |
|---|---|---|---|---|
| 1 | T14.1 profile semantics (and locate the `dedup_by` release note) | — | S | `--release` self-check without overflow notes for `overflow-checks = false`; dev unchanged |
| 2 | T1.1–1.3 constants, immutable statics and tables, local aggregates | — | M | N4 `fnptr_const`, `fnptr_static`, `fnptr_static_table`, `fnptr_local_struct` pass |
| 3 | B callable bindings | — | M | infrastructure; no verdict change alone (predicted) |
| 4 | T3 `Fn` shim, T2 `Box<dyn Fn*>` | 3 | S + S | `gen_declared`, `generic_with_fnptr_local`, `box_dyn_fn` pass; `param_bounds::fn_pointer` call site resolved where the origin is known |
| 5 | T4.3 private-function inference | 3 | M | `mid`-style private helpers lose their call-site report |
| 6 | T7c/d/e/h seed and table extensions | — | S | float, `u128`, math, `hashbrown` cases get verdicts |
| 7 | T7a/b debug builders and `PadAdapter` | — | L | `{:?}`, `{:#?}` on derived `Debug` pass into a buffer; the 3 sidecar `top` lines gone |
| 8 | T7g thread locals (with T1.2) | 2, 3 | M | `TL.with`, `HashMap::new` get verdicts (prediction) |
| 9 | T5 contracts with `param` | 3 | M | `visit(&self, g: &dyn Fn)` contracts |
| 10 | T13.1/13.2 element paths, access-path `requires` | — | S–M | `idx_heap` passes; controls stay |
| 11 | T7j sidecars for every installed `std` target | 6, 7 | M | wasm32 `std_summaries` equals host |
| 12 | T8d, T8b, T8a (AArch64 ELF), T8e/f, T8c | — | S, S, M, M+M, M | more bounded roots in fixture `stack`; per-target expectations |
| 13 | T1.4 certified function pointers | 3 | M | fields of `Certified<N, fn>` type pass |
| 14 | T14.3 allocation-failure label | — | S | wording only |
| 15 | T17 `--pool-hints` | — | M | heuristic notes, opt-in |
| 16 | T13.4 Verus panic-freedom sidecar | — | L | `fip-core` body panic sites dropped by provenance (trust change, needs a user decision) |
| — | T6, T9, T10, T11, T12, T15, T16 | — | — | stay; T9.3 / T10.2 / T12.2 only on demand |

The total for items 1–15 is about 25–32 agent-days (an estimate). Item 16 is
separate, because it changes what is trusted. Items 1, 2, 6 and 10 have no
dependencies. Item 1 comes first because it changes which code is analysed. Every
item lands with:

- its fixtures;
- a `TODOs/fip-prelint.md` section with before/after numbers;
- an amendment to `docs/decisions/2026-11-01-fip-prelint.md`;
- the README row updated, including the stale self-check numbers of N1.

## What would reopen this

- A stable MIR / `rustc_public` API, or a repin that changes MIR shapes (the
  `Box`/`Fn`-shim projections of T2/T3, `LocalKey`'s layout for T7g).
- LLVM emitting frame sizes for Mach-O/COFF (T8a).
- Rust gaining a stable test for the existence of an associated item (T11).
- A user decision to trust Verus results in the driver (T13.4).
- A use case for macro-generated crate attributes (T9.3) or for strict calls through
  another FFI declaration (T10.2).

## Appendix: probe sources (`/tmp/tp-m3`, N3/N4)

The workspace has members `slab`, `app`, `galloc`, `limits` (copied from the limits
plan's `/tmp/pd-allocprobe`, unchanged), plus `top`, `tok` and `cdep2`.

`top/src/lib.rs` (abridged; each root `#[cfg_attr(fip_prelint, fip::mark(..))]`,
`kind = "fip"` unless stated):

```rust
pub fn plus1(v: u8) -> u8 { v.wrapping_add(1) }
pub fn twice(v: u8) -> u8 { v.wrapping_mul(2) }
pub struct Ops { pub f: fn(u8) -> u8 }
pub fn fnptr_field(o: &Ops) -> u8 { (o.f)(1) }
pub fn fnptr_local_struct() -> u8 { let o = Ops { f: plus1 }; (o.f)(1) }
pub static TABLE: [fn(u8) -> u8; 2] = [plus1, twice];
pub fn fnptr_static_table(i: u8) -> u8 { TABLE[(i & 1) as usize](3) } // strict, panic_macros = false
pub static ONE: fn(u8) -> u8 = plus1;   pub fn fnptr_static(x: u8) -> u8 { ONE(x) }
pub const CONE: fn(u8) -> u8 = plus1;   pub fn fnptr_const(x: u8) -> u8 { CONE(x) }
pub fn pick(b: bool) -> fn(u8) -> u8 { if b { plus1 } else { twice } }
pub fn fnptr_returned(b: bool) -> u8 { pick(b)(1) }
pub trait Shape { /* fip::mark(kind = "fip") */ fn area(&self) -> u32; }
pub fn box_dyn_recv(b: &Box<dyn Shape>) -> u32 { b.area() }
pub fn box_dyn_fn(g: &Box<dyn Fn(u8) -> u8>) -> u8 { g(1) }        // param(g = 0)
pub fn ref_dyn_fn(g: &dyn Fn(u8) -> u8) -> u8 { g(1) }             // param(g = 0)
pub fn apply<G: Fn(u8) -> u8>(g: G) -> u8 { g(1) }                 // param(g = 0)
pub fn generic_with_fnptr_local() -> u8 { let p: fn(u8) -> u8 = plus1; apply(p) }
pub fn gen_declared(p: fn(u8) -> u8) -> u8 { apply(p) }            // param(p = 0)
pub fn apply_ptr(p: fn(u8) -> u8) -> u8 { p(1) }                   // param(p = 0)
pub fn mid(q: fn(u8) -> u8) -> u8 { apply_ptr(q) }                 // not a root
pub fn through_mid() -> u8 { mid(plus1) }
pub fn dbg_derive(b: &mut Buf, p: &Pt) -> fmt::Result { write!(b, "{p:?}") } // fbip; Pt: derive(Debug)
pub fn float_disp(b: &mut Buf, x: f64) -> fmt::Result { write!(b, "{x}") }   // fbip
pub fn print_it(x: u32) { println!("{x}") }                                  // fbip
pub fn float_math(x: f64) -> f64 { x.sqrt() + x.sin() }                      // fbip
pub fn add_note(a: u32, b: u32) -> u32 { a + b }                   // strict
pub fn add_err(a: u32, b: u32) -> u32 { a + b }                    // strict, panic_macros = false
pub fn idx_heap(xs: &[usize], ys: &[u8]) -> u8 { if xs.len() > 0 && xs[0] < ys.len() { ys[xs[0]] } else { 0 } }
pub fn nonlinear2(xs: &[u8], n: usize, m: usize, a: usize, b: usize) -> u8 {
    if a < n && b < m && n.checked_mul(m).is_some_and(|nm| nm <= xs.len()) { xs[a * m + b] } else { 0 } }
pub fn hashmap_new() -> usize { std::collections::HashMap::<u8, u8>::new().len() } // fbip
std::thread_local! { static TL: Cell<u32> = const { Cell::new(0) }; }
pub fn tls_get() -> u32 { TL.with(|c| c.get()) }
```

`tok/src/lib.rs` (with `fip-macros`, `fip-strict`; `cdep2` declares
`unsafe extern "C" { pub fn labs(x: c_long) -> c_long; }`):

```rust
type V = Vec<u8>;  use std::vec::Vec as Seq;
#[fip] pub fn alias_alloc() -> usize { let v: V = V::with_capacity(4); v.capacity() }
#[fip] pub fn rename_alloc() -> usize { let v: Seq<u8> = Seq::with_capacity(4); v.capacity() }
#[fip] pub fn generic_default<T: Default>() -> T { T::default() }
mod ffi { #[fip_macros::fip_extern] unsafe extern "C" {
    #[fip_cert(evidence = "C standard 7.24.6.1", allocs = 0)] pub fn labs(x: c_long) -> c_long; } }
#[fip(strict = true)] pub fn strict_local(x: c_long) -> c_long { unsafe { ffi::labs(x) } }
#[fip] pub fn plain_other(x: c_long) -> c_long { unsafe { cdep2::labs(x) } }
#[fip(strict = true)] pub fn strict_other(x: c_long) -> c_long { unsafe { cdep2::labs(x) } } // E0425
```

Commands:

- driver build as in "Measurements";
- per workspace:
  `FIP_PRELINT_TARGET_DIR=/tmp/tp-fx/<name> FIP_PRELINT_DRIVER_PATH=/tmp/tp-prelint-target/debug/fip-prelint FIP_PRELINT_TOOLCHAIN=1.99.1 /tmp/tp-prelint-target/debug/cargo-fip-prelint fip-prelint --message-format short`
  (`--warn-only` for the self-check, `--stack [--release]` for `stack`).
