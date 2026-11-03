<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# Brainstorm: `fip_fn!` and strict higher-order ergonomics

**Status:** BRAINSTORM, 2026-11-03; shortlist being implemented (each idea's
**Status** line says what landed and where).
**Measured with:**

- rustc 1.99.1;
- Verus `0.2026.10.18.7d82994` (upstream, `/usr/bin/verus`);
- the fork `0.2026.10.31.559ac52` (`$HOME/Y4/verus-fork/.../verus`, `VERUS_Z3_PATH=/usr/bin/z3`);
- `fip-prelint` built from `d127bc4`.

Probe files are under `/tmp/tp-verus/p` and `/tmp/tp-m3/tok`. They are summarised in
the appendix.

## The pain, as measured

- `fip_fn!` takes only a closure (`crates/fip-macros/src/lib.rs:3462-3522`;
  `closure_shape`, `3529-3534`, accepts `move` or `|` as the first token).
  - `fip_fn!(inc)` for a named function gives "fip_fn!: expected a closure `|args|
    body`" (probe Q6).
  - So does a closure with a leading attribute (`#[cfg_attr(verus_keep_ghost,
    verus_spec(..))] |x: u32| ..`).
- Under Verus, `Certified<N, C>`'s `pre`/`post` are `C`'s `requires`/`ensures`
  (`crates/fip-strict/src/lib.rs:349-366`). A `fip_fn!` closure has neither, so its
  `post` says nothing.
- A verified caller that needs the step's specification therefore hand-writes
  (`verify/compose_state.rs:114-121`):

  ```rust
  let f = unsafe {
      fip_strict::Certified::<{ __fip_strict_tick_checked.allocs_for("tick_checked") }, _>::assume(tick_checked)
  };
  ```

- A **strict** function cannot write that line at all. The strict scan rejects
  `.allocs_for(..)` ("method call .. cannot be resolved") and, in the path form
  `Cert::allocs_for(__fip_strict_tick, "tick")`, rejects
  `Certified::<..>::assume` ("generic arguments in a callee path cannot be resolved")
  (probe T4, `tok`). So a strict caller cannot pass a specified named function to
  a strict combinator today.
- The strict scan's restrictions apply inside `fip_fn!` bodies too. For example,
  method calls are rejected: `c.wrapping_add(1)` in a strict body gives
  "method call `.wrapping_add(..)` cannot be resolved; call it by path" (probe T4).

## Key measurements

| # | probe | upstream Verus | fork | plain rustc 1.99.1 |
|---|---|---|---|---|
| V1 | `verus_spec(r: u32 => requires x < 10, ensures r == x + 1)` attribute (via `cfg_attr(verus_keep_ghost, ..)`) on a closure passed to `Certified::<0, _>::assume`, then to a generic `apply` requiring `f.pre`/ensuring `f.post`; the caller proves `r == 6` | 2 verified, 0 errors | same | compiles (no error, no warning): `cfg_attr` on a closure in argument position is accepted on stable when the cfg is off |
| V1-neg | same, the caller claims `r == 7` | rejected (postcondition not satisfied) | same | — |
| V1-cap | same with `move |x: u32| x + k`, `ensures r == x + k`, the caller requires `k < 3` | 2 verified | same | — |
| V1-feat | adding `#![feature(stmt_expr_attributes)]` | error: "the feature `stmt_expr_attributes` has already been enabled" (Verus enables it itself) | same | — |
| V2 | `Certified::<0, _>::assume(inc)`, a named function with `verus_spec` | 3 verified | same | compiles |
| V3 | same with a generic `id::<u32>` and an associated `K::add2` (impl under `cfg_attr(verus_keep_ghost, verus_verify)`; without it: E0425 "cannot find function `add2`") | 4 verified | same | — |
| V4 | a hand-written ZST `IncFn` with `unsafe impl FipBound` and `impl FipFn<(u32,)>` in `verus! { }`, `pre`/`post` = `inc.requires(args)`/`inc.ensures(args, out)` | 5 verified | same | (the probe declares it only under Verus) |
| V5 | `verus_exec_expr!(|x: u32| -> (r: u32) requires x < 10 ensures r == x + 1 { x + 1 })` in an attribute-mode body | 2 verified | same | "cannot find macro `verus_exec_expr`" (must be emitted only under Verus) |
| V6 | capture-free closure coerced to `fn(u32) -> u32` in a verified body | "does not yet support .. casting a pointer (here the cast is implicit)" | same | compiles |
| Q1 | `let f: Certified<_, _> = fip_fn!(..)`; `Certified::<0, fn(u8) -> u8>::assume(closure)`; a generic `Compose<F, G>` with `const ALLOCS = F::ALLOCS.saturating_add(G::ALLOCS)`; `fn d() -> impl FipFn<(u8,), Output = u8>` returning `fip_fn!`; reading `F::ALLOCS` from it | — | — | all compile |
| Q2 | `#[fip_macros::fip] |x: u8| x` (proc-macro attribute on a closure expression) | — | — | E0658 "attributes on expressions are experimental", "macro attributes on expressions are unstable" |
| Q6 | `fip_fn!(#[cfg_attr(..)] |x| ..)`, `fip_fn!(inc)`; `fip_fn!(|x: u32| -> u32 { x + 1 })` | — | — | "expected a closure" ×2; the third (explicit return type) compiles |
| D1 | driver: `#[fip] named_ok` passing `Certified::<{cert}, _>::assume(tick)` to `apply0` (`param(g = 0)`) | — | — | passed |
| D2 | driver: `named_lie`, `Certified::<0, _>::assume(boxy)` (`boxy` allocates once) to `apply0` | — | — | error "passes .. an argument for `g` that may allocate 1 time(s) per call": the driver analyses the function, not the claimed `N` |

Source facts used below:

- Verus's attribute rewriting has a closure case (`/opt/verus/builtin_macros/src/attr_rewrite.rs:851-895`).
- It requires a return type, either a closure annotation or `r: T =>` (`865-868`).
- It rejects `with` on closures (`855-857`).
- `fip-macros` recognises Verus's driver at expansion (`under_verus`,
  `crates/fip-macros/src/strict.rs:906-912`).

## Ideas

Each idea has a sketch, how it works, the soundness and trust impact (where
`unsafe`/trust moves), Verus compatibility, and cost (S ≤ 0.5 day, M 1–3 days,
L 3–5 days; estimates).

### 1. `fip_fn!(path)` for function items with a certificate

**Status:** Implemented in 6dbbf4b. As sketched, plus certified function
pointers (idea 5's safe half). Measured:

- `fip_fn!(inc)`: before "expected a closure `|args| body`", after it compiles;
  `fip_fn!(plain)` (no certificate): E0425 "cannot find value `__fip_strict_plain`";
  `fip_fn!(1 + 2)`: "expected a closure `|args| body` or the path of a function with
  a certificate (..)".
- `crates/fip-macros/tests/fip_fn_path.rs` (`#![forbid(unsafe_code)]`): free,
  generic (`id::<u32>`), `#[fip_impl]` (`<Slot<u8>>::get`, bound 1 for `boxed`) and
  trait-impl (`<Ticker as Step>::step`) functions; `core::mem::swap::<u8>` (bound 0)
  and `Box::new` (bound 1); strict callers passing `fip_fn!(tick)` to
  `fip_core::strict::map_in_place_st` and `fip_fn!(id::<u32>)`, `fip_fn!(double)` to
  a `param(g = 0)` callee.
- `let t: [Certified<0, fn(u32) -> u32>; 2] = [fip_fn!(double), fip_fn!(id::<u32>)]`
  compiles: the expected type reaches `Certified::assume`'s argument, a coercion
  site, so the item becomes a pointer while the bound stays the certificate's. A
  wrong `N` is "mismatched types" (`compile_fail` example). Capture-free closures
  work the same way. Plain Rust only (V6).
- `verify/compose_state.rs`: `number_from_11_strict` uses `fip_fn!(tick_checked)`;
  compose_state 9 verified, 0 errors on upstream Verus and on the fork (as before);
  `just verify-negative` controls unchanged and rejected.
- `fip_testkit::summaries`: a `fip_fn!(two)` argument (bound 2) against
  `param(make = 1)`: before `bound: Unknown`, after `Finite(2)`; also through
  `let f = fip_fn!(..)` and for `f::<T>`. Qualified method paths and std constructors
  as values stay `Unknown` there (so the scanned test passes the trait method only
  through `.call`).
- `fip-prelint` fixture `param_bounds`: `fip_fn!(flip)` and its `Certified<0, fn>`
  form pass (19 roots, 12 passed; before 18, 11).
- Not done: `Type::<T>::m` stays rejected as in strict calls (write `<Type<T>>::m`).

```rust
let f = fip_fn!(tick_checked);                 // free function
let g = fip_fn!(shapes::Slot::<u16>::boxed);   // #[fip_impl] method
let h = fip_fn!(<Ticker as Step>::step);       // trait-impl method
```

**How.**

- When the input is a path, not a closure, emit exactly the compose_state line:
  `unsafe { Certified::<{ <checks>; <bound of path> }, _>::assume(path) }`.
- "Bound of path" reuses the strict callee resolution: `a::f` reads
  `a::__fip_strict_f` through `Cert::allocs_for("f")`, and methods read the
  `#[fip_impl]` / `#[fip_trait]` certificates.
- A function without a certificate fails like a strict call of it (E0425 on
  `__fip_strict_f`), which idea 9 can improve.
- No item is declared, so the expression stays valid inside Verus-verified bodies
  (`fip_fn_wrapper`'s rule, `lib.rs:3573-3576`).

**Trust.**

- The `unsafe` moves from the call site into macro output, which is where
  closure `fip_fn!` already puts it.
- The bound is the function's generated certificate, name-checked in constant
  evaluation.
- The remaining loophole is the existing one: a same-named certificate imported from
  another module (`crates/fip-strict/src/lib.rs:25-28`).
- In plain builds a strict caller gets a specified, certified named function without
  writing `unsafe`, which it cannot do at all today (T4).
- The driver is unaffected: it resolves the `FnDef` and analyses the body (D1). A
  wrong claim is caught (D2).

**Verus.** Measured: named, generic and associated functions through
`Certified::assume` verify on both builds (V2, V3). `pre`/`post` are the function's
`requires`/`ensures`. The const block with `allocs_for` inside a verified body is what
`verify/compose_state.rs:117-119` already does under `just verify-compose`.

**Cost.** S–M. It needs path parsing (generic arguments, `<T as Tr>::m`) and reuse of
the strict callee lookup. Tests:

- compose_state rewritten with `fip_fn!(tick_checked)`;
- a strict caller passing `fip_fn!(f)`;
- `compile_fail` for an uncertified function and for a non-path.

### 2. Accept a spec attribute on the closure inside `fip_fn!`

**Status:** Implemented in the commit "fip-macros: spec attributes on fip_fn!
closures (fip-fn ergonomics 2)". `closure_shape` skips leading `#[..]` and the
output keeps them on the closure; `fip_testkit`'s `fip_fn!` parser skips them too.
Measured:

- before: `fip_fn!(#[cfg_attr(verus_keep_ghost, verus_spec(..))] |x: u32| -> u32 { x + 1 })`
  gave "expected a closure `|args| body`"; after: compiles (plain rustc 1.99.1, no
  warning in the workspace, which declares `cfg(verus_keep_ghost)`).
- `verify/compose_state.rs` `number_from_11_closure`: the `tick_checked` step as a
  closure with `verus_spec(r: (u32, u32) => requires c < 1000, ensures r.0 == c + 1,
  r.1 == r.0)` passed to `fip_core::strict::map_in_place_st`, with the same
  invariant and postcondition as `number_from_11_strict`: compose_state 10 verified,
  0 errors (9 before) on upstream Verus and on the fork.
- Negative controls in `just verify-negative`: without the attribute,
  "possible arithmetic underflow/overflow" in the closure and "assertion failed" at
  the caller's `map_st_fip_inv` (the closure's `post` says nothing); with `ensures
  r.0 == c + 2`, "unable to prove post-condition of closure". Both rejected on both
  builds.
- Plain tests (`tests/fip_fn_path.rs`): an attributed closure and an attributed
  capturing `move` closure with a second, ordinary attribute; bounds 0 and 1 as
  without attributes. `fip_testkit::summaries` still sees an attributed `fip_fn!`
  closure as a closure (`fip_fn_with_a_spec_attribute_is_a_closure`).

```rust
fip_fn!(#[cfg_attr(verus_keep_ghost, verus_spec(r: u32 => requires x < 10, ensures r == x + 1))]
        |x: u32| x + 1)
```

**How.** `closure_shape` skips leading outer attributes and keeps them on the closure
in the output. The strict body scan is unchanged: attributes are not body tokens.

**Trust.** None changes. The spec is Verus's business, and the bound is still the
body's.

**Verus.** Measured: the exact output shape (`unsafe { Certified::<N, _>::assume(#[attr]
closure) }`) verifies on both builds, the negative is rejected, and a capturing closure
works (V1, V1-neg, V1-cap). Plain stable rustc accepts the `cfg_attr` in that position
(V1). Verus requires a return type (attr_rewrite `865-868`). A strict closure needs
`-> T` or `r: T =>`, which `fip_fn!` already accepts (Q6).

**Cost.** S. Tests: a Verus gate in `just verify-compose` (closure spec used by
`map_in_place_st`), a plain doctest, and the negative control in
`just verify-negative`.

### 3. `requires`/`ensures` clauses in `fip_fn!` itself

```rust
fip_fn!(requires x < 10, ensures r == x + 1, |x: u32| -> (r: u32) { x + 1 })
```

**How.** Sugar over idea 2.

- Under Verus's driver (`under_verus`), emit `#[verus_spec(r: u32 => requires ..,
  ensures ..)]` on the closure.
- Alternatively, emit `verus_exec_expr!(|x: u32| -> (r: u32) requires .. ensures .. {
  .. })`, measured to verify on both builds (V5).
- Otherwise drop the clauses.
- `fip-macros` decides at expansion, as it does for `cfg(not(verus_keep_ghost))`
  (`TODOs/strict-open-items.md`, item 12), so no `unexpected_cfgs` warning appears
  downstream.

**Trust.** None. The clauses are unchecked text in plain builds, so a typo shows only
under Verus. That is the same as hand-written `cfg_attr(verus_keep_ghost, ..)`.

**Verus.** V1/V5 measured. `with` is not supported on closures (attr_rewrite `855-857`).
Ghost state must use the trace pattern of
`docs/notes/verus-fnmut-monadic-workaround.md`.

**Cost.** S after idea 2. Choose one emission (attribute or `verus_exec_expr!`). The
attribute keeps one code path with idea 2.

### 4. A generated ZST per strict function (auto-impl of `FipFn` for function items)

```rust
#[fip(strict = true)] pub fn tick_checked(c: u32, x: u32) -> (u32, u32) { .. }
// emits: pub struct __FipFn_tick_checked;  + FipBound/FipFn impls (plain and verus!)
let f = fip_fn!(tick_checked);   // could expand to `__FipFn_tick_checked`
struct Machine { step: __FipFn_tick_checked }  // nameable type
```

**How.**

- `#[fip(strict = true)]` emits a unit struct and
  `unsafe impl FipBound { const ALLOCS = <the certificate's bound> }`.
- It also emits `impl FipFn<(A0, ..)>` whose `call` forwards. Under Verus, `pre`/`post`
  are `f.requires(args)`/`f.ensures(args, out)`.

**Trust.** The `unsafe impl` is in generated code (as certificates are). There is no
`unsafe` at the call site.

**Verus.** Measured with a hand-written equivalent: verifies on both builds (V4).

**Costs and problems.**

- One item per strict function.
- Two declarations to keep in sync, which needs a drift test like
  `crates/fip-strict/tests/verus_drift.rs`.
- Reference arguments need HRTB impls (`for<'a> FipFn<(&'a T,)>`).
- Generic functions need `PhantomData<..>` and generics on the ZST.
- Arity is limited by `MAX_ARITY` (`crates/fip-strict/src/lib.rs:377`).

**Value over idea 1.** Only a nameable type (struct fields, no generic parameter).

**Cost.** M–L.

### 5. Certified function pointers (`Certified<N, fn(..)>`) and an `erase` coercion

```rust
let table: [Certified<0, fn(u8) -> u8>; 2] = [fip_fn!(plus1).erase(), fip_fn!(twice).erase()];
```

**How.** A safe `impl<const N: u64, F: Fn..> Certified<N, F> { pub fn erase(self) ->
Certified<N, fn(..) -> ..> }` for capture-free closures and function items, which keeps
`N`. This gives tables and struct fields of one type.

**Trust.** `erase` keeps the bound and makes no new claim. For the driver, calls
through such a value are pointer calls, today `⊤`. See
`docs/decisions/2026-11-03-fip-prelint-top-plan.md` T1.4: assume `N` at the call and
check every analysed construction.

**Verus.** Not usable in verified code: function pointers are unsupported (V6). Plain
Rust only.

**Cost.** S (fip-strict) + M (driver, T1.4).

### 6. Capture-free closure coercion to `fn` pointer in `fip_fn!`

`fip_fn!(as fn, |x: u8| x + 1)` yields `Certified<N, fn(u8) -> u8>` directly. This is
the closure-side half of idea 5. Verus rejects it (V6). Low value on its own, so
subsume it in idea 5. **Cost** S.

### 7. A `#[fip_closure]` attribute

```rust
let f = #[fip_closure] |x: u8| x + 1;
```

Measured: proc-macro attributes on expressions are unstable on 1.99.1 (Q2, E0658).
Verus enables `stmt_expr_attributes` itself (V1-feat), but plain builds cannot.
**Rejected** until `proc_macro_hygiene`/`stmt_expr_attributes` are stable.
Unmeasured: the statement form (`#[fip_closure] let f = ..;`), which is believed to be
gated too.

### 8. State-passing helpers for the `_st` combinators

Sketches:

- **Adapters in `fip-strict`.**
  - `st::stateless(f)`: lift `FipFn<(X,)>` to `FipFn<(S, X)>` as `|s, x| (s, f(x))`.
  - `st::pair(f, g)`: run two state steps.
  - Each is a generic struct with
    `unsafe impl<F: FipBound> FipBound { const ALLOCS = F::ALLOCS }`, written once and
    audited in `fip-strict`. The associated-const form compiles on stable (Q1,
    `Compose`).
  - Under Verus, the adapter's `pre`/`post` would be defined from `F`'s
    (`pre((s, x)) = f.pre((x,))`, `post((s, x), (s2, y)) = s2 == s && f.post((x,), y)`).
- **`fip_fn_st!(state c: u32, |x: u32| -> u32 { .. })`.** Sugar that expands to
  `|c: u32, x: u32| -> (u32, u32)`, returning `(c', y)`, with the body binding a
  mutable local `c` written back. It keeps the plain `Fn` shape that the workaround
  note requires (no `FnMut`).
- **An invariant helper** for `map_st_fip_inv(xs, f, s0, inv)` assertions
  (compose_state.rs:120) as a `proof!` snippet macro.

**Trust.** Adapters: one audited `unsafe impl` per adapter, and none at call sites.
Sugar: none.

**Verus.** Unmeasured: adapter `pre`/`post` in `verus!` impls over a generic `F:
FipFn`, which is the key risk, especially triggers on `f.pre` inside the
`map_st_*_inv` quantifiers. Sugar: the result is an ordinary closure, so V1 applies
if a spec is attached.

**Cost.** M (adapters plus a Verus probe first), S (sugar).

### 9. Better error messages

- `fip_fn!(f)` while idea 1 is missing: say "named functions: write `fip_fn!(f)` once
  supported / see idea 1". With idea 1: "`f` has no certificate: mark it
  `#[fip(strict = true)]`". Today the user sees E0425 on `__fip_strict_f`, as in the FFI
  probe (E0425 "cannot find value `__fip_strict_labs` in crate `cdep2`").
- `#[diagnostic::on_unimplemented]` (stable) on `FipFn`/`FipBound`: "a plain closure
  carries no allocation bound; wrap it with `fip_fn!(..)`". This applies when a raw
  closure is passed where `F: FipFn` is required.
- Leading attribute or `requires` in `fip_fn!` before ideas 2 and 3: a specific message
  instead of "expected a closure".

**Trust.** None. **Verus.** Diagnostics only. **Cost** S.

### 10. Bound checks at the creation site; integration with `param(g = K)`

```rust
apply0(fip_fn!(bound <= 0, |x: u8| x ^ 1))
```

**How.** `fip_fn!(bound <= K, ..)` adds `const { assert!(N <= K) }` with a concrete `N`
at the closure. This runs under `cargo check`, unlike a check inside the generic
callee, which is post-monomorphisation and so INHERENT under `cargo check`
(`TODOs/strict-open-items.md`, item 7). The callee's `param(g = K)` stays the
authoritative declaration, and the driver checks every call site. This is only an
earlier, local error. A `Certified<_, _>` annotation (Q1) lets users state the
expected bound in a type instead (`let f: Certified<0, _> = fip_fn!(..)` fails with a
type mismatch if `N ≠ 0`).

**Trust.** None. **Verus.** A const block in a verified body (as compose_state's).
**Cost** S.

### 11. Driver-checked `fip_fn!` (defer the bound to `fip-prelint`)

```rust
fip_fn!(prelint, 1, |x: u8| x.wrapping_add(1).count_ones() as u8)
```

**How.**

- No strict token scan of the body. Method calls, `use` aliases and inferred types are
  allowed: the scan rejects them today (T4).
- The macro emits `unsafe { Certified::<1, _>::assume(c) }` and nothing else. The
  driver checks **every** `Certified::assume` construction in analysed MIR: the
  closure's analysed bound must be ≤ `N` (assume `N` at uses, guarantee at
  construction).
- It counts these in the crate summary as "N driver-checked certified closures".

**Trust.** In plain builds without the driver, the claim is unchecked. Trust moves
from the macro to the driver run, so it must be in CI. This is weaker than today's
`forbid(unsafe_code)` story (`crates/fip-strict/src/lib.rs:30-38`): crates that rely on
"no certificate without a check at compile time" should not enable it. One option is a
crate-level opt-in (`#![cfg_attr(fip_prelint, fip::driver_certified)]`), without which
`prelint` is a compile error.

**Verus.** Unaffected: the bound is a const, and specs via idea 2.

**Cost.** M (driver: construction check; macro: mode).

### 12. Panic strictness in `FipBound`

`FipBound` carries only `ALLOCS`. A `panic_macros = false` strict callee receiving
`F: FipFn` cannot demand a panic-free argument at compile time, so only the driver
checks it. Sketch:

- `const NO_PANIC_MACROS: bool = false;` as a defaulted associated const, so existing
  impls compile.
- `Certified<N, C, const P: bool = false>`.
- `fip_fn!` sets `P` when the scan ran with `panic_macros = false`.
- Callees with `panic_macros = false` and `param(g = K)` assert `F::NO_PANIC_MACROS`.

**Trust.** It mirrors `Cert::no_panic_macros` (`TODOs/fip-prelint.md`, "`#[fip_impl]`
compares panic strictness"). The assertion is post-monomorphisation in a generic
callee (see idea 10).

**Verus.** Unmeasured: const generic defaults on a struct declared in `verus!`.

**Cost.** M.

### 13. Composition combinators

`fip_strict::compose(f, g)`, `then`, `map_output`, each a struct with
`ALLOCS = F::ALLOCS + G::ALLOCS` (saturating). The associated const compiles on stable
(Q1). Under Verus, `pre` would be `f.pre(a) && forall|r| f.post(a, r) ==> g.pre((r,))`,
which is unmeasured (triggers). **Trust:** an audited `unsafe impl` per combinator.
**Cost** M.

### 14. More arities

`MAX_ARITY = 4` (`crates/fip-strict/src/lib.rs:377`, mirrored in `fip-macros`
`lib.rs:3526`). Extending `certified_fip_fn!` to 8 is mechanical. Unmeasured: Verus
verification time per added impl (`just verify-strict` has 7 items today). **Cost** S.

### 15. Methods and trait methods as values

This covers the method forms of idea 1:

- `fip_fn!(Type::m)` via `#[fip_impl]` certificates;
- `fip_fn!(<T as Tr>::m)` / `fip_fn!(<dyn Tr>::m)` via `#[fip_trait]` (2026-11-01
  amendment, "Strict contracts without hand-written marks").

Verus needs `verus_verify` on the impl for associated functions (V3). **Cost** part of
idea 1. Generic methods need explicit turbofish.

### 16. `impl FipFn` in return position

Builders that return certified closures:
`fn step(k: u8) -> impl FipFn<(u8,), Output = u8> { fip_fn!(move |x: u8| x ^ k) }`.
This compiles today (Q1), and the bound is readable from the opaque type (`F::ALLOCS`,
Q1). Strict callers of `step` need its certificate (it is a strict function). Only
documentation is needed. **Cost** S (docs and an example).

## Ranking

| rank | idea | value | cost | risk | notes |
|---|---|---|---|---|---|
| 1 | 1 `fip_fn!(path)` | removes the hand-written `unsafe` and makes the pattern available to strict callers | S–M | low: V2/V3/D1/D2 measured | subsumes 15 |
| 2 | 2 spec attribute pass-through | specified closures for verified callers | S | low: V1 measured on both builds and on plain rustc | — |
| 3 | 9 error messages | — | S | none | do with 1 and 2 |
| 4 | 10 creation-site bound | — | S | none | — |
| 5 | 3 clause sugar | — | S (after 2) | low | optional over 2 |
| 6 | 8 state-passing adapters/sugar | — | M | medium: Verus specs over generic `F` unmeasured | probe first |
| 7 | 11 driver-checked mode | lifts the strict-scan restrictions | M | trust change | opt-in |
| 8 | 5 certified fn pointers (+6) | — | S + M | plain only (V6) | pairs with top plan T1.4 |
| 9 | 12 panic strictness in `FipBound` | — | M | Verus unmeasured | — |
| 10 | 13 composition | — | M | Verus triggers unmeasured | — |
| 11 | 14 arities | — | S | Verus time unmeasured | on demand |
| 12 | 4 generated ZST | — | M–L | drift, HRTB | only for nameable types |
| 13 | 16 `impl FipFn` docs | — | S | none | docs only |
| — | 7 `#[fip_closure]` | — | — | — | rejected (E0658, Q2) |

## Recommended shortlist

1. **Idea 1, `fip_fn!(path)`.**
   - Rewrite `number_from_11_strict` as `fip_fn!(tick_checked)`.
   - Add a strict caller passing a named function to `fip_core::strict::map_in_place_st`.
   - Add `compile_fail` cases for uncertified functions.
2. **Idea 2, attributes on the closure inside `fip_fn!`.**
   - Add a closure with `verus_spec` passed to a strict `_st` combinator in
     `verify/compose_state.rs`, with a negative in `just verify-negative`.
3. **Ideas 9 and 10** with the above: messages, and `fip_fn!(bound <= K, ..)`.
4. Then a **Verus probe for idea 8's adapters** (generic `F` `pre`/`post` in `verus!`
   impls on both builds) before deciding on 8, 12 and 13.
5. Keep **idea 11** as an explicit opt-in proposal for a user decision (trust moves to
   the driver). Do **idea 5** only together with the top plan's T1.4.

## What would change this

- Stable expression attributes (revisit 7).
- Verus support for function pointers (5/6 in verified code) or for `with` on closures
  (ghost outputs from steps).
- A change of the `forbid(unsafe_code)` guarantee (11).

## Appendix: probes

- `/tmp/tp-verus/p/p1_closure_spec.rs` (V1), `p1_neg.rs`, `p8_capture.rs` (V1-cap),
  `p2_named.rs` (V2), `p7_generic_method.rs` (V3), `p4_zst.rs` (V4),
  `p5_exec_expr.rs` (V5), `p3_fnptr.rs` (V6), `q1.rs` (Q1), `q2.rs` (Q2),
  `p6_macro_attr.rs` (Q6). Shape of V1:

  ```rust
  #[cfg_attr(verus_keep_ghost, verus_spec(r => requires f.pre((x,)), ensures f.post((x,), r)))]
  pub fn apply<F: FipFn<(u32,), Output = u32>>(f: F, x: u32) -> u32 { f.call((x,)) }
  #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == 6))]
  pub fn caller() -> u32 {
      let f = unsafe { Certified::<0, _>::assume(
          #[cfg_attr(verus_keep_ghost, verus_spec(r: u32 => requires x < 10, ensures r == x + 1))]
          |x: u32| x + 1
      ) };
      apply(f, 5)
  }
  ```

- Verus runs: `fip-strict` exported per build with
  `verus --crate-type=lib --crate-name fip_strict --no-cheating crates/fip-strict/src/lib.rs --export /tmp/tp-verus/<b>/fip_strict.vir --compile --out-dir /tmp/tp-verus/<b>`
  (7 verified on each). Probes ran with
  `--crate-type=lib --no-cheating --extern fip_macros=<so> --import fip_strict=.. --extern fip_strict=..`.
  `fip-macros` was built with `cargo +1.99.1 build -p fip-macros --target-dir /tmp/tp-verus/macros`.
- Driver probes D1/D2 and T4: `/tmp/tp-m3/tok/src/lib.rs` (`tick`, `boxy`, `apply0`,
  `named_ok`, `named_lie`; the strict variants behind feature `strict_ffi_other_path`).
