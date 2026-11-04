<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# Decision: driver-checked `fip_fn!` mode (`fip_fn!(prelint, N, ..)`)

**Status:** ACCEPTED and IMPLEMENTED, 2026-11-03, in the commit "fip-macros:
driver-checked fip_fn!(prelint, N, ..) (fip-fn ergonomics 5)" following the review
commit `4e64b70` (section "Implementation"). Review conclusion: implementable as
opt-in, default-off and never silently trusted without the driver (section
"Conclusion").
**Source:** `docs/notes/fip-fn-ergonomics-brainstorm.md`, idea 11 (shortlist item 5).
**Measured with:** rustc 1.99.1, `fip-prelint` built from this branch (`da394d5`),
probe crates `/tmp/tp-m3/drv` and `/tmp/tp-m3/drv_ok`.

## Proposal

`fip_fn!(prelint, N, |x: T| body)` wraps the closure into `Certified<N, _>` without
the token-level strict scan of `body`, so method calls, `use` aliases and inferred
types are allowed in it (the scan rejects them, brainstorm T4). The bound `N` is
written by the user and checked by the MIR checker `fip-prelint` instead of being
computed by `fip-macros`.

## The exact trust change

Today (`fip_fn!(|x| ..)`):

- `N` is computed by `fip-macros` from the closure's tokens: its own allocation sites
  plus the certificates of the functions it calls, which the strict scan requires.
- The claim "at most `N` allocations, no deallocation, no recursion" rests on the
  token scan and on the callees' certificates. It is unchecked for implicit calls
  (drops, operators; `TODOs/strict-open-items.md` item 5), which `fip-prelint`
  catches where it analyses the value's calls.
- The `unsafe` of `Certified::assume` is in proc-macro output, so the macro is the
  trusted party (`crates/fip-strict/src/lib.rs`, "Hand-written certificates are
  visible").

Driver mode:

- `N` is a claim of the user. Nothing in `fip-macros` checks it.
- The trusted party becomes `fip-prelint`: the claim holds only for code the driver
  compiled and analysed without error.
- The claim is checked at the construction, not only where the value is called:
  allocations at most `N`, no free, no recursion, for the closure body and everything
  it reaches (measured below). This is stronger than the token scan, which misses
  implicit frees.

## What happens without the driver

It does not compile. Three independent guards, measured on `/tmp/tp-m3/drv` (five
driver-mode constructions):

| build | result |
|---|---|
| `cargo build` (plain rustc) | 5× "fip_fn!(prelint, ..) is checked only by fip-prelint" (in the implementation: emitted by `fip-macros`, which knows it is not inside the driver) |
| `FIP_PRELINT_DRIVER=1 cargo build` (the macro tricked into believing it is under the driver) | the same 5 errors, from `#[cfg(not(fip_prelint))] compile_error!(..)` in the output |
| `RUSTFLAGS="--cfg fip_prelint" cargo build` (the cfg forged as well) | fails earlier: `fip-strict` itself does not compile (E0433 "cannot find module or crate `fip`" for its `#![cfg_attr(fip_prelint, fip::export)]`); the check function's `fip::mark(..)` fails the same way |

A fourth guard is needed inside the driver. `fip-prelint` compiles some crates
without checking them, while `fip-macros` sees the driver's environment variable
(it is set for every role but the pass-through one, `tools/fip-prelint/src/main.rs`):

- dependencies declaring `fip::export` (`Role::ExportedDependency`:
  `report::check_dependency`, "no roots, no verdicts");
- stack mode (`cargo fip-prelint --stack`: `report::stack_record`, a `cargo build`
  with no allocation verdicts);
- std-summary generation.

In those runs a driver-mode construction would be compiled with its claim and never
checked. So the driver must tell `fip-macros` that this compilation is checked: a
second variable set only for a primary package in check mode, which the macro
requires. Without it the macro emits the same compile error.

So a certificate made in driver mode is unusable outside a checking driver run. Passing it
without the driver needs a deliberate forgery (an environment variable, a cfg, and a
tool attribute namespace `fip` supplied by hand), which is not an accident and is
comparable to writing `unsafe`.

Consequence: a crate using driver mode is built only by a checking driver run.
`fip-prelint` continues compilation after its analysis (`Compilation::Continue`), so
such a run produces artefacts: `cargo build` with the driver as `RUSTC_WRAPPER` (the
environment `cargo fip-prelint` sets) checked `/tmp/tp-m3/drv_ok` ("3 roots, 3
passed") and wrote `target/drvbuild/debug/libdrv_ok.rlib`. Costs, all measured or
read from the driver's source:

- the pinned toolchain with `rustc-dev` and `RUSTC_BOOTSTRAP=1`, for that crate and
  for every crate depending on it (a dependency is not a primary package, so it is
  compiled by the real rustc and fails);
- the driver compiles checked crates with `-Copt-level=0` (`src/main.rs`, flags of
  the analysed roles), so these artefacts are unoptimised;
- not usable from Verus-verified crates or from `cargo fip-prelint --stack`.

This is the price of "unusable without the driver", and the reason the mode is
opt-in per use.

## Threat model

In scope:

- accidental omission of the checker: CI without `cargo fip-prelint`, a plain local
  build, a new contributor's build;
- a wrong `N` (a typo, a body changed later, a callee that started allocating, a free
  or a recursion introduced in a callee);
- driver-mode output compiled by plain rustc through the environment variable alone.

Out of scope (as for every `unsafe` in the workspace):

- a contributor deliberately forging the driver's environment, cfg and tool
  attributes;
- bugs of `fip-prelint` itself (it is the trusted party in this mode; its own tests
  and fixtures are the evidence);
- `--warn-only` runs, which the user asks for explicitly and which report the
  violation as a warning.

## Soundness argument

Under the driver every driver-mode construction expands to

```rust
{
    #[cfg(not(fip_prelint))] ::core::compile_error!("..");
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", param(g = N)))]
    fn __fip_prelint_checked<R>(g: &dyn Fn(T0, ..) -> R) { let _ = g; }
    let __fip_prelint_closure = |x: T0, ..| body;
    __fip_prelint_checked(&__fip_prelint_closure);
    unsafe { Certified::<N, _>::assume(__fip_prelint_closure) }
}
```

1. `__fip_prelint_checked` declares `param(g = N)` for a callable trait object
   parameter. The driver checks every analysed call of a function declaring
   `param(g = K)` (`TODOs/strict-open-items.md` item 7; local functions that are not
   roots included). For a `&dyn Fn` parameter it resolves the one concrete type
   unsized there (the closure) and checks: allocations at most `K` per call, and no
   free or recursion, which the mark (`kind = "fip"`, calls counted by the
   declaration) forbids (top plan T5, T1.4).
2. The call is in the same block as the construction and receives the same closure
   value, so the type checked is the type certified.
3. The block is in the crate being compiled by the driver in check mode, so the
   call site is analysed (a construction in an unchecked compilation cannot exist:
   there it does not compile).
4. A closure in a generic function: its body may call methods of the type
   parameters, which the driver checks per analysed instance or reports as open
   terms. An instance built only in another crate is checked there only if that
   crate is also a checked primary package; it cannot be compiled otherwise (it
   depends on a crate that builds only under a checking driver, item 3), so no
   unchecked instance is built in a cargo build. Not measured beyond that argument;
   a test with a generic enclosing function is part of the fixture.
5. The claim's three parts are exactly what the check verifies; the closure body's
   own panics are allowed, as for `fip_fn!` today.

Measured (`/tmp/tp-m3/drv`, the expansion above written by hand, `cargo fip-prelint`):

| case | `N` | result |
|---|---|---|
| `\|x: u32\| x.wrapping_add(1).count_ones()` (a method call; the token scan rejects it) | 0 | passes |
| `\|x: u32\| *Box::new(x)` | 0 | error: "passes to `lie::__fip_prelint_checked` an argument for `g` that may allocate 1 time(s) per call, but .. declares `param(g = 0)`" |
| `\|x: u32\| countdown(x)`, `countdown` recursive | 0 | error: ".. an argument for `g` that recurses, but .. its mark forbids that" |
| `\|b: Box<u32>\| *b` | 0 | error: ".. an argument for `g` that may free .." |
| `\|x: u32\| *Box::new(x)` | 1 | error "may free" (the box is dropped inside the closure: not FIP; the token scan accepts this body) |
| `\|x: u32\| Box::new(x)` | 1 | passes |

A first variant with a generic parameter `G: FipFn<(T0,)>` instead of `&dyn Fn` caught
only the allocation bound: the recursion and the free passed, because the driver checks
forbidden events only for function-pointer and trait-object parameters. Hence `&dyn Fn`.

## Alternatives considered

- **Crate-level `unsafe` acknowledgement** for plain builds (a hand-written
  `unsafe` item the output references): plain builds would then compile with an
  unchecked claim whenever CI stops running the driver. Silent trust; rejected.
- **A stamp file written by the driver and read by `fip-macros` in plain builds**:
  the stamp would have to cover the closure's callees (other files, other crates),
  and proc-macro file reads are not tracked by incremental compilation on stable
  (`proc_macro::tracked_path` is unstable), so a deleted or stale stamp could still
  pass. Rejected.
- **Checking every `Certified::assume` of a closure** in the driver (no new syntax):
  useful, but it does not lift the token-scan restrictions by itself, and it would
  change verdicts of existing `fip_fn!` values (implicit frees). Left as a separate
  driver change.
- **No driver mode**: keeps the strict scan's restrictions (method calls, aliases).

## Conclusion

The mode can be made opt-in (the `prelint` argument at each use), default-off (no
other syntax changes), and not silently trusted without the driver (plain builds fail;
the measured forgeries need deliberate steps). The trust moves from `fip-macros` to
`fip-prelint` only for those uses, and the driver checks the full claim at the
construction. Implement it, with the constraint that such crates build only under the
driver.

## Implementation

`fip_fn!(prelint, N, closure)` (optionally after `crate = ..`), in the commit
"fip-macros: driver-checked fip_fn!(prelint, N, ..) (fip-fn ergonomics 5)":

- `fip-macros` (`fip_fn_prelint`): the closure's parameter types must be written
  (they form the `&dyn ::core::ops::Fn(..) -> R` of the check function; otherwise
  "write the type of every closure parameter"); outer attributes on the closure are
  kept; `N` is an integer literal; `bound <= K` and a function path are rejected
  with their own messages. The mark is emitted with every key:
  `fip::mark(kind = "fip", n = 0, strict = false, panic_macros = true, param(g = N))`.
- `fip-prelint` (`src/main.rs`, `checks_crate`) sets `FIP_PRELINT_CHECKS=1` in its
  process for `Role::Primary` outside stack mode and generation mode (exactly the runs
  that call `report::check_crate`), and removes it otherwise, also when inherited.
  `fip-macros` requires it together with `FIP_PRELINT_DRIVER`; otherwise the compile
  error "fip_fn!(prelint, ..) is checked only by `cargo fip-prelint`: ..".
- `fip_testkit`'s source model skips the `prelint, N,` prefix (the closure is
  modelled as in the default mode).
- Tests: `compile_fail` examples in `fip-macros` with `# // expect:` (plain build,
  also with `crate = ..`; missing parameter type; `bound <= K`; a non-literal `N`),
  checked by `just compile-fail-reasons`; `crates/fip-macros/tests/driver_mode.rs`
  (a generated crate built plainly, with the driver's environment variables forged,
  and with `--cfg fip_prelint` forged as well: all three fail); fixture
  `tools/fip-prelint/tests/fixtures/driver_checked`.

Measured (rustc 1.99.1, the driver of this commit):

| run | result |
|---|---|
| plain `cargo build` of the generated crate (2 constructions, honest bounds) | 2× "fip_fn!(prelint, ..) is checked only by `cargo fip-prelint`" |
| `FIP_PRELINT_DRIVER=1 FIP_PRELINT_CHECKS=1 cargo build` | 2× "fip_fn!(prelint, ..): `cfg(fip_prelint)` is not set, .." (the guard in the output) |
| the same with `RUSTFLAGS="--cfg fip_prelint"` | `fip-strict` fails: E0433 "cannot find module or crate `fip` in this scope" |
| `cargo fip-prelint`, crate `checked` | method call, inferred local, two parameters, `\|x: u32\| Box::new(x)` with `N = 1`: pass; `*Box::new(x)` with `N = 0`: "may allocate 1 time(s) per call, but .. declares `param(g = 0)`"; `countdown(x)`: "recurses"; `\|b: Box<u32>\| *b`: "may free"; `*Box::new(x)` with `N = 1`: "may free"; summary "10 roots, 10 passed, 7 errors" |
| `cargo fip-prelint`, non-member `drvdep` with `fip::export` (`Role::ExportedDependency`) | the `fip-macros` error |
| `cargo fip-prelint --stack` | the `fip-macros` error at every construction, exit 1 |
| `cargo fip-prelint --stack` with `FIP_PRELINT_CHECKS=1` inherited | the same (the driver removes it); with the removal disabled (mutation) the crate with the lies built, exit 0 |
| generation mode (`FIP_PRELINT_STD_SUMMARIES_OUT` set; fixture variant, and once `cargo fip-prelint --std-summaries --manifest-path ..checked/Cargo.toml` with `-Zbuild-std`, 3 min 44 s) | the `fip-macros` error at every construction |
| mutation: `fip-macros` requiring only `FIP_PRELINT_DRIVER` | `drvdep` compiled (no error), `--stack` built the crate with the lies (exit 0): the hole the review found, closed by `FIP_PRELINT_CHECKS` |

Generation mode of a crate depending on `fip-strict` ICEs in the driver
(`rustc_metadata` decoder, `Option::unwrap` on `None`), with or without driver-mode
constructions and also for the default `fip_fn!`; generation is meant for the seed
crate only, and with this change a driver-mode construction fails earlier, at
expansion. (Fixed 2026-11-04: the cause was listing the functions of the
proc-macro crate `fip-macros`, not a flag mismatch; `TODOs/fip-prelint.md`, "Resolved
2026-11-04: generation mode with a proc-macro dependency (ICE)".)

Generic enclosing functions (soundness argument, point 4): the driver-mode check
runs on the generic body (`generic_lie::<T>`: "may allocate 1 time(s)"); both
constructions in a generic function also get the existing `Certified::assume` check's
`⊤` ("`Certified::assume` with the generic callable type `{closure..}`"), as the
default `fip_fn!` does in a generic function (measured on a probe with both). So a
driver-mode construction in a generic function does not pass today; never silently. (Since 2026-11-04 an allocation-free one passes and one with a call left
generic, such as `T::make`, is `⊤` at the check function; see the open points.)

Open points:

- the `Certified::assume` check reports a closure type of a generic function as a
  generic callable type (`⊤`); a closure type is never a function pointer, so the
  driver could resolve it (a separate driver change, affecting the default mode too).
  Resolved 2026-11-04: analysed through its body; a term left in a driver-mode
  closure (`T::make`) is `⊤` (`TODOs/fip-prelint.md`, "Resolved 2026-11-04:
  `fip_fn!` closures in generic functions");
- parameter types naming type parameters of an enclosing generic function fail with
  E0401 (the check function is a nested item), and a closure returning a borrow of a
  parameter fails with "lifetime may not live long enough" (`R` is not higher-ranked);
  both measured, both compile errors, not silent passes;
- no count of driver-mode constructions in the crate summary yet (they appear as
  roots named `..::__fip_prelint_checked`). Resolved 2026-11-04: counted apart from
  the roots ("N roots, P passed, K `fip_fn!` constructions, Q passed, ..": a root is a
  function declared `#[fip]`, a construction checks a certificate's claim; errors,
  warnings and notes stay totals) (`TODOs/fip-prelint.md`, "Resolved 2026-11-04:
  `fip_fn!` constructions in the crate summary");
- `--warn-only` reports a wrong `N` as a warning (threat model: out of scope);
- Verus is not the driver, so driver mode does not compile in verified crates.
