<!-- SPDX-License-Identifier: MIT OR Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# Redesign: the verified layer proves allocation bounds with Verus `allocates`

**Status:** ACCEPTED by the user, 2026-11-06, with the recommended answers to D1–D6
(D1 keep `fip-strict` with Verus-checked certificates; D2 `DropFreeFn`; D3 accept
cfg-gated `unsafe impl AllocFreeDrop` for user types; D4 `-V alloc-check`, panics stay
with `fip-prelint`; D5 pin the fork commit, keep an upstream-11.02 gate on stripped
sources; D6 keep 1.99.1 for now). Implemented on branch `redesign/verus-allocates`.
Schedule note (user, 2026-11-06): stable Rust 1.100.0 is due in 7 days, and the fork
plans its 1.100 rebase (custom allocators then); keep every toolchain- and
Verus-version pin in one place so the rebase is a re-pin, not a redesign.

**Phase 1 implemented** 2026-11-06 (section 5): fork pin and flags, `fip_fn!` Verus arm,
regenerated sidecars, strip gate `just verify-upstream`. Details: section 5 and
`docs/decisions/2026-10-31-verification-layout.md`.

**Phase 2 implemented** 2026-11-06 (section 5):
- `fip-strict`: `AllocFreeDrop` (Verus: re-export of `vstd::alloc_check::AllocFreeDrop`;
  plain: empty trait with a blanket impl) and `DropFreeFn` (Verus: `Copy`; plain:
  blanket impl). Crate docs record the bounds and the downstream cfg requirement.
- `fip-core`: `T: AllocFreeDrop`, `F: DropFreeFn` on all `Fn`-based functions (`swap`,
  `swap_lt`, `replace`, `update`, `compact`, `map_in_place`, `compact_map`, `dedup_by`,
  `_st` variants); `allocates` bounds (`0` on `swap`, `swap_lt`, `replace`, `dedup_by`,
  `map_in_place_st`, `compact_map_st`; callback sum on `compact`, `map_in_place`,
  `compact_map`; `call_allocates(f, ..)` on `update`). `fip_core::spec` adds the sum
  spec functions (`map_allocs`, `compact_allocs`, `compact_map_allocs`) and the
  broadcast lemmas `group_allocs_zero`. Verified: 64 items (58 baseline + 3 spec
  functions + 3 lemmas). Sidecar regenerated (all 17 listed functions gained bounds).
- `fip-alloc`: `refill` gets `T: fip_strict::AllocFreeDrop` and `allocates 0`. Sidecar
  regenerated.
- `verify/compose_state.rs`: `allocates 0` added to its 4 `fip_core` callers (`counter`,
  `number_from_11`, `odd_count`, `keep_odd`).
- `verify/alloc_callers.rs`: new gate exercising `map_in_place`, `compact`,
  `compact_map`, `update`, `swap`, `dedup_by`, `map_in_place_st` with `Copy` closures
  under `allocates 0`, verified with `group_allocs_zero` (8 verified items).
- Mutants in `just verify-negative`: 6 crate-level allocation mutants (extra
  `Box::new` in `swap`, `map_in_place`, `refill`; sum spec forgetting the last call;
  `map_in_place_st` without its `call_allocates <= 0` requirement) and 4 caller
  controls in `verify/alloc_callers.rs` (allocating closure, unbounded closure,
  unbounded `dedup_by` closure, zero lemmas omitted).
- Downstream measurement (user type with `compact`, non-`Copy` `Node`):
  * without `AllocFreeDrop` impl: plain compiles, Verus rejects (`error[E0277]: the trait bound Node: fip_core::AllocFreeDrop is not satisfied`);
  * ungated `unsafe impl AllocFreeDrop for Node {}`: plain fails (E0119 conflicting impl with blanket, E0199 safe trait in plain build);
  * gated `#[cfg(verus_keep_ghost)] unsafe impl fip_core::AllocFreeDrop for Node {}`:
    plain compiles; Verus requires the struct definition to be verified as well,
    `#[cfg_attr(verus_keep_ghost, verus_verify)] pub struct Node { .. }` (otherwise:
    `error: cannot use type down2::Node which is ignored because it is either declared outside the verus! macro or it is marked as external`),
    and then verifies cleanly (2 verified, 0 errors).
- Strip gate (`verify-upstream` on stripped sources with upstream 0.2026.11.02): green,
  reproducing the baseline counts 19/58/1/3/4/13/2.

Option A (user-approved): the verified layer
(`fip-core`, `fip-alloc`, `fip-strict` under Verus, verified callers) states and proves
allocation bounds with the Verus fork's `allocates` clause; the unverified layer stays
with `fip-macros` and `fip-prelint`. This record contains the feasibility probes, the
architecture, the change of the trust basis, the fix for `verify/compose_state.rs` and a
phased plan.

**Measured with:** Verus fork branch `fip` at `ca33b0438` (version
`0.2026.11.05.ca33b04`, toolchain 1.99.1), upstream Verus `0.2026.11.02.8bf68ee`
(called "11.02" below), Z3 4.16.0 (`VERUS_Z3_PATH=/usr/bin/z3`), rustc 1.99.1, branch
`redesign/verus-allocates` at `aaf7c50`. Probe trees are under
`/home/ybi/pfip-recheck-tmp/redesign/` (named below); they are copies of `crates/*`,
never this checkout.

**Fork documentation read:** `source/docs/guide/src/reference-allocates.md` of the fork.
Where it and the probes differ, the probes are recorded.

Every statement about behaviour below is measured unless it is marked *(unmeasured)*.

## 1. Feasibility probes

### 1.1 Baseline

| tree | Verus | flags | `fip-strict` | `fip-core` | `fip-alloc` |
|---|---|---|---|---|---|
| `base` (unchanged copy) | fork | `--no-cheating` | 19 verified | 58 verified | 1 verified |
| `base` | fork | `--no-cheating -V alloc-check` | 19 | 58 | 1 |
| `p3` (all specs below) | fork | `--no-cheating -V alloc-check` | 20 | 70 | 1 |
| `p3up` (`p3` through `strip_alloc.py`) | 11.02 | `--no-cheating` | 19 | 58 | 1 |

`-V alloc-check` without any `allocates` clause changes nothing (row 2). The extra
verified items in `p3` are the new spec functions and lemmas (`fip-core`) and one more
`Compose` impl (`fip-strict`, section 1.4).

Wall time of the three crate runs (strict, core with `--export --compile`, alloc), 3 runs
each: `base` 3.64 s and 3.71 s; `p3` 4.45 s, 4.45 s, 4.52 s.

### 1.2 Probe table

"Verifies" means: `verus --no-cheating -V alloc-check` on the crate succeeds with the
spec in the left column, in tree `p3`. All specs are in attribute syntax,
`#[cfg_attr(verus_keep_ghost, verus_spec(r => requires .., ensures .., allocates E))]`,
with `allocates` after `ensures`.

| function | `allocates` | verifies | what was needed |
|---|---|---|---|
| `slice::swap_lt` (crate-private) | `0` | yes | `T: AllocFreeDrop` |
| `swap` | `0` | yes | `T: AllocFreeDrop` (rejected without it, although only `&mut [T]` is handled: the drop rule flags the type of the argument of `split_at_mut`) |
| `replace` | `0` | yes | `T: AllocFreeDrop` (rejected without it at the parameter `new: T`, although nothing is dropped) |
| `update(slot, hole, f)` | `call_allocates(f, (*old(slot),))` | yes | `T: AllocFreeDrop`; `F: DropFreeFn` (`f: F` is a parameter type the drop rule must bound) |
| `compact(xs, keep)` | `compact_allocs(keep, old(xs)@, len)` (sum of `call_allocates(keep, (&old[i],))`) | yes | `T`, `F` bounds; loop invariant `allocated() <= compact_allocs(keep, old(xs)@, r)` |
| `map_in_place(xs, hole, f)` | `map_allocs(f, old(xs)@, len)` | yes | as `compact`; invariant over `i` |
| `compact_map(xs, hole, f)` | `compact_map_allocs(f, old(xs)@, len)` | yes | as `compact` |
| `dedup_by(xs, same)` | `0`, with `requires forall i, j < len: call_allocates(same, (&old[i], &old[j])) <= 0` | yes | `T`, `F` bounds. A per-call sum is not expressible: the first argument is the last kept element, known only during the run |
| `map_in_place_st(xs, hole, s0, f)` | `0`, with `requires forall s, x: call_allocates(f, (s, x)) <= 0` | yes | `S`, `T`, `F` bounds. The states are outputs of earlier calls, so a bound evaluated at entry cannot sum over them; a uniform nonzero bound would need a ghost parameter *(unmeasured)* |
| `compact_map_st` | as `map_in_place_st` | yes | as `map_in_place_st` |
| `fip_strict::FipFn::call` (trait decl, Verus block) | `self.allocs()`, new `spec fn allocs(&self) -> nat` | yes | `nat`, not `int`: the fork clamps a declaration's bound at 0 (`vir/src/ast_simplify.rs`, "clamped at 0"), so with `int` a generic caller cannot prove `allocated() <= f.allocs()` (probe `tr/t.rs`, `tr/t2.rs`: fails with `int`, passes with `nat` or a literal) |
| `Certified::call` | `allocs() = ALLOCS as nat`; `pre` gains `call_allocates(self.inner(), args) <= ALLOCS` | yes | argument and result types bounded by `AllocFreeDrop` in the Verus impls |
| `Stateless::call`, `Then::call` | `allocs()` of the parts, summed | yes | `S`, `A`, `B`, `C` bounded |
| `Compose::call` | `self.0.allocs() + self.1.allocs()` | yes, per arity | generic `Args: AllocFreeDrop` is unusable: vstd has no `AllocFreeDrop` for 1-tuples (callers fail on `(u32,)`); one impl per arity with bounded elements works (arities 1 and 2 probed) |
| `Certified::assume`, `assume_no_panic_macros` | `0` | yes | `C: DropFreeFn` |
| `strict::update` | `f.allocs()` | yes | `T: AllocFreeDrop`, `F: AllocFreeDrop` (the four adapters and `Certified<_, C: Copy>` get `unsafe impl AllocFreeDrop` in the Verus block, accepted by the drop rule) |
| `strict::map_in_place`, `map_in_place_st`, `compact`, `dedup_by`, `compact_map`, `compact_map_st` | `old(xs)@.len() * f.allocs()` (no zero requirement) | yes | bounds as above; invariant `allocated() <= i * f.allocs()`; one `assert((i + 1) * k == i * k + k) by (nonlinear_arith)` per loop (without it, 6 loop invariants fail) |
| `fip_alloc::refill(Box<T>, T)` | `0` | yes | `T: AllocFreeDrop`. Frees are not counted by `allocates` (fork doc, "What a bound means"), so F2 for `refill` is not proved |

Verified callers (tree `p3`, `client/`):

| probe | result |
|---|---|
| `c1.rs`: `map_in_place` with a closure with and without `requires`, a closure capturing `&u8`, `update`, `swap` on `[Box<u8>]`, `compact`, `dedup_by`, `map_in_place_st`, each caller `allocates 0` | 7 verified, after `broadcast use fip_core::spec::group_allocs_zero` (three lemmas "zero per element ⇒ zero sum"); without them, the 3 sum-bounded callers fail |
| `c2.rs`: non-`Copy` user struct, `#![forbid(unsafe_code)]`, `replace` | rejected: `Node: AllocFreeDrop` not satisfied |
| `c3.rs`: the same with `unsafe impl AllocFreeDrop for Node {}` inside `verus!` | 1 verified; an `unsafe impl` for a type whose `Drop` allocates is rejected ("its `Drop::drop` is not bounded by `allocates 0`") |
| `c4.rs`: closure that moves in a `Box` | rejected by `map_in_place` (closure not `Copy`); accepted by a `&F` variant written in the probe (3 verified) |

### 1.3 Failures and their causes

1. **Drop rule over-approximates.** Every type parameter that appears in a parameter or
   expression type needs `T: Copy` or `T: vstd::alloc_check::AllocFreeDrop`, even where
   the value is only moved (`replace`, `swap`). The bound then propagates to every caller
   (measured: 6 E0277 errors in `slice.rs` after bounding only `replace`).
2. **Closures by value.** `f: F` needs a bound on `F`. A closure type cannot implement
   `AllocFreeDrop` (no impl can name it; measured: 6 E0277 in `c1.rs` with
   `F: AllocFreeDrop`). `F: Copy` works for closures whose captures are `Copy`. A
   supertrait does not count: `trait DropFreeFn: Copy` with a blanket impl is rejected
   ("add the bound `F: AllocFreeDrop` (or `F: Copy`)"); the bound must resolve to `Copy`
   itself.
3. **`F::Output` / associated types.** Not hit: every `FipFn` bound in `fip_core::strict`
   fixes `Output = ..` to a concrete type expression, and the probes verify.
4. **Trait-method bounds over a generic receiver.** Need a `nat` bound (above).
5. **Tuples.** No vstd `AllocFreeDrop` for 1-tuples; `Compose` needs per-arity impls.
6. **Nonlinear products of adapter bounds.** `len * Compose(d1, d2).allocs()` is not
   proved zero without a hint in the caller (section 4).
7. **`-V alloc-check-strict`.** Tree `p3s` (every `allocates` function also `no_unwind`):
   `fip-strict` fails 5× "cannot show this call will not unwind" at `(self.f)(..)`;
   `fip-core` fails 13× the same at every callback call, once because `FipFn::call`
   lacks `no_unwind`, and once an existing assertion (`compact_map_st_fip_post` in
   `strict::compact_map_st`). `swap`, `swap_lt`, `replace`, `refill` pass. The fork doc
   also says that closures cannot carry bounds in this mode. Strict mode is not usable
   for the higher-order functions.

### 1.4 Workarounds and what they cost

**Marker traits, cfg-split, in `fip-strict`** (tree `p3`):

```rust
#[cfg(verus_keep_ghost)]
pub use vstd::alloc_check::AllocFreeDrop;
#[cfg(not(verus_keep_ghost))]
pub trait AllocFreeDrop {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized> AllocFreeDrop for T {}

#[cfg(verus_keep_ghost)]
pub use core::marker::Copy as DropFreeFn;
#[cfg(not(verus_keep_ghost))]
pub trait DropFreeFn {}
#[cfg(not(verus_keep_ghost))]
impl<F: ?Sized> DropFreeFn for F {}
```

`fip-core` re-exports both; `fip-alloc` uses `fip_strict::AllocFreeDrop`.

- **No `vstd` at run time:** kept. Plain `cargo build` of the three crates succeeds;
  `cargo tree -p fip-core` lists only `fip-macros`, `fip-lint-rules`, `fip-strict`, and
  `fip-alloc` only `fip-strict`. `cargo test` of the three crates passes except
  `fip-strict/tests/verus_drift.rs` (2 tests), which compares the plain and the Verus
  declarations and sees the Verus-only additions; it has to learn them.
- **Why not `cfg` on the bound:** `#[cfg(verus_keep_ghost)] T: Marker` in a `where`
  clause is E0658 "attributes in `where` clause are unstable" on rustc 1.99.1, also when
  the cfg is off (probe `wc/a.rs`). A direct `vstd::...` bound breaks the plain build
  (E0433 in `fip-alloc`, measured).
- **Public API, plain builds:** every generic function gains `T: AllocFreeDrop` (and `S`),
  callables gain `DropFreeFn`, `Certified::assume` gains `C: DropFreeFn`. Every type
  satisfies them, so no caller breaks; `fip-macros` strict mode accepts the bounded
  signatures (plain build and `strict_behaviour` tests pass). Rustdoc shows the bounds.
- **Public API, Verus builds:** element types must be `Copy` or `AllocFreeDrop` (user
  types need `unsafe impl` inside `verus!`, impossible under `#![forbid(unsafe_code)]`,
  `c2.rs`); closures must be `Copy` (`c4.rs`).
- **Downstream impls must be Verus-only (measured 2026-11-06, `down/`):** in the plain
  build `AllocFreeDrop` is a blanket `impl<T: ?Sized> AllocFreeDrop for T {}`, so a
  downstream `unsafe impl fip_strict::AllocFreeDrop for Node {}` fails the plain build
  with E0119 (conflicting implementations) and E0199 (the plain trait is not `unsafe`).
  With `#[cfg(verus_keep_ghost)]` on the impl the plain build succeeds. Every user type
  under Verus therefore needs a cfg-gated `unsafe impl` (plus a `check-cfg` entry for
  `verus_keep_ghost`). Not yet measured: the gated impl inside a Verus build of a
  downstream crate that depends on the Verus build of `fip-strict`.
- **Alternative `f: &F`:** accepts every closure under Verus (`c4.rs`), but changes the
  plain API (`map_in_place(xs, h, &|v| ..)`) and `update` loses `FnOnce`. Not chosen as
  default; decision point D2.

**Strip gate:** `strip_alloc.py` removes the allocation layer (clauses, invariants,
sum spec functions and lemmas, bounds, `AllocFreeDrop` impls, `allocs()`); the result
differs from `base` only by the two marker traits and a comment, and 11.02 verifies it
with the baseline counts (19/58/1, table 1.1).

## 2. Architecture under option A

### 2.1 Which guarantees move to proofs

| property | today | after |
|---|---|---|
| `fip-core` allocates nothing | crate links no `alloc` | unchanged, plus a Verus proof per function (`allocates 0`, or the callbacks' sum) |
| `fip-alloc::refill` allocates nothing | allocation-count tests | Verus proof (`allocates 0`, normal return, `T: AllocFreeDrop`); the count tests stay as run-time evidence |
| frees (F2) in `refill` and everywhere | tests, `fip-prelint` | unchanged: `allocates` does not count deallocation |
| strict variants' callable bound | `param(f = 0)` checked by `fip-macros` at instantiation | Verus proof of `len * f.allocs()`; `f.allocs()` of a `Certified` is its `ALLOCS`, checked by Verus at each verified call through `Certified::pre` |
| a verified caller allocates at most N | not expressible | `allocates N` on the caller, proved over callees' bounds |
| bounds on panicking paths | `fip-prelint` | still `fip-prelint`: `allocates` bounds only normally returning calls (fork doc), and strict mode is not usable (1.3.7) |
| unverified `#[fip]` code, `dyn`, fn pointers, FFI, stack bytes, recursion outside Verus | `fip-macros`, `fip-prelint`, `fip-testkit` | unchanged (the fork rejects `dyn` and fn pointers in bounded code; doc "Known limitations") |

### 2.2 `fip-strict`

Options:

1. **Derive certificates from Verus `allocates`.** In Verus builds `Certified::pre`
   requires `call_allocates(inner, args) <= ALLOCS`, so a wrong `ALLOCS` fails at the
   call (measured: callbacks without `allocates` fail `pre`, section 4). `FipBound::ALLOCS`
   stays the plain-build certificate. Next step (later phase): a verified strict function
   gets its plain certificate from its proved bound, checked by `fip-prelint` against
   the allocation sidecar instead of computed from tokens.
2. **Keep only for unverified code.** Verified code uses the `Fn` variants with
   `allocates`; `Cert`, `Certified`, `FipBound`, `FipFn`, `param(g = K)`, `fip_fn!` serve
   strict mode in unverified code only.
3. **Deprecate.** Once verified callers and the driver cover the uses, remove strict mode.

**Recommendation: option 1 now, revisit 3 after the driver consumes allocation
sidecars.** Reasons: option 1 is measured to work with small changes (`allocs()`,
`pre`, per-arity `Compose`, four `unsafe impl AllocFreeDrop`), keeps every existing user
of strict mode working, and makes the certificate numbers Verus-checked wherever a
verified caller uses them. Trade-offs: `Certified::pre` becomes stronger (a closure must
carry an `allocates` bound to be usable under Verus); the twin declarations (plain and
`verus!`) of `FipFn` impls diverge further (`verus_drift.rs`, and the cfg hole in 2.4);
`fip_core::strict::*` duplicates the `Fn` variants for verified callers, whose only extra
value is strict-mode callers in unverified code.

`param(g = K)` and `fip_fn!` stay as they are in plain builds. Under Verus, `fip_fn!`
must not read certificates (section 4).

### 2.3 `fip-macros` strict mode

Unchanged for unverified code: token scan, audited `core` table, certificate sums in
constant evaluation, `param(..)`. For a function that also has a `verus_spec` with
`allocates`, the macro's token-level bound and Verus's bound are two claims about the
same body; until phase 5 both are kept and the driver reports a disagreement
*(design, unmeasured)*. A strict function that allocates cannot be `no_unwind`, which
only matters if `-V alloc-check-strict` were used; it is not (D4).

### 2.4 `fip-prelint`

Keeps: frees (F2), unverified code, function pointers and `dyn`, stack bytes, FFI marks,
panics (with the Verus panic-freedom sidecar), cfg divergence between builds.

Consumes Verus results through the existing sidecar, extended *(design, unmeasured)*:

- **Format 5:** per listed function also its proved `allocates` expression (literal, or
  the hash of the expression text), and `flags --no-cheating -V alloc-check`.
  Measured today: the generator runs with the fork (`fip-strict`: 2 listed, 10 skipped)
  but stamps only `flags --no-cheating` (`verusgen.rs` keeps only `NO_CHEATING`), and an
  import of the resulting sidecar is refused because the driver's pin is 10.18
  (`verus-trusted.txt`).
- **Trust rules:** as for panic sites (item text hash, every source hash, Verus-only cfg
  forms, tainted callers), plus: the crate was verified with `--compile` (the fork marks
  the exported `.vir` checked only then; measured: an importer of a failed `fip-strict`
  run is refused with "its crate was not verified with -V alloc-check"); a literal bound
  `K` discharges allocation sites of the body only for instantiations whose bounded type
  parameters the driver itself finds to have alloc-free drop glue (the plain marker traits
  hold for every type, so the Verus premise must be re-established per instance).
- **Frees are never discharged** by a Verus bound.

**Panic-freedom sidecar:** keep; it becomes one sidecar with two kinds of entries.

**Open hole (generic trait call through a cfg-skipped impl):** it also covers
allocation. Probe `hole/lib.rs`: trait `Step` with `fn step(&self) -> u8 allocates 0`
inside `#[cfg(verus_keep_ghost)] verus! { }`, a plain-only impl that calls `Box::new`;
`run<T: Step>` and `run_s` with `allocates 0` verify (3 verified), and the plain build
compiles the allocating impl. Verus cannot see this; the generator must taint every
caller of a trait method whose impls (or the trait) have cfg-divergent declarations in
the scanned sources, and refuse such a crate's trait bounds. `fip-strict`'s twin `FipFn`
impls are exactly this pattern, so they must either be unified into one attribute-mode
source or excluded from discharge (phase 4).

## 3. Trust basis

| | today | after |
|---|---|---|
| Verus | upstream `0.2026.10.18.7d82994`, `--no-cheating` (pinned in `tools/fip-prelint/verus-trusted.txt`, installed `verus` reports 10.18) | fork `fip` `0.2026.11.05.ca33b04` (`ca33b0438c36…`), `--no-cheating -V alloc-check` |
| trusted in addition | — | vstd's allocation specifications (509 occurrences of the word `allocates` in 34 vstd source files, `grep -w`, comments included; the fork reply's "~513 specs" was not recounted), vstd's trusted std drops and `AllocFreeDrop` impls, the fork's `alloc_check` VIR pass, `external_body` bounds (none in this repository) |
| toolchain | 1.99.1 | 1.99.1 (the fork's `--version`), MSRV and `prelint_tc` unchanged |

**Upstream gate:** `allocates` is a parse error on 11.02 in both syntaxes (attribute:
"unexpected token" at the bound; `verus!`: "expected curly braces"), and
`call_allocates` is unresolved (E0425). An 11.02 gate can therefore only run on stripped
sources: `strip_alloc.py` + 11.02 reproduces the baseline counts (1.1). Recommended: keep
it as `just verify-upstream`, proving that the functional proofs do not depend on the
fork's VIR pass. `.vir` files of one build cannot be imported by the other, so the gate
re-verifies all crates (about 3.8 s measured for the three).

**Stamps and pins:** `verus-trusted.txt` repinned to the fork commit (a trust decision);
the generator must keep `-V alloc-check` in `flags`; the justfile needs a pinned fork
binary and `verus_flags := "--no-cheating -V alloc-check"` instead of `verus`/`VERUS`
from `PATH`, and a second variable for the upstream gate *(unmeasured)*.

**CI time:** the Verus crate runs grow from 3.6–3.7 s to 4.5 s (1.1); the strip gate adds
about 3.8 s; mutants not measured.

## 4. Fix for `verify/compose_state.rs`

The three errors (fork and 11.02 alike) all come from `fip_fn!(tick_checked)`
(line 123): its expansion `Certified::<{ Cert::allocs_for(__fip_strict_tick_checked,
"tick_checked") }, _, false>::assume(tick_checked)` makes Verus see `Cert`,
`Cert::allocs_for` and the plain-only constant.

Fix:

1. **`fip-macros`:** under Verus's driver (`fip-macros` already detects it, see the
   `let () = const { .. };` handling in its crate docs) `fip_fn!` emits the Verus arm
   `unsafe { Certified::<{K}, _, P>::assume(f) }`, never a certificate read. Sound under
   Verus because `Certified::pre` requires `call_allocates(inner, args) <= K`; plain
   builds unchanged. **Which `K`** (amended 2026-11-06, design, unmeasured): the
   `Certified<N, _>` *type* must be the same in both builds, or code that names the type
   (struct fields, `param(g = N)` callees, arrays of certified callables) compiles
   differently under Verus.
   - **Closure form:** the macro already computes the scanned literal `N` from the body;
     emit that same `N` in both builds. `bound <= K` keeps its meaning (`N <= K`).
   - **Path form** (`fip_fn!(tick_checked)`): plain builds read `N` from
     `Cert::allocs_for`, which Verus cannot see. When `bound <= K` is written, emit
     `Certified<K, _>` in **both** builds; the plain build keeps the existing check
     `N <= K` (the `bound <= K` semantics of `a67a878`), and Verus's `Certified::pre`
     checks `call_allocates(..) <= K`. Only the path form without `bound` differs: plain
     `Certified<N, _>`, Verus `Certified<0, _>`, so verified callers must write
     `fip_fn!(bound <= K, path)` for an allocating path (documented).
2. **`compose_state.rs`:** `allocates 0` on every specified function and closure
   (19 places) and two hints, `assert(old(xs)@.len() * FipFn::<(u32,)>::allocs(&c) == 0)`
   in `quadrupled` and the parts of `Then(t, Stateless(d))` in `numbered_doubled`.

Measured in tree `p3` with the expansion of step 1 written out by hand
(`compose_state.fixed.rs`): 13 verified, 0 errors. With only step 1: the 3 errors are
gone and 9 allocation obligations fail (callbacks without bounds); with `allocates 0`
but without the hints: 2 fail. A bound of the form
`if f.allocs() == 0 { 0 } else { len * f.allocs() }` might remove the hints
*(unmeasured)*.

## 5. Phased plan

| phase | deliverables | gates | stays green | effort |
|---|---|---|---|---|
| 1. basis switch | fork `ca33b04` pinned in justfile and `verus-trusted.txt`; `fip_fn!` Verus arm (section 4 step 1); sidecars regenerated | `just verify` on the fork with flags off; `compose_state.rs` green (no `allocates` yet, so `Certified::pre` unchanged) | everything; strict mode and driver untouched | 0.5–1 day |
| 2. proofs in `fip-core` / `fip-alloc` | marker traits; `allocates` on the 9 `Fn`-based functions and `refill`; sum spec functions and the zero lemmas; README table rows; `verus_drift.rs` updated; allocation mutants (a bound lowered, a `Box::new` in a callback of an `allocates 0` caller) | `-V alloc-check` gate; strip gate on 11.02; mutants fail | plain API (bounds hold for every type), `no_std`, no `vstd` | 1–2 days |
| 3. `fip-strict` / strict variants | `FipFn::allocs`, `Certified::pre`, per-arity `Compose` (to `MAX_ARITY`), `unsafe impl AllocFreeDrop` for `Certified`/adapters, bounds on `fip_core::strict::*`, `compose*.rs` with `allocates` | as phase 2; `hand_written_certs` reviewed (new `unsafe impl`s are Verus-only) | plain strict mode | 1–2 days |
| 4. driver | sidecar format 5 (bounds, flags), consumption rules (2.4), cfg-divergence taint closing the open hole for panics and allocation, unification or exclusion of the twin `FipFn` impls | driver fixtures for each refusal; self-check | panic sidecar behaviour | 3–5 days |
| 5. strict-mode fate | per D1: plain certificates derived from proved bounds (driver-checked), or token-level only for unverified code, or deprecation | per choice | — | 1–5 days |

In parallel, requests to the fork: `AllocFreeDrop` for 1-tuples and longer tuples;
a way for non-`Copy` closures to pass the drop rule in generic `F` positions; a
move-aware drop analysis (would remove most `T: AllocFreeDrop` bounds); documenting
that trait-declaration bounds are clamped at 0.

## 6. Decision points for the user

- **D1, `fip-strict` fate:** recommended option 1 (Verus-checked certificates), revisit
  deprecation after phase 4.
- **D2, callable parameters:** `DropFreeFn` (= `Copy` under Verus; plain API unchanged,
  verified callers limited to `Copy` closures) or `&F` (any closure, plain API break,
  `update` loses `FnOnce`). Recommended: `DropFreeFn`, plus the fork request.
- **D3, user types under Verus:** accept that non-`Copy` element types of verified callers
  need `unsafe impl AllocFreeDrop` inside `verus!`.
- **D4, unwinding:** use `-V alloc-check`, not `-strict`; bounds are stated for normal
  return, panics stay with `fip-prelint`.
- **D5, trust pin:** the fork commit as the only trusted Verus for allocation claims;
  keep the upstream strip gate (recommended).
- **D6, toolchain/MSRV:** no change now (1.99.1 on both); revisit when the fork rebases.

## Probe files

`/home/ybi/pfip-recheck-tmp/redesign/`: `base/` (copy), `p1/` (`T` bounds only),
`p2/` (+ `DropFreeFn`, zero lemmas), `p3/` (final, with `run.sh`, `runc.sh`, `runcs.sh`,
`client/c1.rs`–`c4.rs`, `cs1.rs`–`cs3.rs`), `p3s/` (strict mode), `p3up/` (stripped),
`strip_alloc.py`, `edit_slice.py`, `tr/` (trait bounds), `up/` (11.02 parsing),
`wc/` (`where`-clause cfg), `hole/` (cfg divergence), `ws/` (plain workspace build),
`compose_state.fixed.rs`.
