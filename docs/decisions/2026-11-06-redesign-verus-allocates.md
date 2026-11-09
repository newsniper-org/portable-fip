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

**Phase 5 accepted** by the user 2026-11-09 (D7, section 7): `strict`
becomes the one-declaration contract generator checked by Verus, `total` the strictest
grade; the fork's `#[verifier::fip]`/`fip(strict)` were audited first and are used only
where they are sound and work across crates. The re-pin to fork `fip-beta` is merged;
implementation is next.

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

**Phase 3 implemented** 2026-11-06 (section 5):
- `fip-strict` (Verus block): `FipFn` gains `spec fn allocs(&self) -> nat` and `call`
  is `allocates self.allocs()`. `Certified<ALLOCS, _>`: `allocs()` = `ALLOCS as nat`,
  `pre` = the closure's `requires` `&&& call_allocates(self.inner(), args) <= ALLOCS`.
  So the Verus-side `Certified<0, _>` of `fip_fn!(path)` without `bound`, every scanned
  closure `N` and every `bound <= K` are checked at each verified call. `Stateless`:
  the part's `allocs()`; `Then`: the sum. `Compose`: one `FipFn` impl per arity
  `0..=MAX_ARITY` (`compose_fip_fn!`, Verus only; plain keeps the generic impl), sum of
  the parts. Argument/result type parameters of the Verus impls are bounded
  `vstd::alloc_check::AllocFreeDrop`; four Verus-only `unsafe impl AllocFreeDrop`
  (`Certified<_, C: Copy>`, `Stateless`, `Compose`, `Then`), pinned by
  `tests/hand_written_certs.rs` (`alloc_free_drop_impls_are_exactly_the_documented_ones`;
  the `FipBound` pins are unchanged: the new impls are no certificates).
  `Certified::assume` / `assume_no_panic_macros`: `C: DropFreeFn`, `allocates 0`.
  Verified: 23 (19 + 4 more `Compose` impls).
- `tests/verus_drift.rs` learns the Verus-only additions: `allocates` clauses, the bound
  `: vstd::alloc_check::AllocFreeDrop`, the empty `unsafe impl .. AllocFreeDrop for ..`
  markers (exactly 4), and compares the `compose_fip_fn!` impl (with `$($A,)*` read as
  `Args`) with the plain generic `Compose` impl; the number of `compose_fip_fn!` and
  `certified_fip_fn!` invocations must both be `MAX_ARITY + 1`.
- `fip_core::strict::*`: `update` `allocates f.allocs()`; `map_in_place`,
  `map_in_place_st`, `compact`, `dedup_by`, `compact_map`, `compact_map_st`
  `allocates old(xs)@.len() * f.allocs()`, with the loop invariant
  `allocated() <= i * f.allocs()` and one `nonlinear_arith` step per loop; callables
  bounded `+ AllocFreeDrop`. Verified: 70 (64 + the 6 `nonlinear_arith` steps, each a
  verified item; measured: without them 6 loop invariants fail).
- `verify/compose_state.rs`: `allocates 0` on the 5 strict callers
  (`number_from_11_strict`, `number_from_11_closure`, `doubled_stateless`,
  `quadrupled`, `numbered_doubled`), so every function there is bounded; `fip_fn!(tick_checked)`
  stays (Verus: `Certified<0, _>`, `pre` proved from `tick_checked`'s `allocates 0`).
  Hints: `quadrupled` asserts `allocs(&d1) == 0`, `allocs(&c) == 0` and
  `len * allocs(&c) == 0`; `numbered_doubled` the same for `t`, `d`, `f`. Measured:
  without the hints these 2 callers fail their `allocates 0`. 13 verified.
- `verify/compose_strict.rs`: the `fip_fn!` closure passed to `test_one` (`param(keep = 0)`)
  needs `verus_spec(r: bool => allocates 0)`; without it `Certified::pre` fails (measured).
- `verify/alloc_callers.rs`: `boxed_once` (a `Certified<1, _>` of a closure with
  `allocates 1`, caller `allocates 1`) and `incremented_strict`
  (`fip_core::strict::map_in_place` with a `Certified<0, _>`, caller `allocates 0`, no hint
  needed). 10 verified.
- `verify/fip_fn_types.rs`: `boxed` (`#[fip(1, strict = true)]`, `allocates 1`) and its
  verified caller `boxes_one` through `fip_fn!(bound <= 1, boxed)`. 4 verified; the plain
  build compiles it.
- Mutants and controls in `just verify-negative` (each checked for its reason):
  `strict-compact-calls-twice` (a second `keep.call` per element: invariant
  `allocated() <= r * keep.allocs()` fails), `compose-sum-minus-one` (`Compose::allocs`
  one less than the sum: `call`'s `allocates self.allocs()` fails, every arity),
  `certified-pre-no-alloc` (the `call_allocates` conjunct deleted from `Certified::pre`:
  `call`'s bound fails), controls `callers-certified0-allocating` (`boxed_once` with
  `Certified<0, _>`: precondition `self.pre(args)` fails; the closure has no
  `requires`, so the failing conjunct is `call_allocates(..) <= 0`) and
  `types-path-no-bound` (`fip_fn!(boxed)` in `boxes_one`: the same), and the drift mutant
  `drift-compose` (a changed `Compose::call` body in `compose_fip_fn!`). Updated:
  `certified-pre-true` (the `requires` conjunct replaced by `true`) and the two
  `strict-*-st-not-threaded` mutants (signature now formatted over several lines).
  Observed: when `pre` fails at a call, the caller's own `allocates` also fails (also
  with a caller bound of 5 for a callee bound of 0): the fork assumes the callee's bound
  only under its precondition.
- Strip gate: `strip_alloc.py` rewrites only `src/` of crate directories (a crate's
  `tests/` are plain Rust; `verus_drift.rs` names the syntax in strings), deletes a
  closure attribute `verus_spec(r: T => allocates E)` whose only clause is the bound,
  and multi-line `proof! { .. }` blocks holding only `assert(..allocs(..)..);` lines.
  Upstream 0.2026.11.02 on the stripped sources: 23/58/1/3/4/13/4 (fip-strict counts
  the 5 `Compose` impls, `fip_fn_types.rs` the 2 new functions).
- Observed brittleness *(open)*: in the full-crate run of the `strict-compact-calls-twice`
  mutant, the unchanged `strict::compact_map_st` also fails its final assertion
  (`compact_map_st_fip_post(..)`); verified alone (`--verify-function`) it passes, as
  in the unmutated crate. The proof depends on the context of the module run.

**Phase 4 implemented** 2026-11-06 (section 5; prelint record amendment "cfg twins
and proved allocation bounds (sidecar format 5)"):
- **Cfg-twin hole closed, both sides, fail closed.** Probe
  `/home/ybi/pfip-recheck-tmp/phase4/hole/` (the `hole/` probe of 2.4 with
  `ensures r > 0` on the Verus `Step::step`, a plain-only impl returning 0 after a
  `Box::new`, and three callers): before, `run<T: Step>`, `run_s` and the concrete
  `direct` were listed and both divisions discharged; the VIR records of all three name
  only the trait method. Generator: traits with an implementation or declaration under
  a cfg naming `verus_keep_ghost` are recorded (`divergent`) and every function naming
  one of their methods is skipped with its callers, also through `--import-sidecar`.
  Driver: the Verus results of a listed function are not used for an instance calling a
  trait method (not `Fn*`) implemented, in this build, by a function no sidecar lists
  (outside std). After: the probe lists nothing; with the old listing forged to format 5
  the driver keeps both divisions. Fixtures: `verus_sidecar_twin`, `just verify-sidecar`
  probe `twin`, two unit tests.
- **Twins not unified** into one attribute-mode source: `Compose` is one generic plain
  impl and one Verus impl per arity (no `AllocFreeDrop` for a generic tuple), the Verus
  impls name `AllocFreeDrop` bounds and spec functions the plain build lacks, and the
  plain marker traits are blanket impls. Exclusion is general (also downstream twins).
  Cost, measured: `fip_core::strict::*` (7 functions) are no longer listed in `fip-core`'s
  sidecar, and `strict::dedup_by`'s bounds check is reported again in the release
  self-check.
- **Sidecar format 5 with bounds.** `fn` lines carry the proved `allocates` bound (`-`,
  literal, parameter-linear, `opaque:<sha256>`), `-V alloc-check` is required in the
  stamp (generator and driver). The driver takes a literal bound `K` of a non-generic
  function without `requires` whose instance passes the trait check and whose panic paths
  are allocation failures only, where its own count is `∞` or open; a finite count `m > K`
  is kept and reported as an error; frees, panics, recursion and `⊤` stay the driver's.
  Fixture `verus_alloc` (10 verified): `twice` `∞` → 2; equal counts kept; linear,
  `requires`, generic bounds not used; a forged lower bound reported at 7 roots; a stamp
  without `-V alloc-check` refused. Committed bounds: `fip-core` 6 × `0` and 4 opaque,
  `refill` `0`, `Certified::assume*` `0`; all are generic or have a `requires`, so no
  workspace verdict changes.
- **Not done in phase 4** *(open)*: evaluating parameter-linear bounds at a call site
  (the driver's value analysis would have to bind the parameters); per-instance
  re-establishment of a bounded type parameter's Verus premise (`T: AllocFreeDrop`: the
  driver would check the instance's drop glue itself), which generic functions such as
  `fip_core::slice::swap` (`allocates 0`) need before their bounds can be used; the
  disagreement report between the token-level strict certificate and the proved bound
  (2.3); the `--compile` requirement of imported crates (2.4) is still enforced only by
  the fork's import check.

**Phase 5 implemented** 2026-11-09 (section 7, details in 7.6; branch
`phase5/strict-total`, fork `fip-beta` `6f6975af2`, upstream 0.2026.11.02 for the
strip gate, Z3 4.16.0): `strict` (bare, alias `strict = true`) and `total` in
`fip-macros`, generating the Verus contract under Verus's driver (`requires`,
`allocates N`, for `total` `no_unwind` and `#[verifier::fip]`), with the strip switch
`FIP_MACROS_UPSTREAM=1`; `fip-prelint` discharges a `total` mark only with a listed
`allocates 0` proof; `fip_core::replace` and `fip_alloc::refill` are `total`,
`fip_core::swap` and `swap_lt` `strict` (measured reason in 7.6); closure `no_unwind`
measured as not expressible (7.3); 5 new mutants/controls and a driver fixture.
*Amended 2026-11-09:* `swap` and `swap_lt` are `total` too since the re-pin to fork
`1b27c1101` (7.6, "Not done / open").

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
source or excluded from discharge (phase 4). **Closed in phase 4** by exclusion (see the
phase-4 note at the top): the generator taints callers of divergent traits' methods, the
driver refuses trait calls into implementations no sidecar lists.

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
| 5. strict-mode fate | accepted 2026-11-09, section 7: `strict` = one-declaration contract generator checked by Verus; `total` = the strictest grade, mapped onto the fork's `no_unwind`/`#[verifier::fip]` where they apply and onto `fip-prelint` elsewhere | section 7.5 | plain strict mode (`strict = true` keeps its meaning) | 3–6 days *(estimate)* |

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
  *Amended 2026-11-09:* the fork rebased onto rustc 1.100.0-beta.10 (`fip-beta`); the
  re-pin (branch `repin/fip-beta`) moves the Verus pin and `fip-prelint`'s toolchain to
  `beta-2026-11-05`, and keeps the workspace MSRV at 1.99.1 (`just msrv` passes on
  1.99.1; nothing needs 1.100). See the amendment of that date in
  `2026-11-01-fip-prelint.md`.
- **D7, phase 5 (ACCEPTED by the user 2026-11-09):** names and roles agreed on
  2026-11-06 (chat), the design of section 7 approved on 2026-11-09: `strict` is the
  contract generator, `total` the strictest grade; neither duplicates the fork's
  `#[verifier::fip]`/`fip(strict)`, both map onto them where those are sound and usable
  across crates.

## 7. Phase 5: `strict` and `total` (accepted 2026-11-09)

**Status:** ACCEPTED by the user, 2026-11-09. The names and roles of `strict` and
`total` were agreed in the 2026-11-06 discussion (chat, not recorded before this
section); the design below was reviewed and approved on 2026-11-09. The re-pin to the
fork's `fip-beta` branch (Rust 1.100) is merged into this branch; implementation is
next. Facts marked *measured* were measured on fork `fip-beta`
`6f6975af2` (`0.2026.11.08.6f6975a`, clean build) during the fork audit of 2026-11-07..09
(probes under `/home/ybi/pfip-recheck-tmp/fipbeta/`); everything else is design,
*unmeasured*.

### 7.1 Roles

- **`strict`** (option 1 of the earlier discussion): a *single declaration* from which
  both builds get their contract. `#[fip(N, strict, requires(..))]` keeps the plain
  certificate (token scan, `Cert`, `param(..)`) and, in a Verus build, also emits the
  `verus_spec` with the same `requires` and `allocates N`, so the number the plain
  certificate states is the number Verus proves. Verus checks; the macro never trusts
  its own scan when Verus is present. `strict = true` stays as an alias of `strict`.
  Today `requires(..)` is written twice (the macro cannot read a following
  `cfg_attr(verus_keep_ghost, verus_spec(..))`, measured on 1.97.1 and 1.99.1, crate
  docs of `fip-macros`); generating it removes that duplication and the drift check.
- **`total`** (option 2): the strictest grade, a superset of `strict`, defined by five
  properties of every call on a normal return. It absorbs `panic_macros = false`.

| property of `total` | Verus build (verified crates) | plain build (any `#[fip]` code) | not covered |
|---|---|---|---|
| P1 no allocation | `allocates 0` (fork `-V alloc-check`) | `fip-macros` token scan (bound 0); `fip-prelint` MIR allocation analysis | — |
| P2 no free (F2) | `#[verifier::fip]`, only without callbacks (7.2) | `fip-prelint` MIR free analysis (implicit drops through their glue) | — |
| P3 bounded stack | Verus rejects recursion without `decreases`; the surface gate forbids function-level `decreases` (README "bounded stack, verified crates") | `fip-macros` rejects direct self-recursion; `fip-prelint` rejects recursion through callees; `fip-prelint --stack` measures bytes per build | stack bytes are a per-build measurement, not a proof |
| P4 termination | Verus: loops need `decreases` (`exec_allows_no_decreases_clause` is not allowed by the surface gate), recursion is forbidden (no function-level `decreases`) | none for loops: no recursion (P3) is checked, but a loop may run forever | **loops in unverified `total` code**: the plain build has no termination check; `fip-prelint` must refuse a `total` mark on a function with a loop unless a Verus sidecar lists it |
| P5 no panic / unwind | `no_unwind` with overflow and bounds obligations | `panic_macros = false` (token level) and `fip-prelint` panic analysis (panic paths through callees, overflow checks as the profile has them) | — |

  Before this section `total` was defined only in the 2026-11-06 discussion; this table
  is its definition.

### 7.2 What the fork offers, and whether `total` can use it

| property of `total` | fork mechanism | usable? (measured on `6f6975af2`) | so `total` uses |
|---|---|---|---|
| allocation 0 | `allocates 0` with `-V alloc-check` | yes; the fork audit found no remaining false bound with the global allocator | Verus, via the `strict` generator (`allocates 0`) |
| termination | `decreases` | upstream Verus feature, not re-measured in this audit | the existing surface gate, no new emission: in portable-fip's verified crates function-level `decreases` is forbidden (`with_fn_decreases`, so no recursion, which the stack claim needs) and every loop needs `decreases` because `exec_allows_no_decreases_clause` is not in `VERIFIER_ALLOWED`; a `total` function in a user crate gets the same rule from Verus only if it is verified |
| no panic / unwind | `no_unwind` plus overflow and bounds obligations | upstream Verus feature, not re-measured in this audit | Verus `no_unwind`; `fip-prelint` panic sidecar for unverified callers |
| no free on normal return (F2) | `#[verifier::fip]` | sound in every probe with the global allocator and with library `FipAllocator`s; but closure calls, generic trait-method calls, `?`, `v[i]`, `for` and slice `len` are rejected, and `mem::forget` counts as no free (a leak is allowed) | `#[verifier::fip]` only for non-callback functions (`swap`, `replace`, `refill`-like); `fip-prelint`'s MIR F2 check for everything, and as the only check for callback combinators |
| bounded stack | `#[verifier::fip(strict)]` | sound after the fixes, but **local only**: a strict function cannot call a function of another crate, nor drop a value whose `Drop` is in another crate (`fipdrop3/xc/u10_strict_libH.rs`) | `fip-prelint --stack` (unchanged); a library cannot offer `fip(strict)` functions to user crates |
| custom allocators | `BoundedAllocator`, `FipAllocator` | a verified `unsafe impl Allocator` can keep the permission for a block it handed to std and write through it (`toolchain/r4/scribble.rs`: `ensures r == 5` verified under `--no-cheating`, run returns 0); reported to the fork 2026-11-09 | `total` (and `strict` claims checked by Verus) assume the global allocator; a user `Allocator`/`GlobalAlloc` impl is a trust point the gate reports |

So `total` is not a new Verus mode: it is a grade whose Verus part is
`allocates 0` + `decreases` + `no_unwind` (+ `#[verifier::fip]` where the function takes
no callback), and whose remaining parts (F2 for callbacks, stack, unverified code) stay
with `fip-prelint`. `fip-prelint` keeps refusing a `total` mark it cannot discharge.

### 7.3 Callback combinators

`fip_core`'s `Fn`-based functions and `_st` variants call closures. Under the fork,
`#[verifier::fip]` rejects every closure call (measured), and `-V alloc-check` already
needs `DropFreeFn` (= `Copy`, D2). Until the fork offers a closure form of `fip` and
`no_unwind` (requests already filed: closure `no_unwind`, non-`Copy` closures through
the drop rule), a combinator is `total` only *relative to its callback*: the macro emits
`allocates` as the callbacks' sum (as phase 2 does), `no_unwind` with a requirement on the
callback *(unmeasured: whether Verus can state "the callback does not unwind")*, and F2 is
checked by `fip-prelint` at each instantiation.

**Measured 2026-11-09** (fork `6f6975af2`, probes under
`/home/ybi/pfip-recheck-tmp/phase5/closure/`, `--no-cheating -V alloc-check`): Verus
cannot state "the callback does not unwind" for a closure parameter.

| probe | result |
|---|---|
| `c1.rs`: `fn apply<F: Fn(u8) -> u8>(f: F, x: u8) .. requires f.requires((x,)) no_unwind { f(x) }` | error "cannot show this call will not unwind": the call goes through `vstd::pervasive::exec_nonstatic_call`, which may unwind |
| `c2.rs`: a closure with its own clause, `\|y: u8\| -> (r: u8) no_unwind { y }` | parse error ("expected curly braces"): closures take no `no_unwind` |
| `c3.rs`: a bound specification `F: Fn(u8) -> u8 with { fn call(..) no_unwind; }` | error "a bound specification may only have `requires`, `ensures` and `allocates`" |
| `c4.rs`: a local closure without clause, called in a `no_unwind` function | same error as `c1.rs` (the fork's `sst_to_air.rs`: "Right now all closures are assumed to unwind") |
| `c5.rs`: a trait method declared `no_unwind`, called through `F: Cb` | verifies (3 verified); not usable for closures: an impl wrapping a closure (`Certified`) would call it, which `c1.rs` shows cannot be `no_unwind` |

So the combinators stay `strict` with hand-written callback-relative bounds, and
`total` with callable parameters is a compile error of `fip-macros` (in every build).
F2 of the combinators stays with `fip-prelint` at each instantiation, as above.

### 7.4 Gates added with the re-pin (branch `repin/fip-beta`)

From the fork audit, independent of phase 5 but required for any Verus-backed claim:
every verified crate runs with `--no-cheating` (it does not reach dependencies: a
dependency verified without it may hide a `#[verifier::trusted_call]`, measured
`toolchain/r3/lib1.rs` + `use1.rs`); `#[verifier::trusted_call]` and `--is-vstd` are
refused; `unsafe impl Allocator`/`GlobalAlloc` in a verified crate is a reported trust
point (7.2).

### 7.5 Steps

1. `fip-macros`: parse `strict` and `total` (`strict = true` alias; `total` implies
   `strict`, `panic_macros = false` and bound 0); in a Verus build emit `verus_spec`
   (`requires`, `allocates N`, and for `total` the `no_unwind` clause; never `decreases`,
   see 7.2) and `#[verifier::fip]` for `total` functions without callable parameters.
   Plain build unchanged apart from the `fip::mark` carrying `total`.
   **Surface gate (decided 2026-11-09):** `fip` is added to `VERIFIER_ALLOWED`
   (`fip-testkit::surface`), because `#[verifier::fip]`/`fip(strict)` only add
   obligations (no free, constant stack) and cannot make Verus accept more; this is a
   change of the trust surface and is recorded here. The line-based scanner sees only
   attributes written in the source, so a macro-emitted `#[verifier::fip]` is invisible
   to it; that is acceptable because a missed restriction cannot weaken a proof. To keep
   the macro from emitting a weakening attribute, a `fip-macros` test asserts that every
   `verifier::..` it emits is in `VERIFIER_ALLOWED` and that its `verus_spec` never
   contains `decreases`.
2. `fip-prelint`: a `total` mark is discharged only if the Verus sidecar lists the
   function with `allocates 0` and the flags of 7.4, and the driver's own F2, stack and
   panic checks pass for the instance; otherwise ⊤ with the reason.
3. Apply to `fip_core`/`fip_alloc`: `swap`, `swap_lt`, `replace`, `refill` as `total`;
   the combinators as `strict` with callback-relative bounds (7.3).
4. Gates: a mutant per property (an allocation, a missing `decreases`, a panic path, a
   free, a deep recursion) must be rejected by the check that owns it; the strip gate
   on upstream 11.02 keeps passing.
5. Revisit when the fork answers the cross-crate `fip(strict)` request (2026-11-09) and
   the closure `fip`/`no_unwind` requests: each answer can move one row of 7.2 from
   `fip-prelint` to Verus.

### 7.6 Implemented (2026-11-09)

Branch `phase5/strict-total` (from `redesign/verus-allocates` `34a8188`). Verus fork
`fip-beta` `6f6975af2` (`0.2026.11.08.6f6975a`), upstream `0.2026.11.02.8bf68ee` for the
strip gate, Z3 4.16.0, rustc 1.100.0-beta.10 (Verus/driver), 1.99.1 (MSRV). Every
statement below is measured unless marked *(unmeasured)*.

**Step 1, `fip-macros`.**
- Grammar: `strict` (bare) and `strict = true` (alias); `total`, which implies
  `strict`, `panic_macros = false` and bound 0. Rejected with a compile error (each a
  `compile_fail` example, checked for its reason by `just compile-fail-reasons`, now
  151 examples): `#[fip(1, total)]`, `total` with `panic_macros = true`, `total` with
  `strict = false`, `total` with a callable parameter, `total` on a trait method
  declaration; a panicking macro in a `total` body is rejected as under
  `panic_macros = false`. `total` on a method under `#[fip_impl]` is rejected
  (*unmeasured* beyond the code path: no example).
- Plain build: unchanged apart from `fip::mark(.., total = true)` under the driver
  (the key is emitted only when set, so no other mark changes).
- Verus build (`rust_verify`): the macro merges the generated clauses into the
  hand-written `verus_spec` (module `verus_gen`): the `requires` translated from
  `requires(..)` (`xs.len()` of a `&mut` parameter is `old(xs)@.len()`, else
  `xs@.len()`; an element access `xs[0]` is an error), `allocates N` (the declared
  bound), and for `total` `no_unwind` and `#[cfg_attr(verus_keep_ghost,
  verifier::fip)]`; never `decreases`. Generated tokens carry the span of the
  `strict`/`total` key, so Verus reports a failed generated bound there (measured:
  "postcondition not satisfied" pointing at `#[fip(strict)]`).
- **Hand-written spec, fail-closed choice:** one source per clause. A hand-written
  `requires` next to `requires(..)`, a hand-written `allocates` (except on a function
  with callable parameters, whose callback-relative bound must be written by hand and
  is then required), a hand-written `no_unwind` with `total`, or a function-level
  `decreases` is a compile error under Verus (wrapped in `#[cfg(verus_keep_ghost)]` so
  the erasing pass of the same run, which no longer sees the `cfg_attr` spec, does not
  report it). The former drift check (`requires(..)` ⊆ the Verus `requires`) remains
  for non-strict `#[fip]`; for `fip-core` the source test
  `crates/fip-macros/tests/requires_drift.rs` now checks that every `requires(..)` is
  on a `strict`/`total` attribute that is not compiled out under Verus and whose
  `verus_spec` has no `requires` of its own (2 tests, 3 negative cases).
- **Strip switch** `FIP_MACROS_UPSTREAM=1`, honoured only under Verus's driver: leaves
  out `allocates` and `#[verifier::fip]` (fork-only) and the requirement of a
  hand-written callback-relative `allocates` (stripped from the source by
  `verify/strip_alloc.py`); `requires` and `no_unwind` stay. Upstream 0.2026.11.02
  accepts `no_unwind` (measured: `u1.rs`, 2 verified). Unit tests: the switch never
  changes the generated `requires` (5 grammar forms), and every emitted `verifier::..`
  is in `fip_testkit::surface::VERIFIER_ALLOWED` with no `decreases` in any emitted
  spec (4 hand-written spec shapes × grade × switch × `requires`).
- Certificates: the module `fip_strict::certs` (hand-written certificates of `swap`,
  `replace`, `refill`) is removed; the attributes generate them. No certificate is made
  without `unsafe` any more (pinned by `fip-strict`'s `hand_written_certs`).

**Step 2, `fip-prelint`.** `fip::mark` takes `total = true` (malformed unless
`kind = "fip"`, `n = 0`, `strict = true`, `panic_macros = false`; a contract with
`total` is an error). A `total` root is discharged only if its crate's Verus sidecar
lists it with the literal bound `allocates 0` (sidecars are used only with the trusted
pin and the flags `--no-cheating -V alloc-check`, unchanged sources and item text,
`crate::verustrust`), and the driver's own allocation, F2, recursion and panic checks
of the root pass (they run as for `strict = true, panic_macros = false`); otherwise
⊤ with the reason; a body with a loop (a cycle in its MIR CFG) adds that its
termination is unchecked without the proof (P4). Fixture `verus_total` (`vtotal`, 7
verified, sidecar regenerated by `just verify-sidecar`): 8 roots, 2 passed (`ok`,
`ok_loop`: the success cases), 6 errors: `bound_one` (listed with `allocates 1`),
`unlisted` (not verified), `unlisted_loop` (not verified, reason names the loop),
`frees` (listed, F2 error), `recurses` (listed with `decreases`, recursion error),
`panics` (listed with a `requires`; the `unwrap` panic path stays). Variants `-off`
(`--no-verus`), `-flags` (stamp without `-V alloc-check`), `-cheat` (without
`--no-cheating`): 0 passed, 11 errors, every `total` refused with the reason.
Self-check: `fip_core` 10 roots, 10 passed (was 8: `swap` and `replace` are roots
now), 1 note (`swap`: the driver does not establish `swap_lt`'s precondition
`i < j, j < xs.len()` from `(lo, hi) = if i < j { (i, j) } else { (j, i) }`; a note
under `strict`, it would be an error under `total`), 1 panic site discharged by
Verus; `fip_alloc` 1 root (`refill`, `total`), passed.

**Step 3, application.**
- `fip_core::replace` and `fip_alloc::refill`: `#[fip_macros::fip(total)]`, verified
  with the generated `no_unwind allocates 0` and `#[verifier::fip]` (fip-core 70
  verified, fip-alloc 1, unchanged counts).
- `fip_core::swap` (`requires(i < xs.len(), j < xs.len())`) and `slice::swap_lt`
  (`requires(i < j, j < xs.len())`): **`strict` only.** With `#[verifier::fip]` the
  fork rejects `swap_lt`'s call of `<[T]>::split_at_mut` ("is not
  `#[verifier::fip]` and has no `deallocates_when` condition": vstd's
  `assume_specification` of `split_at_mut` has `no_unwind allocates 0` but no
  `deallocates_when`), and `swap` because it calls `swap_lt` (probe
  `phase5/closure/f1.rs`–`f3.rs`; `allocates 0` and `no_unwind` alone verify). The
  driver's note above is a second, independent obstacle for `swap`.
- Combinators (`update`, `compact`, `map_in_place`, .., `fip_core::strict::*`):
  unchanged, `strict` in plain builds with hand-written callback-relative bounds under
  Verus (7.3). `verify/compose_strict.rs`'s `test_one` (`param(keep = 0)`) now states
  `allocates keep.allocs()` by hand (required) and `F: AllocFreeDrop`.
- Verified callers: `tick_checked` and `boxed` drop their hand-written `allocates`
  (generated now). New gate `verify/total.rs` (6 verified): `total` with and without
  `requires(..)`, a `total` caller of `total` callees, `#[fip(1, strict)]`, a `strict`
  caller of a callee that may unwind.
- Sidecars regenerated: `fip-core` 10 listed / 7 skipped (bounds unchanged: `swap`,
  `swap_lt`, `replace` `0`), `fip-alloc` 1 (`refill` `0`), `fip-strict` 2 / 13
  (line numbers only).

**Step 4, gates.** `just verify-negative`: 85 mutants and controls, each rejected by
the check that owns its property (80 before: 5 new, 2 changed):

| property | mutant / control | rejected by |
|---|---|---|
| allocation | `swap-allocates`, `refill-allocates` (a `Box::new` in `strict`/`total` bodies) | `fip-macros` token scan (it runs in the Verus build now; before, Verus `allocates 0`) |
| allocation | control `total-hidden-alloc` (a callee whose hand-written certificate claims 0 but which allocates once, called by a `strict` function) | Verus: the generated `allocates 0` ("postcondition not satisfied" at `#[fip(strict)]`) |
| free | `refill-frees` (an `Option<Box<u8>>` dropped in `refill`), control `total-free` | Verus: the generated `#[verifier::fip]` ("must not deallocate") |
| free | fixture `verus_total` `frees` | driver F2 |
| recursion | `compact-recursive` (was `swap-recursive`; `swap` is `strict` now, where the macro's direct-recursion check fires first) | Verus ("recursive function must have a `decreases` clause"); surface gate `surface-decreases` |
| recursion | fixture `verus_total` `recurses` | driver recursion check |
| panic / unwind | control `total-unwind` (a `total` caller of a callee without `no_unwind`) | Verus: the generated `no_unwind` ("cannot show this call will not unwind") |
| panic / unwind | fixture `verus_total` `panics` | driver panic analysis |
| loop without `decreases` | `compact-loop-no-decreases` | Verus ("loop must have a `decreases` clause"); surface gate `surface-no-decreases-attr` (the attribute that would allow it) |

Strip gate `just verify-upstream` (with `FIP_MACROS_UPSTREAM=1`): 23/58/1/3/4/13/4 as
before plus `verify/total.rs` 6; control: without the switch upstream rejects the
stripped `verify/total.rs` ("unexpected token" at the generated `allocates`, reported
at `#[fip(total ..)]`). `verify/strip_alloc.py` also removes hand-written
`#[cfg_attr(verus_keep_ghost, verifier::fip)]` lines and fails on a leftover
`verifier::fip`.

**Not done / open:**
- `total` for callback combinators: not expressible (7.3, measured); F2 for them stays
  with the driver.
- ~~`swap`/`swap_lt` as `total`~~ **done 2026-11-09:** the fork `1b27c1101` gives the
  slice views (`split_at_mut` among them) `deallocates_when(0, false)` (requested
  2026-11-09), so `#[verifier::fip]` accepts `swap_lt`; and `swap` now calls `swap_lt` in
  two branches (`if i < j { swap_lt(xs, i, j) } else if j < i { swap_lt(xs, j, i) }`)
  instead of through a `(lo, hi)` tuple, so the driver proves `swap_lt`'s precondition
  at both calls (with the tuple it could not, which `total` makes an error). Measured:
  Verus fip-core 70 verified; the driver passes all 10 fip-core roots on x86_64 (self-check notes 1 instead of 2
  in debug, 0 instead of 1 in release) and no longer needs a Verus-discharged panic site; on the other
  10 targets `swap`/`swap_lt` are refused as ⊤ like `replace` (the sidecar is
  x86_64-only). The mutants `swap-no-op`, `swap-allocates` and
  `swap-lt-requires-dropped` follow the new body and attribute.
- `total` on `#[fip_impl]` methods and trait contracts: rejected, not designed.
- A `total` function in a user crate is refused by the driver unless the crate
  publishes a Verus sidecar (by design of 7.5 step 2).
- The generator's `requires` translation covers the `fip_lint_rules::requires`
  grammar except element accesses (`xs[0]`, an error); whether `w.f` of a reference
  parameter verifies as written is *unmeasured* (no such function in the workspace).

## Probe files

`/home/ybi/pfip-recheck-tmp/redesign/`: `base/` (copy), `p1/` (`T` bounds only),
`p2/` (+ `DropFreeFn`, zero lemmas), `p3/` (final, with `run.sh`, `runc.sh`, `runcs.sh`,
`client/c1.rs`–`c4.rs`, `cs1.rs`–`cs3.rs`), `p3s/` (strict mode), `p3up/` (stripped),
`strip_alloc.py`, `edit_slice.py`, `tr/` (trait bounds), `up/` (11.02 parsing),
`wc/` (`where`-clause cfg), `hole/` (cfg divergence), `ws/` (plain workspace build),
`compose_state.fixed.rs`.
