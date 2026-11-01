<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# Note: Verus does not verify stateful `FnMut`; pass the state explicitly ("monadic" style)

**Status:** NOTE (reusable outside this repository), 2026-11-02.
**Measured with:** Verus `0.2026.10.18.7d82994` (upstream release), and a downstream
fork rebased on the same release, both with Z3 4.16.0. Probe sources are in
[`verus-fnmut/`](verus-fnmut/). They are reference material and are not run by `just ci`.
**Used in this repository by:** `fip_core::{map_in_place_st, compact_map_st}` and
their `fip_core::strict` variants (commits `06c99ac`, `6fe289b`).

## Problem

If a higher-order function takes a closure with mutable state (`FnMut`), Verus cannot
give it a meaningful specification. The probes below measure three things:

| probe | what it does | result |
|---|---|---|
| `a_generic.rs` | generic `F: FnMut(u32) -> bool`, called in a loop; the postcondition does **not** mention the closure's results | verifies — this only shows that an `FnMut` *can be called*, nothing more |
| `b_capture.rs` | a closure in verified code that captures a local mutably (`c = c + 1`) | **rejected**: "Verus does not currently support closures capturing a mutable reference for variables of any mode" |
| `c_state.rs` | after `let b = f(1)` on `f: F: FnMut`, `assert(f == f0)` where `f0` is the value before the call | **verifies** — Verus does not model a post-call state of an `FnMut` value |

`c_state.rs` decides the question. Suppose a combinator generic over `FnMut` is
verified. Its proof covers only closures without state, which an `Fn` version covers
anyway. Now suppose unverified code passes it a closure that does have state. Then the
proof relies on `f == f0`, which is false for that closure, so the proof guarantees
nothing about the call. **Do not write `FnMut` combinators and present them as
verified for stateful closures.**

## Workaround: pass the state as a value

Make the state an explicit value. The step takes the current state and returns the
next one:

```rust
fn count_st<S, F: Fn(S, u32) -> (S, bool)>(xs: &Vec<u32>, s0: S, f: F) -> (r: (usize, S))
```

The closure is a plain `Fn`, so it has no hidden state, and every state passes through
the arguments and results. The postcondition can then describe the whole run as a
**trace**: a sequence of states `ss` and a sequence of step results `bs` with

- `ss[0] == s0` and `ss.last() == r.1` (the returned state);
- `call_ensures(f, (ss[k], xs[k]), (ss[k + 1], bs[k]))` for every `k` (each step
  follows `f`'s specification from the state before it to the state after it);
- whatever the combinator itself guarantees, stated in terms of `bs` (here: `r.0` is
  the number of `true` in `bs`).

The loop keeps `ss` and `bs` as ghost sequences, pushes one element of each per
iteration, and carries the `call_ensures` chain as an invariant (`e_monadic.rs`).

A verified caller can then prove facts about the final state from the postcondition
alone. In `e_monadic.rs` the caller threads a counter through three elements and
proves the final state is `3`. The negative control `e_negative.rs` claims `4` and is
rejected, so the proof is not vacuous. The same two results were measured on both
Verus builds.

This is the state monad written out by hand: `S -> (S, A)` for each step, with the
trace standing in for the sequence of binds.

## Practical points (measured)

1. **Pass the state by value, not as `&mut S`.** An `&mut S` argument
   (`F: Fn(&mut S, u32) -> bool`, `d_state_arg.rs`) does verify, with these costs:
   - the closure's postcondition must use `*old(s)` / `*final(s)`;
   - in the combinator's `requires`, the quantifier has to range over `&mut S` itself:
     `forall|s: &mut S, x| f.requires((s, x))`. Writing `forall|s: S| f.requires((&mut s, x))`
     fails with "mutable borrow is not allowed in spec context";
   - we did not measure whether such a combinator can carry the state chain through
     its loop.

   The by-value form avoids all of this. It also fits ownership-based in-place code:
   the state is moved in and moved out, never aliased.
2. **Concrete inputs at the caller.** With `vec![..]` the caller's assertions about
   individual steps failed. Building the vector with `push` and asserting
   `xs@ =~= seq![..]` made them verify (`e_monadic.rs`, `caller`).
3. **Exposing the trace to callers.**
   - **Any `with` clause is unusable under `--no-cheating`.** In attribute mode, a
     `with` clause makes the macro emit a copy of the function marked `external_body`
     for unverified callers, and `--no-cheating` rejects `external_body` outside
     `vstd`. Measured on both Verus builds; it fails with
     "external_body/assume_specification not allowed". This covers:
     - a ghost return value, `verus_spec(r => with … -> trace: Ghost<Seq<S>>)`;
     - `with Tracked(out): Tracked<&mut Ghost<..>>`;
     - a ghost input.
   - **An existential in the postcondition works**, but every caller needs a `choose`.
   - **What `fip-core` does (commit `6fe289b`): name the trace with a spec function
     defined by `choose`.** For example, `map_st_by_trace(old, new, f, s0, s)` returns
     the trace, and the `ensures` states the postcondition *for exactly that trace*.
     A caller then writes `let ss = map_st_by_trace(..)` and uses it directly. It needs
     no `choose` and no lemma call (`verify/compose_state.rs`).
4. **Precondition with a state invariant.** The simplest precondition requires `f` to
   accept *any* state: `forall s, x: f.requires((s, x))`. This is too strong for steps
   that rely on an invariant of the state, such as a counter that must stay below its
   overflow point.
   - **What `fip-core` does (commit `6fe289b`):** the precondition is a spec predicate
     (`map_st_by_ok(xs, f, s0)`). It holds if `f` accepts any state, or if some
     `inv: spec_fn(int, S) -> bool` meets three conditions:
     - `inv(0, s0)` holds;
     - `f` accepts element `k` in every state with `inv(k, _)`;
     - every call takes `inv(k, _)` to `inv(k + 1, _)`.
   - A caller states its invariant by asserting `map_st_by_inv(..)` for a concrete
     lambda before the call. The postcondition carries the invariant along the trace.
   - `spec_fn` applications cannot be triggers, so the quantifiers trigger on
     `f.requires` / `f.ensures` and on `ss[k]`.
   - Also measured on both builds: passing the invariant as a value of a trait type
     with a `spec fn inv` verifies. It was not adopted because Rust has no default type
     parameters on functions.
5. **Cost.** The state is moved twice per step, once in and once out. For large `S`,
   measure before you use this pattern on a hot path. It was not measured here.

## Applying it elsewhere

- Any verified combinator that would take `FnMut` (fold, scan, filter with a counter,
  stateful map, iterator adapters with internal state) can take
  `Fn(S, X) -> (S, Y)` plus an initial state instead, and return the final state.
- If callers already have `FnMut` closures, they can wrap them in **unverified** code
  as an adapter that keeps the state outside. Such an adapter is not covered by the
  proof. Say so wherever it is used.
- Do not depend on `FnMut` reasoning improving in a later Verus release. Re-run the
  probes in `verus-fnmut/`. If `c_state.rs` stops verifying, Verus has started to model
  post-call state, and this note should be revisited.
