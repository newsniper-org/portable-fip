<!-- SPDX-License-Identifier: MIT OR Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# portable-fip

Building blocks, lints and test tools for writing Rust in the style of
**FP²: Fully in-Place Functional Programming** (Lorenzen, Leijen, Swierstra,
ICFP 2023): owned values are consumed and their memory is reused in place, so a
function neither allocates nor frees.

Portable means: `no_std` where possible, no dependencies, stable rustc, and no
build-time dependency on the verifier. The same crates serve a hosted program and
a kernel.

## Crates

| crate | `no_std` | `alloc` | `unsafe` | what it is |
|---|---|---|---|---|
| `fip-core` | yes | **no** | forbidden | `replace`, `update`, `swap`, `compact`, `dedup_by`, `compact_map`, `map_in_place` on `&mut` slots and slices; state-passing `map_in_place_st`, `compact_map_st`; `fip_core::strict::*`: the same over certified `FipFn` callables; all Verus-verified |
| `fip-alloc` | yes | yes | forbidden | `refill`: reuse a `Box` cell instead of drop + `Box::new`; Verus-verified |
| `fip-arch` | yes | no | 3 `asm!` hints | `ARCH`, `CACHE_LINE` (overridable), `per_cache_line`, `prefetch_read`, chosen by `cfg(target_arch)` |
| `fip-strict` | yes | no | 9 trusted items | `Cert` (named), `FipBound`, `FipFn` (with Verus `pre`/`post` specs), `Certified`: allocation certificates for strict mode; Verus-verified |
| `fip-macros` | n/a (proc-macro) | — | forbidden | `#[fip]`, `#[fip(N)]`, `#[fbip]` lints (on a trait method declaration: a contract of every implementation, checked by `fip-prelint`); `strict` (`= true`) and `total` modes (under Verus they generate the Verus contract); `#[fip_trait]`; `#[fip_impl]`; `#[fip_extern]`; `#[fip_cert]`; `#[fip_exclude]`; `fip_fn!` |
| `fip-lint-rules` | yes | no | forbidden | the rule tables shared by `fip-macros` and `fip-testkit` (allocation sites, ghost macros, audited `core` table) |
| `fip-testkit` | no (tests) | — | 1 `impl` | counting allocator (`assert_fip!`, `assert_fbip!`, `assert_fip_n!`, `assert_fip_all_threads!`); `callgraph` (recursion across crates); `summaries` (interprocedural `fip`/`fip(N)` allocation bounds); `surface`, `certs` (source gates) |

No external dependencies; only dependencies between workspace crates. `fip-core` and
`fip-alloc` depend on `fip-strict` and `fip-macros` (their functions are
`#[fip_macros::fip(strict ..)]`/`(total)`, which generates their certificates and,
under Verus, their allocation contracts); `fip-macros` and
`fip-testkit` depend on `fip-lint-rules`. "Trusted items" in the `unsafe` column:
`unsafe` appears only on the four certificate constructors (`Cert::assume`,
`Cert::assume_no_panic_macros`, `Certified::assume`,
`Certified::assume_no_panic_macros`), on `unsafe trait FipBound` and on its four
built-in `unsafe impl`s (for `Certified`, `Stateless`, `Compose`, `Then`; the trait
and the impls are declared once for plain builds and once inside `verus!`), marking
trusted claims; there is no `unsafe` operation.

## What is guaranteed, and by what

FP²'s `fip` result (no allocation, no deallocation, constant stack) is a theorem
about a linear calculus, checked by Koka's compiler. Rust has no such checker, so
each property here has its own mechanism, and the strength differs:

| property | mechanism | strength |
|---|---|---|
| `fip-core` cannot allocate | it does not link `alloc` | by construction |
| functions do what their spec says | Verus fork `fip` `0.2026.11.23.2e6f587` (pinned in `tools/fip-prelint/verus-trusted.txt`, checked by `just verus-pin`), `--no-cheating -V alloc-check --edition 2024` on every run (`just verify-flags`); the same sources with the allocation layer stripped verify on upstream Verus `0.2026.11.02` (`just verify-upstream`); specs pre-verified against concrete accept/reject cases; 37 functional mutants (plus 4 that check the hand-written `ensures` and the generated `requires` survive the `strict`/`total` merge, 1 recursive, 1 loop without `decreases`, 11 surface-gate and 2 spec-drift mutants; the surface gate also rejects `trusted_call`, the identifier `internal` (`verus::internal(..)`) and allocator trait implementations in the verified sources) and 14 wrong claims of verified callers (final states, missing or unpreserved state invariants, closure specifications, adapters) must fail; a functional mutant must break a loop invariant or the postcondition, and none may hit the resource limit | proof (Verus trust base) |
| a verified function or closure with an allocation bound allocates at most that much when it returns normally | Verus fork, `-V alloc-check` (`fip-core`'s `Fn`-based functions `allocates 0` or callback sums, `fip-alloc::refill` `allocates 0`; `fip-strict`'s `FipFn::call` `allocates self.allocs()`, where a `Certified<N, _>` has `allocs()` = `N`, checked at each verified call by `Certified::pre` (`call_allocations(closure, args) <= N`), and the adapters the sum of their parts; `fip_core::strict::*` `old(xs)@.len() * f.allocs()` (`update`: `f.allocs()`); the step functions and `fip_fn!` closures and the verified callers of `compose_state.rs`, `verify/alloc_callers.rs` and `verify/fip_fn_types.rs`; 9 allocation mutants in `fip-strict`/`fip-core`/`fip-alloc` (2 of them, in the `strict` `swap` and the `total` `refill`, are rejected first by the `fip-macros` token scan, which runs in the Verus build since phase 5) and 8 allocating or unbounded caller controls (including a `Certified<0, _>` of an allocating closure, and `fip_fn!(path)` without `bound` of an allocating function) must fail; since phase 5 `strict`/`total` functions get `allocates N` generated from `#[fip(N, ..)]`, and an allocation hidden from the token scan behind a hand-written certificate fails it (`verify/total.rs`); decision `docs/decisions/2026-11-06-redesign-verus-allocates.md`, phases 2, 3 and 5). `cargo fip-prelint` reads the proved bounds from the Verus sidecars (format 5, phase 4) and takes a literal bound `K` in place of its own count of a listed non-generic function without `requires` whose panic paths are allocation failures only, where its count is not a finite number `<= K`; a finite count above `K` is an error (fixture `verus_alloc`) | proof (fork trust base, plus vstd's allocation specifications and the fork's allocation pass); frees and panicking paths are not covered by `allocates`; for `total` functions the generated `#[verifier::fip]` proves no free on a normal return and `no_unwind` no unwinding (controls in `just verify-negative`) |
| no allocation in a `#[fip]` body | `fip-macros` token scan; constructors of empty std collections that never allocate (`Vec::new`, `String::default`, …) are not sites: audited in the `alloc` sources of rustc 1.97.1/1.99.1/1.100.0-beta.10 (a test fails on other compilers), measured 0 allocations, agreed by `fip-prelint` | heuristic: blind to callees, trait methods, macros |
| no allocation when the code runs | `fip-testkit` counts (per thread, or process-wide) | evidence for the tested inputs |
| bounded stack, verified crates | Verus rejects recursion without `decreases`; the surface gate forbids function-level `decreases` and `verifier::` attributes outside an allowlist (`exec_allows_no_decreases_clause`); a recursive mutant must fail | proof that the call graph is acyclic (closures passed in excluded) |
| no recursion, other `#[fip]` code | `#[fip]` rejects direct self-recursion; `fip_testkit::callgraph` reports cycles across one or several crates (module-aware paths, `macro_rules!` bodies, `include!`, functions used as values, indirect calls from `#[fip]` functions) | check, not proof: method calls match by name (over-reports); misses functions generated by macros, pointers from outside the scanned sources, and crates not scanned. No stack bound is claimed for unverified code, except the per-build measurement below |
| allocation, frees, recursion and panics through callees, on MIR | `cargo fip-prelint` (`tools/fip-prelint`, rustc driver pinned to `1.100.0` (stable, the Verus fork's toolchain), repinned with `just prelint-repin`): resolved calls, implicit `Drop` (a free only when its drop glue deallocates; generic drop glue field by field, a bare `drop(T)` is a term, a glue rustc cannot build for the generic type is ⊤), operator impls, generic instances, loops from the CFG, overflow checks and debug assertions as the profile has them (not as `-Copt-level=0` would), declared `param(g = K)` bounds at every call site (a private function that is never used as a value and passes an undeclared callable parameter on is checked at its own call sites, with what each passes); dependencies analysed only if they declare `fip::export` (read from the crate root's parsed inner attributes, `cfg_attr` forms included; one made by a macro is not seen, so ⊤); standard-library functions without MIR (`core::fmt::write`, `format!`'s `format_inner`, integer, 128-bit and float formatting, derived `Debug` and the debug builders with `{:?}` and `{:#?}`, ..) through generated summaries (`tools/fip-prelint/std-summaries/`, from a `-Zbuild-std` analysis with the shipped std's release settings, stamped with the rustc version and target, one per installed target with `std` (10: the host and 9 cross targets, wasm32 included); another compiler or target, or a function not covered, is ⊤; a change of their content re-checks every crate, also when the file's modification time did not move), so `write!` into a buffer is checked and `format!` is a violation, not ⊤ (a `&dyn Debug` is resolved to the concrete type its call site unsizes; one read from data is ⊤); a foreign call inside a summarised function (`syscall`, `read`, `__errno_location`, ..) is resolved with the analysed crate's FFI marks by link symbol and ABI (certified, excluded, else the FFI error naming the std function), not ⊤; the crates `std` itself depends on (`hashbrown`, ..) are analysed like `std`; float math intrinsics (`sqrt`, `sin`, ..) are trusted to lower to instructions or to the C math library's allocation-free function of that name; anything else without MIR is ⊤ and reported. Allocation = global-allocator entry points, `GlobalAlloc`/`Allocator` impl methods, foreign C allocation functions (`malloc`, `free`, ..), and functions declared `fip::alloc_source`/`fip::free_source`; these are opaque (their bodies, the allocator's internals, are outside FIP) | check, not proof: an unmarked pure-Rust pool (an arena handing out slices of its buffer) is ordinary code and not an allocation, so a crate that declares `fip::export` and hands out memory from its own pools must mark them (`cargo fip-prelint --pool-hints` prints opt-in heuristic notes for pool-shaped unmarked methods of such crates and of the checked packages; they change no verdict); source marks are trusted (the summary counts them); sites discharged by Verus are trusted to Verus 0.2026.10.18.7d82994 with Z3 4.16.0 (`tools/fip-prelint/verus-trusted.txt`) and to the sidecar's provenance (the generator reads Verus's VIR log of a successful `--no-cheating` run over the entire crate; a hash mismatch means not used; `just verify-core` fails on a stale committed sidecar), and the summary counts them; path conditions only within one function (bounds/overflow/division checks behind integer guards, slice lengths and `for` over ranges, inclusive ranges, reversed ranges, slice iterators, their `enumerate` and `zip` are proved and dropped; calls, allocations, frees, panics and ⊤ on a branch proved infeasible are not counted; values returned by calls are related to their arguments by return summaries computed from the callee's MIR, through access paths (fields, and elements at a constant index: `xs[0]`, or at an index local while it is unchanged: `xs[k]` read twice) only behind shared references to `Freeze` types, and by an audited table for intrinsics; callees with checks are analysed in each call site's context, up to 3 levels; declared preconditions `#[fip(requires(..))]` (also over such access paths, `w.n`, `xs[0]`) are assumed in the root and checked at every analysed call site, never read from Verus (written by hand, compared with the `verus_spec` requires where visible); callers outside the analysed crates are not checked; a package may declare a Verus sidecar (`[package.metadata.fip-prelint] verus-sidecar`, `fip-strict`, `fip-core` and `fip-alloc` do): the body-local overflow, bounds and division checks of the exec functions a `--no-cheating` Verus run of the whole crate verified are discharged under their Verus `requires` while the sidecar's stamp is the pinned Verus and Z3 with the build's target and features, every source hash of the run and the function's item hash (attributes, `verus_spec`, body) match, and are counted in the crate summary with the stamp; a call Verus did not check carries the callee's Verus `requires` as a panic path; a stale, foreign-stamped or missing sidecar is not used, with the reason; `cargo fip-prelint --no-verus` ignores sidecars); a `dyn` or function-pointer call is resolved only when the pointer comes from one function or one concrete type on every path of its body (also through a field of a local aggregate or an element of a local array assigned only as a whole), or is read from a constant, an immutable static of a `Freeze` type or constant memory (also behind a shared reference stored there, to immutable memory of a `Freeze` type), also through a parameter bound at its call site to a reference to such data (`LocalKey::with` on a `const` thread local) (from the evaluated initializer; every element an index may select is a candidate and their maximum counts), counts the bound `N` of a `fip_strict::Certified<N, fn(..)>` it is held in (every analysed `Certified::assume` is checked against `N` like a `param(f = N)` argument; a pointer of unknown origin or a generic callable type is ⊤ there, a closure generic only through the enclosing function's parameters is analysed through its body; constructions in crates the driver does not analyse are trusted, `assume` being `unsafe`; the certificate bounds no panics), counts the declared `param(g = K)` of a function-pointer, `&dyn Fn*`, `&Box<dyn Fn*>`, `&Rc<dyn Fn*>` or `&Arc<dyn Fn*>` parameter (the argument is checked at every analysed call site; a generic `G: Fn*` or `G: FnMut*` instantiated with a function pointer is checked through its shim, bound to the argument), or, inside a root's graph, uses what the call sites pass for such a parameter (the function, table candidates, trait object type, or a declared parameter of the caller; up to 3 nested callees), or costs the contract on the trait method's declaration (`#[fip]`, `#[fip(N)]`, `#[fbip]` there, with `param(g = K)` for a callable parameter: implementations assume it, every call through the contract checks its argument; every implementation is checked in its own crate, without preconditions, and its own weaker mark is an error; one in a crate without `fip::export` is ⊤); otherwise it is ⊤ (pointers loaded through parameters or from mutable data, `static mut`, interior mutability, call results, `dyn` values of unknown origin without a contract); measured on this workspace: 119 roots, 3 real errors in the deliberate `strict_gaps` test crate, 0 ⊤, 1 real warning, 45 `param` call sites within their bounds, 38 panic-path notes, 12 of them labelled "allocation failure path" (`handle_alloc_error` under a mark that permits the allocation) (21 with `--release`, whose profile has no overflow checks, 12 of them allocation failure paths; 1 site discharged by Verus there, `fip_core::strict::dedup_by`'s bounds check, whose unverified caller `pipeline` carries its precondition instead; 0 in dev); the same verdicts for every installed target (10 with `std`; `x86_64-unknown-none` for the `no_std` crates; the Verus sidecars, stamped for `x86_64-unknown-linux-gnu`, are refused on the other 10 targets, with no verdict changed), measured on an x86_64 Linux host only; the rejected behaviour examples of `fip-macros` are rejected by it too (19, 18 for the documented reason, `HashMap::new` as ⊤); uniqueness, aliasing and interior mutability (`Cell`, `RefCell`, `UnsafeCell`) are not checked, by decision: only their allocations (`Rc::new`), frees (a last `Rc`, a `Box` taken out of a `Cell`) and panic paths (`RefCell::borrow*`) count |
| stack bytes of a root, one build | `cargo fip-prelint --stack` (a `cargo build` of the libraries, and with `--tests`/`--bins` of those targets, with `-Zemit-stack-sizes -Zshare-generics=no -Zcross-crate-inline-threshold=never`; `--build-std` builds the standard library too, with the profile's settings): the longest path over the build's direct calls (from the objects' relocations) of `.stack_sizes` frames plus the return address (8 bytes on x86_64, 4 on i386 plus 4 for a function without callees, 0 on AArch64 and ARM), every function on it mapped to the MIR instance rustc codegened; a generic root is bounded per instance the build codegens (a test or another crate instantiates it); a symbol without a frame size that the root's crate declares with `fip::stack_leaf(sym = B, evidence = "..")` counts `B` (trusted, listed); `⊤` with the reason for recursion in the build, a call through a function pointer or `dyn`, an unresolved call, inline assembly, an unsized local, an undeclared callee without a frame size in the build (precompiled `std`, foreign, `memcpy`, the allocator), a root without a symbol (inlined into every caller, or generic without an instance) | measured for that build only (target, opt-level and flags stated; x86_64, AArch64, i386 and ARM (not Thumb) ELF only, Mach-O/COFF/WASM carry no frame sizes), trusting LLVM's frame sizes and the declared stack leaves; panic paths, unwinding, signal and interrupt contexts excluded; not a proof and never reused across builds |
| allocation through callees, unverified `#[fip]`/`#[fip(N)]` code | `fip_testkit::summaries::fip_violations`: per-function bounds {0..N, ∞, ⊤} over the call graph, unresolved calls are ⊤ (reported, never passed), closure parameters symbolic, witness chain per violation | check, not proof: blind to implicit calls (`Drop`, operators); by-name method matching over-reports on large codebases (measured: 0 violations on `fip-macros/tests`, many false positives when all workspace sources are scanned at once) |

Nothing in this repository says "proved zero-allocation" about code that only the
lint or the tests checked. `#[fip]` adds a `# FIP` doc section stating exactly what
it checked.

## Strict mode

`#[fip(strict = true)]` and `#[fip(N, strict = true)]` restrict a function to calling
(1) an audited table of `core` functions, by absolute path (`::core::..`, `::std::..`), and (2) functions carrying a
certificate, which strict functions generate. The total allocation bound is summed
over callees and checked at compile time, callees in loops must have bound 0, and
recursion through strict functions is rejected as a cycle in constant evaluation.
Higher-order functions take `fip_strict::FipFn` parameters with declared bounds
(`param(g = K)`); arguments are certified closures from `fip_fn!(|x: T| ..)`, or
functions with a certificate from `fip_fn!(f)` (also `a::f`, `f::<T>`,
`<Type<..>>::m`, `Type::<..>::m`, `<Type as Trait>::m`): the bound is the function's own certificate,
no `unsafe` is written, and strict bodies may use it. With an expected type
`Certified<N, fn(..) -> ..>` the value is a certified function pointer.
`fip_fn!(bound <= K, ..)` fails to compile (also under `cargo check`) when the
computed bound exceeds `K`. Opt-in per use, `fip_fn!(prelint, N, |x: T| ..)` skips
the token scan of the closure (method calls, `use` aliases and inferred types
allowed) and leaves the declared `N` to `fip-prelint`, which checks it at the
construction (allocations, frees, recursion; in a generic function a call left
generic, such as `T::make`, is ⊤; the crate summary counts these constructions
apart from the roots: "N roots, P passed, K `fip_fn!` constructions, Q passed"); it
compiles only in a checking
`cargo fip-prelint` run, never in a plain build
(`docs/decisions/2026-11-03-fip-fn-driver-mode.md`). `fip_strict::Stateless(f)` lifts
a one-argument callable to a state-passing step for the `_st` combinators,
`fip_strict::Compose(f, g)` calls `g(f(args))` (any arity of `f`) and
`fip_strict::Then(f, g)` runs two state-passing steps, each with the summed bound;
all are also specified under Verus. `fip_fn!(panic_macros = false, ..)` certifies a
closure scanned with `panic_macros = false` (or a function whose certificate says
so) as `FipBound::NO_PANIC_MACROS`, and a strict callee declared `panic_macros =
false` rejects `param(..)` arguments without it.

```rust
#[fip(strict = true, param(keep = 0))]
fn count_kept<F: for<'a> FipFn<(&'a u8,), Output = bool>>(xs: &[u8], keep: F) -> usize { /* … */ }

count_kept(&xs, fip_fn!(|v: &u8| *v > 1));
count_kept(&xs, fip_fn!(is_big)); // `#[fip(strict = true)] fn is_big(v: &u8) -> bool`
```

Certificates are claims, so hand-writing one requires `unsafe` (`Cert::assume`,
`Certified::assume`, their `assume_no_panic_macros` forms, `unsafe impl FipBound`; a
strict trait contract needs an `unsafe trait`, `#[fip_extern]` an `unsafe extern`
block); in a `#![forbid(unsafe_code)]` crate it is impossible while generated
certificates still compile. Callers read a certificate as
`Cert::allocs_for(cert, "f")`, so a look-alike type with an `allocs_for` method (no
`unsafe` needed) does not compile as one. `fip_testkit::certs::hand_written` lists
every hand-written one. No certificate is made without `unsafe` (the former
`fip_strict::certs` for `fip-core` and `fip-alloc` were replaced by generated ones in
phase 5; a test pins that none is left). Certificates carry the function's name and strict
callers check it at compile time, so aliasing another function's certificate fails
(a same-named function's certificate imported from another module still passes).

**`strict` and `total`** (decision `2026-11-06-redesign-verus-allocates`, section 7).
`#[fip(strict)]` is `#[fip(strict = true)]`; under Verus it also *generates the
Verus contract* from the one declaration: `requires(..)` becomes the Verus
`requires`, the declared bound `N` becomes `allocates N`, merged into the hand-written
`verus_spec` (which keeps `ensures`); a hand-written `requires`, `allocates` or (for
`total`) `no_unwind` next to the generated one is a compile error, so the number of the
plain certificate is the number Verus proves. `#[fip(total)]` is the strictest grade:
`strict`, bound 0, `panic_macros = false`, and under Verus `no_unwind` and the fork's
`#[verifier::fip(strict)]` (no free on a normal return, constant stack; plain
`#[verifier::fip]` before the fork `c716c2bfd`); `fip-prelint` discharges a `total`
mark only if the crate's Verus sidecar lists the function with `allocates 0` (a
sidecar is used only from a `--no-cheating -V alloc-check` run of the pinned fork) and
the driver's own free, recursion and panic checks pass, else ⊤ with the reason (a loop
without a listed proof is named: its termination is unchecked).

| property of `total` | Verus build | plain build / `fip-prelint` |
|---|---|---|
| no allocation | generated `allocates 0` | token scan (bound 0); MIR allocation analysis |
| no free (F2) | generated `#[verifier::fip(strict)]` (functions without callbacks) | MIR free analysis |
| bounded stack | generated `#[verifier::fip(strict)]`: callees strict (also across checked crates) or std calls the fork knows drop nothing, recursion only through `become`; and recursion needs `decreases`, which the surface gate forbids | `#[fip]` direct recursion; MIR recursion check; `--stack` per build |
| termination | every loop needs `decreases` | ⊤ unless the sidecar lists the function |
| no panic / unwind | generated `no_unwind` | `panic_macros = false`; MIR panic analysis |

`fip_core::replace`, `fip_core::swap` (and its helper `swap_lt`) and `fip_alloc::refill`
are `total` (`swap`/`swap_lt` since the fork `1b27c1101`, whose slice views carry
`deallocates_when(0, false)`; on `6f6975af2` the fork's `#[verifier::fip]` rejected their
call of `split_at_mut`, measured 2026-11-09); the combinators stay `strict` with callback-relative bounds
written by hand (Verus cannot state that a closure call does not unwind, measured on
the fork; `total` with callable parameters is a compile error).

Generated strict code names `::fip_strict` by default. A crate that gets the macros
through a facade crate (which re-exports `fip_macros::{fip, fbip, fip_fn, fip_impl}`
and `fip_strict`) passes the path instead of depending on `fip-strict` directly:

```rust
#[fip(strict = true, crate = my_facade::fip_strict)]
fn f(a: &mut u8, b: &mut u8) { ::core::mem::swap(a, b) }

#[fip_impl(crate = my_facade::fip_strict)] // inherited by the strict methods
impl Slot { /* … */ }

let g = fip_fn!(crate = my_facade::fip_strict, |x: u8| x + 1);
```

Without the argument at every use: the facade wraps `fip_fn!` in a `macro_rules!`
that fills in `$crate::fip_strict`, and re-exports `Cert`, `Certified` and `FipBound`
at its root so that consumers can write `extern crate my_facade as fip_strict;` once
(`macro_rules!` attributes, which could wrap `#[fip]`, are unstable in rustc 1.99.1).
`crates/fip-macros/tests/facade.rs` builds both setups with a consumer that depends
on the facade only; details in the `fip-macros` crate documentation.

Methods: `#[fip_impl]` on an `impl` block certifies its strict methods, including
generic impls and trait impls (`__fip_strict_<Type>__<m>`); callers use `Type::m`,
`Self::m` or `<Type as Tr>::m`. `panic_macros = false` additionally rejects the
panicking macros.

Strict contracts on trait methods are declared as `#[fip(strict = true)]`
(or `#[fip(N, strict = true)]`) under `#[fip_trait]` on the trait, which must be an
`unsafe trait`: each implementation is an `unsafe impl` (the user's claim) or is
written under `#[fip_impl(contract)]`, which checks it against every contract of the
trait and emits the `unsafe` itself. `#[fip_trait]`
emits the contract certificates `<dyn Trait>::__fip_strict_<m>` and
`__fip_strict_<Trait>__<m>`, which strict callers use for `x.m()`, `Trait::m(x)` and
`<dyn Trait>::m(x)`. Strict implementations under `#[fip_impl]` are checked against
the contract at compile time (impl certificate bound ≤ contract bound, and
`panic_macros = false` in the contract requires it in the implementation; every
certificate is of kind `fip`) and by the driver always; a non-strict implementation
(`#[fbip]`, plain `#[fip]`, none) has no certificate and is checked by the driver only.
Foreign functions: `#[fip_extern]` on an `unsafe extern` block (required, also in
edition 2021) certifies foreign functions with `#[fip_cert(evidence = "..")]` (or
`#[fip(evidence = "..")]`), emitting module-level certificates for strict callers and
driver marks for `fip-prelint` (a function certified to free, `frees = true` or
`kind = "fbip"`, gets the driver mark only), or excludes them with `#[fip_exclude]`
(user assumption, contributing no events). Every foreign function reachable from a FIP root must be certified or
excluded; unannotated calls are rejected with a specific error. `fip-prelint` matches
these marks by **link symbol** (`#[link_name]`, else the name) and ABI, so a
declaration in your crate also covers the same symbol declared in `std`, `libc` or
any other dependency (each such match is listed in the crate summary); marks on one
symbol must agree everywhere (certified and excluded, or two certificates with
different properties, are errors), and a declaration with another ABI is not
covered (an error). Strict callers use the certificate's own path, or map the
dependency's path to it with `#[fip(strict = true, ffi(dep::sym = local::sym))]`
(`fip-prelint` checks that both declarations share symbol and ABI; without it the
mapping is trusted, only the certificate's name is checked).
The `core` table is **audited** (at rustc 1.97.1, 1.99.1, 1.100.0-beta.10 and, through identical `library/` sources, 1.100.0; a test fails on any
other compiler) rather than machine-proved, except that "no allocation" follows from
`core` having no allocator; the installed `vstd` specifies 7 of its 11 entries.
Bare panicking macros are emitted as `::core::assert!` etc. (a local macro of that
name is not what runs), and a bare ghost-code macro (`proof!`) is emitted as
`const { proof! {} };`, its contents dropped.
Not covered by the attribute macro (measured, see `TODOs/strict-open-items.md`):
implicit calls (`Drop`, operators, `Deref`, `Index`), panics other than the macros,
generic instantiations under `cargo check`, `use` aliases, and a local type named like
a std heap type (`struct Vec` with an allocating `new`). `fip-prelint` (below)
catches implicit calls and `use` aliases on MIR (`crates/fip-macros/tests/strict_gaps.rs`
with `tools/fip-prelint/tests/selfcheck.expected` pins the implicit-call cases), and it
checks every call site's argument against the callee's declared `param(g = K)` bound
under `cargo check`, also in callers that are not `#[fip]` (fixture
`tools/fip-prelint/tests/fixtures/param_bounds`); a full build checks the same through
a post-monomorphisation assertion, and the token-level `fip_testkit::summaries`
(`ArgumentExceedsDeclared`) too. `assert_fip!` catches implicit calls at run time. See
`docs/decisions/2026-11-01-strict-core-table.md`.

## `fip-prelint`

A rustc driver (`tools/fip-prelint`, its own cargo project outside the workspace,
toolchain `1.100.0` with `rustc-dev`) that checks `#[fip]`, `#[fip(N)]` and `#[fbip]`
functions on MIR, after type checking. It sees what the token-level tools cannot:
implicit `Drop`, operator and trait-impl calls resolved to their implementations,
generic instances, `use` aliases. `cargo fip-prelint` runs `cargo check` with the
driver as `RUSTC_WRAPPER`: workspace members are analysed; dependencies whose source
declares `fip::export` (e.g. portable-fip crates used as git or path dependencies by
another project) are compiled with the driver's flags so their MIR is usable; all other
crates are compiled by the real rustc and stay ⊤.

- Roots come from `#[cfg_attr(fip_prelint, fip::mark(..))]`, which `fip-macros` emits
  only when expanded inside the driver, so plain builds are unchanged.
- A crate opts in to having its MIR used downstream with
  `#![cfg_attr(fip_prelint, fip::export)]` (`fip-core`, `fip-alloc`, `fip-strict`,
  `fip-arch` do). Other crates' functions are ⊤, reported, never passed. The driver
  reads the attribute from the crate root as rustc parses it (also inside other or
  nested `cfg_attr`; never from comments or strings); an attribute generated by a
  macro is not seen.
- Allocation is detected at the allocator entry points (`__rust_alloc*`,
  `__rust_realloc`, `__rust_dealloc` on rustc 1.99.1 and 1.100.0), at the methods of
  `GlobalAlloc`/`Allocator` implementations, at foreign C allocation functions
  (`malloc`, `calloc`, `free`, `realloc`, ..), and at functions declared
  `#[cfg_attr(fip_prelint, fip::alloc_source)]` (`n = N` per call) or
  `fip::free_source` (`n = N` deallocations per call; also on trait method
  declarations and foreign functions). A
  source is opaque: a call counts at the call site and its body is not analysed.
  **Deallocation bound** (2026-11-20, an extension: FP²'s `fbip` bounds allocation
  only): `#[fbip(frees = M)]` (`fip::mark(kind = "fbip", frees = M)`) allows at most
  `M` deallocations per call. The count is finite through calls of free sources, of
  an allocator's `deallocate`/`realloc`-like methods (one each: dropping a `Box` is 1)
  and through a literal `deallocates` bound Verus proved (taken as `allocates` is);
  it is `∞` in loops and recursion, through std summaries, imported summaries,
  certificates and contracts that only say "may free", and through calls of
  parameters. The macro checks nothing about `frees`; the driver does.
  An exported crate that hands out memory from its own pools must mark them; an
  unmarked pool is ordinary code. `#[fip]` on a source is an error. Intrinsics come
  from a table in `fip_lint_rules::mir`.
- Dropping a trait object (`Box<dyn Trait>`, `drop_in_place` of a `*mut dyn Trait`,
  also inside another type's drop glue) runs the drop glue of a type the driver does
  not know: it is unresolved (`cannot check`), as a dynamic call of a method without a
  contract is. Borrowing one (`&dyn Trait`) drops nothing.
- A call of a function declaring `param(g = K)` is an error when the argument passed
  for `g` (closure, `fip_fn!` value, named function; computed from its MIR) may
  allocate more than `K` times per call, or is ⊤. This is checked in roots, in what
  they reach, and in every other local function and closure. `g` may also be a
  function pointer or a `&dyn Fn*`/`&dyn FipFn`: a call through it then counts `K`
  (and what the function's own mark allows), and the argument must be a function
  reified, or a value unsized, from one origin in the caller's body (else ⊤ at the
  call site), and must not free or recurse under a `fip` callee.
- Function pointers and `dyn` values whose origin is one function or one concrete type
  on every path of the function are resolved to it. `#[fip]`, `#[fip(N)]` or
  `#[fbip]` on a trait method declaration (`fn area(&self) -> u32;`, or one with a
  default body; the emitted `fip::mark` may also be written by hand) is a contract: a
  `dyn` call or generic call (`self.m()`, `<S: Trait>`) of the method costs it, and
  every implementation is checked against it as a root in the crate that contains it
  (also in a dependency that declares `fip::export`), without any `fip::requires(..)`
  (a `dyn` or generic call checks none); an
  implementation's own mark that is weaker than the contract is an error; an
  implementation in a crate without `fip::export` is ⊤ in every analysed crate that
  sees it. `param(g = K)` on a declaration (without `strict = true`) bounds a
  function-pointer or callable trait-object parameter `g`: every implementation is
  checked with `g` costing `K` (named by position in the implementation; its own
  tighter `param` is an error), and every call through the contract, dynamic or on a
  type parameter, checks its argument against `K`. `requires(..)` is rejected on a
  declaration by `fip-macros` and the driver; `strict = true` on a declaration is
  supported under `#[fip_trait]`, without `param(..)`.
- `#[fip(.., requires(i < j, j < xs.len()))]` (emitted as
  `#[cfg_attr(fip_prelint, fip::requires(..))]`, also written directly) declares a
  precondition over integer parameters, slice lengths `xs.len()` and access paths
  below a parameter of type `&T` with `T: Freeze` (fields and elements at a literal
  index: `w.n`, `xs[0]`, `w.b.len()`): the function is checked under it as a root,
  and every analysed call site must establish it (else a panic path there); taking
  such a function as a function value is a panic path. It is written by hand next to a Verus `requires`
  and compared with it where `#[fip]` sees the `verus_spec`.
- Verus as an oracle for panic freedom (opt-in per package): with
  `[package.metadata.fip-prelint] verus-sidecar = "verus-verified.txt"` the driver
  reads the committed sidecar that `cargo fip-prelint --verus-sidecar -- <verus ..>`
  writes from a `--no-cheating` Verus run of the whole crate (the exec functions in
  Verus's VIR log with a body and without `external_body`, with their file, the line
  and SHA-256 of their item text and the SHA-256 of every source file of the run;
  stamped with the Verus version and commit and the Z3 version). Impl methods are
  matched by path without the impl number, file and line (Verus's `impl&%N` and
  rustc's `{impl#N}` number differently where `cfg(verus_keep_ghost)` adds or removes
  impl blocks); methods inside `#[cfg(verus_keep_ghost)]` or generated by a macro are
  not listed, and an impl block whose header mentions `verus_keep_ghost` is not used.
  Verus compiles without `--cfg fip_prelint`, the features and `cfg(test)`: an item
  whose text holds a `cfg` other than the Verus-only attribute forms is not listed, nor
  is a caller verified against such a function's specification; a crate any of whose
  listed sources (also outside `src/`) tests any cfg but `verus_keep_ghost` and
  `feature`, reads the environment (`env!`, `option_env!`, `include*!`) or invokes a
  macro the scan cannot read (one of a dependency, `$m!`, a bare `cfg` token in a
  macro's arguments) gets no sidecar, and the run's target and features are
  stamped and must match the build; a source with the identifier `internal` in code
  (`verus::internal(..)`, the attributes Verus's own macros write for the verifier, in
  any spelling) gets no sidecar either. Sidecar format 7
  (format 5, redesign phase 4, plus each function's `deallocates` bound, whether it
  has `encapsulates`, and the run's edition): the run must name `--edition` (Verus's
  default is not cargo's; the driver uses a sidecar only for a crate compiled for the
  recorded edition, read for a dependency from its package's manifest; a sidecar of a
  run with `--import` names each imported crate with the hash of the sidecar it was
  imported with, and is used only while that crate's sidecar in the build is that one,
  usable, and the crate compiled for its edition) and must
  use `-V alloc-check` (stamped, required by the driver); a trait with an
  implementation or declaration under a cfg naming `verus_keep_ghost` (`fip-strict`'s
  twin `FipFn` impls) is recorded as `divergent`, and every function naming one of
  its methods is not listed, also in importing crates' runs (Verus assumes the trait's
  specification for implementations it never compiled); the driver also refuses the
  Verus results of a listed function for an instance that calls a trait method
  implemented by a function no sidecar lists (outside the standard library, `Fn*`
  exempt). Each entry records its proved `allocates` bound (`-`, a literal, a
  parameter-linear form or `opaque:<hash>`); a literal bound of a non-generic function
  without `requires` and without non-allocation-failure panic paths replaces the
  driver's count where that count is `∞` or open, a finite count above it is an error,
  and the crate summary counts the bounds taken; frees, panics, recursion and `⊤` stay
  the driver's.
  Every `--import` of the run needs the imported crate's committed sidecar (trusted
  stamp, `--no-cheating`, unchanged sources) and a VIR file a generator run exported.
  The fork audit (2026-11-09): a sidecar whose `flags` record anything but
  `--no-cheating -V alloc-check` (e.g. `--is-vstd`, which the generator refuses) is
  not used. **Trust boundary (allocators):** Verus can prove false facts about memory
  managed by an allocator whose methods touch its state (`Allocator` is stable since
  rustc 1.100), in the crate that uses it. So a sidecar whose listed sources
  implement `Allocator`, `GlobalAlloc` or an allocator marker trait is not used at all
  (neither panic facts nor `allocates` bounds), and an entry is not used for a
  function whose MIR uses an allocator other than `Global`/`System` (a type outside
  the standard library implementing one of those traits, a type parameter bounded by
  one, a trait object of one; any type parameter if such an implementation is
  blanket); the reason is reported. A `#[global_allocator]` is not covered (Verus
  models `Global` by its specification). portable-fip's own verified crates have no
  allocator implementation (surface gate). **Declared sources** (2026-11-19, rule of
  2026-11-20): Verus counts calls of allocator methods (one each, as the driver does)
  and a callee's clause, but does not know that a function declared `fip::alloc_source`
  allocates. The fork's declaration for an allocator with its own interface is
  `encapsulates alloc(a, d)`: callers are charged `a` allocations and `d`
  deallocations, the body is not checked against them. So no Verus bound is taken for
  a function that reaches a declared source unless a sidecar lists the source with
  `encapsulates alloc(a, d)`, `a` the literal `n` of `fip::alloc_source` and `d` the
  literal `n` of `fip::free_source` (0 without the attribute; for a source declared on
  a trait method: on the implementation). Other counts in the clause are an error on the source. A
  function with `encapsulates` that is not a declared source gives no bound, and none
  is taken through it: the driver analyses its body. The summary lists the bounds not
  taken.
  A body-local overflow, bounds or division check of a listed function is discharged
  when the stamp equals `tools/fip-prelint/verus-trusted.txt` and every hash matches;
  the crate summary counts these sites with the stamp. Callers that Verus did not
  check carry the callee's Verus `requires` as a panic path. Anything else (stale,
  missing, other Verus build) keeps the sites, with the reason. `just verify-strict`,
  `verify-core` and `verify-alloc` regenerate `crates/{fip-strict,fip-core,fip-alloc}/verus-verified.txt`
  (2, 10 and 1 functions listed; `fip_core::strict::*` name `FipFn` and are not
  listed since phase 4) and fail if one differs (`FIP_VERUS_BLESS=1` after
  review); the sidecars of path dependencies outside the workspace, and the current
  content of every source file a sidecar lists, are part of the analysis cache key;
  `cargo fip-prelint --no-verus` ignores sidecars.
- `cargo fip-prelint --stack [--release ..]` builds the workspace libraries with
  `-Zemit-stack-sizes` and reports, per root, "uses at most B bytes in this build
  (target, opt-level)" with the longest path, or ⊤ with the reason. The bound is read
  from the objects (frames from `.stack_sizes`, direct calls from relocations), each
  function mapped to its MIR instance (which must contain no indirect call); it holds
  for that build only.
- The shipped standard library has no MIR for functions that are neither generic nor
  `#[inline]` (`core::fmt::write`, `format_inner`, integer formatting). For those,
  the driver reads `tools/fip-prelint/std-summaries/<release>-<target>.txt`: summaries
  generated by `just prelint-std-summaries` (the driver's own analysis of a
  `-Zbuild-std` build with the release settings of the shipped std), with the calls
  they make through their parameters (the output written to, the formatting functions
  of the `fmt::Arguments`) left open and resolved at each call site. The file is
  committed and stamped with the rustc version and target; for any other compiler or
  target it is not used and such functions stay ⊤.

Design and measurements: `docs/decisions/2026-11-01-fip-prelint.md`,
`TODOs/fip-prelint.md`.

## Verification

Specifications are written in Verus's attribute syntax and are compiled only by the
`verus` driver (`cfg(verus_keep_ghost)`); plain builds do not see them. See
`docs/decisions/2026-10-31-verification-layout.md`.

```rust
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures *final(slot) == new, r == *old(slot),
))]
pub fn replace<T>(slot: &mut T, new: T) -> T { /* … */ }
```

`compact` is specified as: the slice is permuted (equal multisets), `keep` returned
`true` for every element before the returned length and `false` after it, and the
retained elements keep their original order.

**State-passing variants.** `map_in_place_st` and `compact_map_st` take
`Fn(S, T) -> (S, T)` / `Fn(S, T) -> (S, T, bool)` and thread the state `S` by value.
Their postconditions (`map_st_by_post`, `compact_map_st_by_post` in
`fip-core/src/spec.rs`, module `state`) contain a state trace `ss` with `ss[0] == s0`,
`ss[len]` the returned state, and `f`'s `ensures` relating `(ss[k], old[k])` to
`(ss[k + 1], new[k])` for every `k` (for `compact_map_st`: to `(ss[k + 1], ys[k],
ks[k])`, plus everything `compact_map` guarantees). There are no `FnMut` variants:
Verus 0.2026.10.18 rejects closures that capture a local mutably and, after a
`FnMut` call, proves the closure unchanged, so such a proof says nothing about the
state.

- **Named trace.** The postcondition names its witnesses with spec functions,
  `map_st_by_trace(old, new, f, s0, s)` and `compact_map_st_by_witnesses(..)`
  (defined with `choose`), so callers use them directly instead of choosing a trace.
  Not a ghost output: every attribute-mode `verus_spec(with ..)` (ghost inputs,
  `-> Ghost` outputs, `Tracked<&mut ..>` parameters) generates an `external_body`
  twin of the function, which `--no-cheating` rejects (measured on both Verus builds
  below).
- **State invariants.** `f` need not accept every state: the precondition
  (`map_st_by_ok`) also holds when the caller proves an invariant
  `map_st_by_inv(xs, f, s0, inv)`, where `inv(k, s)` means "state `s` before call `k`":
  it holds on `s0`, `f` accepts `xs[k]` with every state satisfying it before call `k`,
  and every call preserves it. The postcondition then gives `inv(k, ss[k])` along the
  trace. `verify/compose_state.rs` numbers a slice of any length below 990 with a step
  that requires the count below 1000 (invariant `c == 10 + k`); without the invariant
  the call is rejected.
- **Strict forms.** `fip_core::strict::*_st` have the same specifications with
  `FipFn::pre` / `post`. A verified caller passes a named function as a `FipFn` value
  (`fip_fn!(tick_checked)`, bounded by the function's generated certificate in the
  plain build, no `unsafe` at the call site), whose `pre` / `post` are the function's
  `requires` / `ensures`. Under Verus `fip_fn!` reads no certificate: a closure keeps
  its scanned bound `N`, `fip_fn!(bound <= K, path)` is `Certified<K, _>` in both
  builds, `fip_fn!(path)` is `Certified<0, _>` (`verify/fip_fn_types.rs` checks the
  types agree). Verus checks that number: `Certified<K, _>`'s `pre` requires
  `call_allocations(f, args) <= K`, so a verified caller of an allocating function
  writes `fip_fn!(bound <= K, path)` (`boxes_one` in `verify/fip_fn_types.rs`); without
  `bound` the call fails its precondition. A closure works too: `fip_fn!` keeps a
  `#[cfg_attr(verus_keep_ghost, verus_spec(r: T => requires .., ensures ..))]`
  attribute on it, and `pre` / `post` are its `requires` / `ensures`
  (`number_from_11_closure`).

Measured (`--no-cheating -V alloc-check`, Verus fork 0.2026.11.05.ca33b04, Z3 4.16.0,
2026-11-06, and the same counts on the forks 0.2026.11.08.6f6975a, 0.2026.11.09.1b27c11 and 0.2026.11.09.c716c2b, rustc
1.100.0-beta.10, 2026-11-09; on stripped sources with upstream 0.2026.11.02.8bf68ee:
23/58/1/3/4/13/4, and 6 for `verify/total.rs` (phase 5, 2026-11-09)):
`fip-strict` 23 (19 before the per-arity `Compose` impls, 5 instead of 1), `fip-core`
70 (58 before the 3 sum spec functions, 3 zero lemmas and the 6 `nonlinear_arith`
steps of the strict loops), `fip-alloc` 1, `verify/compose.rs` 3,
`verify/compose_strict.rs` 4, `verify/compose_state.rs` 13, `verify/alloc_callers.rs`
10, `verify/fip_fn_types.rs` 4, `verify/total.rs` 6 (phase 5; the counts of the other
files are unchanged by phase 5, measured 2026-11-09).

**Pre-verification → implementation → post-verification.** For `dedup_by` and
`compact_map` the postcondition was first written as a spec predicate
(`dedup_post`, `compact_map_post` in `fip-core/src/spec.rs`) and checked on concrete
inputs before any code existed: the intended answer satisfies it, and wrong answers
(keeping a duplicate, merging different elements; keeping a dropped element,
missing a kept one, returning an unmapped value) provably do not. Then the
function was implemented and verified against that predicate, and mutants of it
must fail.

`fip-strict` declares `FipBound`/`FipFn`/`Certified` twice, as plain Rust and inside
`verus!` with `pre`/`post` specs; `tests/verus_drift.rs` checks the two declarations
agree. Verifying `fip-core` therefore needs the exported `fip-strict` metadata (see
the `verify-core` recipe).

Requirements: the Verus fork with `allocates` (branch `fip`, the commit in
`tools/fip-prelint/verus-trusted.txt`) as `VERUS` (its Z3 is `VERUS_Z3_PATH`, else
the `z3` next to it; `just verus-pin` fails on any other build), Singular
(`VERUS_SINGULAR_PATH`, default `/usr/bin/Singular`), and for the strip gate upstream
Verus `0.2026.11.02` as `VERUS_UPSTREAM` (required by `just ci`; `just verify-upstream`
alone, or `just ci-gates`, prints `SKIPPED` without it). Pins and where they live: the justfile header.

## Gates

`just ci` runs all of them (`just ci-gates` without `FIP_PRELINT_REQUIRE_TARGETS=1`,
which turns a driver test skipped for a missing target, tool or host into a failure);
cargo runs with `--locked`:

| recipe | checks |
|---|---|
| `fmt-check`, `lint` | rustfmt; clippy with `all = deny`, `pedantic = warn`, `-D warnings` |
| `test` | unit, integration, doc tests (allocation tests run in parallel) |
| `msrv` | the same on rustc 1.100.0 (the workspace `rust-version`; since 2026-11-17 also the toolchain `rust-toolchain.toml` pins for every other gate, so this gate repeats `test` unless the pin moves ahead of the MSRV) |
| `nostd` | `x86_64-unknown-none` build of `fip-core`, `fip-alloc`, `fip-arch`, `fip-strict`, `fip-lint-rules` (only `core`/`alloc` exist there) |
| `cross` | `aarch64`, `riscv64gc` and `aarch64-apple-darwin` checks; `fip-arch`'s unit tests built for `aarch64`/`riscv64gc` musl (linked by `rust-lld`), which assembles the `asm!` templates |
| `arch-override` | `fip_cache_line` = 32/128 take effect; other values are rejected with the `build.rs` message |
| `verify` | `verus-pin` (`VERUS` is the pinned fork, Z3 and toolchain); `verify-flags` (every Verus run of the justfile uses `--no-cheating` and no standard-library crate flag, `verify/no_cheating_flags.py`; 4 mutated justfiles fail); Verus proofs (`--no-cheating -V alloc-check`) of `fip-strict`, `fip-core` (imports `fip-strict`), `fip-alloc`; `#[fip]` and strict composition with `verus_spec`; verified callers of the state-passing variants and of `fip-core`'s allocation bounds (`verify/compose_state.rs`, `verify/alloc_callers.rs`, imports `fip-core`), with `allocates 0`; `fip_fn!` types equal in the plain and the Verus build (`verify/fip_fn_types.rs`, 3 mutated annotations fail both builds, a closure calling a certified function is rejected under Verus); the Verus sidecars of verified bodies of `fip-strict`, `fip-core`, `fip-alloc` and of the driver's `verus_sidecar` fixture regenerated and equal to the committed ones, and the generator's refusals (no `--no-cheating`; an `external_body` function fails the run; an item with a Verus-only `cfg` is not listed; a crate testing `fip_prelint` gets no sidecar; an `--import` without the imported crate's committed sidecar, or of a VIR file no generator run exported; a run without `-V alloc-check`; callers of a trait with a plain-only implementation are not listed); the `verus_alloc` fixture's sidecar with its proved bounds; 38 Verus mutants (incl. one recursive and one loop without `decreases`), 14 wrong claims of verified callers and 2 allocations under `allocates 0`, 3 surface-gate mutants and 1 spec-drift mutant must fail, none on the resource limit; phase 5 (`strict`/`total` generate the Verus contract): `verify/total.rs` verifies, and its controls (a `total` caller of a callee that may unwind, an allocation behind a hand-written certificate, a free in a `total` function) and the mutant `refill-frees` are rejected by the generated `no_unwind`, `allocates 0` and `#[verifier::fip]`; the `verus_total` fixture's sidecar |
| `verify-upstream` | strip gate: `verify/strip_alloc.py` removes the allocation layer, upstream Verus `0.2026.11.02` (`VERUS_UPSTREAM`) verifies every crate and `verify/` file of the copy with `--no-cheating`, with `FIP_MACROS_UPSTREAM=1` (`fip-macros` then leaves out the fork-only `allocates` and `#[verifier::fip]` it generates for `strict`/`total`, never `requires` or `no_unwind`), and a control shows that without the switch upstream rejects the stripped `verify/total.rs`; `SKIPPED` without `VERUS_UPSTREAM` when run alone or in `ci-gates`; a failure in `ci` (`FIP_REQUIRE_UPSTREAM=1`) |
| `prelint` | rustfmt and clippy (`-D warnings`) on the driver; `fip-prelint` fixture workspaces (cross-crate export, implicit drop, operator impl, generics, closures, declared parameter bounds at call sites, allocation and free sources, drops through their glue, declared preconditions, function pointers, trait objects and trait method contracts, std summaries (and a stale one ignored), Verus sidecars (impl methods matched by location; stale, forged, foreign-stamped, missing, moved and differently configured ones not used; format 4 refused; trait calls into unverified implementations refused; proved allocation bounds taken, kept, exceeded and refused without `-V alloc-check`; `total` marks discharged only with a listed `allocates 0` proof and the driver's own free, recursion and panic checks, ⊤ with the reason otherwise, fixture `verus_total`), the soundness audit's probes (tail calls, `dyn` recursion under a contract, standard-library look-alikes, foreign `link_name`s), mode variables of the shell not inherited, bad attributes) a self-check of this workspace against `selfcheck.expected`, the same for every installed target (`targets.expected`), stack bounds of one fixture in two stated builds, and the rejected behaviour examples of `fip-macros` through the driver (mark-only mode); its `-Zbuild-std` runs fetch the standard library's crates.io dependencies into the cargo registry cache on a cold cache |
| `prelint-repin` | not in `ci`: `just prelint-repin <version>` runs the checks of a move to another rustc (driver build, probes, entry points, std summaries, driver tests) and lists the pins and tables to re-audit |
| `prelint-std-summaries` | not in `ci`: regenerates `tools/fip-prelint/std-summaries/<release>-<target>.txt` (`-Zbuild-std` of the seed crate, ~2 min); run after a repin or a seed change, and commit the result |
| `compile-fail-reasons` | each of the 151 `compile_fail` examples of `fip-macros` (106 of them in the strict-mode section) fails for its stated reason (`# // expect:`), not another error; every constructor spelling of `fip_lint_rules::callee::SPELLINGS` is classified as stated under `#[fip]` and strict mode (`verify/ctor_spellings.py`, 100 checks) |

## Usage notes

- Write `#[fip]` **above** `verus_spec`. Below it, the macro sees Verus's rewritten
  item and reports an error.
- `#[fip]` on a trait method declaration checks nothing in a plain build (the macro
  sees no implementation); the contract is enforced by `cargo fip-prelint`.
- `update`, `map_in_place`, `compact_map` and the `_st` variants take a `hole` value and
  return it: no `Default` bound, nothing is manufactured. A capability-like type never
  has to be minted as a placeholder.
- If a callable panics, slots and slices hold only valid values (the failing slot
  holds `hole`; `compact`/`dedup_by` leave a permutation); each function's `# Panics`
  section says what, measured in `fip-core/tests/panic_state.rs`. The proofs do not
  cover unwinding.
- `fip_testkit::install!()` once per test binary; the assertion macros panic if
  it is missing, so a missing allocator cannot give a vacuous pass.

## Scope notes

- A compaction whose predicate mutates elements through `&mut T` is provided as
  `compact_map`, which takes each element by value and returns `(value, keep)`:
  Verus cannot specify closures taking `&mut` arguments, and the by-value form is
  the FIP shape anyway.
- `dedup_by` takes a predicate rather than requiring `PartialEq`: `vstd` specifies
  `==` only for types with proved equality laws, while a closure keeps the function
  generic and fully specified.
- `CACHE_LINE` override: `RUSTFLAGS='--cfg fip_cache_line="128"'` (32, 64, 128).
- `fip-testkit` sees only the Rust global allocator.
- Limitations of `fip_testkit::callgraph` and `summaries` (remaining false negatives
  and false positives; the two lexer bugs are fixed) are tracked with reproducers in
  `TODOs/callgraph-limitations.md` and `TODOs/callgraph-fip-summaries.md`.

## Acknowledgements

Ideas, not code: FP² (ICFP 2023), Perceus (PLDI 2021), Frame-Limited Reuse
(ICFP 2022), Koka's `fip`/`fbip`. The scope of each guarantee is shaped by the
reviews of two earlier in-house FIP implementations.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
