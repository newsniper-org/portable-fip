<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `#[fip(strict = true)]`: certificates and the audited `core` table

**Status:** ACCEPTED, 2026-11-01. Amended 2026-10-31 (named certificates,
`#[fip_impl]`, `Certified`, Verus specs for `FipFn`, `panic_macros = false`,
audit at rustc 1.97.1). Amended 2026-11-01 (`crate = ..` path, certificates read
through the `Cert` type; non-allocating constructors of std heap types). Open items: `TODOs/strict-open-items.md`.

## Decision

A strict function may call only

1. functions in the `core` table below, named by a full path rooted at `core` or
   `std` (`core::mem::swap(..)`; `use` aliases are not recognised and are rejected), or
2. functions with a certificate: a `fip_strict::Cert` constant next to the function
   (or, for values called through `FipFn`, a `fip_strict::FipBound` impl):

   | callee as written | certificate read |
   |---|---|
   | `f(..)`, `a::f(..)` | `__fip_strict_f`, `a::__fip_strict_f` |
   | `Type::m(..)`, `a::Type::m(..)`, `<Type<..>>::m(..)`, `Self::m(..)` | `__fip_strict_Type__m` (module level) |
   | `<Type as Tr>::m(..)`, `<Self as Tr>::m(..)` | `__fip_strict_Type__Tr__m` (module level) |

`#[fip(strict = true)]`, `#[fip_impl]` (methods) and `fip_fn!` generate certificates
from a checked body. The certificate's bound is the body's own allocation sites plus
the callees' certificates, so the total is checked at compile time and recursion
through strict functions becomes a cycle in constant evaluation, which rustc rejects.

### Certificates name their function

`Cert::assume(name, allocs)`; generated certificates carry the part of their
identifier after `__fip_strict_` (`"f"`, `"Type__m"`, `"Type__Tr__m"`). A strict
caller reads a bound only through `Cert::allocs_for(cert, "<name>")`, which panics in
constant evaluation if the names differ. `use a::__fip_strict_g as __fip_strict_f;`
therefore fails where `f` is called (`compile_fail` example in `fip-macros`).
Still possible without `unsafe`: importing a **same-named** function's certificate
from another module (`use a::__fip_strict_f;` next to a local `fn f`). The token-level
caller cannot tell which `f` it calls; `fip_testkit::certs::hand_written` reports the
`__fip_strict_` identifier in source.

The read goes through the type (`Cert::allocs_for(cert, ..)`), not method syntax
(`cert.allocs_for(..)`, before 2026-11-01). Measured with method syntax: in a
`#![forbid(unsafe_code)]` crate, `const __fip_strict_two: Fake = Fake;` with
`impl Fake { const fn allocs_for(self, _: &str) -> u64 { 0 } }` was accepted as the
certificate of a function allocating twice, and its strict caller got a certificate
of bound 0 — no `unsafe` needed. With the typed read it is a type error
(`compile_fail` example "look-alike certificate type").

### The `fip_strict` path: `crate = ..`

Generated code names `Cert`, `FipBound` and `Certified`. Under the fixed path
`::fip_strict`, a crate using the macros through a facade crate (one that
re-exports `fip_macros::{fip, fbip, fip_fn, fip_impl}` and `pub use fip_strict;`)
still had to depend on `fip-strict` itself. Measured 2026-11-01 (rustc 1.99.1, a
facade and a consumer depending on the facade only, under `/tmp`): 5 errors
"cannot find `fip_strict` in the list of imported crates", one per strict function,
`#[fip_impl]` method and `fip_fn!`. A crate-root `use facade::fip_strict;` does not
help (same 5 errors): `::name` resolves only through the extern prelude.

Decision: an argument `crate = <path>` on `#[fip(.., strict = true, ..)]`,
`#[fip_impl(..)]` (inherited by the block's strict methods that set none) and
`fip_fn!(crate = <path>, |..| ..)`; a path, or the same path as a string literal
(serde's form). Default stays `::fip_strict`. Every emission uses it: the
certificate constant and its `Cert::assume`, the typed `Cert::allocs_for` reads of
callees, the `FipBound` assertions of `param(..)`, and `Certified` in `fip_fn!`.
The appended segments carry the span of the path's last token, so a wrong path is
reported at the argument (`compile_fail` examples: unresolved path, path without
the items, non-path, `crate` without `strict = true`). The `fip::mark(..)` of
`fip-prelint` names no path and is unchanged; the driver finds `Certified` calls on
MIR, not by path. `#[fip_impl]` now recognises strict methods under any attribute
path ending in `fip` (`#[my_facade::fip(..)]`), not only `fip` / `fip_macros::fip`.

Defaults without an argument at every use, evaluated:

| option | result |
|---|---|
| facade wraps `fip_fn!` in `macro_rules!` filling in `crate = $crate::fip_strict` | works (`$crate` resolves to the facade); adopted for `fip_fn!` |
| facade wraps the attributes in `macro_rules!` | not on stable: rustc 1.99.1 "`macro_rules!` attributes are unstable" (measured) |
| consumer writes `extern crate my_facade as fip_strict;` once; the facade re-exports `Cert`, `Certified`, `FipBound` at its root | works for all three macros with no argument: an `extern crate` item at the crate root enters the extern prelude, so `::fip_strict` names the facade; adopted |
| relative default path `fip_strict` (resolved through the caller's `use`) | rejected: changes the default, and any local item named `fip_strict` would capture it |
| env var / consumer build script / reading the consumer's `Cargo.toml` | rejected: a proc macro cannot see the dependency graph; these are per-consumer configuration anyway, need a TOML parser (no deps), and do not apply under the `verus` driver or plain `rustc` |

`crates/fip-macros/tests/facade.rs` builds a facade and consumers that depend on the
facade only (nested `cargo`, offline): with explicit `crate = ..` everywhere (plus
the `fip_fn!` wrapper), with the `extern crate` alias and no argument, and a
control with neither, which must fail with "could not find `fip_strict`".
`tests/strict_crate_path.rs` covers the argument forms in-crate.

Trust: the path selects which `Cert` type a strict function's own certificate has
and which type it accepts from callees. A crate can point it at a module of its
own with look-alike items, but the certificates made that way have that type, and a
caller under the real `fip_strict` path rejects them (type error).

### Methods: `#[fip_impl]`

An associated constant needs inferable type arguments (`Type::<T>::C` cannot be
written with `T` unknown) and a trait impl cannot add items, so certificates of
methods are emitted at module level, before the `impl` block, by `#[fip_impl]`. The
name identifies one method only if no other impl can define the same name for the
same type name, so `#[fip_impl]` rejects:

- bounds on the impl's parameters and `where` clauses (a bounded impl leaves other
  instantiations to other impls);
- self types that are not `Name<exactly the impl's parameters>` (`impl Foo<u8>`,
  `impl<T> Tr for T`, `&Foo`);
- generic traits (`impl Tr<u8> for Foo`), and `<Type as Tr<..>>::m` in callers.

A trait method is reached only through `<Type as Tr>::m`: `Type::m` resolves to an
inherent method of that name first, and its certificate name is the inherent one.
A strict method with a `self` receiver outside `#[fip_impl]`, and `Self::m` outside
it, are compile errors. Residual: a type with **defaulted** parameters
(`struct Foo<T = u8>`) written as `impl Foo` covers only the default; the macro
cannot see the definition. Trait default methods get no certificate.

### Certified closures: `fip_strict::Certified`

`fip_fn!(|x: T| ..)` expands to
`unsafe { ::fip_strict::Certified::<{ checks; bound }, _>::assume(closure) }`: the
bound is a const argument of the type, and `Certified::assume` is the `unsafe`
claim. No item is declared, so the expression is accepted inside Verus-verified
bodies (Verus rejects item statements there; measured). `FipFn` is implemented for
closure arities 0–4. A `fip_fn!(..)` argument inside a strict body is not scanned
by the outer function (`fip_fn!` checks it; its calls are bounded by the receiving
function's `param(..)`).

### Verus specifications of `FipFn`

Under the `verus` driver `fip-strict` declares `FipBound`, `FipFn` and `Certified`
inside `verus! { }`; `FipFn` gains `spec fn pre(&self, args)` and
`spec fn post(&self, args, out)`, and `call` requires `pre` / ensures `post`. For
`Certified`, `pre`/`post` are the closure's `requires`/`ensures`. Plain builds keep
the dependency-free declarations; `fip-strict/tests/verus_drift.rs` compares the
exec items of both. Probed before implementing (Verus 0.2026.10.18.7d82994): `unsafe
trait` with an associated const, spec fns in traits, HRTB bounds
(`for<'a> FipFn<(&'a T,)>`), and the generic wrapper all verify; item statements in
verified bodies do not.

## The `core` table is audited, not proved

"Proved beforehand" holds only partly, and per property:

| property | evidence for every entry | strength |
|---|---|---|
| no heap allocation | `core` has no allocator API (crate boundary) | by construction |
| no deallocation | signature and body: no value of a caller-chosen type is dropped | audited (rustc 1.97.1 and 1.99.1 `core` sources) |
| no call into user code | no closure / trait-object / user-trait parameter is invoked | audited (same) |
| no recursion | implementation read | audited (same) |
| functional behaviour | `vstd` specification | only where marked below |

Line references are into `library/core/src` of the `rust-src` component; `vstd`
references into the `vstd` of the installed Verus (`/opt/verus/vstd`, 0.2026.10.18.7d82994).
A `vstd` specification is an `assume_specification`: trusted, and it states
functional behaviour only, not "no deallocation".

| entry | rustc 1.99.1 | rustc 1.97.1 | `vstd` spec | notes |
|---|---|---|---|---|
| `mem::swap` | `mem/mod.rs:830-834`: `intrinsics::typed_swap_nonoverlapping(x, y)` | `mem/mod.rs:785-789`, identical | yes (`std_specs/core.rs:129`) | drops nothing |
| `mem::replace` | `mem/mod.rs:961-979`: `read_via_copy` + `write_via_move`; "Nothing is dropped and nothing here can panic" (`:967`) | `mem/mod.rs:916-934`, identical | no | returns the old value |
| `mem::size_of` | `mem/mod.rs:375-384`: `<T as SizedTypeProperties>::SIZE` | `mem/mod.rs:373-375`, same body (1.99.1 adds a comment) | yes (`layout.rs:77`) | compile-time constant |
| `mem::align_of` | `mem/mod.rs:543-545`: `<T as SizedTypeProperties>::ALIGN` | `mem/mod.rs:528-530`, identical | yes (`layout.rs:85`) | compile-time constant |
| `hint::black_box` | `hint.rs:490-492`: `intrinsics::black_box(dummy)` | `hint.rs:490-492`, identical | no | returns its argument |
| `convert::identity` | `convert/mod.rs:106-108`: `x` | `convert/mod.rs:105-107`, identical | no | returns its argument |
| `slice::len` | `slice/mod.rs:116-118`: `ptr::metadata(self)` | same lines, identical | yes (`slice.rs:83`) | |
| `slice::is_empty` | `slice/mod.rs:136-138`: `self.len() == 0` | same lines, identical | yes (`slice.rs:95`) | |
| `slice::swap` | `slice/mod.rs:908-916`: bounds checks `&self[a]`, `&self[b]`, then `swap_unchecked` (`:947-…`: `ptr::swap(ptr.add(a), ptr.add(b))`) | `slice/mod.rs:906-918`: `&raw mut self[a]`, `&raw mut self[b]`, `ptr::swap(pa, pb)`; `ptr/mod.rs:1316-…` copies through a `MaybeUninit` | no | **differs** between the versions; both copy bytes, drop nothing, call no user code, may panic on an index |
| `slice::split_at` | `slice/mod.rs:1961-1966`: `split_at_checked`, `panic!("mid > len")` | `slice/mod.rs:1953-1958`, identical (`split_at_checked` `:2154-2162`, `split_at_unchecked` `:2039-2055`, identical) | yes (`std_specs/slice.rs:539`) | may panic |
| `slice::split_at_mut` | `slice/mod.rs:1995-2000` (`split_at_mut_checked` `:2201-2209`, `split_at_mut_unchecked` `:2101-2121`) | `slice/mod.rs:1987-1992` (`:2193-2201`, `:2093-2113`), identical | yes (`std_specs/slice.rs:549`) | may panic |

Excluded on purpose: `mem::take` (calls `Default::default`, user code),
`mem::drop` (runs drop glue, may free), `cmp::min`/`max` (call `Ord`, user code),
anything taking a closure.

The audit is tied to a toolchain. `fip_lint_rules::CORE_TABLE_AUDITED_AT` lists the
audited versions (`1.97.1`, `1.99.1`), and `fip-macros/tests/strict_toolchain.rs`
fails on any other compiling rustc (`fip-macros/build.rs` records it; measured to
fail on 1.96.0). When the toolchain changes, re-read the implementations above,
update the line references, and add the version.

## Non-allocating constructors of std heap types

**Added 2026-11-01.** The token rule "`Type::ctor` with `Type` in `HEAP_TYPES` and
`ctor` in `HEAP_CONSTRUCTORS` is an allocation site" rejected constructors that never
allocate: `#[fip] fn f(v: &mut Vec<u8>) -> Vec<u8> { core::mem::replace(v, Vec::new()) }`
did not compile (measured before the change: the 18 functions of
`fip-macros/tests/non_allocating_ctors.rs` gave 19 "allocation site" errors).
`fip_lint_rules::NON_ALLOCATING_CONSTRUCTORS` lists the `(type, constructor)` pairs
that are not allocation sites; `#[fip]` (base scan), strict mode and
`fip_testkit::summaries` read it through `is_heap_constructor` /
`is_non_allocating_constructor`.

Strict mode accepts the listed constructors **without a certificate, with bound 0**.
They meet the `core` table's rules: no allocation (below), no deallocation (each
builds a value from nothing and drops none), no call into user code (no method of the
element type or of a caller-chosen trait is invoked; `BinaryHeap::new` is in
`impl<T> BinaryHeap<T>`), no recursion. Unlike the `core` table they are recognised
by the type's **last path segment** (`Vec::new`, `std::vec::Vec::new`,
`alloc::vec::Vec::new`), as every `HEAP_TYPES` constructor already was: a user type
named `Vec` with an allocating `new` would be taken for the std one by the macro
(`fip-prelint` resolves the call on MIR and is not fooled).

Audit, per entry: every constructor is a `const fn` building an empty value;
`RawVec::new` (`raw_vec/mod.rs:103-105` → `new_in` `:199-203` →
`RawVecInner::new_in`) stores a dangling, well-aligned pointer with capacity 0.
Paths are under `library/alloc/src` of the `rust-src` component.

| entry | rustc 1.99.1 | rustc 1.97.1 |
|---|---|---|
| `Vec::new` | `vec/mod.rs:461-463`: `Vec { buf: RawVec::new(), len: 0 }` | `vec/mod.rs:463-465`, identical |
| `Vec::default` | `vec/mod.rs:4366-4372`: `Vec::new()` (`const impl`) | `vec/mod.rs:4293-4299` (`impl const`), same body |
| `String::new` | `string.rs:446-448`: `String { vec: Vec::new() }` | same lines, identical |
| `String::default` | `string.rs:2737-2742`: `String::new()` | `string.rs:2713-2718`, same body |
| `VecDeque::new` | `collections/vec_deque/mod.rs:826-829`: `{ head: WrappedIndex::zero(), len: 0, buf: RawVec::new() }` | `:828-831`, identical |
| `VecDeque::default` | `collections/vec_deque/mod.rs:162-167`: `VecDeque::new()` | same lines, identical |
| `BTreeMap::new` | `collections/btree/map.rs:651-653`: `{ root: None, length: 0, alloc: ManuallyDrop::new(Global), .. }` | same lines, identical |
| `BTreeMap::default` | `collections/btree/map.rs:2598-2603`: `BTreeMap::new()` | `:2597-2601`, same body |
| `BTreeSet::new` | `collections/btree/set.rs:344-346`: `BTreeSet { map: BTreeMap::new() }` | same lines, identical |
| `BTreeSet::default` | `collections/btree/set.rs:1640-1645`: `BTreeSet::new()` | same lines, identical |
| `LinkedList::new` | `collections/linked_list.rs:448-450`: `{ head: None, tail: None, len: 0, .. }` | `:447-449`, identical |
| `LinkedList::default` | `collections/linked_list.rs:426-432`: `Self::new()` | `:425-431`, identical |
| `BinaryHeap::new` | `collections/binary_heap/mod.rs:514-516`: `BinaryHeap { data: vec![] }`; `vec![]` is `$crate::vec::Vec::new()` (`macros.rs:43-46`) | same lines (`macros.rs:42-45`), identical |
| `BinaryHeap::default` | `collections/binary_heap/mod.rs:469-475`: `BinaryHeap::new()` | same lines, identical |

Measured: `fip-macros/tests/non_allocating_ctors.rs` runs each entry under the
counting allocator (0 allocations, 0 reallocations, 0 frees, also when the empty
values are dropped), on rustc 1.99.1 and 1.97.1; a test pins that it measures
exactly the table. `fip-prelint` agrees: its self-check reports the 18 roots of that
test crate (15 `#[fip]`, 3 strict) as passed with 0 errors; its dump shows it read
each constructor's MIR body and found no allocation entry point.

Not listed, on purpose:

- `HashMap::new` / `HashSet::new` (`std/src/collections/hash/map.rs:269-271`,
  `hash/set.rs:149-151`: `Default::default()` → `HashMap::with_hasher(Default::default())`,
  `map.rs:1488-1496`): `RandomState::new` (`std/src/hash/random.rs:55-76`) reads a
  lazily initialised `thread_local!` filled by `hashmap_random_keys()` (OS code). On
  targets without native thread-locals `std` uses the `os` implementation
  (`std/src/sys/thread_local/mod.rs:36-57`), which stores each thread's value in a
  `System.alloc` allocation (`sys/thread_local/os.rs:99-110`), invisible to a counting
  global allocator. Not allocation-free on every target, so not listed.
- `HashMap::default` / `HashSet::default`: call the hasher's `Default` (user code).
- `with_capacity` (also `with_capacity(0)`), `from`, `from_iter`: argument-dependent.
- every `Box` / `Rc` / `Arc` constructor, incl. `Box::default`
  (`alloc/src/boxed.rs:2008-2016`: `Box::new_uninit()`), `Rc::default`
  (`rc.rs:2540`), `Arc::default` (`sync.rs:3780`).

The audit is tied to a toolchain like the `core` table:
`fip_lint_rules::NON_ALLOCATING_CONSTRUCTORS_AUDITED_AT` (`1.97.1`, `1.99.1`), and
`fip-macros/tests/strict_toolchain.rs` fails on any other compiling rustc (measured
on 1.96.0: both toolchain tests fail).

## Hand-written certificates

A certificate is a claim. Writing one by hand needs `unsafe`
(`Cert::assume` and `Certified::assume` are `unsafe fn`s, `FipBound` an
`unsafe trait`):

- in a crate with `#![forbid(unsafe_code)]` it is impossible, while macro output still
  compiles (rustc does not apply `unsafe_code` to proc-macro output; measured
  2026-11-01 with a probe crate: generated `unsafe impl` accepted, hand-written one
  rejected; `compile_fail` examples for `Cert::assume`, `Certified::assume` and
  `unsafe impl FipBound`);
- elsewhere it is visible, and `fip_testkit::certs::hand_written` lists every
  occurrence (`Cert::assume` — which also matches `Certified::assume` —,
  `unsafe impl … FipBound`, and any `__fip_strict_` identifier in source).

The hand-written certificates in this repository live in `fip_strict::certs` and are
re-exported by `fip-core` and `fip-alloc` next to the functions, so those crates keep
`#![forbid(unsafe_code)]`. Being inside the crate that defines `Cert`, they are built
without `Cert::assume`; that module is the only place where this is possible, and a
test pins its exact contents, including that each names its function (plus the
re-exports in each crate):

| for | certificate (name) | justification |
|---|---|---|
| `fip_core::swap`, `fip_core::replace` | `__fip_strict_swap` (`"swap"`), `__fip_strict_replace` (`"replace"`) | `fip-core` links no `alloc`; drops nothing; calls no user code; Verus rejects recursion |
| `fip_alloc::refill` | `__fip_strict_refill` (`"refill"`) | body is `core::mem::swap` only; moves the `Box`; allocation-free behaviour measured |

`fip_core::strict::*` and the internal `swap_lt` carry generated certificates
(`#[fip(strict = true)]` in plain builds).

## What strict does not cover

Measured in `fip-macros/tests/strict_gaps.rs`; each is accepted with bound 0:

- **Implicit calls** (INHERENT for a token-level macro): `Drop` of locals (a strict
  function dropping its `Box` argument frees once), overloaded operators (`+` on a
  type whose `Add` allocates allocates once), `Deref`, `Index` on user types.
  `fip_testkit::assert_fip!` fails on both measured cases; closing the gap
  statically needs type information (a rustc driver), which is not dependency-free.
- **Panic paths** (MITIGATED): `panic_macros = false` rejects the panicking macros.
  A panicking strict function allocates on the `std` panic path (measured). Panics
  from indexing, overflow, division and callees remain.
- **Generic parameters** (INHERENT on stable): `FipFn` arguments are checked after
  monomorphisation. Measured with rustc 1.99.1: `--emit=metadata` (`cargo check`)
  accepts an argument exceeding its declared bound; a full build rejects it. A trait
  bound `ALLOCS <= K` needs `generic_const_exprs` (unstable).
- **`use` aliases** of table functions are rejected by design (the macro does not
  resolve names).

## What would reopen this

- A `vstd` (or other machine-checked) specification for the remaining table entries
  covering "no deallocation, no user code", which would turn audit into proof.
- rustc applying `unsafe_code` to proc-macro output (the forbid-crate story would
  need a different marker).
- Stable const-generic expressions (would let `Certified<N, _>: AtMost<K>` be checked
  by `cargo check`).
- Verus supporting item statements in verified bodies (not needed any more by
  `fip_fn!`, but by hand-written `FipBound` markers).
