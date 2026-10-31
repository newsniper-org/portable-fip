<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# TODO: limitations of `fip_testkit::callgraph`

**Status:** items 1–3 and 6–10 FIXED, items 4 and 5 PARTLY FIXED (the remaining parts
are inherent), 2026-10-31. **Recorded:** 2026-10-31, against commit `43a671b`.
**Component:** `crates/fip-testkit/src/callgraph.rs` (`fip_cycles`, `fip_cycles_in`,
`fip_cycles_multi`, `fip_cycles_in_crates`), front end in
`crates/fip-testkit/src/srcmodel/`.

## Context

`fip_cycles` lexes the `.rs` files under one directory (`fip_cycles_multi`: several
crates), builds a call graph and reports every cycle reachable from a function marked
`#[fip]` / `#[fip(N)]`. It covers what `#[fip]` cannot see on its own: recursion
through other functions.

It is a **check, not a proof**. It gives no stack bound for unverified code. The
proved bound exists only for crates verified with Verus (see
`docs/decisions/2026-10-31-stack-bound.md`). Each item below either let a real cycle
through (**false negative**), reported a cycle that does not exist (**false
positive**), or was a lexer **bug**.

The "measured" results before the fixes were obtained on 2026-10-31 by calling
`fip_cycles_in` on the snippet shown (probe crate `/tmp/cgprobe`). The results after
the fixes are the unit tests in `callgraph.rs` named per item (`cargo test -p
fip-testkit`, all passing).

Follow-up design built on this checker (interprocedural `#[fip(N)]` allocation
summaries, implemented as `fip_testkit::summaries`): `TODOs/callgraph-fip-summaries.md`.

## How the graph is built now

The front end (`srcmodel`) replaced the name-only graph:

- tokens carry file and line; literals are tokens (needed for `#[path]`, `include!`,
  `fip(N)`);
- `include!("..")` is spliced at the token level, relative to the including file;
- the module tree comes from `mod` declarations (`#[path]` honoured, inline `mod m {}`,
  `mod.rs`/`lib.rs`/non-mod-rs rules); a file no `mod` declares is a crate root of its
  own (as `tests/*.rs` are);
- functions are keyed by crate, module path and `impl`/`trait` owner; closures are
  nodes of their own (reached from the function that contains them, folded into it in
  reported cycles);
- calls are resolved by path (`crate::`, `self::`, `super::`, local modules, `use`
  imports, aliases, globs and `pub use` re-exports, `Self::`, `Type::`, other scanned
  crates by name); only a path that cannot be resolved falls back to every function of
  that name (in the unit, then the crate).

## Summary

| # | item | kind | before | now | test(s) |
|---|---|---|---|---|---|
| 1 | `#[fip]` applied through `cfg_attr` | false negative | `[]` | **FIXED**: `[["a", "b", "a"]]` | `fip_through_cfg_attr_is_a_root`, `cfg_attr_without_fip_is_not_a_root` |
| 2 | calls produced by a macro's expansion | false negative | `[]` | **FIXED** for `macro_rules!` in the scanned sources: `[["a", "b", "a"]]`; macros from elsewhere remain invisible | `calls_in_local_macro_bodies_are_edges`, `nested_and_recursive_macros_terminate`, `macro_metavariables_are_not_calls` |
| 3 | `include!`d source files, `#[path]` modules | false negative | `[]` | **FIXED**: `[["a", "b", "a"]]` | `include_is_spliced_relative_to_the_including_file`, `nested_and_item_position_includes`, `include_and_path_modules_are_read_from_disk` |
| 4 | indirect calls whose target is not named in the caller | false negative | `[]` | **PARTLY FIXED**: `[["a", "c", "b", "a"], ["b", "c", "b"]]`; pointers from outside the scanned sources and indirect calls in unmarked functions remain (inherent / by design) | `call_through_expression_reaches_functions_used_as_values`, `call_through_local_or_parameter_reaches_values_and_closures`, `use_imports_are_not_values`, `closure_called_through_a_local_is_seen` |
| 5 | functions outside the scanned directory | false negative | — | **PARTLY FIXED**: several crates at once (`fip_cycles_multi`); dependencies outside the scanned set remain (inherent) | `cycles_across_crates`, `crate_paths_fall_back_to_names_within_that_crate` |
| 6 | raw identifiers `r#name` | bug | named `r` | **FIXED** 2026-11-01 | `raw_identifiers_keep_their_name`, `distinct_raw_identifiers_do_not_collide` |
| 7 | byte / C string literals | bug → false positive | `[["a", "b", "a"]]` | **FIXED** 2026-11-01: `[]` | `byte_and_c_string_literals_are_not_identifiers`, `literals_do_not_hide_following_calls` |
| 8 | same-named functions in different modules or types | false positive | `[["a", "f", "a"]]` | **FIXED** for resolvable paths: `[]`; unresolvable paths still match by name | `same_named_functions_in_different_modules_are_distinct`, `methods_of_different_types_are_distinct_for_paths`, `use_imports_resolve_paths`, `unresolvable_paths_fall_back_to_names` |
| 9 | calls through a generic parameter `T::f()` | false positive | `[["a", "f", "a"]]` | **FIXED**: `[]` (only `impl`/`trait` members) | `generic_parameter_paths_do_not_reach_free_functions` |
| 10 | no regression test for the false negatives | test gap | 6, 7 only | **FIXED**: every snippet of 1–9 is a test with its correct result; none is `#[ignore]`d | above |

What already worked is kept and pinned by the original tests (all unchanged and
passing): closures stored then called (`let k = || b(); k()`), trait-object dispatch to
a local method (`t.go()`), functions passed as values (`iter.map(f)`,
`let g: fn() = f`), turbofish and path calls, `core`/`std`/`alloc` paths treated as
external, Verus ghost code skipped.

Measured on the workspace (2026-10-31): `crates/fip-macros/tests` with `fip_core`,
`fip_alloc`, `fip_strict` (`fip_cycles` over the tests directory, the
`no_indirect_recursion` test, and the summary run in
`crates/fip-macros/tests/checker_agreement.rs`): no cycle, 39 roots. Scanning all eleven
source and test directories of the workspace at once takes 0.12 s for the cycles and
reports 40 cycles, all false positives of item 8's remaining part (method calls are
resolved by name: `.push(..)` on a `Vec` reaches `Lexer::push`, `.max(..)` reaches
`Sum::max`, `.stream()` reaches the proc-macro's `Scan::stream`) and of item 4
(parameter calls in `#[fip]` functions reach every closure the checker's own sources
pass around). Scan the crates a root actually calls, not everything.

---

## 1. `#[fip]` applied through `cfg_attr` (false negative, high) — FIXED

```rust
#[cfg_attr(feature = "x", fip)]
fn a() { b() }
fn b() { a() }
```

Before: `[]`. `attr_mark` took the first identifier of the attribute that was not
followed by `::` and saw `cfg_attr`, so `a` was never a root.

**Fixed:** `srcmodel::parse::attr` skips the predicate of `cfg_attr(<pred>, attrs…)`
and inspects every attribute after the first top-level comma (also nested, also
`fip_macros::fip(N)`). The function is marked regardless of the predicate: a
conservative check covers every configuration. Now `[["a", "b", "a"]]`; a `cfg_attr`
without `fip` (also one whose predicate is named `fip`) reports nothing. The
`fip-core` functions marked `#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(..))]`
are roots of the workspace run (6 roots).

## 2. Calls produced by a macro's expansion (false negative, high) — FIXED for local macros

```rust
macro_rules! call_b { () => { b() } }
#[fip]
fn a() { call_b!() }
fn b() { a() }
```

Before: `[]`. Macro invocations were scanned only for their arguments.

**Fixed with option (a):** every transcriber body of every `macro_rules!` in the
scanned sources (found anywhere, by name) is scanned as part of each invoking
function, at the invocation's loop depth; nested invocations are expanded with a
recursion guard; metavariables (`$x`) are not names; `$crate` is resolved as
`crate` of the invoking function (exact for macros used in the crate defining them).
The invocation's arguments are still scanned as code. Now `[["a", "b", "a"]]`.

**Remains (inherent without expansion):** macros from other crates (their bodies are
not scanned), and functions *generated* by macros (no node exists for them). Macro
scoping is ignored (name-level: a macro of the same name elsewhere also contributes),
which only adds edges. Option (b), running on `rustc -Zunpretty=expanded` output,
would be exact but needs nightly; not done.

## 3. `include!`d source files (false negative, medium) — FIXED

```rust
#[fip]
fn a() { include!("other.rs") }
```

Before: `[]` (the file was not read).

**Fixed:** `include!("…")` with a string literal is resolved relative to the including
file and its tokens are spliced in place (expression and item position alike, nested
includes too, with file and line of the included file kept for witnesses). The target
is taken from the scanned sources or read from disk; an included file is not parsed a
second time as a crate root. `#[path = "…"] mod m;` is resolved by the reference rules
(relative to the file's directory outside inline modules, to the inline module
directories inside them) and read from disk if it lies outside the scanned tree. With
`other.rs` containing `b()` and `fn b() { a() }` defined, the cycle is reported; the
on-disk test also covers a `#[path]` module in another directory.

**Remains:** `include!(concat!(..))` and other non-literal paths; such an `include!`
in a body is an unknown (`⊤`) for `fip_testkit::summaries`, no edge for the cycle
check.

## 4. Indirect calls whose target is not named in the caller (false negative) — PARTLY FIXED

```rust
struct H { f: fn() }
#[fip]
fn a(h: &H) { (h.f)() }
fn b() { let h = H { f: c }; a(&h) }
fn c() { b() }
```

Before: `[]`. The real cycle is `a → c → b → a`, but nothing in `a` names `c`.

**Fixed with the first option:** in a function marked `#[fip]`/`#[fip(N)]` (and its
closures), a call through an expression (`(h.f)()`, `a[i]()`, `f(x)(y)`), through a
local that is not bound to a closure literal (`let k = g; k()`), or through a callable
parameter (`g()`, `g.call(..)`, `FipFn::call(&g, ..)`) adds edges to every function
whose name is used as a value anywhere in the scanned sources (names in `use` items do
not count) and to every closure passed as an argument or used as a value. Now
`[["a", "c", "b", "a"], ["b", "c", "b"]]`; the second cycle is the value edge `b → c`
(a name used as a value is a possible call), as the checker always treated it.

**Remains:**
- function pointers, closures and trait objects created outside the scanned sources
  (inherent);
- indirect calls in functions that are not marked: they add no edges (by design, as
  the TODO proposed; otherwise every value-using helper becomes a self-cycle, e.g. the
  pinned test `function_used_as_value_is_an_edge`). `fip_testkit::summaries` reports
  every indirect call reachable from a root as unknown (`⊤`), so the allocation check
  does not pass such roots;
- a closure is reached from the function that contains it, so `fn b() { a(|| b()) }`
  also reports `["b", "b"]` (over-approximation).

## 5. Functions outside the scanned directory (false negative) — PARTLY FIXED

**Fixed:** `fip_cycles_multi(&[("fip_core", dir), ("app", dir2)])` /
`fip_cycles_in_crates` scan several crates at once, keyed by crate name. A path
`crate_name::..` resolves into that crate: through its module tree and `pub use`
re-exports where possible, else by name within that crate. Names in reported cycles
carry the crate name (`x::a`, `y::inner::g`); a test file that is its own crate
carries its file stem. Test: a cycle `x::a → y::g` (re-exported from `y::inner`)
`→ x::a` is reported only when both crates are scanned.

**Remains (inherent):** dependencies outside the scanned set, `std`, and code reached
only through them (callbacks registered with an external crate).

## 6. Raw identifiers `r#name` (bug) — FIXED 2026-11-01

**Fixed:** `lex` reads the identifier after `r#` when it starts with a letter or
`_` (`r#"…"` is still a raw string). After the fix the snippet reports
`[["a", "b", "a"]]`. Tests: `raw_identifiers_keep_their_name`,
`distinct_raw_identifiers_do_not_collide`.

```rust
#[fip]
fn a() { r#b() }
fn r#b() { a() }
```

Measured before: `[["a", "r", "a"]]`.

## 7. Byte and C string literals (bug → false positive) — FIXED 2026-11-01

**Fixed:** the prefixes `r`, `br`, `cr` followed by `"` or `#"` and `b`, `c`
followed by `"` (and `b` followed by `'`) are lexed as one literal. After the fix the
snippet reports `[]`. Tests: `byte_and_c_string_literals_are_not_identifiers` (10
literal forms), `literals_do_not_hide_following_calls`.

```rust
#[fip]
fn a() { let _s = b"b()"; }
fn b() { a() }
```

Measured before: `[["a", "b", "a"]]`.

## 8. Same-named functions in different modules or types (false positive) — FIXED for resolvable paths

```rust
mod m { pub fn f() {} }
mod n { pub fn f() { super::a() } }
#[fip]
fn a() { m::f() }
```

Before: `[["a", "f", "a"]]`.

**Fixed:** nodes are keyed by crate, module path and owner; `path::name(..)` is
resolved by its path (`crate`, `self`, `super`, `Self`, local module names, `use`
imports and aliases, globs, `Type::name` to members of `impl Type` blocks). Now `[]`;
calling `n::f()` instead reports `[["a", "n::f", "a"]]`. All earlier tests pass
unchanged.

**Remains (by design):**
- a path that cannot be resolved (an external crate, a type whose members are not
  scanned) falls back to every function of that name in the unit, then the crate, to
  stay conservative (`unresolvable_paths_fall_back_to_names`); `summaries` treats such
  a name-only match as unknown (`⊤`), not as the matched function;
- method calls `expr.m(..)` still reach every scanned method named `m` taking `self`
  (no receiver types); this is the main source of false positives when many crates
  are scanned together (see the workspace measurement above);
- types are keyed by their last name, so two types `S` in different modules share
  their `impl` members for `S::f` paths.

## 9. Calls through a generic parameter `T::f()` (false positive) — FIXED

```rust
trait K { fn f(); }
#[fip]
fn a<T: K>() { T::f() }
fn f() { a::<u8>() }
```

Before: `[["a", "f", "a"]]`.

**Fixed:** when the path root is a generic parameter of the enclosing function or
`impl`, the call links only to functions defined inside `impl` or `trait` blocks with
that name, never to free functions. Now `[]`; with `impl K for u8 { fn f() { a::<u8>() } }`
the real cycle `[["a", "u8::f", "a"]]` is reported.

## 10. Regression tests for the false negatives (test gap) — FIXED

Every snippet of items 1–9 is a unit test in `callgraph.rs` with its correct expected
result (names listed in the summary table); none needed `#[ignore]` because every item
is fixed or partly fixed with the snippet detected.
