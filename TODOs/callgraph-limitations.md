<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# TODO: limitations of `fip_testkit::callgraph`

**Status:** OPEN. **Recorded:** 2026-10-31, against commit `43a671b`.
**Component:** `crates/fip-testkit/src/callgraph.rs` (`fip_cycles`, `fip_cycles_in`).

## Context

`fip_cycles` lexes the `.rs` files under one directory, builds a call graph by
function **name**, and reports every cycle reachable from a function marked
`#[fip]` / `#[fip(N)]`. It covers what `#[fip]` cannot see on its own: recursion
through other functions.

It is a **check, not a proof**. It gives no stack bound for unverified code. The
proved bound exists only for crates verified with Verus (see
`docs/decisions/2026-10-31-stack-bound.md`). Each item below either lets a real cycle
through (**false negative**), reports a cycle that does not exist (**false
positive**), or is a lexer **bug**.

All results below were measured on 2026-10-31 by calling `fip_cycles_in` on the
snippet shown (probe crate `/tmp/cgprobe`).

Follow-up design that builds on this checker (interprocedural `#[fip(N)]`
allocation summaries): `TODOs/callgraph-fip-summaries.md`.

## Summary

| # | item | kind | measured result | priority |
|---|---|---|---|---|
| 1 | `#[fip]` applied through `cfg_attr` | false negative | `[]` | high |
| 2 | calls produced by a macro's expansion | false negative | `[]` | high |
| 3 | `include!`d source files | false negative | `[]` | medium |
| 4 | indirect calls whose target is not named in the caller | false negative | `[]` | medium (inherent) |
| 5 | functions outside the scanned directory / other crates | false negative | — | medium (inherent) |
| 6 | raw identifiers `r#name` | bug | named `r` instead of `name` | high |
| 7 | byte / C string literals `b"…"`, `br"…"`, `c"…"` | bug → false positive | `[["a", "b", "a"]]` | high |
| 8 | same-named functions in different modules or types | false positive | `[["a", "f", "a"]]` | low (by design) |
| 9 | calls through a generic parameter `T::f()` | false positive | `[["a", "f", "a"]]` | low (by design) |
| 10 | no regression test for the false negatives above | test gap | — | high |

What already works (kept here so a fix does not regress it): closures stored
then called (`let k = || b(); k()`), trait-object dispatch to a local method
(`t.go()`), functions passed as values (`iter.map(f)`, `let g: fn() = f`), turbofish
and path calls, `core`/`std`/`alloc` paths treated as external, Verus ghost code
skipped.

---

## 1. `#[fip]` applied through `cfg_attr` (false negative, high)

```rust
#[cfg_attr(feature = "x", fip)]
fn a() { b() }
fn b() { a() }
```

Measured: `[]`. `attr_mark` takes the first identifier of the attribute that is not
followed by `::` and sees `cfg_attr`, so `a` is never a root.

**Fix:** inside `cfg_attr(<pred>, attrs…)`, skip the predicate and inspect each
attribute after the first top-level comma. Treat the function as marked regardless
of the predicate: a conservative check should cover every configuration.

**Accept:** the snippet reports `[["a", "b", "a"]]`; a `cfg_attr` without `fip`
reports nothing.

## 2. Calls produced by a macro's expansion (false negative, high)

```rust
macro_rules! call_b { () => { b() } }
#[fip]
fn a() { call_b!() }
fn b() { a() }
```

Measured: `[]`. Macro invocations are scanned only for their arguments; the
definition's body is never connected to the call site.

**Options:**
- (a) For `macro_rules!` defined in the scanned sources, collect the identifiers
  called in each macro's body and add them as edges from every function that
  invokes the macro. This is a name-level over-approximation that needs no expansion.
- (b) Run on `cargo expand` / `rustc -Zunpretty=expanded` output. This is exact, but
  needs nightly or an external tool, which conflicts with the zero-dependency stance.
- Macros from other crates remain invisible either way. Document this.

**Accept:** with (a), the snippet reports `[["a", "b", "a"]]`.

## 3. `include!`d source files (false negative, medium)

```rust
#[fip]
fn a() { include!("other.rs") }
```

Measured: `[]` (the file is not read). Code pulled in by `include!` / `#[path]`
modules outside the scanned tree is not lexed.

**Fix:** resolve `include!("…")` paths relative to the including file, and lex the
target as part of the including function's body (for expression includes) or the
file (for item includes). Do the same for `#[path = "…"] mod m;`.

**Accept:** with `other.rs` containing `b()` and `fn b() { a() }` defined, the cycle
is reported.

## 4. Indirect calls whose target is not named in the caller (false negative, inherent)

```rust
struct H { f: fn() }
#[fip]
fn a(h: &H) { (h.f)() }
fn b() { let h = H { f: c }; a(&h) }
fn c() { b() }
```

Measured: `[]`. The real cycle is `a → c → b → a`, but nothing in `a` names `c`.
The value edge `b → c` is found, but `a`'s call `(h.f)()` has no target.

**Options:**
- Any call through an expression (`(expr)(..)`, a local of `fn`/closure type, a
  `dyn Fn` value) from a `#[fip]` function adds edges to **every** defined function
  used as a value anywhere in the scanned sources. Sound for pointers created in the
  scanned sources, but coarse.
- Or report such calls as "unanalysable" warnings and leave the decision to the
  user.
- Pointers created outside the scanned sources stay invisible. This part is inherent;
  document it.

**Accept:** the snippet is reported, either as a cycle or as an explicit
"indirect call in `a`" diagnostic.

## 5. Functions outside the scanned directory (false negative, inherent)

Only one directory is scanned. A cycle through a function in another crate of the
workspace (or a dependency) is missed, e.g. `a` (crate X) → `g` (crate Y) → callback
into `a`.

**Option:** accept several directories (`fip_cycles_multi(&[dir1, dir2])`) so a
workspace can be checked as a whole. Dependencies outside the workspace remain
inherent.

## 6. Raw identifiers `r#name` (bug, high)

```rust
#[fip]
fn a() { r#b() }
fn r#b() { a() }
```

Measured: `[["a", "r", "a"]]`. The lexer's raw-string branch sees `r#`, finds no `"`,
and emits the identifier `r`, dropping `b`. Every raw identifier becomes `r`, so
unrelated `r#…` functions collide (false positives) and names in reports are wrong.

**Fix:** in `lex`, when `r#` is followed by an identifier start, emit the identifier
after `r#` (e.g. `b`).

**Accept:** the snippet reports `[["a", "b", "a"]]`; `fn r#x() {}` and `fn r#y() {}`
do not collide.

## 7. Byte and C string literals (bug → false positive, high)

```rust
#[fip]
fn a() { let _s = b"b()"; }
fn b() { a() }
```

Measured: `[["a", "b", "a"]]`, which is a false cycle. The prefix `b` of `b"…"` is
lexed as an identifier, then treated as a value reference to the function `b`. The
same applies to `br"…"`, `br#"…"#`, `c"…"`, `cr"…"`, and the byte character `b'x'`.

**Fix:** recognise the literal prefixes `b`, `br`, `c`, `cr` directly before `"` /
`r"` / `'` and lex them as one literal.

**Accept:** the snippet reports `[]`.

## 8. Same-named functions in different modules or types (false positive, by design)

```rust
mod m { pub fn f() {} }
mod n { pub fn f() { super::a() } }
#[fip]
fn a() { m::f() }
```

Measured: `[["a", "f", "a"]]`. Functions are merged by name, so `m::f` and `n::f` are
one node.

**Option:** key nodes by `module path :: name` from the file and `mod` structure,
and resolve `path::name(..)` calls by their path (`crate`, `self`, `super`, `Self`,
local module names). Unresolvable paths fall back to name matching to stay
conservative.

**Accept:** the snippet reports `[]`, and the existing tests still pass.

## 9. Calls through a generic parameter `T::f()` (false positive, by design)

```rust
trait K { fn f(); }
#[fip]
fn a<T: K>() { T::f() }
fn f() { a::<u8>() }
```

Measured: `[["a", "f", "a"]]`. `T::f` resolves to some impl of `K`, not to the free
function `f`. Name matching links them anyway.

**Option:** when the path root is a generic parameter of the enclosing function,
link only to functions defined inside `impl … for …` blocks whose trait has that
method name, not to free functions.

## 10. Regression tests for the false negatives (test gap, high)

The unit tests in `callgraph.rs` only pin what the checker currently detects.
Items 1–4 and 6–7 have no test, so a fix could not be shown and a regression would
not be caught.

**Do:** add each snippet above as a unit test. Mark the ones not yet fixed
`#[ignore = "TODOs/callgraph-limitations.md #N"]` with the expected (correct)
result, so fixing an item means removing `#[ignore]`.
