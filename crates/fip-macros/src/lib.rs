// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-macros — `#[fip]`, `#[fip(N)]`, `#[fbip]`
//!
//! Attributes that mark a function as written in FP² style and reject, at compile
//! time, the constructs that obviously contradict the mark.
//!
//! **This is a syntactic lint, not a proof.** A proc-macro sees tokens: it cannot see
//! types, callees, trait impls or macro expansions. What it checks:
//!
//! | attribute | rejected in the body |
//! |---|---|
//! | `#[fip]` | any allocation site (below); direct self-recursion |
//! | `#[fip(N)]` | more than `N` allocation sites; any allocation site inside a loop body; direct self-recursion |
//! | `#[fbip]` | any allocation site (frees and recursion are allowed) |
//!
//! Allocation sites are: a constructor path on a std heap type (`Box`, `Vec`, `String`,
//! `Rc`, `Arc`, the std collections) such as `Box::new` or `Vec::with_capacity`; the
//! macros `vec!` and `format!`; and the methods `.clone()`, `.to_vec()`,
//! `.to_owned()`, `.to_string()`, `.collect()` and the growth methods (`.push`,
//! `.push_str`, `.insert`, `.extend`, `.reserve`, `.resize`, `.split_off`, …), which
//! may allocate: `fip_lint_rules::ALLOC_METHODS`, matched by name and audited against
//! `std` (rustc 1.99.1). An allocation site inside a closure body counts as inside a
//! loop (an iterator adaptor may call the closure any number of times), and so does
//! one in a `while` condition.
//!
//! Not allocation sites: the constructors of empty collections that never allocate,
//! `fip_lint_rules::NON_ALLOCATING_CONSTRUCTORS` (`new` and `default` of `Vec`,
//! `String`, `VecDeque`, `BTreeMap`, `BTreeSet`, `LinkedList`, `BinaryHeap`), audited
//! in the `alloc` sources of the toolchains in
//! `fip_lint_rules::NON_ALLOCATING_CONSTRUCTORS_AUDITED_AT` and measured with a
//! counting allocator. `HashMap`/`HashSet` constructors, `with_capacity` (also with
//! `0`), `from` and every `Box`/`Rc`/`Arc` constructor stay allocation sites. Strict
//! mode accepts the listed constructors without a certificate, with bound 0.
//!
//! Every spelling of a constructor path is normalised by `fip_lint_rules::callee`
//! (shared with `fip_testkit`): `Box::<u8>::new`, `<Box<u8>>::new`,
//! `::std::boxed::Box::new`, `<Box<u8> as Default>::default`, and allocating methods
//! called by path on a heap type, slice, `str` or std trait (`Vec::clone(&v)`,
//! `<[u8]>::to_vec(x)`, `Clone::clone(&v)`) are allocation sites; the audited
//! constructors are accepted in every spelling. A constructor-like trait function
//! whose type is inferred (`Default::default()`, `From::from(x)`) cannot be decided by
//! tokens: strict mode rejects it, non-strict mode leaves it to `fip-prelint`, which
//! sees the resolved callee (fixture `ctor_spellings`), as for type aliases and `use`
//! renames. All spellings: `verify/ctor_spellings.py` (in `just compile-fail-reasons`).
//!
//! Not seen: allocation inside called functions, trait methods with other names,
//! user macros, recursion through other functions. For those, use `fip-testkit`:
//! its allocation-count assertions check what the code does, and
//! `fip_testkit::callgraph::fip_cycles` finds recursion through other functions
//! across a crate. Keep allocation-free code in `fip-core`-style crates that do not
//! link `alloc`, where the compiler rules allocation out.
//!
//! Contents of `proof!`, `proof_decl!`, `proof_with!` (written without a path) and
//! of attributes inside the body are skipped: they are Verus ghost code. Outside
//! Verus's driver the macro emits such an invocation as `const { proof! {} };`, so the
//! skipped contents are not compiled whichever `proof!` is in scope (a `proof!` that
//! kept its contents used to run them unchecked). Write
//! `#[fip]` **above** `#[cfg_attr(verus_keep_ghost, verus_spec(..))]` so it runs on
//! the unexpanded body; written below it, the item it receives under `verus` is
//! already rewritten, and the macro reports a compile error instead of guessing.
//!
//! The macros add a `# FIP` section **after** the item's own documentation saying
//! what was checked; they never claim more than that.
//!
//! On a trait method declaration (`fn area(&self) -> u32;`) the attribute declares
//! a *contract* of every implementation; see [Trait methods](#trait-methods).
//!
//! Compiled by the MIR-level checker `fip-prelint` (`tools/fip-prelint`), they also
//! emit `#[cfg_attr(fip_prelint, fip::mark(..))]` with the mode, bound, `strict`,
//! `panic_macros` and `param(..)` bounds; the driver checks those functions over MIR
//! (callees, implicit calls, panics). Plain builds get no such attribute. With
//! `FIP_MACROS_MARK_ONLY=1` as well (honoured only inside the driver), `#[fip]` and
//! `#[fbip]` outside `#[fip_impl]` skip their token-level behaviour checks and emit only
//! the mark, so the driver alone decides (used to run the rejected examples below
//! through it; each carries a hidden `# // prelint: ..` line with the driver's reason).
//!
//! `fip_fn!(prelint, N, ..)` (driver-checked mode, see [`fip_fn!`]) expands only when
//! the driver also sets `FIP_PRELINT_CHECKS=1`, which it does for a primary package in
//! check mode only; everywhere else it is a compile error.
//!
//! `#[fip(.., requires(i < j, j < xs.len()))]` declares a precondition (a conjunction
//! of comparisons between integer parameters, `p.len()` of slice parameters, access
//! paths below a reference parameter such as `w.n`, `xs[0]`, `w.b.len()`, and
//! integer literals; grammar `fip_lint_rules::requires`). It is emitted for the
//! driver as `#[cfg_attr(fip_prelint, fip::requires(..))]`: the driver checks the
//! function under it and checks it at every analysed call site. A Verus `requires`
//! is not read from `verus_spec` (an attribute macro does not see a following
//! `cfg_attr(verus_keep_ghost, ..)` when that cfg is off; measured on rustc
//! 1.97.1 and 1.99.1), so it is written by hand; when the macro does see a
//! `verus_spec` (a Verus build, `#[fip]` above it), every conjunct must appear in
//! its `requires`, else the macro reports the drift.
//!
//! ## Examples
//!
//! ```
//! use fip_macros::{fbip, fip};
//!
//! /// Doubles in place.
//! #[fip]
//! pub fn double(x: &mut i32) {
//!     *x *= 2;
//! }
//!
//! #[fip(1)]
//! pub fn boxed(x: i32) -> Box<i32> {
//!     Box::new(x)
//! }
//!
//! #[fbip]
//! pub fn count_down(n: u32) -> u32 {
//!     if n == 0 { 0 } else { count_down(n - 1) }
//! }
//!
//! /// Takes the vector out, leaving an empty one (`Vec::new` does not allocate).
//! #[fip]
//! pub fn take(v: &mut Vec<u8>) -> Vec<u8> {
//!     ::core::mem::replace(v, Vec::new())
//! }
//! # fn main() { let mut v = 3; double(&mut v); assert_eq!(v, 6); }
//! ```
//!
//! Rejected:
//!
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! #[fip_macros::fip]
//! fn f(x: i32) -> Box<i32> { Box::new(x) }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! # // expect: #[fip]: allocation site `Vec::with_capacity` in the body
//! #[fip_macros::fip]
//! fn f() -> Vec<u8> { Vec::with_capacity(0) }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: cannot check `f` (#[fip]): unresolved
//! # // expect: #[fip]: allocation site `HashMap::new` in the body
//! #[fip_macros::fip]
//! fn f() -> std::collections::HashMap<u8, u8> { std::collections::HashMap::new() }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! # // expect: #[fip]: allocation site `Box::default` in the body
//! #[fip_macros::fip]
//! fn f() -> Box<u8> { Box::default() }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! # // expect: #[fip]: allocation site `Vec::with_capacity` in the body
//! #[fip_macros::fip]
//! fn f() -> Vec<u8> { Vec::<u8>::with_capacity(4) }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! # // expect: #[fip]: allocation site `Box::new` in the body
//! #[fip_macros::fip]
//! fn f(x: u8) -> Box<u8> { <Box<u8>>::new(x) }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! # // expect: #[fip]: allocation site `Vec::clone` in the body
//! #[fip_macros::fip]
//! fn f(v: &Vec<u8>) -> Vec<u8> { <Vec<u8> as Clone>::clone(v) }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! #[fip_macros::fip]
//! fn f(x: &[u8]) -> usize { let v = vec![0u8; 4]; v.len() + x.len() }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! #[fip_macros::fip]
//! fn f(x: &[u8]) -> usize { let y = x.to_vec(); y.len() }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: `f` is #[fip] but recurses
//! #[fip_macros::fip]
//! fn f(n: u32) -> u32 { if n == 0 { 0 } else { f(n - 1) } }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate ∞ time(s), at most 1 allowed
//! #[fip_macros::fip(1)]
//! fn f(n: u32) -> u32 { let mut s = 0; for i in 0..n { let b = Box::new(i); s += *b; } s }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: may allocate 2 time(s), at most 1 allowed
//! #[fip_macros::fip(1)]
//! fn f(a: u8, b: u8) -> (Box<u8>, Box<u8>) { (Box::new(a), Box::new(b)) }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // prelint: `f` is #[fbip] but may allocate ∞ time(s), at most 0 allowed
//! #[fip_macros::fbip]
//! fn f(x: u8) -> String { format!("{x}") }
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip(unknown)]
//! fn f() {}
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fbip(1)]
//! fn f() {}
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip]
//! struct S;
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip]
//! type F = fn();
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip]
//! const C: fn() = g;
//! fn g() {}
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip]
//! static S: fn() = g;
//! fn g() {}
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip]
//! async fn f() {}
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // expect: `requires(..)`: unexpected `!=` in a comparison
//! #[fip_macros::fip(requires(i != j))]
//! fn f(i: usize, j: usize) -> usize { i ^ j }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // expect: `requires(..)`: `k` is not a parameter of `f`
//! #[fip_macros::fip(requires(i < k))]
//! fn f(i: usize) -> usize { i }
//! # fn main() {}
//! ```
//! An allocation in a closure body counts as in a loop (an iterator adaptor may call
//! it any number of times; before: accepted by `#[fip(1)]`, measured 100 allocations
//! for `n = 100`):
//! ```compile_fail
//! # // expect: #[fip(1)]: allocation site `Box::new` inside a loop body
//! #[fip_macros::fip(1)]
//! fn f(n: u64) -> u64 { let mut s = 0; (0..n).for_each(|i| { let b = Box::new(i); s += *b; }); s }
//! # fn main() {}
//! ```
//! A `while` condition runs on every iteration:
//! ```compile_fail
//! # // expect: #[fip(1)]: allocation site `Box::new` inside a loop body
//! #[fip_macros::fip(1)]
//! fn f(n: u64) -> u64 { let mut i = 0; while *Box::new(i) < n { i += 1; } i }
//! # fn main() {}
//! ```
//! The body of a loop whose header contains a block (before: the block was taken for
//! the body, measured 50 allocations at `#[fip(1)]`):
//! ```compile_fail
//! # // expect: #[fip(1)]: allocation site `Box::new` inside a loop body
//! #[fip_macros::fip(1)]
//! #[allow(unused_braces)]
//! fn f(n: u64) -> u64 { let mut s = 0; for i in { 0..n } { s += *Box::new(i); } s }
//! # fn main() {}
//! ```
//! The contents of a ghost-code macro are not compiled, whatever `proof!` is in scope
//! (before: a `proof!` that keeps them allocated unseen):
//! ```compile_fail
//! # // expect: cannot find value `b` in this scope
//! macro_rules! proof { ($($t:tt)*) => { $($t)* } }
//! #[fip_macros::fip]
//! fn f() -> usize { proof! { let b = [1_u8, 2]; } b.len() }
//! # fn main() {}
//! ```
//! A growth method (`fip_lint_rules::ALLOC_METHODS`, audited against `std`):
//! ```compile_fail
//! # // expect: #[fip]: allocation site `.push_str()` in the body
//! #[fip_macros::fip]
//! fn f(s: &mut String) { s.push_str("abc") }
//! # fn main() {}
//! ```
//!
//! ## Trait methods
//!
//! On a trait method **declaration** the attribute is a *contract* of every
//! implementation of the method: `#[fip]` (no allocation, no free, no recursion),
//! `#[fip(N)]` (at most `N` allocations per call, no free, no recursion) or `#[fbip]`
//! (no allocation). The macro sees only the declaration, so it checks nothing there;
//! it emits the declaration unchanged with a `# FIP` section and, under
//! `fip-prelint`, the same `fip::mark(..)` as on a function. The driver makes it a
//! contract: every implementation is checked against it in the crate that contains
//! it (a crate without `fip::export` cannot be checked: an error), a dynamic call
//! (`&dyn Trait`) or generic call (`self.m()`, `<S: Trait>`) of the method costs the
//! contract, and an implementation's own `#[fip(..)]` that is weaker than the contract
//! is an error. Plain builds check no implementation: use `fip-prelint`
//! (`docs/decisions/2026-11-01-fip-prelint.md`).
//! Strict contracts on trait methods are declared as `#[fip(strict = true)]`
//! (or `#[fip(N, strict = true)]`) under `#[fip_trait]` on the trait, which must be
//! an **`unsafe trait`**. `#[fip_trait]` emits `<dyn Trait>::__fip_strict_<m>`,
//! `__fip_strict_<Trait>__<m>` and the list `<dyn Trait>::__FIP_CONTRACTED`; strict
//! callers use the contract for `x.m()` and `T::m(x)` on a parameter of that trait
//! (`x: &dyn Trait`, `x: &T` with `T: Trait`), `<T as Trait>::m(x)` and
//! `<dyn Trait>::m(x)`. A strict caller pays the contract whatever implementation
//! runs, so the trust rule is: an implementation is either written `unsafe impl`
//! (a visible claim that it keeps the contracts) or is an `impl` under
//! `#[fip_impl(contract)]`, which checks every contracted method against its contract
//! at compile time (each must be implemented with `strict = true`, its certificate's
//! bound at most the contract's, `panic_macros = false` if the contract says so) and
//! writes the `unsafe` of the `impl` itself. A strict implementation in an `unsafe
//! impl` under `#[fip_impl]` is compared the same way. `#[fip_impl]` on a plain
//! `impl Trait for Type` (a trait without strict contracts, possibly not
//! dyn-compatible) compares nothing. Contracts without `strict = true` are driver
//! contracts and need no `unsafe trait`. A crate with `#![forbid(unsafe_code)]`
//! can implement such a trait with `#[fip_impl(contract)]` but not declare one.
//!
//! With a **default body**, the body gets the usual checks (above), and the mark is
//! still the contract of every implementation (a kept default body is checked for
//! each implementation by the driver).
//!
//! ```
//! use fip_macros::{fbip, fip};
//!
//! pub trait Shape {
//!     /// Area; every implementation is allocation-free.
//!     #[fip]
//!     fn area(&self) -> u32;
//!     /// At most one allocation per call.
//!     #[fip(1)]
//!     fn boxed(&self) -> Box<u32>;
//!     /// No allocation; frees and recursion allowed.
//!     #[fbip]
//!     fn depth(&self) -> u32;
//!     /// A default body, checked like a function body.
//!     #[fip]
//!     fn twice(&self) -> u32 {
//!         self.area().wrapping_mul(2)
//!     }
//! }
//!
//! pub struct Square(pub u32);
//!
//! impl Shape for Square {
//!     /// An implementation may repeat the contract (or declare a stronger one).
//!     #[fip]
//!     fn area(&self) -> u32 { self.0.wrapping_mul(self.0) }
//!     fn boxed(&self) -> Box<u32> { Box::new(self.0) }
//!     fn depth(&self) -> u32 { 0 }
//! }
//! # fn main() { assert_eq!(Square(3).twice(), 18); }
//! ```
//!
//! A declaration may bound a callable parameter with `param(g = K)` (without
//! `strict = true`): `g` must be a parameter of function-pointer or callable
//! trait-object type (`fn(..)`, `&dyn Fn*`, `&Box<dyn Fn*>`, `&dyn FipFn`; a generic
//! parameter would make the method not dyn-compatible). `fip-macros` checks the name
//! and the type; `fip-prelint` checks every implementation with `g` costing `K`
//! (mapped by position to the implementation's parameter names) and every call
//! through the contract, dynamic or on a type parameter, against `K`:
//!
//! ```
//! pub trait Visit {
//!     /// Calls `g` any number of times; `g` must not allocate.
//!     #[fip_macros::fip(param(g = 0))]
//!     fn visit(&self, g: &dyn Fn(u8) -> u8) -> u8;
//! }
//! pub struct One(pub u8);
//! impl Visit for One {
//!     fn visit(&self, f: &dyn Fn(u8) -> u8) -> u8 { f(self.0) }
//! }
//! # fn main() { assert_eq!(One(1).visit(&|x| x + 1), 2); }
//! ```
//!
//! Rejected on a declaration, because no implementation could be held to it:
//! `strict = true` (a certificate `__fip_strict_..` belongs to one function body, and a
//! declaration has none; so also `panic_macros = ..` and `crate = ..`, which need it;
//! under `#[fip_trait]`, see below, without `param(..)`, whose bounds a certificate
//! does not carry) and `requires(..)` (a dynamic call does not check a precondition).
//! A strict contract, which `fip-prelint` supports, is written by hand:
//! `#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false))]`.
//! `strict = true` on a default body is rejected as well, with a message saying so
//! (a certificate belongs to one body; `#[fip_impl]` cannot certify a default body
//! its impl block does not contain). The tokens of a default body without receiver
//! are those of a free function, so the attribute reads the enclosing block from the
//! item's source file (`Span::local_file`/`line`/`column`; used only when the file at
//! that position holds the item's own `fn <name>` and the block header is exactly a
//! `trait` header). Where the file cannot be read that way (e.g. a span from another
//! macro), the certificate is emitted with `pub(self)` as before, which rustc rejects
//! on a trait item with its generic E0449 ("visibility qualifiers are not permitted
//! here"); `#[fip_trait]` on the trait always gives the specific message.
//!
//! A bodiless function is also what a foreign function looks like. Inside
//! `#[fip_extern]` the block attribute sees the items (`#[fip]` there needs
//! `evidence = ".."`). A bare foreign item is rejected when its tokens show it is one
//! (a visibility, the `safe` qualifier or a variadic `...` parameter, none of which
//! rustc accepts on a trait method declaration; measured, rustc 1.99.1), or when its
//! source file shows it inside an `extern` block (as above). A probe item that fails
//! only in an `extern` block (a hidden function with a body: "incorrect function
//! inside `extern` block") was measured and not used: it would add an associated
//! function to every trait the attribute is used in. Where neither applies,
//! `fip-prelint` rejects the mark ("foreign functions must be certified with
//! `fip::cert` or excluded with `fip::exclude`", measured).
//!
//! a plain foreign function (checked by `just compile-fail-reasons` on a real file;
//! rustdoc's doctests have no source file position to read, so there the mark compiles
//! and the driver rejects it):
//! ```compile_fail,ignore
//! # // expect: #[fip] on a foreign function (it is declared in an `extern` block)
//! unsafe extern "C" {
//!     #[fip_macros::fip]
//!     fn c_h();
//! }
//! # fn main() {}
//! ```
//!
//! a public foreign function:
//! ```compile_fail
//! # // expect: #[fip] on a foreign function (it has a visibility, which a trait method declaration cannot have)
//! unsafe extern "C" {
//!     #[fip_macros::fip]
//!     pub fn c_f(x: i32) -> i32;
//! }
//! # fn main() {}
//! ```
//! a `safe` foreign function:
//! ```compile_fail
//! # // expect: #[fip] on a foreign function (it has the `safe` qualifier, which a trait method declaration cannot have)
//! unsafe extern "C" {
//!     #[fip_macros::fip]
//!     safe fn c_g(x: i32) -> i32;
//! }
//! # fn main() {}
//! ```
//! a variadic foreign function:
//! ```compile_fail
//! # // expect: #[fbip] on a foreign function (it has a variadic `...` parameter, which a trait method declaration cannot have)
//! unsafe extern "C" {
//!     #[fip_macros::fbip]
//!     fn c_printf(fmt: *const u8, ...) -> i32;
//! }
//! # fn main() {}
//! ```
//!
//! a default body that allocates:
//! ```compile_fail
//! # // prelint: may allocate 1 time(s), at most 0 allowed
//! # // expect: #[fip]: allocation site `Box::new` in the body
//! trait T {
//!     #[fip_macros::fip]
//!     fn f(&self) -> Box<u8> { Box::new(1) }
//! }
//! # fn main() {}
//! ```
//! What `#[fip_impl]` compares at compile time for a strict implementation of a
//! strict contract (in an `unsafe impl` or under `#[fip_impl(contract)]`), mirroring
//! the driver's `Mark::weaker_than` as far as a certificate (`fip_strict::Cert`,
//! made only by `unsafe` constructors) carries it: the allocation bound (impl ≤
//! contract) and panic strictness (a contract with `panic_macros = false` needs an
//! implementation with `panic_macros = false`). The kind needs no comparison: every
//! certificate is `fip` (`#[fbip]` has no strict mode). An implementation that is not
//! strict (`#[fbip]`, `#[fip]` without `strict = true`, or no attribute) has no
//! certificate: `#[fip_impl(contract)]` rejects it for a contracted method, and in a
//! hand-written `unsafe impl` it is the user's claim, which `fip-prelint` checks
//! (measured: an `#[fbip]` implementation of a strict contract is a `fip-prelint`
//! error, "the declaration is weaker than the contract").
//!
//! A strict contract on a trait that is not an `unsafe trait`:
//! ```compile_fail
//! # // expect: a trait with a strict contract must be an `unsafe trait`
//! #[fip_macros::fip_trait]
//! pub trait Shape {
//!     #[fip_macros::fip(strict = true)]
//!     fn area(&self) -> u32;
//! }
//! # fn main() {}
//! ```
//! A plain `impl` of a trait with strict contracts (neither `unsafe impl` nor
//! `#[fip_impl(contract)]`):
//! ```compile_fail
//! # // expect: requires an `unsafe impl` declaration
//! #[fip_macros::fip_trait]
//! pub unsafe trait Shape {
//!     #[fip_macros::fip(strict = true)]
//!     fn area(&self) -> u32;
//! }
//! pub struct Square(pub u32);
//! impl Shape for Square {
//!     fn area(&self) -> u32 { *Box::new(self.0) }
//! }
//! # fn main() {}
//! ```
//! `#[fip_impl(contract)]` without a strict implementation of a contracted method:
//! ```compile_fail
//! # // expect: #[fip_impl(contract)]: a method with a strict contract in the trait is not implemented in this block
//! use fip_macros::{fip, fip_impl, fip_trait};
//! #[fip_trait]
//! pub unsafe trait Shape {
//!     #[fip(strict = true)]
//!     fn area(&self) -> u32;
//!     #[fip(strict = true)]
//!     fn side(&self) -> u32;
//! }
//! pub struct Square(pub u32);
//! #[fip_impl(contract)]
//! impl Shape for Square {
//!     #[fip(strict = true)]
//!     fn area(&self) -> u32 { self.0 }
//!     fn side(&self) -> u32 { self.0 }
//! }
//! # fn main() {}
//! ```
//! Implementation with a certificate weaker than the trait's contract (more
//! allocations):
//! ```compile_fail
//! # // expect: #[fip_impl]: impl certificate is weaker than contract (more allocations)
//! use fip_macros::{fip, fip_impl, fip_trait};
//! #[fip_trait]
//! pub unsafe trait Shape {
//!     #[fip(strict = true)]
//!     fn area(&self) -> u32;
//! }
//! pub struct Square(pub u32);
//! #[fip_impl(contract)]
//! impl Shape for Square {
//!     #[fip(1, strict = true)]
//!     fn area(&self) -> u32 { *Box::new(self.0) }
//! }
//! # fn main() {}
//! ```
//! An implementation that allows the panicking macros under a contract with
//! `panic_macros = false`:
//! ```compile_fail
//! # // expect: #[fip_impl]: impl certificate is weaker than contract (the contract has `panic_macros = false`, the implementation does not)
//! use fip_macros::{fip, fip_impl, fip_trait};
//! #[fip_trait]
//! pub unsafe trait Step {
//!     #[fip(strict = true, panic_macros = false)]
//!     fn step(&self, x: u8) -> u8;
//! }
//! pub struct Id;
//! #[fip_impl(contract)]
//! impl Step for Id {
//!     #[fip(strict = true)]
//!     fn step(&self, x: u8) -> u8 { x }
//! }
//! # fn main() {}
//! ```
//! A checked implementation, and a strict caller through the contract:
//! ```
//! use fip_macros::{fip, fip_impl, fip_trait};
//! /// # Safety
//! /// Implementations keep the strict contract of `area`.
//! #[fip_trait]
//! pub unsafe trait Shape {
//!     #[fip(strict = true)]
//!     fn area(&self) -> u32;
//! }
//! pub struct Square(pub u32);
//! #[fip_impl(contract)]
//! impl Shape for Square {
//!     #[fip(strict = true)]
//!     fn area(&self) -> u32 { self.0 ^ 1 }
//! }
//! #[fip(strict = true)]
//! fn area_of(s: &dyn Shape) -> u32 { s.area() }
//! # fn main() { assert_eq!(area_of(&Square(3)), 2); }
//! ```
//! `strict = true` on a declaration without `#[fip_trait]`:
//! ```compile_fail
//! # // expect: `strict = true` on a trait method declaration requires `#[fip_macros::fip_trait]` on the trait
//! trait T {
//!     #[fip_macros::fip(strict = true)]
//!     fn f(&self) -> u8;
//! }
//! # fn main() {}
//! ```
//! Strict caller of an uncontracted trait method:
//! ```compile_fail
//! # // expect: no associated function or constant named `__fip_strict_size` found for trait `dyn Plain`
//! use fip_macros::fip;
//! pub trait Plain {
//!     fn size(&self) -> u32;
//! }
//! #[fip(strict = true)]
//! pub fn call_plain(p: &dyn Plain) -> u32 {
//!     p.size()
//! }
//! # fn main() {}
//! ```
//! `param(..)` with `strict = true` on a declaration (accepted without it, above):
//! ```compile_fail
//! # // expect: `param(..)` with `strict = true` is not supported on a trait method declaration
//! #[fip_macros::fip_trait]
//! unsafe trait T {
//!     #[fip_macros::fip(strict = true, param(g = 0))]
//!     fn f(&self, g: fn(u8) -> u8) -> u8;
//! }
//! # fn main() {}
//! ```
//! `param(..)` on a declaration's parameter that is not callable:
//! ```compile_fail
//! # // expect: `param(n = ..)` in a contract needs a parameter of function-pointer or callable trait-object type
//! trait T {
//!     #[fip_macros::fip(param(n = 0))]
//!     fn f(&self, n: u8) -> u8;
//! }
//! # fn main() {}
//! ```
//! `requires(..)` on a declaration:
//! ```compile_fail
//! # // expect: `requires(..)` is not supported on a trait method declaration
//! trait T {
//!     #[fip_macros::fip(requires(i < xs.len()))]
//!     fn f(&self, xs: &[u8], i: usize) -> u8;
//! }
//! # fn main() {}
//! ```
//! `strict = true` on a default body with a receiver:
//! ```compile_fail
//! # // expect: #[fip] strict: `strict = true` on a trait method's default body is not supported
//! trait T {
//!     #[fip_macros::fip(strict = true)]
//!     fn f(&self) -> u8 { 1 }
//! }
//! # fn main() {}
//! ```
//! `strict = true` on a default body without a receiver:
//! ```compile_fail
//! # // expect: #[fip] strict: `strict = true` on a trait method's default body is not supported
//! trait T {
//!     #[fip_macros::fip(strict = true)]
//!     fn f() -> u8 { 1 }
//! }
//! # fn main() {}
//! ```
//! `strict = true` on a default body under `#[fip_trait]`:
//! ```compile_fail
//! # // expect: #[fip_trait]: #[fip] strict: `strict = true` on a trait method's default body is not supported
//! #[fip_macros::fip_trait]
//! trait T {
//!     #[fip_macros::fip(strict = true)]
//!     fn f() -> u8 { 1 }
//! }
//! # fn main() {}
//! ```

//!
//! ## Strict mode
//!
//! `#[fip(strict = true)]` / `#[fip(N, strict = true)]`: the function may call only
//! functions in the audited `core` table (by absolute `::core::`/`::std::` path, so a
//! local module named `core` cannot stand in, or `<[T]>::method` for slice methods)
//! and functions with a certificate
//! (`fip_strict::Cert` constant `__fip_strict_<fn>`, generated by strict functions;
//! for methods `__fip_strict_<Type>__<m>` / `__fip_strict_<Type>__<Trait>__<m>`,
//! generated by [`macro@fip_impl`]). Every certificate names its function, and a
//! caller checks the name, so a certificate re-exported under another name is
//! rejected. The total allocation bound (own sites + callee certificates) is checked
//! at compile time; a callee in a loop must have bound 0; recursion through strict
//! functions is a cycle in constant evaluation. `param(g = K)` declares the bound
//! of a `fip_strict::FipFn` parameter, called as `g.call((..))` or
//! `FipFn::call(&g, (..))`; arguments come from [`fip_fn!`] (also inside strict
//! bodies) and are checked against `K` when the instantiation is built (not by
//! `cargo check`). `panic_macros = false` rejects the panicking macros
//! (`assert!`, `panic!`, `unreachable!`, ...); panics from indexing, arithmetic
//! overflow or callees remain. Not seen: implicit calls (`Drop`, overloaded
//! operators, `Deref`, `Index`); `fip_testkit::assert_fip!` counts what they free or
//! allocate. Details and limits: `docs/decisions/2026-11-01-strict-core-table.md`.
//!
//! Name resolution the tokens cannot see is either made irrelevant by rewriting the
//! emitted body (outside Verus's driver, which gets the body as written) or rejected:
//!
//! - **Constructors.** A call of a capitalised name, `Name(a, b)` / `E::V(a)`, is
//!   emitted as `(Name { 0: a, 1: b })`, which rustc accepts only for a tuple struct
//!   or tuple variant (in patterns too), so a function, `static`, `const` or
//!   parameter named like one does not compile instead of being called unchecked.
//!   `Self(..)` is kept. `fip_fn!(Name)` of a capitalised path is rejected.
//! - **Shadowing.** A bare call `f(..)` is rejected when `f` is also bound in the
//!   function (a parameter, `let`, pattern or closure parameter, or a value named
//!   `f`), and item declarations and `use` inside a strict body are rejected: the
//!   certificate is read at module level. `g.call(..)` on a `param(g = ..)` parameter
//!   is emitted as `(&g as &G).call(..)`, and `x.m(..)` on a parameter of a trait with
//!   strict contracts as `Trait::m(x, ..)`, so a rebound `g` / `x` is a type error.
//! - **Macros.** The panicking macros are emitted as `::core::assert!` etc. (a
//!   local `macro_rules! assert` is not what runs); written with a path they must be
//!   `::core::..` or `::std::..`. `vec![a, b]` must be written `::std::vec!` or
//!   `::alloc::vec!`; `vec![e; n]` (clones `e`) and `format!` (runs `Display` code,
//!   grows its buffer) are rejected. A bare ghost-code macro (`proof!`,
//!   `proof_decl!`, `proof_with!`) is not scanned and is emitted as
//!   `const { proof! {} };`: its contents are dropped, and whatever macro of that
//!   name is in scope runs with no input in a const block (the same in `#[fip]`
//!   without `strict`). `fip_fn!` is recognised by its last segment: a `macro_rules!
//!   fip_fn` or `use .. as fip_fn` is trusted, and `fip_testkit::certs` lists it.
//! - **Calls through values.** `(f)(x)`, `a[i](x)`, `{ f }(x)` and `s.0(x)` are
//!   rejected (a block that ends a statement, `if c { .. } (a, b)`, is not a call).
//! - **Loops.** The header and body of `while` count as in the loop (the condition
//!   runs on every iteration), and so does a closure body; a `for` loop must iterate
//!   over a range (`a..b`): any other iterable calls a user `Iterator::next`.
//! - **Generic parameters.** `T::m(..)` / `<T as Tr>::m(..)` for a type parameter
//!   `T` read the contract of its trait (`#[fip_trait]`), never a type named `T`.
//! - **Certificate names.** Parts are joined with `__`, so a strict function name
//!   containing `__`, or a type, trait or method part containing `__` or starting or
//!   ending with `_`, is rejected (`fn Foo__new` would certify `Foo::new`).
//! - **Trait paths.** `<Type as a::Trait>::m(..)` reads `__fip_strict_Type__Trait__m`
//!   and checks that `a::Trait` is the trait of the `#[fip_impl]` block that made it
//!   (generic functions that require each trait to imply the other). In a trait impl,
//!   `self.m()` is rejected: write `<Self as Trait>::m(self)`, which reads the impl's
//!   own certificate (so recursion through the impl's methods is a cycle) and cannot
//!   pick an inherent method of the same name.
//!
//! A local `assert!` that allocates is not what a strict body runs (measured):
//!
//! ```
//! fip_testkit::install!();
//! #[allow(unused_macros)]
//! macro_rules! assert { ($e:expr) => {{ let _b = Box::new($e); }} }
//! #[fip_macros::fip(strict = true)]
//! fn checked(x: u8) -> u8 { assert!(x < 200); x + 1 }
//! fn main() {
//!     let (r, s) = fip_testkit::measure(|| checked(3));
//!     assert_eq!((r, s.allocs), (4, 0));
//! }
//! ```
//!
//! Not covered (driver only): a local type named like a std heap type (`struct Vec`
//! with an allocating `new` is counted as the std constructor; `fip-prelint` resolves
//! it). Measured and recorded in `TODOs/strict-open-items.md`.
//!
//! A strict body starts with a statement re-checking the bound after
//! monomorphisation (`let () = const { .. };`). Verus does not support inline `const`
//! blocks, so under Verus's driver (executable `rust_verify`) the statement carries
//! `#[cfg(not(verus_keep_ghost))]`; in every other build it carries no cfg, so
//! consumers need no `check-cfg` entry and get no `unexpected_cfgs` warning.
//!
//! A constructor-like trait function whose type is inferred is rejected in strict mode
//! (the tokens cannot tell what it builds):
//! ```compile_fail
//! # // expect: #[fip] strict: `Default::default`: the type it builds is inferred
//! #[fip_macros::fip(strict = true)]
//! fn f() -> Box<u8> { Default::default() }
//! # fn main() {}
//! ```
//!
//! ### The `fip_strict` path: `crate = ..`
//!
//! Generated code names three items of `fip-strict`: `Cert` (certificates and the
//! bound of every callee, read as `Cert::allocs_for(cert, "name")`), `FipBound`
//! (bounds of `param(..)` arguments) and `Certified` (`fip_fn!`). By default it
//! names them under `::fip_strict`, so the crate must have `fip_strict` in its extern
//! prelude. A crate that gets the macros through a facade crate sets the path:
//!
//! | macro | argument |
//! |---|---|
//! | `#[fip(..)]` | `#[fip(strict = true, crate = my_facade::fip_strict)]` (after `strict = true`) |
//! | `#[fip_impl]` | `#[fip_impl(crate = my_facade::fip_strict)]`, inherited by its strict methods that set none |
//! | `fip_fn!` | `fip_fn!(crate = my_facade::fip_strict, \|x: u8\| ..)` |
//!
//! The value is a path (`a::b`, `::a::b`, `crate::a`, `$crate::a` from a
//! `macro_rules!`) or the same path as a string literal (`crate = "a::b"`); it must
//! name `Cert`, `FipBound` and `Certified` of `fip-strict`, e.g. a re-export of the
//! whole crate. Without writing the argument at every use:
//!
//! - the facade re-exports `fip_fn!` as a hidden `__fip_fn` and defines
//!   `macro_rules! fip_fn { ($($t:tt)*) => { $crate::__fip_fn!(crate = $crate::fip_strict, $($t)*) } }`;
//! - attribute macros cannot be wrapped by `macro_rules!` on stable Rust (rustc
//!   1.99.1: "`macro_rules!` attributes are unstable"), so instead the facade
//!   re-exports `Cert`, `Certified` and `FipBound` at its root and the consumer writes
//!   `extern crate my_facade as fip_strict;` once in its crate root: `::fip_strict`
//!   then names the facade. (A crate-root `use my_facade::fip_strict;` does not
//!   work: `::name` resolves only through the extern prelude.)
//!
//! `crates/fip-macros/tests/facade.rs` builds both setups with a consumer that
//! depends on the facade only. The path decides which `Cert` type a strict function
//! trusts: a constant of another type fails to compile where it is read, so a
//! certificate made under another path (or a look-alike type without `unsafe`) is not
//! accepted by callers using the real one.
//!
//! Rejected in strict mode (each example fails for exactly the stated reason;
//! `verify/compile_fail_reasons.py` checks that):
//!
//! calls a function without a certificate:
//! ```compile_fail
//! # // expect: cannot find value `__fip_strict_helper`
//! fn helper() {}
//! #[fip_macros::fip(strict = true)]
//! fn f() { helper() }
//! # fn main() {}
//! ```
//! calls a non-strict `#[fip]` function:
//! ```compile_fail
//! # // expect: cannot find value `__fip_strict_helper`
//! #[fip_macros::fip]
//! fn helper() {}
//! #[fip_macros::fip(strict = true)]
//! fn f() { helper() }
//! # fn main() {}
//! ```
//! reaches a table function through a `use` alias:
//! ```compile_fail
//! # // expect: cannot find value `__fip_strict_sw`
//! use core::mem::swap as sw;
//! #[fip_macros::fip(strict = true)]
//! fn f(a: &mut u8, b: &mut u8) { sw(a, b) }
//! # fn main() {}
//! ```
//! method call:
//! ```compile_fail
//! # // expect: method call `.len(..)` cannot be resolved
//! #[fip_macros::fip(strict = true)]
//! fn f(x: &[u8]) -> usize { x.len() }
//! # fn main() {}
//! ```
//! total bound exceeded through callees:
//! ```compile_fail
//! # // prelint: `two` is #[fip(1, strict = true)] but may allocate 2 time(s), at most 1 allowed
//! # // expect: the callees may allocate more than 1 times in total
//! #[fip_macros::fip(1, strict = true)]
//! fn one(x: u8) -> Box<u8> { Box::new(x) }
//! #[fip_macros::fip(1, strict = true)]
//! fn two(x: u8) -> (Box<u8>, Box<u8>) { (one(x), one(x)) }
//! # fn main() {}
//! ```
//! allocating callee inside a loop:
//! ```compile_fail
//! # // prelint: `many` is #[fip(1, strict = true)] but may allocate ∞ time(s), at most 1 allowed
//! # // expect: `one` is called in a loop and may allocate
//! #[fip_macros::fip(1, strict = true)]
//! fn one(x: u8) -> Box<u8> { Box::new(x) }
//! #[fip_macros::fip(1, strict = true)]
//! fn many(n: u8) { for i in 0..n { let _b = one(i); } }
//! # fn main() {}
//! ```
//! recursion through another strict function:
//! ```compile_fail
//! # // prelint: `a` is #[fip(strict = true)] but recurses
//! # // expect: cycle detected
//! #[fip_macros::fip(strict = true)]
//! fn a(n: u8) -> u8 { if n == 0 { 0 } else { b(n - 1) } }
//! #[fip_macros::fip(strict = true)]
//! fn b(n: u8) -> u8 { a(n) }
//! # fn main() {}
//! ```
//! `?` operator:
//! ```compile_fail
//! # // expect: the `?` operator
//! #[fip_macros::fip(strict = true)]
//! fn f(x: Option<u8>) -> Option<u8> { let y = x?; Some(y) }
//! # fn main() {}
//! ```
//! macro outside the allowlist:
//! ```compile_fail
//! # // expect: cannot be checked (its expansion is not visible)
//! #[fip_macros::fip(strict = true)]
//! fn f(x: u8) { std::println!("{x}"); }
//! # fn main() {}
//! ```
//! call through an expression:
//! ```compile_fail
//! # // expect: call through an expression
//! #[fip_macros::fip(strict = true)]
//! fn f(g: fn(u8) -> u8) -> u8 { (g)(1) }
//! # fn main() {}
//! ```
//! undeclared `FipFn` parameter:
//! ```compile_fail
//! # // expect: method call `.call(..)` cannot be resolved
//! use fip_strict::FipFn;
//! #[fip_macros::fip(strict = true)]
//! fn f<F: FipFn<(u8,), Output = u8>>(g: F) -> u8 { g.call((1,)) }
//! # fn main() {}
//! ```
//! parameter with a non-zero bound called in a loop:
//! ```compile_fail
//! # // expect: is called in a loop, so its declared bound must be 0
//! use fip_strict::FipFn;
//! #[fip_macros::fip(1, strict = true, param(g = 1))]
//! fn f<F: FipFn<(u8,), Output = u8>>(g: F) { for i in 0..3 { g.call((i,)); } }
//! # fn main() {}
//! ```
//! argument exceeding the declared parameter bound:
//! ```compile_fail
//! # // prelint: but `f` declares `param(g = 0)`
//! # // expect: may allocate more than its declared bound 0
//! use fip_strict::FipFn;
//! #[fip_macros::fip(strict = true, param(g = 0))]
//! fn f<F: FipFn<(u8,), Output = Box<u8>>>(g: F) -> u8 { *g.call((1,)) }
//! fn main() { f(fip_macros::fip_fn!(|x: u8| Box::new(x))); }
//! ```
//! uncertified closure as a `FipFn` argument (`#[diagnostic::on_unimplemented]` on
//! `FipFn` points to `fip_fn!`; before: "the trait bound `{closure}: FipFn<(u8,)>` is
//! not satisfied"):
//! ```compile_fail
//! # // expect: is not a certified callable taking `(u8,)`
//! use fip_strict::FipFn;
//! #[fip_macros::fip(strict = true, param(g = 0))]
//! fn f<F: FipFn<(u8,), Output = u8>>(g: F) -> u8 { g.call((1,)) }
//! fn main() { f(|x: u8| x); }
//! ```
//! hand-written certificate in a `forbid(unsafe_code)` crate:
//! ```compile_fail
//! # // expect: usage of an `unsafe` block
//! #![forbid(unsafe_code)]
//! #[allow(non_upper_case_globals)]
//! const __fip_strict_g: fip_strict::Cert = unsafe { fip_strict::Cert::assume("g", 0) };
//! # fn main() {}
//! ```
//! look-alike certificate type (no `unsafe` needed to write it):
//! ```compile_fail
//! # // expect: mismatched types
//! #![forbid(unsafe_code)]
//! pub struct Fake;
//! impl Fake { pub const fn allocs_for(self, _: &str) -> u64 { 0 } }
//! #[allow(non_upper_case_globals)]
//! const __fip_strict_two: Fake = Fake;
//! fn two() -> (Box<u8>, Box<u8>) { (Box::new(1), Box::new(2)) }
//! #[fip_macros::fip(strict = true)]
//! fn f() -> (Box<u8>, Box<u8>) { two() }
//! # fn main() {}
//! ```
//! a `crate = ..` path that does not resolve:
//! ```compile_fail
//! # // expect: cannot find module or crate `nowhere`
//! #[fip_macros::fip(strict = true, crate = nowhere::fip_strict)]
//! fn f() {}
//! # fn main() {}
//! ```
//! a `crate = ..` path without the `fip-strict` items:
//! ```compile_fail
//! # // expect: `Cert` in
//! #[fip_macros::fip(strict = true, crate = core)]
//! fn f() {}
//! # fn main() {}
//! ```
//! `crate = ..` that is not a path:
//! ```compile_fail
//! # // expect: `crate = ..` takes the path of the `fip_strict` crate
//! #[fip_macros::fip(strict = true, crate = 1)]
//! fn f() {}
//! # fn main() {}
//! ```
//! `crate = ..` without `strict = true`:
//! ```compile_fail
//! # // expect: `crate = ..` requires `strict = true` before it
//! #[fip_macros::fip(crate = fip_strict)]
//! fn f() {}
//! # fn main() {}
//! ```
//! hand-written `FipBound` in a `forbid(unsafe_code)` crate:
//! ```compile_fail
//! # // expect: implementation of an `unsafe` trait
//! #![forbid(unsafe_code)]
//! struct W;
//! unsafe impl fip_strict::FipBound for W { const ALLOCS: u64 = 0; }
//! # fn main() {}
//! ```
//! `param` without `strict = true`:
//! ```compile_fail
//! # // expect: `param(..)` requires `strict = true`
//! #[fip_macros::fip(param(g = 0))]
//! fn f() {}
//! # fn main() {}
//! ```
//! allocation in a loop inside a `fip_fn!` closure:
//! ```compile_fail
//! # // expect: allocation site `Box::new` inside a loop body
//! fn main() { let _w = fip_macros::fip_fn!(|n: u8| { for i in 0..n { let _b = Box::new(i); } }); }
//! ```
//! hand-written `Certified` closure in a `forbid(unsafe_code)` crate:
//! ```compile_fail
//! # // expect: usage of an `unsafe` block
//! #![forbid(unsafe_code)]
//! fn main() { let _w = unsafe { fip_strict::Certified::<0, _>::assume(|x: u8| x) }; }
//! ```
//! more than four closure parameters:
//! ```compile_fail
//! # // expect: at most 4 closure parameters
//! fn main() { let _w = fip_macros::fip_fn!(|a: u8, b: u8, c: u8, d: u8, e: u8| a + b + c + d + e); }
//! ```
//! `fip_fn!` of a function without a certificate:
//! ```compile_fail
//! # // expect: cannot find value `__fip_strict_plain`
//! fn plain(x: u8) -> u8 { x }
//! fn main() { let _w = fip_macros::fip_fn!(plain); }
//! ```
//! `fip_fn!` of something that is neither a closure nor a function path:
//! ```compile_fail
//! # // expect: fip_fn!: expected a closure `|args| body` or the path of a function with a certificate
//! fn main() { let _w = fip_macros::fip_fn!(1 + 2); }
//! ```
//! `fip_fn!(bound <= K, ..)` with a larger computed bound (checked where the value is
//! written, also by `cargo check`, unlike a callee's `param(g = K)`):
//! ```compile_fail
//! # // expect: fip_fn!: the allocation bound exceeds the declared `bound <= 0`
//! fn main() { let _w = fip_macros::fip_fn!(bound <= 0, |x: u8| Box::new(x)); }
//! ```
//! the same for a named function:
//! ```compile_fail
//! # // expect: fip_fn!: the allocation bound exceeds the declared `bound <= 0`
//! #[fip_macros::fip(1, strict = true)]
//! fn boxed(x: u8) -> Box<u8> { Box::new(x) }
//! fn main() { let _w = fip_macros::fip_fn!(bound <= 0, boxed); }
//! ```
//! a named function with `bound <= K` is a `Certified<K, _>` (the type the Verus
//! build names too), not the certificate's `Certified<N, _>`:
//! ```compile_fail
//! # // expect: mismatched types
//! #[fip_macros::fip(1, strict = true)]
//! fn boxed(x: u8) -> Box<u8> { Box::new(x) }
//! fn main() { let _w: fip_strict::Certified<1, fn(u8) -> Box<u8>> = fip_macros::fip_fn!(bound <= 3, boxed); }
//! ```
//! `bound <= ..` without an integer literal:
//! ```compile_fail
//! # // expect: fip_fn!: expected `bound <= K, ..` with an integer literal `K`
//! const K: u64 = 0;
//! fn main() { let _w = fip_macros::fip_fn!(bound <= K, |x: u8| x); }
//! ```
//! `requires` / `ensures` as `fip_fn!` arguments:
//! ```compile_fail
//! # // expect: fip_fn!: `requires` clauses are not arguments of `fip_fn!`
//! fn main() { let _w = fip_macros::fip_fn!(requires x < 10, |x: u8| x + 1); }
//! ```
//! an attribute on a named function:
//! ```compile_fail
//! # // expect: fip_fn!: attributes are kept only on a closure
//! #[fip_macros::fip(strict = true)]
//! fn flip(x: u8) -> u8 { x ^ 1 }
//! fn main() { let _w = fip_macros::fip_fn!(#[allow(unused)] flip); }
//! ```
//! a method of a value:
//! ```compile_fail
//! # // expect: a method of a value (`x.m`) cannot be named
//! fn main() { let v = 3_u8; let _w = fip_macros::fip_fn!(v.count_ones); }
//! ```
//! `fip_fn!(prelint, N, ..)` (driver-checked mode) in a plain build: never trusted
//! without the driver:
//! ```compile_fail
//! # // expect: fip_fn!(prelint, ..) is checked only by `cargo fip-prelint`
//! fn main() { let _w = fip_macros::fip_fn!(prelint, 0, |x: u32| x.wrapping_add(1).count_ones()); }
//! ```
//! the same with a `crate = ..` path and an honest bound:
//! ```compile_fail
//! # // expect: fip_fn!(prelint, ..) is checked only by `cargo fip-prelint`
//! fn main() { let _w = fip_macros::fip_fn!(crate = ::fip_strict, prelint, 1, |x: u32| Box::new(x)); }
//! ```
//! driver-checked mode without a parameter type:
//! ```compile_fail
//! # // expect: write the type of every closure parameter
//! fn main() { let _w = fip_macros::fip_fn!(prelint, 0, |x| x + 1_u8); }
//! ```
//! driver-checked mode with `bound <= K`:
//! ```compile_fail
//! # // expect: `bound <= K` is not an argument here
//! fn main() { let _w = fip_macros::fip_fn!(prelint, 0, bound <= 0, |x: u8| x); }
//! ```
//! driver-checked mode without an integer literal bound:
//! ```compile_fail
//! # // expect: fip_fn!: expected `prelint, N, |x: T, ..| body` with an integer literal `N`
//! const N: u64 = 0;
//! fn main() { let _w = fip_macros::fip_fn!(prelint, N, |x: u8| x); }
//! ```
//! `fip_strict::Compose` whose summed bound overflows (a compile error, not a wrapped
//! bound):
//! ```compile_fail
//! # // expect: attempt to compute `u64::MAX + 1_u64`, which would overflow
//! use fip_strict::FipFn;
//! #[fip_macros::fip(strict = true, param(g = 0))]
//! fn f<F: FipFn<(u8,), Output = u8>>(g: F) -> u8 { g.call((1,)) }
//! fn main() {
//!     let big = unsafe { fip_strict::Certified::<{ u64::MAX }, _>::assume(|x: u8| x) };
//!     f(fip_strict::Compose(big, unsafe { fip_strict::Certified::<1, _>::assume(|x: u8| x) }));
//! }
//! ```
//! a `panic_macros = false` strict callee given a callable not certified with
//! `panic_macros = false` (`FipBound::NO_PANIC_MACROS` is `false`):
//! ```compile_fail
//! # // expect: the argument passed as `g` is not certified with `panic_macros = false`
//! use fip_strict::FipFn;
//! #[fip_macros::fip(strict = true, panic_macros = false, param(g = 0))]
//! fn f<F: FipFn<(u8,), Output = u8>>(g: F) -> u8 { g.call((1,)) }
//! fn main() { f(fip_macros::fip_fn!(|x: u8| x ^ 1)); }
//! ```
//! `fip_fn!(panic_macros = false, ..)` with a panicking macro in the closure:
//! ```compile_fail
//! # // expect: `assert!` may panic, and `panic_macros = false` rejects panicking macros
//! fn main() { let _w = fip_macros::fip_fn!(panic_macros = false, |x: u8| { assert!(x > 0); x }); }
//! ```
//! `fip_fn!(panic_macros = false, path)` of a function whose certificate does not say
//! `panic_macros = false`:
//! ```compile_fail
//! # // expect: fip_fn!(panic_macros = false, ..): `g` is not certified with `panic_macros = false`
//! #[fip_macros::fip(strict = true)]
//! fn g(x: u8) -> u8 { x }
//! fn main() { let _w = fip_macros::fip_fn!(panic_macros = false, g); }
//! ```
//! `fip_fn!(panic_macros = false, path)` of a function without a certificate stating
//! it (a `core` table function):
//! ```compile_fail
//! # // expect: fip_fn!(panic_macros = false, path) takes a function with a certificate
//! fn main() { let _w = fip_macros::fip_fn!(panic_macros = false, ::core::mem::swap::<u8>); }
//! ```
//! `panic_macros = false` with the driver-checked mode:
//! ```compile_fail
//! # // expect: fip_fn!(panic_macros = false, prelint, ..) is not supported
//! fn main() { let _w = fip_macros::fip_fn!(panic_macros = false, prelint, 0, |x: u8| x); }
//! ```
//! `fip_fn!(path)` claiming another bound than the certificate's:
//! ```compile_fail
//! # // expect: mismatched types
//! #[fip_macros::fip(1, strict = true)]
//! fn boxed(x: u8) -> Box<u8> { Box::new(x) }
//! fn main() { let _w: fip_strict::Certified<0, fn(u8) -> Box<u8>> = fip_macros::fip_fn!(boxed); }
//! ```
//! a certificate re-exported under another function's name:
//! ```compile_fail
//! # // expect: the certificate names another function
//! mod a {
//!     #[fip_macros::fip(strict = true)]
//!     pub fn g() {}
//! }
//! use a::__fip_strict_g as __fip_strict_f;
//! fn f() {}
//! #[fip_macros::fip(strict = true)]
//! fn h() { f() }
//! # fn main() {}
//! ```
//! `panic_macros = false` and a panicking macro:
//! ```compile_fail
//! # // prelint: reachable panic path: `f` -> `core::panicking::panic`
//! # // expect: `assert!` may panic
//! #[fip_macros::fip(strict = true, panic_macros = false)]
//! fn f(x: u8) -> u8 { assert!(x > 0); x - 1 }
//! # fn main() {}
//! ```
//! a function named like a constructor (before: accepted with bound 0, measured 1
//! allocation):
//! ```compile_fail
//! # // expect: cannot find struct, variant or union type `Evil`
//! #[allow(non_snake_case)]
//! fn Evil() -> Box<u64> { Box::new(1) }
//! #[fip_macros::fip(strict = true)]
//! fn f() -> Box<u64> { Evil() }
//! # fn main() {}
//! ```
//! a capitalised function-pointer parameter:
//! ```compile_fail
//! # // expect: cannot find struct, variant or union type `G`
//! #[fip_macros::fip(strict = true)]
//! #[allow(non_snake_case)]
//! fn f(G: fn() -> Box<u64>) -> Box<u64> { G() }
//! # fn main() {}
//! ```
//! `fip_fn!` of a capitalised path:
//! ```compile_fail
//! # // expect: fip_fn!: a capitalised path
//! #[allow(non_snake_case)]
//! fn Evil(x: u8) -> Box<u8> { Box::new(x) }
//! fn main() { let _w = fip_macros::fip_fn!(Evil); }
//! ```
//! a call through a block (before: bound 0, measured 1 allocation):
//! ```compile_fail
//! # // expect: call through an expression
//! fn helper(x: u8) -> Box<u8> { Box::new(x) }
//! #[fip_macros::fip(strict = true)]
//! fn f(c: bool, x: u8) -> Box<u8> { let r = if c { helper } else { helper }(x); r }
//! # fn main() {}
//! ```
//! a call through a tuple field:
//! ```compile_fail
//! # // expect: call through a tuple field or literal
//! pub struct S(pub fn(u8) -> Box<u8>);
//! #[fip_macros::fip(strict = true)]
//! fn f(s: &S, x: u8) -> Box<u8> { s.0(x) }
//! # fn main() {}
//! ```
//! a `core` table function by a relative path (a local `mod core` would be called):
//! ```compile_fail
//! # // expect: write the `core` table function with an absolute path, `::core::mem::swap`
//! #[fip_macros::fip(strict = true)]
//! fn f(a: &mut u8, b: &mut u8) { core::mem::swap(a, b) }
//! # fn main() {}
//! ```
//! a panicking macro under another path:
//! ```compile_fail
//! # // expect: macro `my::assert!` is not the `core` macro
//! mod my { macro_rules! assert { ($e:expr) => {{ let _b = Box::new($e); }} } pub(crate) use assert; }
//! #[fip_macros::fip(strict = true)]
//! fn f(x: bool) { my::assert!(x) }
//! # fn main() {}
//! ```
//! `vec![e; n]` (before: bound 1, measured 10 allocations with an allocating `Clone`):
//! ```compile_fail
//! # // expect: `vec![e; n]` clones `e` n - 1 times
//! #[fip_macros::fip(1, strict = true)]
//! fn f(e: u8) -> Vec<u8> { ::std::vec![e; 10] }
//! # fn main() {}
//! ```
//! `vec!` without an absolute path:
//! ```compile_fail
//! # // expect: write `vec!` as `::std::vec!` or `::alloc::vec!`
//! #[fip_macros::fip(1, strict = true)]
//! fn f(e: u8) -> Vec<u8> { vec![e, e] }
//! # fn main() {}
//! ```
//! `format!` (before: bound 1, measured 51 allocations with an allocating `Display`):
//! ```compile_fail
//! # // expect: `format!` calls the arguments' `Display` / `Debug` code
//! #[fip_macros::fip(1, strict = true)]
//! fn f(e: u8) -> String { format!("{e}") }
//! # fn main() {}
//! ```
//! the contents of a ghost macro are not compiled (before: a `proof!` that keeps its
//! contents ran them unchecked, measured 2 allocations at bound 0):
//! ```compile_fail
//! # // expect: cannot find value `b` in this scope
//! macro_rules! proof { ($($t:tt)*) => { $($t)* } }
//! #[fip_macros::fip(strict = true)]
//! fn f() -> u64 { proof! { let b = 1_u64; } b }
//! # fn main() {}
//! ```
//! a `param(..)` parameter rebound in the body (before: bound 0, measured 1
//! allocation through `Evil::call`):
//! ```compile_fail
//! # // expect: `g` is a declared callable parameter and cannot be rebound
//! use fip_strict::FipFn;
//! struct Evil;
//! impl Evil { fn call(&self, _: (u8,)) -> u8 { let _b = Box::new(1_u8); 1 } }
//! #[fip_macros::fip(strict = true, param(g = 0))]
//! fn f<F: FipFn<(u8,), Output = u8>>(g: F) -> u8 { let _ = g; let g = Evil; g.call((1,)) }
//! # fn main() {}
//! ```
//! a `param(..)` parameter rebound to a wrapper whose `Deref` allocates (before:
//! `(&g as &G)` coerced through `W::deref`, bound 0, measured 1 allocation):
//! ```compile_fail
//! # // expect: `g` is a declared callable parameter and cannot be rebound
//! use fip_strict::FipFn;
//! struct W<G>(G);
//! impl<G> ::core::ops::Deref for W<G> {
//!     type Target = G;
//!     fn deref(&self) -> &G { let _b = Box::new(1_u64); &self.0 }
//! }
//! #[fip_macros::fip(strict = true, param(g = 0))]
//! fn f<G: FipFn<(u8,), Output = u8>>(g: G) -> u8 { let g = W(g); g.call((1,)) }
//! # fn main() {}
//! ```
//! the same through a `match` arm, a closure parameter or `if let`:
//! ```compile_fail
//! # // expect: `g` is a declared callable parameter and cannot be rebound
//! use fip_strict::FipFn;
//! struct W<G>(G);
//! impl<G> ::core::ops::Deref for W<G> { type Target = G; fn deref(&self) -> &G { &self.0 } }
//! #[fip_macros::fip(strict = true, param(g = 0))]
//! fn f<G: FipFn<(u8,), Output = u8>>(g: G) -> u8 { match W(g) { g => g.call((1,)) } }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // expect: `g` is a declared callable parameter and cannot be rebound
//! use fip_strict::FipFn;
//! #[fip_macros::fip(strict = true, param(g = 0))]
//! fn f<G: FipFn<(u8,), Output = u8>>(g: G) -> u8 { let _h = |g: u8| g; g.call((1,)) }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // expect: `g` is a declared callable parameter and cannot be rebound
//! use fip_strict::FipFn;
//! struct W<G>(G);
//! impl<G> ::core::ops::Deref for W<G> { type Target = G; fn deref(&self) -> &G { &self.0 } }
//! #[fip_macros::fip(strict = true, param(g = 0))]
//! fn f<G: FipFn<(u8,), Output = u8>>(g: G) -> u8 {
//!     if let Some(g) = Some(W(g)) { g.call((1,)) } else { 0 }
//! }
//! # fn main() {}
//! ```
//! a contract-typed parameter rebound in the body:
//! ```compile_fail
//! # // expect: `x` is a declared callable parameter and cannot be rebound
//! /// # Safety
//! /// Implementations keep the contract.
//! #[fip_macros::fip_trait]
//! pub unsafe trait Tr { #[fip_macros::fip(strict = true)] fn m(&self) -> u8; }
//! struct Evil;
//! impl Evil { fn m(&self) -> u8 { let _b = Box::new(1_u8); 1 } }
//! #[fip_macros::fip(strict = true)]
//! fn f(x: &dyn Tr) -> u8 { let x = Evil; x.m() }
//! # fn main() {}
//! ```
//! a local binding named like a strict function:
//! ```compile_fail
//! # // expect: `helper` is also bound in this function
//! #[fip_macros::fip(strict = true)]
//! fn helper() -> u8 { 0 }
//! #[fip_macros::fip(strict = true)]
//! fn f(e: fn() -> u8) -> u8 { let helper = e; helper() }
//! # fn main() {}
//! ```
//! a `use` inside a strict body (it could shadow a certified function):
//! ```compile_fail
//! # // expect: `use` declares an item inside a strict body
//! mod evil { pub fn helper() -> u8 { 0 } }
//! #[fip_macros::fip(strict = true)]
//! fn helper() -> u8 { 0 }
//! #[fip_macros::fip(strict = true)]
//! fn f() -> u8 { use evil::*; helper() }
//! # fn main() {}
//! ```
//! a `for` loop over something other than a range:
//! ```compile_fail
//! # // expect: a strict `for` loop must iterate over a range
//! #[fip_macros::fip(strict = true)]
//! fn f(xs: &[u8]) -> u8 { let mut s = 0; for x in xs { s ^= *x; } s }
//! # fn main() {}
//! ```
//! a `for` loop whose body follows a block in its header (before: the block was taken
//! for the body, measured 50 allocations at bound 1):
//! ```compile_fail
//! # // expect: a strict `for` loop must iterate over a range
//! #[fip_macros::fip(1, strict = true)]
//! fn one(i: u64) -> Box<u64> { Box::new(i) }
//! #[fip_macros::fip(1, strict = true)]
//! fn f(n: u64) -> u64 { let mut s = 0; #[allow(unused_braces)] for i in { 0..n } { s += *one(i); } s }
//! # fn main() {}
//! ```
//! a free function whose certificate name equals a method's (`Evil::new`):
//! ```compile_fail
//! # // expect: `Evil__new` cannot be the name of a strict function
//! #[allow(non_snake_case)]
//! #[fip_macros::fip(strict = true)]
//! fn Evil__new() -> u8 { 0 }
//! # fn main() {}
//! ```
//! a method through a generic parameter without a contracted bound (before: the
//! certificate of a type named `T` was read):
//! ```compile_fail
//! # // expect: `T` is a generic parameter, so no certificate names the function this calls
//! pub trait Mk { fn m() -> u8; }
//! #[fip_macros::fip(strict = true)]
//! fn g<T>() -> u8 where T: Mk { T::m() }
//! # fn main() {}
//! ```
//! `<Type as a::Tr>::m` where the certificate is for another trait of the same name
//! (before: bound 0, measured 1 allocation):
//! ```compile_fail
//! # // expect: the trait bound `__FipT:
//! pub struct Foo;
//! mod a { pub trait Tr { fn m(&self) -> Box<u8>; } }
//! mod b { pub trait Tr { fn m(&self) -> Box<u8>; } }
//! impl a::Tr for Foo { fn m(&self) -> Box<u8> { Box::new(1) } }
//! #[fip_macros::fip_impl]
//! impl b::Tr for Foo { #[fip_macros::fip(1, strict = true)] fn m(&self) -> Box<u8> { Box::new(2) } }
//! #[fip_macros::fip(1, strict = true)]
//! fn f(x: &Foo) -> Box<u8> { <Foo as a::Tr>::m(x) }
//! # fn main() {}
//! ```
//! recursion through the methods of a trait impl (before: both certified 0):
//! ```compile_fail
//! # // expect: cycle detected
//! /// # Safety
//! /// Implementations keep the contracts.
//! #[fip_macros::fip_trait]
//! pub unsafe trait Tr {
//!     #[fip_macros::fip(strict = true)] fn m(&self, n: u8) -> u8;
//!     #[fip_macros::fip(strict = true)] fn k(&self) -> u8;
//! }
//! pub struct Foo;
//! #[fip_macros::fip_impl(contract)]
//! impl Tr for Foo {
//!     #[fip_macros::fip(strict = true)] fn m(&self, n: u8) -> u8 { <Self as Tr>::k(self) + n }
//!     #[fip_macros::fip(strict = true)] fn k(&self) -> u8 { <Self as Tr>::m(self, 1) }
//! }
//! # fn main() {}
//! ```
//! `self.m()` in a trait impl:
//! ```compile_fail
//! # // expect: write `<Self as Tr>::k(self, ..)`
//! pub trait Tr { fn m(&self) -> u8; fn k(&self) -> u8; }
//! pub struct Foo;
//! #[fip_macros::fip_impl]
//! impl Tr for Foo {
//!     #[fip_macros::fip(strict = true)] fn m(&self) -> u8 { self.k() }
//!     #[fip_macros::fip(strict = true)] fn k(&self) -> u8 { 0 }
//! }
//! # fn main() {}
//! ```
//!
//! Methods (`#[fip_impl]`, see [`macro@fip_impl`]):
//!
//! strict associated function in a plain `impl` block (checked on a real file:
//! rustdoc's doctests have no source position to read the block from; before:
//! accepted, and its bound checked only by `cargo build`):
//! ```compile_fail,ignore
//! # // expect: an associated function needs `#[fip_macros::fip_impl]` on its `impl` block
//! struct S;
//! impl S {
//!     #[fip_macros::fip(strict = true)]
//!     fn n() -> u8 { 0 }
//! }
//! # fn main() {}
//! ```
//! an argument other than `crate = ..`:
//! ```compile_fail
//! # // expect: the arguments are `crate = path::to::fip_strict` and `contract`
//! struct S;
//! #[fip_macros::fip_impl(strict = true)]
//! impl S {}
//! # fn main() {}
//! ```
//! strict method without `#[fip_impl]` on its `impl` block:
//! ```compile_fail
//! # // expect: a method needs `#[fip_macros::fip_impl]` on its `impl` block
//! struct S(u8);
//! impl S {
//!     #[fip_macros::fip(strict = true)]
//!     fn get(&self) -> u8 { self.0 }
//! }
//! # fn main() {}
//! ```
//! an associated function and `Self::m` outside `#[fip_impl]` ("an associated
//! function needs `#[fip_macros::fip_impl]` on its `impl` block" where the macro can
//! read the item's source file, "`Self` in a strict function needs `#[fip_impl]` on
//! the `impl` block" everywhere):
//! ```compile_fail
//! # // expect: fip_impl]` on
//! struct S;
//! impl S {
//!     #[fip_macros::fip(strict = true)]
//!     fn a() {}
//!     #[fip_macros::fip(strict = true)]
//!     fn b() { Self::a() }
//! }
//! # fn main() {}
//! ```
//! a trait method called as `Type::m` (could be an inherent method of that name):
//! ```compile_fail
//! # // expect: cannot find value `__fip_strict_S__m`
//! #[fip_macros::fip_trait]
//! unsafe trait Tr { #[fip_macros::fip(strict = true)] fn m(&self) -> u8; }
//! struct S;
//! #[fip_macros::fip_impl(contract)]
//! impl Tr for S {
//!     #[fip_macros::fip(strict = true)]
//!     fn m(&self) -> u8 { 1 }
//! }
//! #[fip_macros::fip(strict = true)]
//! fn f(s: &S) -> u8 { S::m(s) }
//! # fn main() {}
//! ```
//! a method of a `#[fip_impl]` type that is not strict:
//! ```compile_fail
//! # // expect: cannot find value `__fip_strict_S__peek`
//! struct S(u8);
//! #[fip_macros::fip_impl]
//! impl S {
//!     fn peek(s: &S) -> u8 { s.0 }
//! }
//! #[fip_macros::fip(strict = true)]
//! fn f(s: &S) -> u8 { S::peek(s) }
//! # fn main() {}
//! ```
//! bounds on the impl's parameters:
//! ```compile_fail
//! # // expect: bounds on the impl's parameters and `where` clauses are rejected
//! struct W<T>(T);
//! #[fip_macros::fip_impl]
//! impl<T: Copy> W<T> {
//!     #[fip_macros::fip(strict = true)]
//!     fn get(w: &W<T>) -> T { w.0 }
//! }
//! # fn main() {}
//! ```
//! an impl for one instantiation only:
//! ```compile_fail
//! # // expect: the self type must be a named type whose arguments are exactly the impl's parameters
//! struct W<T>(T);
//! #[fip_macros::fip_impl]
//! impl W<u8> {
//!     #[fip_macros::fip(strict = true)]
//!     fn get(w: &W<u8>) -> u8 { w.0 }
//! }
//! # fn main() {}
//! ```
//! a generic trait:
//! ```compile_fail
//! # // expect: generic traits (`impl Tr<..> for Foo`) are rejected
//! trait Tr<X> { fn m(&self) -> u8; }
//! struct S;
//! #[fip_macros::fip_impl]
//! impl Tr<u8> for S {
//!     #[fip_macros::fip(strict = true)]
//!     fn m(&self) -> u8 { 1 }
//! }
//! # fn main() {}
//! ```
//! a generic trait under `#[fip_trait]`:
//! ```compile_fail
//! # // expect: generic traits (`trait Tr<..>`) are not supported for `#[fip_trait]`
//! #[fip_macros::fip_trait]
//! trait Tr<X> {
//!     #[fip_macros::fip(strict = true)]
//!     fn m(&self) -> u8;
//! }
//! # fn main() {}
//! ```
//! a generic trait method under `#[fip_trait]`:
//! ```compile_fail
//! # // expect: generic trait methods (`fn m<..>(..)`) are not supported for strict contracts under `#[fip_trait]`
//! #[fip_macros::fip_trait]
//! unsafe trait Tr {
//!     #[fip_macros::fip(strict = true)]
//!     fn m<T>(&self, x: T) -> u8;
//! }
//! # fn main() {}
//! ```
//! a generic trait in a qualified callee path:
//! ```compile_fail
//! # // expect: a generic trait in `<Type as Trait<..>>::f` cannot be resolved
//! trait Tr<X> { fn m(&self) -> u8; }
//! struct S;
//! impl Tr<u8> for S { fn m(&self) -> u8 { 1 } }
//! #[fip_macros::fip(strict = true)]
//! fn f(s: &S) -> u8 { <S as Tr<u8>>::m(s) }
//! # fn main() {}
//! ```
//! `#[fip_cert]` directly on a foreign function without `#[fip_extern]`:
//! ```compile_fail
//! # // expect: #[fip_cert] cannot emit a certificate from inside an `extern` block: put `#[fip_extern]` on the enclosing `extern` block
//! unsafe extern "C" {
//!     #[fip_macros::fip_cert(evidence = "audit")]
//!     fn c_f();
//! }
//! # fn main() {}
//! ```
//! `#[fip_cert]` missing `evidence = ".."`:
//! an `extern` block without `unsafe` (the block's certificates are trusted claims;
//! before: accepted in edition 2021 under `#![forbid(unsafe_code)]`):
//! ```compile_fail
//! # // expect: #[fip_extern]: write `unsafe extern`
//! #[fip_macros::fip_extern]
//! extern "C" {
//!     #[fip_cert(evidence = "trust me", allocs = 0)]
//!     pub fn helper();
//! }
//! # fn main() {}
//! ```
//! a strict call of a foreign function certified to free (`frees = true` or
//! `kind = "fbip"`: no `fip_strict::Cert`, which promises no deallocation; before: a
//! `Cert` with bound 0):
//! ```compile_fail
//! # // expect: cannot find value `__fip_strict_free`
//! mod sys {
//!     #[fip_macros::fip_extern]
//!     unsafe extern "C" {
//!         #[fip_cert(evidence = "C11 7.22.3.3: deallocates", kind = "fbip", frees = true)]
//!         pub fn free(p: *mut core::ffi::c_void);
//!     }
//! }
//! #[fip_macros::fip(strict = true)]
//! fn f(p: *mut core::ffi::c_void) { unsafe { sys::free(p) } }
//! # fn main() {}
//! ```
//! ```compile_fail
//! # // expect: `evidence = ".."` is required to certify a foreign function
//! #[fip_macros::fip_extern]
//! unsafe extern "C" {
//!     #[fip_cert]
//!     fn c_f();
//! }
//! # fn main() {}
//! ```
//! `#[fip]` inside `#[fip_extern]` without evidence:
//! ```compile_fail
//! # // expect: certifying a foreign function requires `evidence = ".."`
//! #[fip_macros::fip_extern]
//! unsafe extern "C" {
//!     #[fip]
//!     fn c_f();
//! }
//! # fn main() {}
//! ```
//! both certified and excluded on one foreign function:
//! ```compile_fail
//! # // expect: is both certified and excluded: choose exactly one
//! #[fip_macros::fip_extern]
//! unsafe extern "C" {
//!     #[fip_cert(evidence = "audit")]
//!     #[fip_exclude]
//!     fn c_f();
//! }
//! # fn main() {}
//! ```
//! `#[fip_exclude]` on a function with a body:
//! ```compile_fail
//! # // expect: #[fip_exclude] applies to foreign functions in `extern` blocks
//! #[fip_macros::fip_exclude]
//! fn f() {}
//! # fn main() {}
//! ```
//! strict caller of an excluded foreign function has no certificate:
//! ```compile_fail
//! # // expect: cannot find value `__fip_strict_c_log` in this scope
//! #[fip_macros::fip_extern]
//! unsafe extern "C" {
//!     #[fip_exclude]
//!     fn c_log();
//! }
//! #[fip_macros::fip(strict = true)]
//! fn call_log() {
//!     unsafe { c_log() };
//! }
//! # fn main() {}
//! ```
//! `ffi(..)` without `strict = true`:
//! ```compile_fail
//! # // expect: `ffi(..)` requires `strict = true` before it
//! mod dep { unsafe extern "C" { pub fn labs(x: core::ffi::c_long) -> core::ffi::c_long; } }
//! #[fip_macros::fip(ffi(dep::labs = sys::labs))]
//! fn f(x: core::ffi::c_long) -> core::ffi::c_long { unsafe { dep::labs(x) } }
//! # fn main() {}
//! ```
//! an `ffi(..)` entry that is not a `path = path` pair:
//! ```compile_fail
//! # // expect: `ffi(..)` takes `dependency::path = local::path` pairs
//! mod dep { unsafe extern "C" { pub fn labs(x: core::ffi::c_long) -> core::ffi::c_long; } }
//! #[fip_macros::fip(strict = true, ffi(dep::labs))]
//! fn f(x: core::ffi::c_long) -> core::ffi::c_long { unsafe { dep::labs(x) } }
//! # fn main() {}
//! ```
//! an `ffi(..)` left side that is a bare name (it has its own certificate):
//! ```compile_fail
//! # // expect: the left side names a foreign function of another module or crate by its path
//! unsafe extern "C" { fn labs(x: core::ffi::c_long) -> core::ffi::c_long; }
//! #[fip_macros::fip(strict = true, ffi(labs = sys::labs))]
//! fn f(x: core::ffi::c_long) -> core::ffi::c_long { unsafe { labs(x) } }
//! # fn main() {}
//! ```
//! one dependency path mapped twice:
//! ```compile_fail
//! # // expect: `ffi(..)` maps `dep::labs` twice
//! mod dep { unsafe extern "C" { pub fn labs(x: core::ffi::c_long) -> core::ffi::c_long; } }
//! #[fip_macros::fip(strict = true, ffi(dep::labs = a::labs, dep::labs = b::labs))]
//! fn f(x: core::ffi::c_long) -> core::ffi::c_long { unsafe { dep::labs(x) } }
//! # fn main() {}
//! ```
//! a mapping no call of the body uses:
//! ```compile_fail
//! # // expect: `ffi(dep::labs = ..)`: the body has no call of `dep::labs` written with this path
//! #[fip_macros::fip(strict = true, ffi(dep::labs = sys::labs))]
//! fn f(x: u8) -> u8 { x }
//! # fn main() {}
//! ```

#![forbid(unsafe_code)]

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

mod context;
mod flow;
mod strict;

use fip_lint_rules::{ALLOC_MACROS, ALLOC_METHODS, GHOST_MACROS, callee};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Fip,
    FipN(u64),
    Fbip,
}

impl Mode {
    fn name(self) -> String {
        match self {
            Mode::Fip => "#[fip]".to_string(),
            Mode::FipN(n) => format!("#[fip({n})]"),
            Mode::Fbip => "#[fbip]".to_string(),
        }
    }
}

/// Marks a function as fully in place: no allocation, no free, no self-recursion.
/// `#[fip(N)]` allows at most `N` allocation sites, none inside a loop.
///
/// `strict = true` (`#[fip(strict = true)]`, `#[fip(N, strict = true)]`) additionally
/// restricts calls to certified functions and checks the total bound at compile time;
/// `param(f = K, ..)` declares bounds for `FipFn` parameters. See the crate
/// documentation for exactly what is checked.
#[proc_macro_attribute]
pub fn fip(attr: TokenStream, item: TokenStream) -> TokenStream {
    match parse_fip_args(attr) {
        Ok(args) => expand(args.mode, Some(&args), item),
        Err((span, msg)) => {
            let mut out = compile_error(span, &msg);
            out.extend(item);
            out
        }
    }
}

/// Parsed `#[fip(..)]` arguments.
struct FipArgs {
    mode: Mode,
    strict: bool,
    trait_checked: bool,
    params: Vec<(String, u64, Span)>,
    /// `param(..)` written without `strict = true` before it: rejected on a function
    /// with a body ("requires `strict = true`"), accepted on a trait method
    /// declaration (a contract's parameter bounds, checked by `fip-prelint`).
    param_unstrict: Option<Span>,
    /// `panic_macros = false`: strict bodies may not use the panicking macros.
    panic_macros: bool,
    /// `crate = path`: path of the `fip_strict` crate in generated code.
    krate: Option<TokenStream>,
    /// `requires(..)`: the declared precondition, emitted for `fip-prelint` as
    /// `fip::requires(..)`.
    requires: Option<(Vec<fip_lint_rules::requires::Conjunct>, Span)>,
    /// `ffi(dep::sym = local::sym, ..)`: strict calls of `dep::sym` read the
    /// certificate of the `#[fip_extern]` declaration `local::sym`.
    ffi: Vec<strict::FfiMap>,
}

const FIP_ARGS_HELP: &str = "expected `#[fip]`, `#[fip(N)]`, `#[fip(strict = true)]`, `#[fip(N, strict = true)]`, optionally with `param(name = K, ..)`, `panic_macros = false`, `crate = path::to::fip_strict` and `ffi(dep::sym = local::sym)` after `strict = true`, and `requires(i < j, j < xs.len())`";

const KRATE_HELP: &str = "`crate = ..` takes the path of the `fip_strict` crate as the caller sees it, e.g. `crate = my_facade::fip_strict` or `crate = \"my_facade::fip_strict\"`";

/// The path after `crate =`: `a::b`, `::a::b`, `$crate::b` (as tokens, possibly in an
/// invisible group from a `macro_rules!` fragment), or the same as a string literal.
/// Tokens keep their spans, so a path that does not resolve is reported at it.
fn parse_krate(key: Span, rest: &[TokenTree]) -> Result<TokenStream, (Span, String)> {
    let toks: Vec<TokenTree> = match rest {
        [TokenTree::Group(g)] if g.delimiter() == Delimiter::None => {
            g.stream().into_iter().collect()
        }
        [TokenTree::Literal(l)] => {
            let s = l.to_string();
            let inner = s
                .strip_prefix('"')
                .and_then(|x| x.strip_suffix('"'))
                .ok_or((l.span(), KRATE_HELP.to_string()))?;
            let parsed: TokenStream = inner
                .parse()
                .map_err(|_| (l.span(), KRATE_HELP.to_string()))?;
            parsed
                .into_iter()
                .map(|mut t| {
                    t.set_span(l.span());
                    t
                })
                .collect()
        }
        _ => rest.to_vec(),
    };
    let sp = toks.first().map_or(key, TokenTree::span);
    let mut i = 0;
    let mut segments = 0;
    loop {
        let sep = toks.get(i).is_some_and(|t| is_punct(t, ':'))
            && toks.get(i + 1).is_some_and(|t| is_punct(t, ':'));
        if sep {
            i += 2;
        } else if segments > 0 {
            break;
        }
        match toks.get(i) {
            Some(TokenTree::Ident(_)) => {
                segments += 1;
                i += 1;
            }
            _ => return Err((sp, KRATE_HELP.to_string())),
        }
        if i == toks.len() {
            break;
        }
    }
    if i != toks.len() {
        return Err((sp, KRATE_HELP.to_string()));
    }
    Ok(toks.into_iter().collect())
}

const FFI_HELP: &str = "`ffi(..)` takes `dependency::path = local::path` pairs: strict calls of the dependency's foreign function read the certificate of the `#[fip_extern]` declaration at the local path, e.g. `ffi(libc::labs = sys::labs)`";

/// A plain path `a::b::c` or `::a::b` (identifiers only, no generic arguments):
/// `(tokens, identifier segments)`.
fn plain_path(toks: &[TokenTree], at: Span) -> Result<Vec<String>, (Span, String)> {
    let sp = toks.first().map_or(at, TokenTree::span);
    let mut segs = Vec::new();
    let mut i = 0;
    if toks.len() >= 2 && is_punct(&toks[0], ':') && is_punct(&toks[1], ':') {
        i = 2;
    }
    loop {
        match toks.get(i) {
            Some(TokenTree::Ident(id)) => segs.push(id.to_string()),
            _ => return Err((sp, FFI_HELP.to_string())),
        }
        i += 1;
        if i == toks.len() {
            return Ok(segs);
        }
        if !(is_punct(&toks[i], ':') && toks.get(i + 1).is_some_and(|t| is_punct(t, ':'))) {
            return Err((toks[i].span(), FFI_HELP.to_string()));
        }
        i += 2;
    }
}

/// The pairs of `ffi(dep::sym = local::sym, ..)`.
fn parse_ffi_maps(key: Span, g: &Group) -> Result<Vec<strict::FfiMap>, (Span, String)> {
    let mut maps: Vec<strict::FfiMap> = Vec::new();
    let pairs = split_commas(g.stream());
    if pairs.is_empty() {
        return Err((g.span(), FFI_HELP.to_string()));
    }
    for pair in pairs {
        let sp = pair.first().map_or(key, TokenTree::span);
        let eqs: Vec<usize> = pair
            .iter()
            .enumerate()
            .filter(|(_, t)| is_punct(t, '='))
            .map(|(k, _)| k)
            .collect();
        let [eq] = eqs.as_slice() else {
            return Err((sp, FFI_HELP.to_string()));
        };
        let (dep, local) = (&pair[..*eq], &pair[*eq + 1..]);
        let dep_segs = plain_path(dep, pair[*eq].span())?;
        let local_segs = plain_path(local, pair[*eq].span())?;
        if dep_segs.len() < 2 {
            return Err((
                sp,
                "`ffi(..)`: the left side names a foreign function of another module or crate by its path (`dep::sym`); a function in scope by its bare name already has its own certificate".to_string(),
            ));
        }
        let key_of = |segs: &[String]| segs.join("::");
        if key_of(&dep_segs) == key_of(&local_segs) {
            return Err((sp, "`ffi(..)` maps a path to itself".to_string()));
        }
        if maps.iter().any(|m| m.dep_key == key_of(&dep_segs)) {
            return Err((sp, format!("`ffi(..)` maps `{}` twice", key_of(&dep_segs))));
        }
        let (name, prefix) = local.split_last().expect("a plain path has a segment");
        maps.push(strict::FfiMap {
            dep_key: key_of(&dep_segs),
            dep: dep.to_vec(),
            local: local.to_vec(),
            local_prefix: prefix.to_vec(),
            local_name: strict::bare(&name.to_string()).to_string(),
            span: sp,
        });
    }
    Ok(maps)
}

fn split_commas(ts: TokenStream) -> Vec<Vec<TokenTree>> {
    let mut parts = vec![Vec::new()];
    for t in ts {
        if is_punct(&t, ',') {
            parts.push(Vec::new());
        } else if let Some(last) = parts.last_mut() {
            last.push(t);
        }
    }
    if parts.last().is_some_and(Vec::is_empty) {
        parts.pop();
    }
    parts
}

fn int_literal(t: &TokenTree) -> Option<u64> {
    match t {
        TokenTree::Literal(l) => l.to_string().trim_end_matches("u64").parse().ok(),
        _ => None,
    }
}

/// `Err` "`<what>` requires `strict = true` before it" unless `strict`.
fn needs_strict(strict: bool, key: &Ident, what: &str) -> Result<(), (Span, String)> {
    if strict {
        Ok(())
    } else {
        Err((
            key.span(),
            format!("{what} requires `strict = true` before it"),
        ))
    }
}

const FFI_TWICE: &str = "`ffi(..)` is given twice; list every mapping in one `ffi(..)`";

fn parse_fip_args(attr: TokenStream) -> Result<FipArgs, (Span, String)> {
    let mut args = FipArgs {
        mode: Mode::Fip,
        strict: false,
        trait_checked: false,
        params: Vec::new(),
        panic_macros: true,
        param_unstrict: None,
        krate: None,
        requires: None,
        ffi: Vec::new(),
    };
    let mut seen_strict = false;
    for (k, part) in split_commas(attr).into_iter().enumerate() {
        let sp = part.first().map_or_else(Span::call_site, TokenTree::span);
        match part.as_slice() {
            [lit] if k == 0 && int_literal(lit).is_some() => {
                args.mode = Mode::FipN(int_literal(lit).unwrap_or(0));
            }
            [TokenTree::Ident(key), eq, TokenTree::Ident(v)]
                if key.to_string() == "strict" && is_punct(eq, '=') && !seen_strict =>
            {
                args.strict = match v.to_string().as_str() {
                    "true" => true,
                    "false" => false,
                    _ => return Err((v.span(), "`strict` takes `true` or `false`".to_string())),
                };
                seen_strict = true;
            }
            [TokenTree::Ident(m)] if m.to_string() == "__fip_trait_checked" => {
                args.trait_checked = true;
            }
            [TokenTree::Ident(key), eq, TokenTree::Ident(v)]
                if key.to_string() == "panic_macros" && is_punct(eq, '=') =>
            {
                needs_strict(args.strict, key, "`panic_macros = ..`")?;
                args.panic_macros = match v.to_string().as_str() {
                    "true" => true,
                    "false" => false,
                    _ => {
                        return Err((
                            v.span(),
                            "`panic_macros` takes `true` or `false`".to_string(),
                        ));
                    }
                };
            }
            [TokenTree::Ident(key), eq, rest @ ..]
                if key.to_string() == "crate" && is_punct(eq, '=') && args.krate.is_none() =>
            {
                needs_strict(args.strict, key, "`crate = ..`")?;
                args.krate = Some(parse_krate(key.span(), rest)?);
            }
            [TokenTree::Ident(key), TokenTree::Group(g)]
                if key.to_string() == "requires"
                    && g.delimiter() == Delimiter::Parenthesis
                    && args.requires.is_none() =>
            {
                let cs = fip_lint_rules::requires::parse(&g.stream().to_string())
                    .map_err(|e| (g.span(), format!("`requires(..)`: {e}")))?;
                args.requires = Some((cs, g.span()));
            }
            [TokenTree::Ident(key), TokenTree::Group(g)]
                if key.to_string() == "ffi" && g.delimiter() == Delimiter::Parenthesis =>
            {
                needs_strict(args.strict, key, "`ffi(..)`")?;
                if !args.ffi.is_empty() {
                    return Err((key.span(), FFI_TWICE.to_string()));
                }
                args.ffi = parse_ffi_maps(key.span(), g)?;
            }
            [TokenTree::Ident(key), TokenTree::Group(g)]
                if key.to_string() == "param" && g.delimiter() == Delimiter::Parenthesis =>
            {
                // Without `strict = true` only a trait method declaration accepts it
                // (decided when the item is seen, `expand_parts`/`expand_decl`).
                if !args.strict && args.param_unstrict.is_none() {
                    args.param_unstrict = Some(key.span());
                }
                for decl in split_commas(g.stream()) {
                    match decl.as_slice() {
                        [TokenTree::Ident(name), eq, lit]
                            if is_punct(eq, '=') && int_literal(lit).is_some() =>
                        {
                            args.params.push((
                                name.to_string(),
                                int_literal(lit).unwrap_or(0),
                                name.span(),
                            ));
                        }
                        _ => {
                            let sp = decl.first().map_or(g.span(), TokenTree::span);
                            return Err((sp, "expected `name = K` with an integer K".to_string()));
                        }
                    }
                }
            }
            _ => return Err((sp, FIP_ARGS_HELP.to_string())),
        }
    }
    Ok(args)
}

/// Marks a function as functional-but-in-place: no allocation; frees and
/// recursion are allowed. See the crate documentation for exactly what is checked.
#[proc_macro_attribute]
pub fn fbip(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(first) = attr.into_iter().next() {
        return arg_error(first.span(), "fbip", item);
    }
    expand(Mode::Fbip, None, item)
}

fn arg_error(span: Span, which: &str, item: TokenStream) -> TokenStream {
    let msg = if which == "fip" {
        "expected `#[fip]` or `#[fip(N)]` with an integer literal N"
    } else {
        "`#[fbip]` takes no arguments"
    };
    let mut out = compile_error(span, msg);
    out.extend(item);
    out
}

/// Builds `::core::compile_error! { "msg" }` with every token at `span`.
fn compile_error(span: Span, msg: &str) -> TokenStream {
    let mut lit = Literal::string(msg);
    lit.set_span(span);
    let body = TokenStream::from(TokenTree::Literal(lit));
    let mut group = Group::new(Delimiter::Brace, body);
    group.set_span(span);
    let mut toks: Vec<TokenTree> = Vec::new();
    for seg in ["core", "compile_error"] {
        let mut c1 = Punct::new(':', Spacing::Joint);
        c1.set_span(span);
        let mut c2 = Punct::new(':', Spacing::Alone);
        c2.set_span(span);
        toks.push(TokenTree::Punct(c1));
        toks.push(TokenTree::Punct(c2));
        toks.push(TokenTree::Ident(Ident::new(seg, span)));
    }
    let mut bang = Punct::new('!', Spacing::Alone);
    bang.set_span(span);
    toks.push(TokenTree::Punct(bang));
    toks.push(TokenTree::Group(group));
    toks.into_iter().collect()
}

fn is_ident(t: &TokenTree, s: &str) -> bool {
    matches!(t, TokenTree::Ident(i) if i.to_string() == s)
}

fn is_punct(t: &TokenTree, c: char) -> bool {
    matches!(t, TokenTree::Punct(p) if p.as_char() == c)
}

fn is_group(t: &TokenTree, d: Delimiter) -> bool {
    matches!(t, TokenTree::Group(g) if g.delimiter() == d)
}

struct FnShape {
    /// Index of the first token after the outer attributes.
    after_attrs: usize,
    /// Visibility tokens (`pub`, `pub(crate)`, or none).
    vis: Vec<TokenTree>,
    name: String,
    generics: Vec<TokenTree>,
    /// Parameter list `( .. )`.
    params: Option<Group>,
    /// `{ body }`; `None` for a declaration ending in `;` (a trait method declaration:
    /// a contract, see [`expand_decl`]).
    body: Option<Group>,
}

/// Recognises `#[attr]* vis? (const|async|unsafe|safe|extern "abi"?)* fn name ... { body }`
/// and the bodiless `... fn name ... ;`.
fn parse_fn(toks: &[TokenTree]) -> Result<FnShape, (Span, String)> {
    let first_span = toks.first().map_or_else(Span::call_site, TokenTree::span);
    let not_fn = || {
        (
            first_span,
            "FIP attributes apply only to functions (with a body, or trait method declarations)"
                .to_string(),
        )
    };
    let mut i = 0;
    while i + 1 < toks.len()
        && is_punct(&toks[i], '#')
        && is_group(&toks[i + 1], Delimiter::Bracket)
    {
        // `verus_spec` has already expanded (it rewrites the item and tags it
        // `#[verus::internal(..)]`); the body is no longer the user's code.
        if let TokenTree::Group(g) = &toks[i + 1]
            && g.stream()
                .into_iter()
                .next()
                .is_some_and(|t| is_ident(&t, "verus"))
        {
            return Err((
                toks[i].span(),
                "write FIP attributes above `verus_spec`, so they see the unexpanded body"
                    .to_string(),
            ));
        }
        i += 2;
    }
    let after_attrs = i;
    if i < toks.len() && is_ident(&toks[i], "pub") {
        i += 1;
        if i < toks.len() && is_group(&toks[i], Delimiter::Parenthesis) {
            i += 1;
        }
    }
    let vis = toks[after_attrs..i].to_vec();
    loop {
        let Some(t) = toks.get(i) else {
            return Err(not_fn());
        };
        if is_ident(t, "async") {
            return Err((
                t.span(),
                "FIP attributes do not support `async fn`".to_string(),
            ));
        }
        if is_ident(t, "const") || is_ident(t, "unsafe") || is_ident(t, "safe") {
            i += 1;
        } else if is_ident(t, "extern") {
            i += 1;
            if matches!(toks.get(i), Some(TokenTree::Literal(_))) {
                i += 1;
            }
        } else {
            break;
        }
    }
    if !toks.get(i).is_some_and(|t| is_ident(t, "fn")) {
        return Err(not_fn());
    }
    let Some(TokenTree::Ident(name)) = toks.get(i + 1) else {
        return Err(not_fn());
    };
    let body = match toks.last() {
        Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Brace => Some(g.clone()),
        Some(t) if is_punct(t, ';') => None,
        _ => return Err(not_fn()),
    };
    let (generics, params) = param_list_and_generics(&toks[i + 2..]);
    Ok(FnShape {
        after_attrs,
        vis,
        name: name.to_string(),
        generics,
        params,
        body,
    })
}

/// The parameter list `( .. )` of a signature starting right after the function
/// name: skips generic parameters `<..>` (whose bounds may contain `Fn(..) -> R`).
fn param_list_and_generics(sig: &[TokenTree]) -> (Vec<TokenTree>, Option<Group>) {
    let mut j = 0;
    let mut generics = Vec::new();
    if sig.first().is_some_and(|t| is_punct(t, '<')) {
        let mut depth = 0_i32;
        while j < sig.len() {
            let t = &sig[j];
            let arrow = j > 0 && is_punct(&sig[j - 1], '-');
            if is_punct(t, '<') {
                depth += 1;
            } else if is_punct(t, '>') && !arrow {
                depth -= 1;
                if depth == 0 {
                    j += 1;
                    break;
                }
            }
            j += 1;
        }
        generics = sig[..j].to_vec();
    }
    let params = match sig.get(j) {
        Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis => Some(g.clone()),
        _ => None,
    };
    (generics, params)
}

struct Site {
    span: Span,
    what: String,
    in_loop: bool,
}

struct Scan<'a> {
    fn_name: &'a str,
    sites: Vec<Site>,
    recursion: Vec<Span>,
}

impl Scan<'_> {
    /// Scans `ts` and returns it as emitted: the same tokens, except that ghost-code
    /// macros (`proof!`, ..; [`GHOST_MACROS`], written without a path) are removed
    /// outside Verus's driver, so their contents, which this scan skips, are not
    /// compiled whichever macro of that name is in scope.
    fn stream(&mut self, ts: TokenStream, in_loop: bool) -> TokenStream {
        let toks: Vec<TokenTree> = ts.into_iter().collect();
        let texts = path_texts(&toks);
        let ptoks = path_toks(&toks, &texts);
        let loops = flow::loop_regions(&toks);
        let erase = !strict::under_verus();
        let mut out: Vec<TokenTree> = Vec::with_capacity(toks.len());
        let mut i = 0;
        while i < toks.len() {
            let t = &toks[i];
            let in_loop_here = in_loop || loops[i];
            // Attributes inside the body (e.g. Verus loop invariants): skip.
            if is_punct(t, '#')
                && toks
                    .get(i + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Bracket))
            {
                out.extend(toks[i..i + 2].iter().cloned());
                i += 2;
                continue;
            }
            if let TokenTree::Ident(id) = t {
                let s = id.to_string();
                let bang_next = toks.get(i + 1).is_some_and(|n| is_punct(n, '!'))
                    && toks
                        .get(i + 2)
                        .is_some_and(|n| matches!(n, TokenTree::Group(_)));
                let prev_path = i > 0 && is_punct(&toks[i - 1], ':');
                // Ghost code (a bare `proof!` etc.) is skipped, and removed from the
                // emitted body outside Verus; a `fip_fn!` closure is checked by
                // `fip_fn!` and counted through the declared bound of the parameter it
                // is passed to.
                if bang_next && !prev_path && GHOST_MACROS.contains(&s.as_str()) {
                    if erase {
                        out.extend(strict::ghost_stub(&toks, i));
                    } else {
                        out.extend(toks[i..i + 3].iter().cloned());
                    }
                    i += 3;
                    continue;
                }
                if bang_next && s == "fip_fn" {
                    out.extend(toks[i..i + 3].iter().cloned());
                    i += 3;
                    continue;
                }
                if bang_next && ALLOC_MACROS.contains(&s.as_str()) {
                    self.site(id.span(), format!("`{s}!`"), in_loop_here);
                }
                let prev_dot = i > 0 && is_punct(&toks[i - 1], '.');
                // The last segment of a path (any spelling: `Box::new`,
                // `Box::<u8>::new`, `<Box<u8>>::new`, `<Box<u8> as Default>::default`,
                // `::alloc::boxed::Box::new`, ..), called or passed as a value.
                let sep_next = toks.get(i + 1).is_some_and(|n| is_punct(n, ':'))
                    && toks.get(i + 2).is_some_and(|n| is_punct(n, ':'));
                let path_end = !prev_dot && !bang_next && !sep_next;
                if path_end {
                    let start = callee::path_start(&ptoks, i);
                    let c = callee::classify(&ptoks[start..=i]);
                    if let callee::Callee::Alloc { .. } = c {
                        self.site(toks[start].span(), c.shown(), in_loop_here);
                    }
                }
                let call_next = toks
                    .get(i + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Parenthesis))
                    || (toks.get(i + 1).is_some_and(|n| is_punct(n, ':'))
                        && toks.get(i + 2).is_some_and(|n| is_punct(n, ':'))
                        && toks.get(i + 3).is_some_and(|n| is_punct(n, '<')));
                if prev_dot && call_next && ALLOC_METHODS.contains(&s.as_str()) {
                    self.site(id.span(), format!("`.{s}()`"), in_loop_here);
                }
                if s == self.fn_name
                    && toks
                        .get(i + 1)
                        .is_some_and(|n| is_group(n, Delimiter::Parenthesis))
                {
                    let via_self_path = i >= 3
                        && is_punct(&toks[i - 1], ':')
                        && is_punct(&toks[i - 2], ':')
                        && is_ident(&toks[i - 3], "Self");
                    let via_self_dot = i >= 2 && prev_dot && is_ident(&toks[i - 2], "self");
                    if (!prev_path && !prev_dot) || via_self_path || via_self_dot {
                        self.recursion.push(id.span());
                    }
                }
            }
            if let TokenTree::Group(g) = t {
                let inner = self.stream(g.stream(), in_loop_here);
                let mut ng = Group::new(g.delimiter(), inner);
                ng.set_span(g.span());
                out.push(TokenTree::Group(ng));
            } else {
                out.push(t.clone());
            }
            i += 1;
        }
        out.into_iter().collect()
    }

    fn site(&mut self, span: Span, what: String, in_loop: bool) {
        self.sites.push(Site {
            span,
            what,
            in_loop,
        });
    }
}

/// The identifier text of each token (empty for the others), for [`path_toks`].
pub(crate) fn path_texts(toks: &[TokenTree]) -> Vec<String> {
    toks.iter()
        .map(|t| match t {
            TokenTree::Ident(id) => id.to_string(),
            _ => String::new(),
        })
        .collect()
}

/// `toks` as `fip_lint_rules::callee` reads a path (`texts` from [`path_texts`]).
pub(crate) fn path_toks<'a>(toks: &[TokenTree], texts: &'a [String]) -> Vec<callee::Tok<'a>> {
    toks.iter()
        .zip(texts)
        .map(|(t, text)| match t {
            TokenTree::Ident(_) => callee::Tok::Ident(text),
            TokenTree::Punct(p) => callee::Tok::Punct(p.as_char()),
            TokenTree::Group(g) if g.delimiter() == Delimiter::Bracket => callee::Tok::Slice,
            _ => callee::Tok::Other,
        })
        .collect()
}

/// Generic type of each simple `name: T` parameter in a parameter list.
fn param_types(params: Option<&Group>) -> Vec<(String, Ident)> {
    let mut out = Vec::new();
    let Some(g) = params else { return out };
    for part in split_commas(g.stream()) {
        let toks: Vec<&TokenTree> = part.iter().filter(|t| !is_ident(t, "mut")).collect();
        if let [TokenTree::Ident(name), colon, TokenTree::Ident(ty)] = toks.as_slice()
            && is_punct(colon, ':')
        {
            out.push((name.to_string(), ty.clone()));
        }
    }
    out
}

fn expand(mode: Mode, args: Option<&FipArgs>, item: TokenStream) -> TokenStream {
    match expand_parts(mode, args, &item, None) {
        Ok((mut items, f)) => {
            items.extend(f);
            items
        }
        Err(mut errors) => {
            errors.extend(item);
            errors
        }
    }
}

/// Where a strict function lives: inside a `#[fip_impl]` block for `self_ty`
/// (implementing `trait_name`, if any), or at module level (`None`).
struct ImplCtx {
    self_ty: String,
    trait_name: Option<String>,
    trait_toks: Vec<TokenTree>,
    /// Parameter names of `impl<..>` (lifetimes as `'a`).
    params: Vec<String>,
}

/// A parameter (or generic type parameter) mapped to its trait: `(name, (trait
/// module prefix, trait name))`.
type TraitOf = (String, (Vec<TokenTree>, String));

/// Parameters whose type names a trait (`x: &dyn Tr`, `s: &S` with `S: Tr`), and
/// the first trait bound of each generic type parameter. A `self` receiver is not
/// mapped: inside `impl Tr for Ty`, `self.m()` would also call an inherent method
/// `Ty::m` and would read the contract instead of the impl's own certificate (which
/// keeps recursion through the impl's methods a constant-evaluation cycle), so a
/// strict trait-impl method writes `<Self as Tr>::m(self, ..)`.
fn extract_param_traits(
    params: Option<&Group>,
    generics: &[TokenTree],
) -> (Vec<TraitOf>, Vec<TraitOf>) {
    let mut out = Vec::new();
    let mut type_bounds: Vec<TraitOf> = Vec::new();

    if generics.first().is_some_and(|t| is_punct(t, '<')) && generics.len() >= 2 {
        let inner: TokenStream = generics[1..generics.len() - 1].iter().cloned().collect();
        for part in split_commas(inner) {
            if let Some(colon_pos) = part.iter().position(|t| is_punct(t, ':'))
                && let Some(TokenTree::Ident(type_param)) = part.first()
            {
                let bounds_toks = &part[colon_pos + 1..];
                let trait_toks: Vec<TokenTree> = bounds_toks
                    .iter()
                    .take_while(|t| !is_punct(t, '+'))
                    .cloned()
                    .collect();
                if let Some((TokenTree::Ident(trait_name), prefix)) = trait_toks.split_last() {
                    type_bounds.push((
                        type_param.to_string(),
                        (prefix.to_vec(), trait_name.to_string()),
                    ));
                }
            }
        }
    }

    if let Some(g) = params {
        for part in split_commas(g.stream()) {
            let toks: Vec<TokenTree> = part.into_iter().filter(|t| !is_ident(t, "mut")).collect();
            if toks.first().is_some_and(|t| is_ident(t, "self"))
                || (toks.first().is_some_and(|t| is_punct(t, '&'))
                    && toks.get(1).is_some_and(|t| is_ident(t, "self")))
            {
                continue;
            }
            if let Some(colon_pos) = toks.iter().position(|t| is_punct(t, ':'))
                && let Some(TokenTree::Ident(param_name)) = toks.first()
            {
                let type_toks = &toks[colon_pos + 1..];
                if let Some(dyn_pos) = type_toks.iter().position(|t| is_ident(t, "dyn")) {
                    let after_dyn: Vec<TokenTree> = type_toks[dyn_pos + 1..]
                        .iter()
                        .take_while(|t| !is_punct(t, '+') && !is_punct(t, '>'))
                        .cloned()
                        .collect();
                    if let Some((TokenTree::Ident(trait_name), prefix)) = after_dyn.split_last() {
                        out.push((
                            param_name.to_string(),
                            (prefix.to_vec(), trait_name.to_string()),
                        ));
                    }
                } else if let Some(TokenTree::Ident(last_ty)) =
                    type_toks.iter().rfind(|t| !is_punct(t, '&'))
                {
                    let ty_str = last_ty.to_string();
                    if let Some((_, (prefix, trait_name))) =
                        type_bounds.iter().find(|(t, _)| t == &ty_str)
                    {
                        out.push((param_name.to_string(), (prefix.clone(), trait_name.clone())));
                    }
                }
            }
        }
    }
    (out, type_bounds)
}

/// Certificate name of a strict function: `f`, `Type__m` or `Type__Trait__m`, or
/// why its parts cannot form one unambiguously (`strict::segment_error`).
fn cert_name(fn_name: &str, ctx: Option<&ImplCtx>) -> Result<String, String> {
    let f = strict::bare(fn_name);
    let parts: Vec<&str> = match ctx {
        None => {
            return strict::fn_name_error(f).map_or_else(|| Ok(f.to_string()), Err);
        }
        Some(ImplCtx {
            self_ty,
            trait_name: None,
            ..
        }) => vec![self_ty, f],
        Some(ImplCtx {
            self_ty,
            trait_name: Some(t),
            ..
        }) => vec![self_ty, t, f],
    };
    match parts.iter().find_map(|p| strict::segment_error(p)) {
        Some(e) => Err(e),
        None => Ok(parts.join("__")),
    }
}

/// `true` if the first parameter is a `self` receiver.
fn has_receiver(params: Option<&Group>) -> bool {
    params.is_some_and(|g| {
        g.stream()
            .into_iter()
            .take_while(|t| !is_punct(t, ','))
            .any(|t| is_ident(&t, "self"))
    })
}

/// Errors of a strict function outside `#[fip_impl]` that is not a free function: a
/// trait method's default body, a method, or an associated function of a plain
/// `impl` block (located through the source file, `context::enclosing`).
fn strict_placement_errors(
    tag: &str,
    toks: &[TokenTree],
    shape: &FnShape,
    body: &Group,
) -> TokenStream {
    let mut errors = TokenStream::new();
    let in_trait = shape.vis.is_empty()
        && fn_keyword_span(toks, shape)
            .is_some_and(|sp| context::enclosing(sp, &shape.name) == context::Enclosing::Trait);
    if in_trait {
        errors.extend(compile_error(body.span(), &strict_default_body_error(tag)));
    } else if has_receiver(shape.params.as_ref()) {
        errors.extend(compile_error(
        body.span(),
        &format!(
            "{tag} strict: a method needs `#[fip_macros::fip_impl]` on its `impl` block, which names its certificate `__fip_strict_<Type>__{}` (strict mode is not available on trait method declarations, see the crate documentation)",
            shape.name
        ),
    ));
    } else if fn_keyword_span(toks, shape)
        .is_some_and(|sp| context::enclosing(sp, &shape.name) == context::Enclosing::Impl)
    {
        // An associated function in a plain `impl` block: its certificate would be an
        // associated constant that no strict caller names and that `cargo check`
        // does not evaluate.
        errors.extend(compile_error(
        body.span(),
        &format!(
            "{tag} strict: an associated function needs `#[fip_macros::fip_impl]` on its `impl` block, which names its certificate `__fip_strict_<Type>__{}`",
            shape.name
        ),
    ));
    }
    errors
}

/// Checks and rewrites one function. `Ok((items, function))`: the items go before
/// the function (or before the `impl` block for `ctx = Some`); `Err(errors)`.
fn expand_parts(
    mode: Mode,
    args: Option<&FipArgs>,
    item: &TokenStream,
    ctx: Option<&ImplCtx>,
) -> Result<(TokenStream, TokenStream), TokenStream> {
    let toks: Vec<TokenTree> = item.clone().into_iter().collect();
    let shape = parse_fn(&toks).map_err(|(span, msg)| compile_error(span, &msg))?;
    let Some(body) = shape.body.clone() else {
        return expand_decl(mode, args, &toks, &shape, ctx);
    };
    if let Some(sp) = args.and_then(|a| a.param_unstrict) {
        return Err(compile_error(
            sp,
            "`param(..)` requires `strict = true` before it",
        ));
    }
    let mut scan = Scan {
        fn_name: &shape.name,
        sites: Vec::new(),
        recursion: Vec::new(),
    };
    let base_body = scan.stream(body.stream(), false);

    let tag = mode.name();
    // Mark-only mode (`fip-prelint`'s behaviour check of rejected examples): no
    // token-level behaviour checks and no strict rewriting for free functions.
    let mark_only = ctx.is_none() && mark_only();
    let mut errors = if mark_only {
        TokenStream::new()
    } else {
        base_errors(mode, &tag, &scan, &shape.name)
    };
    let strict_args = args.filter(|a| a.strict && !mark_only);
    if strict_args.is_some() && ctx.is_none() {
        errors.extend(strict_placement_errors(&tag, &toks, &shape, &body));
    }
    let cert = strict_args.map(|_| cert_name(&shape.name, ctx));
    if let Some(Err(e)) = &cert {
        errors.extend(compile_error(
            fn_keyword_span(&toks, &shape).unwrap_or_else(|| body.span()),
            &format!("{tag} strict: {e}"),
        ));
    }
    let strict_scan =
        strict_args.map(|a| run_strict_scan(a, &shape, &body, &tag, ctx, &mut errors));
    if let Some((cs, sp)) = args.and_then(|a| a.requires.as_ref()) {
        errors.extend(check_requires(cs, *sp, &shape, &toks[..shape.after_attrs]));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let doc = if mark_only {
        mark_only_doc()
    } else {
        fip_doc(mode, strict_scan.is_some())
    };
    let mark = prelint_mark(mode, args);
    let mut items = TokenStream::new();
    let mut toks = toks;
    if strict_scan.is_none() && !mark_only {
        let mut g = Group::new(Delimiter::Brace, base_body);
        g.set_span(body.span());
        if let Some(last) = toks.last_mut() {
            *last = TokenTree::Group(g);
        }
    }
    if let Some((ss, emitted)) = &strict_scan {
        let n = match mode {
            Mode::FipN(n) => n,
            Mode::Fip | Mode::Fbip => 0,
        };
        let local = u64::try_from(scan.sites.len()).unwrap_or(u64::MAX);
        let vis: Vec<TokenTree> = match ctx {
            Some(ImplCtx {
                trait_name: Some(_),
                ..
            }) => vec![TokenTree::Ident(Ident::new("pub", Span::call_site()))],
            // A free function without visibility: `pub(self)` (the same), which rustc
            // rejects on a trait item (E0449). So `strict = true` on a trait method
            // with a default body and no receiver, whose certificate would become an
            // associated constant that no strict caller names and that is not evaluated
            // eagerly, does not compile; one with a receiver is rejected above.
            None if shape.vis.is_empty() => "pub(self)"
                .parse::<TokenStream>()
                .map_or_else(|_| Vec::new(), |ts| ts.into_iter().collect()),
            Some(_) | None => shape.vis.clone(),
        };
        let name = match &cert {
            Some(Ok(name)) => name.clone(),
            _ => String::new(),
        };
        let (cert_items, stmt) = ss.emit_fn(&tag, &name, &vis, n, local);
        items.extend(cert_items);
        let mut new_body = stmt;
        if std::env::var_os(PRELINT_ENV).is_some() {
            new_body.extend(ss.emit_ffi_checks());
        }
        new_body.extend(emitted.clone());
        let mut g = Group::new(Delimiter::Brace, new_body);
        g.set_span(body.span());
        if let Some(last) = toks.last_mut() {
            *last = TokenTree::Group(g);
        }
    }
    let mut f = TokenStream::new();
    f.extend(toks[..shape.after_attrs].iter().cloned());
    f.extend(doc);
    f.extend(mark);
    f.extend(toks[shape.after_attrs..].iter().cloned());
    Ok((items, f))
}

/// A function declaration without a body: in valid Rust a trait method declaration
/// (`fn m(&self) -> u8;`) or a foreign function. On a trait method the mark is a
/// *contract* for `fip-prelint`: every implementation is checked against it, and a
/// dynamic call of the method costs it. `fip-macros` checks nothing (there is no
/// body): the item is emitted unchanged with the `# FIP` section and, under the
/// driver, the same `fip::mark(..)` a hand-written contract carries.
///
/// `param(g = K)` (without `strict = true`) is accepted when `g` is a parameter of
/// the declaration whose type is a function pointer or a callable trait object
/// (`&dyn Fn*`, `&mut dyn Fn*`, `Box<dyn Fn*>`, `&Box<dyn Fn*>`, `&dyn FipFn`):
/// `fip-prelint` checks every implementation with `g` costing `K` and every call
/// through the contract against `K`. Rejected:
///
/// - `param(..)` with `strict = true`: a `#[fip_trait]` certificate
///   (`<dyn Trait>::__fip_strict_..`) carries no parameter bounds;
/// - `strict = true` (and so `panic_macros = ..` and `crate = ..`, which need it)
///   without `#[fip_trait]`: a certificate `__fip_strict_..` belongs to one function
///   body, and a declaration has none;
/// - `requires(..)`: a dynamic call does not check a precondition, so an
///   implementation could not assume it.
fn expand_decl(
    mode: Mode,
    args: Option<&FipArgs>,
    toks: &[TokenTree],
    shape: &FnShape,
    ctx: Option<&ImplCtx>,
) -> Result<(TokenStream, TokenStream), TokenStream> {
    let tag = mode.name();
    let span = Span::call_site();
    if ctx.is_some() {
        return Err(compile_error(
            span,
            "FIP attributes apply only to functions with a body inside an `impl` block",
        ));
    }
    if let Some((sp, why)) = foreign_signal(toks, shape) {
        return Err(compile_error(
            sp,
            &format!(
                "{tag} on a foreign function ({why}): a foreign function has no body to check; certify it with `#[fip_cert(evidence = \"..\")]` or exclude it with `#[fip_exclude]`, under `#[fip_macros::fip_extern]` on the `extern` block"
            ),
        ));
    }
    let mut errors = TokenStream::new();
    if let Some(a) = args {
        if let Some((_, _, sp)) = a.params.first()
            && a.strict
        {
            errors.extend(compile_error(
                *sp,
                &format!(
                    "{tag}: `param(..)` with `strict = true` is not supported on a trait method declaration: a `#[fip_trait]` certificate carries no parameter bounds; declare the contract without `strict = true` (`fip-prelint` checks its `param(..)` at every implementation and every call)"
                ),
            ));
        }
        if !a.strict {
            for (g, _, sp) in &a.params {
                match param_type(shape.params.as_ref(), g) {
                    None => errors.extend(compile_error(
                        *sp,
                        &format!("{tag}: `param({g} = ..)`: `{g}` is not a parameter of `{}`", shape.name),
                    )),
                    Some(t) if !callable_param_type(&t) => errors.extend(compile_error(
                        *sp,
                        &format!(
                            "{tag}: `param({g} = ..)` in a contract needs a parameter of function-pointer or callable trait-object type (`fn(..)`, `&dyn Fn*`, `&Box<dyn Fn*>`, `&dyn FipFn`), whose argument a dynamic call can check"
                        ),
                    )),
                    Some(_) => {}
                }
            }
        }
        if let Some((_, sp)) = &a.requires {
            errors.extend(compile_error(
                *sp,
                &format!(
                    "{tag}: `requires(..)` is not supported on a trait method declaration: a dynamic call of `{}` does not check a precondition, so an implementation could not assume it",
                    shape.name
                ),
            ));
        }
        if a.strict && !a.trait_checked {
            errors.extend(compile_error(
                span,
                &format!(
                    "{tag}: `strict = true` on a trait method declaration requires `#[fip_macros::fip_trait]` on the trait: a certificate (`<dyn Trait>::__fip_strict_..`) must be generated outside the trait"
                ),
            ));
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let mut f = TokenStream::new();
    f.extend(toks[..shape.after_attrs].iter().cloned());
    let strict = args.is_some_and(|a| a.strict);
    f.extend(decl_doc(mode, strict));
    f.extend(prelint_mark(mode, args));
    f.extend(toks[shape.after_attrs..].iter().cloned());
    Ok((TokenStream::new(), f))
}

/// The span of the `fn` keyword of the item.
fn fn_keyword_span(toks: &[TokenTree], shape: &FnShape) -> Option<Span> {
    toks[shape.after_attrs..]
        .iter()
        .find(|t| is_ident(t, "fn"))
        .map(TokenTree::span)
}

/// The error for `strict = true` on a trait method's default body.
fn strict_default_body_error(tag: &str) -> String {
    format!(
        "{tag} strict: `strict = true` on a trait method's default body is not supported: a certificate `__fip_strict_..` belongs to one function body, and `#[fip_impl]` cannot certify a default body its impl block does not contain. Declare the method without a body under `#[fip_macros::fip_trait]` (a strict contract; each implementation is certified by `#[fip_impl]`), or drop `strict = true` (the default body is still checked by `#[fip]`, and by `fip-prelint` against the contract)"
    )
}

/// A token of a bodiless function that rustc accepts only on a foreign function
/// (rejected on a trait method declaration, measured with rustc 1.99.1): a
/// visibility (E0449 in a trait), the `safe` qualifier, or a variadic `...`
/// parameter. A bare `fn f();` carries none of them; then its source file decides:
/// the innermost block around it is an `extern` block ([`context::enclosing`]). If
/// that is not determined, the driver rejects a mark on a foreign function.
fn foreign_signal(toks: &[TokenTree], shape: &FnShape) -> Option<(Span, &'static str)> {
    if let Some(v) = shape.vis.first() {
        return Some((
            v.span(),
            "it has a visibility, which a trait method declaration cannot have",
        ));
    }
    let mut i = shape.after_attrs;
    while let Some(t) = toks.get(i) {
        if is_ident(t, "fn") {
            break;
        }
        if is_ident(t, "safe") {
            return Some((
                t.span(),
                "it has the `safe` qualifier, which a trait method declaration cannot have",
            ));
        }
        i += 1;
    }
    let params: Vec<TokenTree> = shape
        .params
        .as_ref()
        .map(|g| g.stream().into_iter().collect())
        .unwrap_or_default();
    if let Some(w) = params
        .windows(3)
        .find(|w| w.iter().all(|t| is_punct(t, '.')))
    {
        return Some((
            w[0].span(),
            "it has a variadic `...` parameter, which a trait method declaration cannot have",
        ));
    }
    let sp = fn_keyword_span(toks, shape)?;
    (context::enclosing(sp, &shape.name) == context::Enclosing::Extern)
        .then_some((sp, "it is declared in an `extern` block"))
}

/// The `# FIP` doc section of a trait method declaration (a contract).
fn decl_doc(mode: Mode, strict: bool) -> TokenStream {
    let what = match mode {
        Mode::Fip => "no allocation, no free and no recursion".to_string(),
        Mode::FipN(n) => format!("at most {n} allocations per call, no free and no recursion"),
        Mode::Fbip => "no allocation (frees and recursion allowed)".to_string(),
    };
    let mut doc = format!(
        "#[doc = \"\"] #[doc = \"# FIP\"] #[doc = \"\"] #[doc = {:?}] #[doc = \"\"] \
         #[doc = \"Not checked by `fip-macros`, which sees only this declaration. The MIR checker `fip-prelint` checks every implementation (and a default body) against the contract; a dynamic call of the method costs it.\"]",
        format!(
            "Contract `{}` of every implementation: {what}.",
            mode.name()
        )
    );
    if strict {
        doc.push_str(" #[doc = \"\"] #[doc = \"Strict contract: verified against implementations by `fip-prelint`, certified for strict callers through `#[fip_trait]`.\"]");
    }
    doc.parse().unwrap_or_default()
}

/// Names of the parameters in `( .. )`: the last identifier before the first `:` of
/// each parameter (`mut x: T` → `x`, `self`).
fn param_names(params: Option<&Group>) -> Vec<String> {
    let Some(g) = params else {
        return Vec::new();
    };
    split_commas(g.stream())
        .iter()
        .filter_map(|part| {
            let head = part.iter().take_while(|t| !is_punct(t, ':'));
            head.filter_map(|t| match t {
                TokenTree::Ident(i) => Some(i.to_string()),
                _ => None,
            })
            .filter(|n| n != "mut")
            .last()
        })
        .collect()
}

/// The type tokens of the parameter `name` in `( .. )` (after its first `:`),
/// splitting at commas outside `<..>` (a `>` of `->` does not close one).
fn param_type(params: Option<&Group>, name: &str) -> Option<Vec<TokenTree>> {
    let g = params?;
    let mut parts: Vec<Vec<TokenTree>> = vec![Vec::new()];
    let mut depth = 0_i32;
    let mut prev_dash = false;
    for t in g.stream() {
        let dash = is_punct(&t, '-');
        if is_punct(&t, '<') {
            depth += 1;
        } else if is_punct(&t, '>') && !prev_dash {
            depth -= 1;
        }
        prev_dash = dash;
        if depth == 0 && is_punct(&t, ',') {
            parts.push(Vec::new());
        } else if let Some(last) = parts.last_mut() {
            last.push(t);
        }
    }
    parts.into_iter().find_map(|part| {
        let colon = part.iter().position(|t| is_punct(t, ':'))?;
        let own = part[..colon]
            .iter()
            .filter_map(|t| match t {
                TokenTree::Ident(i) if i.to_string() != "mut" => Some(i.to_string()),
                _ => None,
            })
            .next_back()?;
        (own == name).then(|| part[colon + 1..].to_vec())
    })
}

/// `true` if the type tokens `t` are a function pointer (`fn(..)`, `unsafe fn`,
/// `extern ".." fn`) or a callable trait object a dynamic call can pass: `&dyn Tr`,
/// `&mut dyn Tr`, `Box<dyn Tr>`, `&Box<dyn Tr>` with `Tr` one of `Fn`, `FnMut`,
/// `FnOnce`, `FipFn` (the last segment of its path).
fn callable_param_type(t: &[TokenTree]) -> bool {
    let mut i = 0;
    loop {
        match t.get(i) {
            Some(x) if is_punct(x, '&') => i += 1,
            Some(x) if is_punct(x, '\'') => i += 2,
            Some(x) if is_ident(x, "mut") => i += 1,
            _ => break,
        }
    }
    let rest = &t[i.min(t.len())..];
    match rest.first() {
        Some(x) if is_ident(x, "fn") || is_ident(x, "unsafe") || is_ident(x, "extern") => {
            rest.iter().any(|x| is_ident(x, "fn"))
        }
        Some(x) if is_ident(x, "dyn") => {
            let path_end = rest[1..]
                .iter()
                .position(|x| {
                    matches!(x, TokenTree::Group(_)) || is_punct(x, '<') || is_punct(x, '+')
                })
                .map_or(rest.len(), |p| p + 1);
            rest[1..path_end]
                .iter()
                .rev()
                .find_map(|x| match x {
                    TokenTree::Ident(id) => Some(id.to_string()),
                    _ => None,
                })
                .is_some_and(|last| matches!(last.as_str(), "Fn" | "FnMut" | "FnOnce" | "FipFn"))
        }
        _ => {
            // `Box<..>`, possibly by path (`std::boxed::Box<..>`).
            let open = rest.iter().position(|x| is_punct(x, '<'));
            match open {
                Some(o)
                    if o > 0
                        && is_ident(&rest[o - 1], "Box")
                        && rest.last().is_some_and(|x| is_punct(x, '>')) =>
                {
                    let inner = &rest[o + 1..rest.len() - 1];
                    inner.first().is_some_and(|x| is_ident(x, "dyn")) && callable_param_type(inner)
                }
                _ => false,
            }
        }
    }
}

/// `requires(..)`: every name it uses is a parameter, and, when the item carries a
/// `#[verus_spec(..)]` (a Verus build, where `cfg_attr(verus_keep_ghost, ..)` is
/// expanded), every conjunct appears in its `requires` clause, so the precondition
/// `fip-prelint` uses cannot drift from the verified one.
fn check_requires(
    cs: &[fip_lint_rules::requires::Conjunct],
    span: Span,
    shape: &FnShape,
    attrs: &[TokenTree],
) -> TokenStream {
    use fip_lint_rules::requires::{Term, display, from_verus, not_in};
    let mut errors = TokenStream::new();
    let names = param_names(shape.params.as_ref());
    for c in cs {
        for side in [&c.a, &c.b] {
            if let Term::Param(n) | Term::Len(n) | Term::Path(n, _) | Term::PathLen(n, _) =
                &side.term
                && !names.contains(n)
            {
                errors.extend(compile_error(
                    span,
                    &format!(
                        "`requires(..)`: `{n}` is not a parameter of `{}`",
                        shape.name
                    ),
                ));
            }
        }
    }
    for pair in attrs.chunks(2) {
        let [_, TokenTree::Group(g)] = pair else {
            continue;
        };
        let inner: Vec<TokenTree> = g.stream().into_iter().collect();
        if let [TokenTree::Ident(i), TokenTree::Group(spec)] = inner.as_slice()
            && i.to_string() == "verus_spec"
        {
            let verus = from_verus(&spec.stream().to_string());
            for c in not_in(cs, &verus) {
                errors.extend(compile_error(
                    span,
                    &format!(
                        "`requires(..)`: `{}` is not in the `requires` of `verus_spec`; the precondition `fip-prelint` assumes must be the verified one",
                        display(c)
                    ),
                ));
            }
        }
    }
    errors
}

/// Errors of the non-strict checks: allocation sites and direct self-recursion.
fn base_errors(mode: Mode, tag: &str, scan: &Scan<'_>, fn_name: &str) -> TokenStream {
    let mut errors = TokenStream::new();
    match mode {
        Mode::Fip | Mode::Fbip => {
            for s in &scan.sites {
                errors.extend(compile_error(
                    s.span,
                    &format!("{tag}: allocation site {} in the body", s.what),
                ));
            }
        }
        Mode::FipN(n) => {
            for s in scan.sites.iter().filter(|s| s.in_loop) {
                errors.extend(compile_error(
                    s.span,
                    &format!("{tag}: allocation site {} inside a loop body", s.what),
                ));
            }
            let count = u64::try_from(scan.sites.len()).unwrap_or(u64::MAX);
            if count > n
                && let Some(s) = scan.sites.get(usize::try_from(n).unwrap_or(usize::MAX))
            {
                errors.extend(compile_error(
                    s.span,
                    &format!("{tag}: {count} allocation sites, at most {n} allowed"),
                ));
            }
        }
    }
    if mode != Mode::Fbip {
        for sp in &scan.recursion {
            errors.extend(compile_error(
                *sp,
                &format!(
                    "{tag}: direct recursion into `{fn_name}` (stack is not bounded); use #[fbip] or a loop"
                ),
            ));
        }
    }
    errors
}

/// Environment variable the `fip-prelint` driver sets in its own process before it
/// expands any crate. Proc macros run inside the compiler process, so they see it.
const PRELINT_ENV: &str = "FIP_PRELINT_DRIVER";

/// Mark-only mode: set together with [`PRELINT_ENV`] (never honoured alone, so a
/// plain build always runs every check).
const MARK_ONLY_ENV: &str = "FIP_MACROS_MARK_ONLY";

/// `true` when `#[fip]`/`#[fbip]` on a free function emit only the mark (and the
/// argument and `requires(..)` validation): `FIP_MACROS_MARK_ONLY=1` inside the
/// `fip-prelint` driver. The token-level behaviour checks (allocation sites,
/// recursion, the strict rules and certificates) are skipped, so the driver decides
/// alone; `tools/fip-prelint/tests/compile_fail.rs` runs the rejected behaviour
/// examples of this crate's documentation that way. `#[fip_impl]` methods and
/// `fip_fn!` are expanded as usual.
fn mark_only() -> bool {
    std::env::var_os(PRELINT_ENV).is_some()
        && std::env::var_os(MARK_ONLY_ENV).is_some_and(|v| v == "1")
}

/// The `# FIP` doc section in mark-only mode: nothing was checked by the macro.
fn mark_only_doc() -> TokenStream {
    "#[doc = \"\"] #[doc = \"# FIP\"] #[doc = \"\"] #[doc = \"Expanded in mark-only mode: not checked by `fip-macros`; only `fip-prelint` checks this function.\"]"
        .parse()
        .unwrap_or_default()
}

/// The inert `#[cfg_attr(fip_prelint, fip::mark(..))]` read by the MIR checker
/// `fip-prelint` (`tools/fip-prelint`).
///
/// Emitted only when the expanding compiler is the `fip-prelint` driver (it sets
/// [`PRELINT_ENV`] in its own process); plain builds get no extra tokens at all.
/// Emitting it unconditionally would make every downstream crate without
/// `check-cfg = ["cfg(fip_prelint)"]` warn `unexpected_cfgs` (measured, rustc 1.99).
/// Under the driver `--cfg fip_prelint` is set, so the attribute stays.
///
/// Syntax (every key always present, in this order):
///
/// `fip::mark(kind = "fip"|"fbip", n = N, strict = true|false,
/// panic_macros = true|false[, param(name = K, ..)])`
///
/// `n` is the declared allocation bound (`#[fip]` and `#[fbip]`: 0, `#[fip(N)]`: N);
/// `param(..)` repeats the declared parameter bounds (of strict functions, and of
/// trait method declarations: a contract's callable parameters).
/// With `requires(..)` a second attribute follows:
/// `#[cfg_attr(fip_prelint, fip::requires(..))]` (normalised conjuncts).
fn prelint_mark(mode: Mode, args: Option<&FipArgs>) -> TokenStream {
    if std::env::var_os(PRELINT_ENV).is_none() {
        return TokenStream::new();
    }
    let (kind, n) = match mode {
        Mode::Fip => ("fip", 0),
        Mode::FipN(n) => ("fip", n),
        Mode::Fbip => ("fbip", 0),
    };
    let strict = args.is_some_and(|a| a.strict);
    let panic_macros = args.is_none_or(|a| a.panic_macros);
    let mut parts = vec![
        format!("kind = \"{kind}\""),
        format!("n = {n}"),
        format!("strict = {strict}"),
        format!("panic_macros = {panic_macros}"),
    ];
    if let Some(a) = args
        && !a.params.is_empty()
    {
        let decls: Vec<String> = a
            .params
            .iter()
            .map(|(p, k, _)| format!("{p} = {k}"))
            .collect();
        parts.push(format!("param({})", decls.join(", ")));
    }
    let mut out = format!("#[cfg_attr(fip_prelint, fip::mark({}))]", parts.join(", "));
    if let Some((cs, _)) = args.and_then(|a| a.requires.as_ref()) {
        out += "#[cfg_attr(fip_prelint, fip::requires(";
        out += &fip_lint_rules::requires::display_all(cs);
        out += "))]";
    }
    out.parse().unwrap_or_default()
}

/// The `# FIP` doc section stating what was checked.
fn fip_doc(mode: Mode, strict: bool) -> TokenStream {
    let note = match mode {
        Mode::Fip => "declared `fip`: no allocation site and no direct self-recursion in the body",
        Mode::FipN(_) => {
            "declared `fip(N)`: at most N allocation sites, none in a loop, and no direct self-recursion in the body"
        }
        Mode::Fbip => {
            "declared `fbip`: no allocation site in the body (frees and recursion allowed)"
        }
    };
    let suffix = if let Mode::FipN(n) = mode {
        format!(" (N = {n}).")
    } else {
        ".".to_string()
    };
    let doc = format!(
        "#[doc = \"\"] #[doc = \"# FIP\"] #[doc = \"\"] #[doc = {:?}] #[doc = \"\"] \
         #[doc = \"Checked syntactically by `fip-macros`; this is a lint, not a proof. \
         Allocation behaviour is checked by `fip-testkit` tests.\"]",
        format!("{note}{suffix}")
    );
    let mut doc: TokenStream = doc.parse().unwrap_or_default();
    if strict {
        doc.extend(
            "#[doc = \"\"] #[doc = \"Strict: calls only certified functions (`fip_strict::Cert`) and the audited `core` table; the total allocation bound is checked at compile time.\"]"
                .parse::<TokenStream>()
                .unwrap_or_default(),
        );
    }
    doc
}

/// Names of the type parameters in a generic parameter list `<..>` (lifetimes and
/// const parameters left out), split at top-level commas only.
fn generic_type_params(generics: &[TokenTree]) -> Vec<String> {
    let mut names = Vec::new();
    if generics.len() < 2 {
        return names;
    }
    let inner = &generics[1..generics.len() - 1];
    let mut depth = 0_i32;
    let mut at_start = true;
    for (k, t) in inner.iter().enumerate() {
        let arrow = k > 0 && is_punct(&inner[k - 1], '-');
        if is_punct(t, '<') {
            depth += 1;
        } else if is_punct(t, '>') && !arrow {
            depth -= 1;
        } else if is_punct(t, ',') && depth == 0 {
            at_start = true;
            continue;
        }
        if at_start {
            if let TokenTree::Ident(id) = t
                && id.to_string() != "const"
                && !(k > 0 && is_punct(&inner[k - 1], '\''))
            {
                names.push(id.to_string());
            }
            at_start = false;
        }
    }
    names
}

/// Runs the strict checks on a function body; errors are appended to `errors`.
/// Returns the scan and the body as emitted (see `strict::StrictScan::stream`).
fn run_strict_scan(
    args: &FipArgs,
    shape: &FnShape,
    body: &Group,
    tag: &str,
    ctx: Option<&ImplCtx>,
    errors: &mut TokenStream,
) -> (strict::StrictScan, TokenStream) {
    let (param_traits, type_bounds) = extract_param_traits(shape.params.as_ref(), &shape.generics);
    let mut generic_params = generic_type_params(&shape.generics);
    if let Some(c) = ctx {
        generic_params.extend(c.params.iter().filter(|p| !p.starts_with('\'')).cloned());
    }
    let mut shadowed = Vec::new();
    if let Some(g) = &shape.params {
        for part in split_commas(g.stream()) {
            let pat: TokenStream = part
                .iter()
                .take_while(|t| !is_punct(t, ':'))
                .cloned()
                .collect();
            strict::bound_names(pat, &mut shadowed);
        }
    }
    strict::bound_names(body.stream(), &mut shadowed);
    let mut ss = strict::StrictScan {
        self_ty: ctx.map(|c| c.self_ty.clone()),
        impl_trait: ctx.and_then(|c| c.trait_name.clone()),
        no_panic_macros: !args.panic_macros,
        krate: args.krate.clone(),
        param_traits,
        type_bounds,
        generic_params,
        shadowed,
        ffi: args.ffi.clone(),
        ffi_used: vec![false; args.ffi.len()],
        keep_tokens: strict::under_verus(),
        std_roots: strict::std_roots_used(body.stream()),
        ..strict::StrictScan::default()
    };
    let types = param_types(shape.params.as_ref());
    for (name, k, sp) in &args.params {
        let mentioned = shape
            .params
            .as_ref()
            .is_some_and(|g| g.stream().into_iter().any(|t| is_ident(&t, name)));
        if !mentioned {
            errors.extend(compile_error(
                *sp,
                &format!("`{name}` is not a parameter of this function"),
            ));
        }
        let ty = types
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, t)| t.clone());
        ss.params.push(strict::Param {
            name: name.clone(),
            ty,
            bound: Some(*k),
        });
    }
    let mut callable: Vec<String> = args.params.iter().map(|(n, _, _)| n.clone()).collect();
    callable.extend(ss.param_traits.iter().map(|(n, _)| n.clone()));
    ss.errors
        .extend(strict::rebinding_errors(body.stream(), &callable));
    let emitted = ss.stream(body.stream(), false);
    ss.check_params();
    for (m, used) in ss.ffi.iter().zip(&ss.ffi_used) {
        if !used {
            ss.errors.push((
                m.span,
                format!(
                    "`ffi({} = ..)`: the body has no call of `{}` written with this path",
                    m.dep_key, m.dep_key
                ),
            ));
        }
    }
    for (sp, msg) in &ss.errors {
        errors.extend(compile_error(*sp, &format!("{tag} strict: {msg}")));
    }
    (ss, emitted)
}

/// Certificates for the strict methods of an `impl` block.
///
/// Inside `#[fip_impl]`, every method marked `#[fip(strict = true)]` (or
/// `#[fip(N, strict = true)]`) is checked like a strict function, and its certificate
/// is emitted **before the `impl` block**, at module level:
///
/// | impl | certificate | strict callers write |
/// |---|---|---|
/// | `impl Type { fn m }`, `impl<T> Type<T> { fn m }` | `__fip_strict_Type__m` | `Type::m(..)`, `<Type<..>>::m(..)`, `Self::m(..)` |
/// | `impl Trait for Type { fn m }` | `__fip_strict_Type__Trait__m` | `<Type as Trait>::m(..)`, `<Self as Trait>::m(..)` |
///
/// A module-level constant needs no type arguments, so methods of generic types are
/// callable from strict code, and trait impls (which cannot gain items) get
/// certificates too. Callers in other modules name the type by a path
/// (`a::Type::m(..)` reads `a::__fip_strict_Type__m`) or import the certificate
/// together with the type.
///
/// Rejected, because the certificate would not identify one method:
///
/// - bounds on the impl's parameters and `where` clauses (a bounded impl does not
///   cover every instantiation, so another impl could define a method of the same
///   name for other type arguments); put bounds on the methods instead;
/// - a self type whose arguments are not exactly the impl's parameters
///   (`impl Foo<u8>`), or that is a parameter (`impl<T> Tr for T`) or not a named
///   path (`&Foo`, tuples);
/// - generic traits (`impl Tr<u8> for Foo`).
///
/// A trait method is reached only through `<Type as Trait>::m`: `Type::m` would pick
/// an inherent method of the same name first.
///
/// `#[fip_impl(crate = path::to::fip_strict)]` sets the path of the `fip_strict` crate
/// (see `crate = ..` in the crate documentation) for every strict method of the block
/// that does not set its own. Strict methods are recognised by any attribute path
/// ending in `fip` (`#[fip(..)]`, `#[fip_macros::fip(..)]`, `#[my_facade::fip(..)]`);
/// the attribute is consumed (not re-emitted on the method).
///
/// **Traits with strict contracts** (`#[fip_trait]` on an `unsafe trait`):
/// `#[fip_impl(contract)]` on `impl Trait for Type` checks every contracted method of
/// `<dyn Trait>::__FIP_CONTRACTED` is a strict method of the block whose certificate
/// is at most as weak as the contract (allocations, `panic_macros = false`), and emits
/// the block as `unsafe impl`; on a hand-written `unsafe impl`, its strict methods are
/// compared the same way. A plain `impl` is not compared (the trait may have no
/// contract or not be dyn-compatible). For every trait impl with a strict method the
/// block also emits `__fip_traitid_<Type>__<Trait>` / `__fip_traitsup_<Type>__<Trait>`,
/// against which a strict caller of `<Type as path::Trait>::m` checks that its trait
/// is this block's. Inside a trait impl, call another method of the trait as
/// `<Self as Trait>::m(self, ..)` (not `self.m()`).
///
/// ```
/// use fip_macros::{fip, fip_impl};
/// pub struct Cell<T> { v: T }
/// #[fip_impl]
/// impl<T> Cell<T> {
///     #[fip(strict = true)]
///     pub fn put(&mut self, v: T) -> T { ::core::mem::replace(&mut self.v, v) }
/// }
/// #[fip(strict = true)]
/// fn put_twice(c: &mut Cell<u8>) -> u8 { Cell::put(c, 1); Cell::put(c, 2) }
/// # fn main() { let mut c = Cell { v: 0 }; assert_eq!(put_twice(&mut c), 1); }
/// ```
#[proc_macro_attribute]
pub fn fip_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut krate = None;
    let mut contract = false;
    for part in split_commas(attr) {
        match part.as_slice() {
            [TokenTree::Ident(key), eq, rest @ ..]
                if key.to_string() == "crate" && is_punct(eq, '=') && krate.is_none() =>
            {
                match parse_krate(key.span(), rest) {
                    Ok(k) => krate = Some(k),
                    Err((span, msg)) => {
                        let mut out = compile_error(span, &format!("#[fip_impl]: {msg}"));
                        out.extend(strip_fip_attrs(item));
                        return out;
                    }
                }
            }
            [TokenTree::Ident(key)] if key.to_string() == "contract" && !contract => {
                contract = true;
            }
            _ => {
                let mut out = compile_error(
                    part.first().map_or_else(Span::call_site, TokenTree::span),
                    &format!("#[fip_impl]: {FIP_IMPL_ARGS_IMPL}"),
                );
                out.extend(strip_fip_attrs(item));
                return out;
            }
        }
    }
    match fip_impl_inner(&item, krate.as_ref(), contract) {
        Ok(out) => out,
        Err((span, msg)) => {
            let mut out = compile_error(span, &format!("#[fip_impl]: {msg}"));
            out.extend(strip_fip_attrs(item));
            out
        }
    }
}
/// Certificates for the strict contracts of a trait.
///
/// Inside `#[fip_trait]`, every method declaration marked `#[fip(strict = true)]`
/// (or `#[fip(N, strict = true)]`) declares a strict contract, and its certificate
/// is emitted as `<dyn Trait>::__fip_strict_<m>` and `__fip_strict_<Trait>__<m>`, with
/// the list of contracted methods `<dyn Trait>::__FIP_CONTRACTED` (one inherent
/// `impl dyn Trait` block):
///
/// | item | certificate | strict callers write |
/// |---|---|---|
/// | `unsafe trait Trait { fn m }` | `__fip_strict_Trait__m` | `x.m()` on `x: &dyn Trait` or `x: &T` with `T: Trait`, `T::m(x)`, `<T as Trait>::m(x)`, `<dyn Trait>::m(x)` |
///
/// A trait with a strict contract must be an `unsafe trait`: a strict caller pays the
/// contract whatever implementation runs, so each implementation is an `unsafe impl`
/// (the user's claim) or is checked by `#[fip_impl(contract)]`. Methods without
/// `strict = true` (driver contracts) need no `unsafe trait`.
///
/// `#[fip_trait(crate = path::to::fip_strict)]` sets the path of the `fip_strict` crate.
#[proc_macro_attribute]
pub fn fip_trait(attr: TokenStream, item: TokenStream) -> TokenStream {
    let krate = match split_commas(attr).as_slice() {
        [] => Ok(None),
        [part] => match part.as_slice() {
            [TokenTree::Ident(key), eq, rest @ ..]
                if key.to_string() == "crate" && is_punct(eq, '=') =>
            {
                parse_krate(key.span(), rest).map(Some)
            }
            _ => Err((
                part.first().map_or_else(Span::call_site, TokenTree::span),
                FIP_IMPL_ARGS.to_string(),
            )),
        },
        [_, second, ..] => Err((
            second.first().map_or_else(Span::call_site, TokenTree::span),
            FIP_IMPL_ARGS.to_string(),
        )),
    };
    let krate = match krate {
        Ok(k) => k,
        Err((span, msg)) => {
            return compile_error(span, &format!("#[fip_trait]: {msg}"));
        }
    };
    match fip_trait_inner(&item, krate.as_ref()) {
        Ok(out) => out,
        Err((span, msg)) => compile_error(span, &format!("#[fip_trait]: {msg}")),
    }
}

struct TraitHeader {
    vis: Vec<TokenTree>,
    trait_name: Ident,
    /// `unsafe trait`: required when the trait declares a strict contract.
    is_unsafe: bool,
}

fn parse_trait_header(toks: &[TokenTree]) -> Result<TraitHeader, (Span, String)> {
    let first = toks.first().map_or_else(Span::call_site, TokenTree::span);
    let not_trait = || (first, "expected a `trait` declaration".to_string());
    let mut pos = 0;
    while pos + 1 < toks.len()
        && is_punct(&toks[pos], '#')
        && is_group(&toks[pos + 1], Delimiter::Bracket)
    {
        pos += 2;
    }
    let after_attrs = pos;
    if pos < toks.len() && is_ident(&toks[pos], "pub") {
        pos += 1;
        if pos < toks.len() && is_group(&toks[pos], Delimiter::Parenthesis) {
            pos += 1;
        }
    }
    let vis = toks[after_attrs..pos].to_vec();
    let is_unsafe = toks.get(pos).is_some_and(|t| is_ident(t, "unsafe"));
    if is_unsafe {
        pos += 1;
    }
    if !toks.get(pos).is_some_and(|t| is_ident(t, "trait")) {
        return Err(not_trait());
    }
    pos += 1;
    let Some(TokenTree::Ident(trait_name)) = toks.get(pos) else {
        return Err(not_trait());
    };
    if toks.get(pos + 1).is_some_and(|t| is_punct(t, '<')) {
        let sp = toks[pos + 1].span();
        return Err((
            sp,
            "generic traits (`trait Tr<..>`) are not supported for `#[fip_trait]`".to_string(),
        ));
    }
    Ok(TraitHeader {
        vis,
        trait_name: trait_name.clone(),
        is_unsafe,
    })
}

/// The contract certificate of one strict method declaration: the constant of the
/// `impl dyn Trait` block (`__fip_strict_<m>`, without the block) and the
/// module-level `__fip_strict_<Trait>__<m>`.
fn emit_trait_method_cert(
    trait_name: &Ident,
    vis: &[TokenTree],
    shape: &FnShape,
    args: &FipArgs,
) -> Result<(TokenStream, TokenStream), (Span, String)> {
    if !shape.generics.is_empty() {
        let sp = shape
            .generics
            .first()
            .map_or_else(Span::call_site, TokenTree::span);
        return Err((
            sp,
            "generic trait methods (`fn m<..>(..)`) are not supported for strict contracts under `#[fip_trait]`".to_string(),
        ));
    }
    let t = strict::bare(&trait_name.to_string()).to_string();
    let m = strict::bare(&shape.name).to_string();
    for seg in [&t, &m] {
        if let Some(e) = strict::segment_error(seg) {
            return Err((trait_name.span(), e));
        }
    }
    let n = match args.mode {
        Mode::FipN(n) => n,
        Mode::Fip | Mode::Fbip => 0,
    };
    let krate = args.krate.clone().unwrap_or_else(strict::default_krate);
    let assume = if args.panic_macros {
        "assume"
    } else {
        "assume_no_panic_macros"
    };
    let attrs = "#[doc(hidden)] #[allow(non_upper_case_globals, non_snake_case, dead_code, clippy::all, clippy::pedantic)]";
    let in_dyn = format!(
        "{attrs} pub const __fip_strict_{m}: __FIP_KRATE__::Cert = unsafe {{ __FIP_KRATE__::Cert::{assume}({:?}, {n}u64) }};",
        format!("{t}__{m}")
    );
    let tr = TokenStream::from(TokenTree::Ident(trait_name.clone()));
    let vis: TokenStream = vis.iter().cloned().collect();
    let module = format!(
        "{attrs} __FIP_VIS__ const __fip_strict_{t}__{m}: __FIP_KRATE__::Cert = <dyn __FIP_TRAIT__>::__fip_strict_{m};"
    );
    let sub = [
        ("__FIP_KRATE__", &krate),
        ("__FIP_TRAIT__", &tr),
        ("__FIP_VIS__", &vis),
    ];
    Ok((subst(ts_of(&in_dyn), &sub), subst(ts_of(&module), &sub)))
}

fn mark_trait_method(item_toks: &[TokenTree], at: usize) -> Vec<TokenTree> {
    let mut out = item_toks.to_vec();
    if at + 1 < out.len()
        && let TokenTree::Group(attr_group) = &out[at + 1]
    {
        let inner: Vec<TokenTree> = attr_group.stream().into_iter().collect();
        if let Some((TokenTree::Group(arg_group), path)) = inner.split_last()
            && arg_group.delimiter() == Delimiter::Parenthesis
        {
            let mut new_args = arg_group.stream();
            if let Ok(marker) = ", __fip_trait_checked".parse::<TokenStream>() {
                new_args.extend(marker);
            }
            let mut new_arg_group = Group::new(Delimiter::Parenthesis, new_args);
            new_arg_group.set_span(arg_group.span());
            let mut new_inner: TokenStream = path.iter().cloned().collect();
            new_inner.extend([TokenTree::Group(new_arg_group)]);
            let mut new_attr = Group::new(Delimiter::Bracket, new_inner);
            new_attr.set_span(attr_group.span());
            out[at + 1] = TokenTree::Group(new_attr);
        }
    }
    out
}

fn fip_trait_inner(
    item: &TokenStream,
    krate: Option<&TokenStream>,
) -> Result<TokenStream, (Span, String)> {
    let toks: Vec<TokenTree> = item.clone().into_iter().collect();
    let first = toks.first().map_or_else(Span::call_site, TokenTree::span);
    let not_trait = || (first, "expected a `trait` declaration".to_string());
    let header = parse_trait_header(&toks)?;
    let Some(TokenTree::Group(body)) = toks.last() else {
        return Err(not_trait());
    };
    if body.delimiter() != Delimiter::Brace {
        return Err(not_trait());
    }
    let mut module_items = TokenStream::new();
    let mut dyn_items = TokenStream::new();
    let mut contracted: Vec<String> = Vec::new();
    let mut new_body = TokenStream::new();
    let body_toks: Vec<TokenTree> = body.stream().into_iter().collect();
    let mut next = 0;
    while next < body_toks.len() {
        let start = next;
        let mut end = next;
        while end < body_toks.len() {
            let t = &body_toks[end];
            if is_punct(t, '#')
                && body_toks
                    .get(end + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Bracket))
            {
                end += 2;
                continue;
            }
            end += 1;
            if is_punct(t, ';') || is_group(t, Delimiter::Brace) {
                break;
            }
        }
        next = end;
        let item_toks = &body_toks[start..end];
        let mut strict_attr = None;
        let mut at = 0;
        while at + 1 < item_toks.len() && is_punct(&item_toks[at], '#') {
            if let TokenTree::Group(g) = &item_toks[at + 1]
                && let Some(args) = fip_attr_args(g)
            {
                let mut parsed = parse_fip_args(args)?;
                if parsed.krate.is_none() {
                    parsed.krate = krate.cloned();
                }
                if parsed.strict {
                    strict_attr = Some((at, parsed));
                    break;
                }
            }
            at += 2;
        }
        let Some((at, args)) = strict_attr else {
            new_body.extend(item_toks.iter().cloned());
            continue;
        };
        let shape = parse_fn(item_toks)?;
        if let Some(body) = &shape.body {
            return Err((body.span(), strict_default_body_error(&args.mode.name())));
        }
        if !header.is_unsafe {
            return Err((
                header.trait_name.span(),
                format!(
                    "a trait with a strict contract must be an `unsafe trait`: strict callers of `{}` pay the contract, and an implementation the macros do not check (one without `#[fip_impl(contract)]`) is trusted to keep it, so it must be written `unsafe impl`",
                    shape.name
                ),
            ));
        }
        let (in_dyn, module) =
            emit_trait_method_cert(&header.trait_name, &header.vis, &shape, &args)?;
        dyn_items.extend(in_dyn);
        module_items.extend(module);
        contracted.push(strict::bare(&shape.name).to_string());
        new_body.extend(mark_trait_method(item_toks, at));
    }
    if !contracted.is_empty() {
        // One inherent block on `dyn Trait`: the contracts and the list of contracted
        // methods `#[fip_impl(contract)]` checks an implementation against.
        let names: Vec<String> = contracted.iter().map(|m| format!("{m:?}")).collect();
        let list = format!(
            "#[doc(hidden)] #[allow(non_upper_case_globals, clippy::all, clippy::pedantic)] pub const __FIP_CONTRACTED: &'static [&'static str] = &[{}];",
            names.join(", ")
        );
        dyn_items.extend(ts_of(&list));
        let tr = TokenStream::from(TokenTree::Ident(header.trait_name.clone()));
        let mut block = subst(
            ts_of("#[doc(hidden)] #[allow(clippy::all, clippy::pedantic)] impl dyn __FIP_TRAIT__"),
            &[("__FIP_TRAIT__", &tr)],
        );
        block.extend([TokenTree::Group(Group::new(Delimiter::Brace, dyn_items))]);
        module_items.extend(block);
    }
    let mut new_trait_toks = toks[..toks.len() - 1].to_vec();
    let mut g = Group::new(Delimiter::Brace, new_body);
    g.set_span(body.span());
    new_trait_toks.push(TokenTree::Group(g));
    let mut out = module_items;
    out.extend(new_trait_toks);
    Ok(out)
}
/// Marks a foreign function as excluded from FIP aggregation.
///
/// Calls to an excluded function contribute no events to FIP. This represents a
/// user assumption that the function satisfies the relevant FIP properties.
/// Excluded foreign functions are counted and listed in the crate summary and
/// cannot be called from strict code (no certificate is generated).
#[proc_macro_attribute]
pub fn fip_exclude(attr: TokenStream, item: TokenStream) -> TokenStream {
    let toks: Vec<TokenTree> = item.clone().into_iter().collect();
    if let Ok(shape) = parse_fn(&toks)
        && shape.body.is_some()
    {
        return compile_error(
            toks.first().map_or_else(Span::call_site, TokenTree::span),
            "#[fip_exclude] applies to foreign functions in `extern` blocks",
        );
    }
    let reason = match parse_exclude_attr(attr) {
        Ok(r) => r,
        Err((sp, msg)) => return compile_error(sp, &format!("#[fip_exclude]: {msg}")),
    };
    let doc = "#[doc = \"\"] #[doc = \"# FIP\"] #[doc = \"\"] #[doc = \"Excluded from FIP aggregation (`fip-prelint`). Calls contribute no events (user assumption).\"] #[allow(dead_code)]";
    let mut out = doc.parse::<TokenStream>().unwrap_or_default();
    out.extend(exclude_mark(reason.as_ref()));
    out.extend(item);
    out
}

/// Standalone certificate attribute: instructs the user to place `#[fip_extern]`
/// on the enclosing `extern` block.
#[proc_macro_attribute]
pub fn fip_cert(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let sp = item
        .clone()
        .into_iter()
        .next()
        .map_or_else(Span::call_site, |t| t.span());
    let mut out = compile_error(
        sp,
        "#[fip_cert] cannot emit a certificate from inside an `extern` block: put `#[fip_extern]` on the enclosing `extern` block",
    );
    out.extend(item);
    out
}

/// Certifies and excludes foreign functions in an `extern` block.
///
/// The block must be `unsafe extern` (also in edition 2021): its certificates are
/// trusted claims about foreign code, so it carries a visible `unsafe`. The driver
/// marks (`fip::cert`, `fip::exclude`) are emitted only under `fip-prelint`, with the
/// `evidence` / `reason` literal as written.
///
/// Inside `#[fip_extern]`, foreign function declarations can be:
/// - certified: `#[fip_cert(evidence = "..", allocs = N)]` or `#[fip(evidence = "..")]`
///   (requires non-empty `evidence = ".."`, emits `<vis> const __fip_strict_<name>: Cert`
///   outside the block for strict callers and a driver mark for `fip-prelint`); with
///   `frees = true` or `kind = "fbip"` only the driver mark (a `Cert` promises no
///   deallocation, so strict code cannot call it);
/// - excluded: `#[fip_exclude]` (optionally with `reason = ".."`), removing calls
///   from FIP aggregation (counted and listed in the crate summary);
/// - allocator sources: `#[fip::alloc_source]` / `#[fip::free_source]` (or in the foreign
///   allocation table);
/// - unannotated: reachable calls will produce a specific error in `fip-prelint`.
///
/// `fip-prelint` matches certificates and exclusions by **link symbol**
/// (`#[link_name = ".."]`, else the item's name) and ABI, not by declaration: a mark
/// here covers every declaration of the same symbol with the same ABI reachable from
/// the analysed crates, including those in `std`, `libc` or any other dependency
/// (each such match is listed in the crate summary). Certified and excluded for one
/// symbol anywhere, two certificates of one symbol with different properties, and a
/// marked declaration whose ABI differs from the called one are errors. Marked items
/// get `#[allow(dead_code)]`: a declaration may exist only to carry the mark. The
/// emitted `__fip_strict_<name>` certificate is still found only through this
/// declaration's path, so a strict caller calls this declaration, not the
/// dependency's, or maps the dependency's path to it with
/// `#[fip(strict = true, ffi(dep::sym = local::sym, ..))]`.
///
/// **`ffi(dep::sym = local::sym)`.** Strict calls of `dep::sym` written with exactly
/// this path read the certificate of `local::sym` (`local::__fip_strict_sym`, its name
/// checked by `Cert::allocs_for`). Under `cargo fip-prelint` the attribute also emits
/// a hidden check function naming both (`fip::ffi_map`), and the driver reports a pair
/// whose link symbols or ABIs differ. **Trust without the driver:** the mapping is
/// unchecked; the only compile-time check is the certificate's name, so a mapping to
/// a `#[fip_extern]` declaration of another symbol compiles and its bound is used for
/// `dep::sym`. Rejected: a left side without a module path (a function in scope by
/// its bare name has its own certificate), a path mapped twice or to itself, generic
/// arguments, and a mapping no call of the body uses.
///
/// ```
/// mod dep {
///     // A dependency's declaration without FIP marks.
///     unsafe extern "C" { pub fn labs(x: core::ffi::c_long) -> core::ffi::c_long; }
/// }
/// mod sys {
///     #[fip_macros::fip_extern]
///     unsafe extern "C" {
///         #[fip_cert(evidence = "C standard 7.24.6.1: computes a value", allocs = 0)]
///         pub fn labs(x: core::ffi::c_long) -> core::ffi::c_long;
///     }
/// }
/// #[fip_macros::fip(strict = true, ffi(dep::labs = sys::labs))]
/// fn abs_of(x: core::ffi::c_long) -> core::ffi::c_long { unsafe { dep::labs(x) } }
/// # fn main() { assert_eq!(abs_of(-3), 3); }
/// ```
///
/// ```
/// // A dependency (here `std`, as `std::sys::..::errno_location`) declares
/// // `__errno_location` without FIP marks; this declaration excludes the symbol.
/// #[fip_macros::fip_extern]
/// unsafe extern "C" {
///     #[fip_exclude(reason = "returns the address of the thread's errno")]
///     #[link_name = "__errno_location"]
///     fn errno_location() -> *mut core::ffi::c_int;
/// }
/// ```
///
/// `#[fip_extern(crate = path::to::fip_strict)]` sets the path of the `fip_strict` crate.
#[proc_macro_attribute]
pub fn fip_extern(attr: TokenStream, item: TokenStream) -> TokenStream {
    let krate = match split_commas(attr).as_slice() {
        [] => Ok(None),
        [part] => match part.as_slice() {
            [TokenTree::Ident(key), eq, rest @ ..]
                if key.to_string() == "crate" && is_punct(eq, '=') =>
            {
                parse_krate(key.span(), rest).map(Some)
            }
            _ => Err((
                part.first().map_or_else(Span::call_site, TokenTree::span),
                FIP_IMPL_ARGS.to_string(),
            )),
        },
        [_, second, ..] => Err((
            second.first().map_or_else(Span::call_site, TokenTree::span),
            FIP_IMPL_ARGS.to_string(),
        )),
    };
    let krate = match krate {
        Ok(k) => k,
        Err((span, msg)) => return compile_error(span, &format!("#[fip_extern]: {msg}")),
    };
    match fip_extern_inner(&item, krate.as_ref()) {
        Ok(out) => out,
        Err((span, msg)) => compile_error(span, &format!("#[fip_extern]: {msg}")),
    }
}

struct FfiCertArgs {
    kind: String,
    allocs: u64,
    frees: bool,
    evidence: String,
    /// The `evidence = ".."` literal as written, re-emitted unchanged in the driver
    /// mark (so its escapes are not escaped again).
    evidence_lit: Literal,
    krate: Option<TokenStream>,
}

/// `#[cfg_attr(fip_prelint, fip::exclude(..))]`, emitted only under the driver
/// (like [`prelint_mark`]: elsewhere `fip_prelint` is an undeclared cfg, an
/// `unexpected_cfgs` warning in every consumer). `reason` is the literal as written.
fn exclude_mark(reason: Option<&Literal>) -> TokenStream {
    if std::env::var_os(PRELINT_ENV).is_none() {
        return TokenStream::new();
    }
    let src = if reason.is_some() {
        "#[cfg_attr(fip_prelint, fip::exclude(reason = __FIP_REASON__))]"
    } else {
        "#[cfg_attr(fip_prelint, fip::exclude)]"
    };
    let lit = reason.map_or_else(TokenStream::new, |l| {
        TokenStream::from(TokenTree::Literal(l.clone()))
    });
    subst(ts_of(src), &[("__FIP_REASON__", &lit)])
}

fn parse_exclude_attr(attr: TokenStream) -> Result<Option<Literal>, (Span, String)> {
    let parts = split_commas(attr);
    if parts.is_empty() {
        return Ok(None);
    }
    match parts.as_slice() {
        [] => Ok(None),
        [part] => match part.as_slice() {
            [TokenTree::Ident(key), eq, TokenTree::Literal(l)]
                if key.to_string() == "reason"
                    && is_punct(eq, '=')
                    && l.to_string().starts_with('"') =>
            {
                Ok(Some(l.clone()))
            }
            _ => Err((
                part.first().map_or_else(Span::call_site, TokenTree::span),
                "expected `reason = \"..\"` in `#[fip_exclude(..)]`".to_string(),
            )),
        },
        [_, second, ..] => Err((
            second.first().map_or_else(Span::call_site, TokenTree::span),
            "expected at most one argument `reason = \"..\"` in `#[fip_exclude(..)]`".to_string(),
        )),
    }
}
fn parse_cert_kind(s: &str, span: Span) -> Result<(String, bool), (Span, String)> {
    let s = s
        .strip_prefix('"')
        .and_then(|x| x.strip_suffix('"'))
        .unwrap_or(s);
    if s != "fip" && s != "fbip" {
        return Err((span, "`kind` must be \"fip\" or \"fbip\"".to_string()));
    }
    Ok((s.to_string(), s == "fbip"))
}

fn parse_ffi_cert_args(attr_name: &str, attr: TokenStream) -> Result<FfiCertArgs, (Span, String)> {
    let mut kind = if attr_name == "fbip" {
        "fbip".to_string()
    } else {
        "fip".to_string()
    };
    let mut allocs = 0u64;
    let mut frees = kind == "fbip";
    let mut evidence = None;
    let mut evidence_lit = None;
    let mut krate = None;
    for (k, part) in split_commas(attr).into_iter().enumerate() {
        let sp = part.first().map_or_else(Span::call_site, TokenTree::span);
        match part.as_slice() {
            [lit] if k == 0 && int_literal(lit).is_some() => {
                allocs = int_literal(lit).unwrap_or(0);
            }
            [TokenTree::Ident(key), eq, TokenTree::Literal(l)]
                if key.to_string() == "evidence" && is_punct(eq, '=') =>
            {
                let s = l.to_string();
                let ev = s
                    .strip_prefix('"')
                    .and_then(|x| x.strip_suffix('"'))
                    .unwrap_or(&s);
                if ev.trim().is_empty() {
                    return Err((
                        l.span(),
                        "`evidence` must be a non-empty string reference to the proof or audit"
                            .to_string(),
                    ));
                }
                if !s.starts_with('"') {
                    return Err((
                        l.span(),
                        "`evidence` must be a plain string literal `\"..\"`".to_string(),
                    ));
                }
                evidence = Some(ev.to_string());
                evidence_lit = Some(l.clone());
            }
            [TokenTree::Ident(key), eq, lit]
                if (key.to_string() == "allocs" || key.to_string() == "n")
                    && is_punct(eq, '=')
                    && int_literal(lit).is_some() =>
            {
                allocs = int_literal(lit).unwrap_or(0);
            }
            [TokenTree::Ident(key), eq, val] if key.to_string() == "kind" && is_punct(eq, '=') => {
                let (k, f) = parse_cert_kind(&val.to_string(), val.span())?;
                kind = k;
                if f {
                    frees = true;
                }
            }
            [TokenTree::Ident(key), eq, TokenTree::Ident(v)]
                if key.to_string() == "frees" && is_punct(eq, '=') =>
            {
                frees = match v.to_string().as_str() {
                    "true" => true,
                    "false" => false,
                    _ => return Err((v.span(), "`frees` takes `true` or `false`".to_string())),
                };
            }
            [TokenTree::Ident(key), eq, rest @ ..]
                if key.to_string() == "crate" && is_punct(eq, '=') && krate.is_none() =>
            {
                krate = Some(parse_krate(key.span(), rest)?);
            }
            _ => {
                return Err((
                    sp,
                    "expected `evidence = \"..\"`, optionally with `allocs = N`, `kind = \"fip\"|\"fbip\"`, `frees = true|false`, `crate = ..`".to_string(),
                ));
            }
        }
    }
    let (Some(evidence), Some(evidence_lit)) = (evidence, evidence_lit) else {
        return Err((
            Span::call_site(),
            "`evidence = \"..\"` is required to certify a foreign function (reference the proof or audit)".to_string(),
        ));
    };
    Ok(FfiCertArgs {
        kind,
        allocs,
        frees,
        evidence,
        evidence_lit,
        krate,
    })
}

fn parse_extern_header(toks: &[TokenTree]) -> Result<usize, (Span, String)> {
    let first = toks.first().map_or_else(Span::call_site, TokenTree::span);
    let not_extern = || (first, "expected an `extern` block".to_string());
    let mut pos = 0;
    while pos + 1 < toks.len()
        && is_punct(&toks[pos], '#')
        && is_group(&toks[pos + 1], Delimiter::Bracket)
    {
        pos += 2;
    }
    // `unsafe extern`: the certificates are claims about foreign code, so the block
    // carries the `unsafe` the user wrote (in edition 2021 a plain `extern` block is
    // accepted by rustc and not linted by `unsafe_code`).
    if !toks.get(pos).is_some_and(|t| is_ident(t, "unsafe")) {
        if toks.get(pos).is_some_and(|t| is_ident(t, "extern")) {
            return Err((
                toks[pos].span(),
                "write `unsafe extern`: the certificates of a `#[fip_extern]` block are trusted claims about foreign code, so the block must carry a visible `unsafe`".to_string(),
            ));
        }
        return Err(not_extern());
    }
    pos += 1;
    if !toks.get(pos).is_some_and(|t| is_ident(t, "extern")) {
        return Err(not_extern());
    }
    pos += 1;
    if matches!(toks.get(pos), Some(TokenTree::Literal(_))) {
        pos += 1;
    }
    if pos >= toks.len() {
        return Err(not_extern());
    }
    Ok(pos)
}

fn filter_fip_attrs(item_toks: &[TokenTree], indices: &[usize]) -> Vec<TokenTree> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < item_toks.len() {
        if indices.contains(&i) {
            i += 2;
        } else {
            out.push(item_toks[i].clone());
            i += 1;
        }
    }
    out
}

fn process_extern_item(
    item_toks: &[TokenTree],
    krate: Option<&TokenStream>,
) -> Result<(TokenStream, TokenStream), (Span, String)> {
    let shape = parse_fn(item_toks);
    let fn_name = shape.as_ref().map(|s| s.name.clone()).unwrap_or_default();

    let mut exclude_attr = None;
    let mut cert_attr = None;
    let mut fip_no_evidence = None;
    let mut at = 0;
    let mut fip_attr_indices = Vec::new();

    while at + 1 < item_toks.len() && is_punct(&item_toks[at], '#') {
        if let TokenTree::Group(g) = &item_toks[at + 1]
            && let Some((attr_name, args)) = attr_name_and_args(g)
        {
            if attr_name == "fip_exclude" {
                let parsed = parse_exclude_attr(args)?;
                exclude_attr = Some((at, parsed));
                fip_attr_indices.push(at);
            } else if attr_name == "fip_cert" {
                let parsed = parse_ffi_cert_args(&attr_name, args)?;
                cert_attr = Some((at, parsed));
                fip_attr_indices.push(at);
            } else if attr_name == "fip" || attr_name == "fbip" {
                match parse_ffi_cert_args(&attr_name, args.clone()) {
                    Ok(parsed) => {
                        cert_attr = Some((at, parsed));
                        fip_attr_indices.push(at);
                    }
                    Err(_) => {
                        fip_no_evidence = Some(item_toks[at].span());
                    }
                }
            }
        }
        at += 2;
    }

    if let Some(sp) = fip_no_evidence
        && cert_attr.is_none()
        && exclude_attr.is_none()
    {
        return Err((
            sp,
            format!(
                "foreign function `{fn_name}` carries `#[fip]` without evidence: certifying a foreign function requires `evidence = \"..\"` under `#[fip_extern]`, or use `#[fip_exclude]`"
            ),
        ));
    }

    if let (Some((excl_at, _)), Some(_)) = (&exclude_attr, &cert_attr) {
        let sp = item_toks[*excl_at].span();
        return Err((
            sp,
            format!(
                "foreign function `{fn_name}` is both certified and excluded: choose exactly one"
            ),
        ));
    }

    if let Some((_, excl)) = exclude_attr {
        let shape = shape?;
        let doc = "#[doc = \"\"] #[doc = \"# FIP\"] #[doc = \"\"] #[doc = \"Excluded from FIP aggregation (`fip-prelint`). Calls contribute no events (user assumption).\"] #[allow(dead_code)]";
        let mut mark_ts = doc.parse::<TokenStream>().unwrap_or_default();
        mark_ts.extend(exclude_mark(excl.as_ref()));
        let mut final_item = TokenStream::new();
        final_item.extend(filter_fip_attrs(
            &item_toks[..shape.after_attrs],
            &fip_attr_indices,
        ));
        final_item.extend(mark_ts);
        final_item.extend(item_toks[shape.after_attrs..].iter().cloned());
        return Ok((TokenStream::new(), final_item));
    }

    if let Some((_, cert)) = cert_attr {
        let shape = shape?;
        return emit_ffi_cert_item(&shape, &fn_name, &cert, krate, item_toks, &fip_attr_indices);
    }

    let mut item_ts = TokenStream::new();
    item_ts.extend(item_toks.iter().cloned());
    Ok((TokenStream::new(), item_ts))
}

fn emit_ffi_cert_item(
    shape: &FnShape,
    fn_name: &str,
    cert: &FfiCertArgs,
    krate: Option<&TokenStream>,
    item_toks: &[TokenTree],
    fip_attr_indices: &[usize],
) -> Result<(TokenStream, TokenStream), (Span, String)> {
    if !shape.generics.is_empty() {
        let sp = shape
            .generics
            .first()
            .map_or_else(Span::call_site, TokenTree::span);
        return Err((
            sp,
            "foreign functions may not have generic parameters".to_string(),
        ));
    }
    let cert_krate = cert.krate.as_ref().or(krate);
    let krate_path = cert_krate.cloned().unwrap_or_else(strict::default_krate);
    let vis: TokenStream = shape.vis.iter().cloned().collect();
    let name = strict::bare(fn_name);
    // A certificate is of kind `fip` (no deallocation, see `fip_strict::Cert`): a
    // foreign function that frees (`frees = true`, `kind = "fbip"`) gets only the
    // driver mark, so a strict body cannot call it.
    let frees = cert.frees || cert.kind == "fbip";
    let module_items = if frees {
        TokenStream::new()
    } else {
        let src = format!(
            "#[doc(hidden)] #[allow(non_upper_case_globals, non_snake_case, dead_code, clippy::all, clippy::pedantic)] __FIP_VIS__ const __fip_strict_{name}: __FIP_KRATE__::Cert = unsafe {{ __FIP_KRATE__::Cert::assume({name:?}, {}u64) }};",
            cert.allocs
        );
        subst(
            ts_of(&src),
            &[("__FIP_KRATE__", &krate_path), ("__FIP_VIS__", &vis)],
        )
    };
    let free_part = if cert.frees { ", frees = true" } else { "" };
    let mark = if std::env::var_os(PRELINT_ENV).is_some() {
        let src = format!(
            "#[cfg_attr(fip_prelint, fip::cert(kind = {:?}, n = {}, evidence = __FIP_EVIDENCE__{free_part}))]",
            cert.kind, cert.allocs
        );
        let lit = TokenStream::from(TokenTree::Literal(cert.evidence_lit.clone()));
        subst(ts_of(&src), &[("__FIP_EVIDENCE__", &lit)])
    } else {
        TokenStream::new()
    };
    let evidence = cert.evidence.replace("\\\"", "\"").replace("\\\\", "\\");
    let doc = format!(
        "#[doc = \"\"] #[doc = \"# FIP Certificate\"] #[doc = \"\"] \
         #[doc = {:?}] #[doc = \"\"] #[doc = {:?}]",
        if frees {
            format!(
                "Certified {} (frees): at most {} allocation(s); no `__fip_strict_` certificate, so strict code cannot call it.",
                cert.kind, cert.allocs
            )
        } else {
            format!(
                "Certified {}: at most {} allocation(s).",
                cert.kind, cert.allocs
            )
        },
        format!("Evidence: {evidence}")
    );
    // The mark applies to every declaration of the symbol (`fip-prelint` matches by
    // link symbol), so a declaration made only to carry it is not dead code.
    let mut mark_ts = "#[allow(dead_code)]"
        .parse::<TokenStream>()
        .unwrap_or_default();
    mark_ts.extend(doc.parse::<TokenStream>().unwrap_or_default());
    mark_ts.extend(mark);

    let mut final_item = TokenStream::new();
    final_item.extend(filter_fip_attrs(
        &item_toks[..shape.after_attrs],
        fip_attr_indices,
    ));
    final_item.extend(mark_ts);
    final_item.extend(item_toks[shape.after_attrs..].iter().cloned());
    Ok((module_items, final_item))
}

fn fip_extern_inner(
    item: &TokenStream,
    krate: Option<&TokenStream>,
) -> Result<TokenStream, (Span, String)> {
    let toks: Vec<TokenTree> = item.clone().into_iter().collect();
    let first = toks.first().map_or_else(Span::call_site, TokenTree::span);
    let not_extern = || (first, "expected an `extern` block".to_string());
    let header_end = parse_extern_header(&toks)?;
    let Some(TokenTree::Group(body)) = toks.get(header_end) else {
        return Err(not_extern());
    };
    if body.delimiter() != Delimiter::Brace {
        return Err(not_extern());
    }
    let mut module_items = TokenStream::new();
    let mut new_body = TokenStream::new();
    let body_toks: Vec<TokenTree> = body.stream().into_iter().collect();
    let mut next = 0;
    while next < body_toks.len() {
        let start = next;
        let mut end = next;
        while end < body_toks.len() {
            let t = &body_toks[end];
            if is_punct(t, '#')
                && body_toks
                    .get(end + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Bracket))
            {
                end += 2;
                continue;
            }
            end += 1;
            if is_punct(t, ';') {
                break;
            }
        }
        next = end;
        let (mods, rewritten) = process_extern_item(&body_toks[start..end], krate)?;
        module_items.extend(mods);
        new_body.extend(rewritten);
    }
    let mut new_extern_toks = toks[..header_end].to_vec();
    let mut g = Group::new(Delimiter::Brace, new_body);
    g.set_span(body.span());
    new_extern_toks.push(TokenTree::Group(g));
    let mut out = module_items;
    out.extend(new_extern_toks);
    Ok(out)
}

/// Returns the last segment of the attribute path and its argument tokens.
fn attr_name_and_args(g: &Group) -> Option<(String, TokenStream)> {
    let toks: Vec<TokenTree> = g.stream().into_iter().collect();
    let (args, path) = match toks.split_last() {
        Some((TokenTree::Group(a), path)) if a.delimiter() == Delimiter::Parenthesis => {
            (a.stream(), path)
        }
        _ => (TokenStream::new(), toks.as_slice()),
    };
    let plain_path = path
        .iter()
        .all(|t| matches!(t, TokenTree::Ident(_)) || is_punct(t, ':'));
    if !plain_path {
        return None;
    }
    let last = path.last()?;
    if let TokenTree::Ident(id) = last {
        Some((id.to_string(), args))
    } else {
        None
    }
}

const FIP_IMPL_ARGS: &str = "the only argument is `crate = path::to::fip_strict`";

/// The arguments of `#[fip_impl]`.
const FIP_IMPL_ARGS_IMPL: &str = "the arguments are `crate = path::to::fip_strict` and `contract`";

/// The item with the `#[fip(..)]` attributes of its body removed, so a rejected
/// `#[fip_impl]` reports one error rather than one per method.
fn strip_fip_attrs(item: TokenStream) -> TokenStream {
    let mut toks: Vec<TokenTree> = item.into_iter().collect();
    if let Some(TokenTree::Group(body)) = toks.last()
        && body.delimiter() == Delimiter::Brace
    {
        let inner: Vec<TokenTree> = body.stream().into_iter().collect();
        let mut kept = TokenStream::new();
        let mut k = 0;
        while k < inner.len() {
            if is_punct(&inner[k], '#')
                && let Some(TokenTree::Group(g)) = inner.get(k + 1)
                && g.delimiter() == Delimiter::Bracket
                && fip_attr_args(g).is_some()
            {
                k += 2;
                continue;
            }
            kept.extend([inner[k].clone()]);
            k += 1;
        }
        let mut g = Group::new(Delimiter::Brace, kept);
        g.set_span(body.span());
        if let Some(last) = toks.last_mut() {
            *last = TokenTree::Group(g);
        }
    }
    toks.into_iter().collect()
}

const IMPL_BOUNDS: &str = "bounds on the impl's parameters and `where` clauses are rejected: a bounded impl does not cover every instantiation, so another impl could define a method of the same name; put the bounds on the methods";

/// Index just past the `>` matching the `<` at `toks[open]`.
fn angle_end(toks: &[TokenTree], open: usize) -> usize {
    let mut depth = 0_i32;
    let mut j = open;
    while j < toks.len() {
        let arrow = j > 0 && is_punct(&toks[j - 1], '-');
        if is_punct(&toks[j], '<') {
            depth += 1;
        } else if is_punct(&toks[j], '>') && !arrow {
            depth -= 1;
            if depth == 0 {
                return j + 1;
            }
        }
        j += 1;
    }
    toks.len()
}

/// Parameter names of `impl<..>` (lifetimes as `'a`), rejecting bounds and defaults.
fn impl_params(generics: &[TokenTree]) -> Result<Vec<String>, (Span, String)> {
    let inner: TokenStream = generics[1..generics.len().saturating_sub(1)]
        .iter()
        .cloned()
        .collect();
    let mut names = Vec::new();
    for part in split_commas(inner) {
        let sp = part.first().map_or_else(Span::call_site, TokenTree::span);
        match part.as_slice() {
            [TokenTree::Ident(t)] => names.push(t.to_string()),
            [q, TokenTree::Ident(l)] if is_punct(q, '\'') => names.push(format!("'{l}")),
            [
                TokenTree::Ident(c),
                TokenTree::Ident(n),
                colon,
                TokenTree::Ident(_),
            ] if c.to_string() == "const" && is_punct(colon, ':') => {
                names.push(n.to_string());
            }
            _ => return Err((sp, IMPL_BOUNDS.to_string())),
        }
    }
    Ok(names)
}

/// Name of the self type `path::Name<P..>`, checking that the arguments are exactly
/// the impl's parameters.
fn impl_self_ty(ty: &[TokenTree], params: &[String]) -> Result<String, (Span, String)> {
    let sp = ty.first().map_or_else(Span::call_site, TokenTree::span);
    let not_named = || {
        (
            sp,
            "the self type must be a named type whose arguments are exactly the impl's parameters (`impl<T> Foo<T>`); `#[fip_impl]` cannot name a certificate for this impl".to_string(),
        )
    };
    let path_end = ty.iter().position(|t| is_punct(t, '<')).unwrap_or(ty.len());
    let path = &ty[..path_end];
    let Some(TokenTree::Ident(name)) = path.last() else {
        return Err(not_named());
    };
    if !path
        .iter()
        .all(|t| matches!(t, TokenTree::Ident(_)) || is_punct(t, ':'))
        || params.contains(&name.to_string())
    {
        return Err(not_named());
    }
    let mut used: Vec<String> = Vec::new();
    if path_end < ty.len() {
        if angle_end(ty, path_end) != ty.len() {
            return Err(not_named());
        }
        let inner: TokenStream = ty[path_end + 1..ty.len() - 1].iter().cloned().collect();
        for part in split_commas(inner) {
            let arg = match part.as_slice() {
                [TokenTree::Ident(t)] => t.to_string(),
                [q, TokenTree::Ident(l)] if is_punct(q, '\'') => format!("'{l}"),
                _ => return Err(not_named()),
            };
            if !params.contains(&arg) || used.contains(&arg) {
                return Err(not_named());
            }
            used.push(arg);
        }
    }
    if params
        .iter()
        .any(|p| !p.starts_with('\'') && !used.contains(p))
    {
        return Err(not_named());
    }
    Ok(strict::bare(&name.to_string()).to_string())
}

/// `true` if the attribute group `[..]` is `fip(..)` under any path ending in `fip`
/// (`fip`, `fip_macros::fip`, `my_facade::fip`, `::a::b::fip`); returns its
/// argument tokens.
fn fip_attr_args(g: &Group) -> Option<TokenStream> {
    let toks: Vec<TokenTree> = g.stream().into_iter().collect();
    let (args, path) = match toks.split_last() {
        Some((TokenTree::Group(a), path)) if a.delimiter() == Delimiter::Parenthesis => {
            (a.stream(), path)
        }
        _ => (TokenStream::new(), toks.as_slice()),
    };
    let plain_path = path
        .iter()
        .all(|t| matches!(t, TokenTree::Ident(_)) || is_punct(t, ':'));
    let is_fip = plain_path && path.last().is_some_and(|f| is_ident(f, "fip"));
    is_fip.then_some(args)
}

fn fip_impl_inner(
    item: &TokenStream,
    krate: Option<&TokenStream>,
    contract: bool,
) -> Result<TokenStream, (Span, String)> {
    let toks: Vec<TokenTree> = item.clone().into_iter().collect();
    let first = toks.first().map_or_else(Span::call_site, TokenTree::span);
    let not_impl = || (first, "expected an `impl` block".to_string());
    let mut pos = 0;
    while pos + 1 < toks.len()
        && is_punct(&toks[pos], '#')
        && is_group(&toks[pos + 1], Delimiter::Bracket)
    {
        pos += 2;
    }
    let unsafe_impl = toks.get(pos).is_some_and(|t| is_ident(t, "unsafe"));
    if unsafe_impl {
        pos += 1;
    }
    if !toks.get(pos).is_some_and(|t| is_ident(t, "impl")) {
        return Err(not_impl());
    }
    let impl_at = pos;
    pos += 1;
    let mut params = Vec::new();
    if toks.get(pos).is_some_and(|t| is_punct(t, '<')) {
        let end = angle_end(&toks, pos);
        params = impl_params(&toks[pos..end])?;
        pos = end;
    }
    let Some(TokenTree::Group(body)) = toks.last() else {
        return Err(not_impl());
    };
    if body.delimiter() != Delimiter::Brace {
        return Err(not_impl());
    }
    let ctx = impl_ctx(&toks[pos..toks.len() - 1], params, first)?;
    if contract && ctx.trait_name.is_none() {
        return Err((
            toks[impl_at].span(),
            "`contract` applies to an `impl Trait for Type` block of a trait with strict contracts"
                .to_string(),
        ));
    }
    let check = ImplCheck {
        compare: ctx.trait_name.is_some() && (unsafe_impl || contract),
        complete: contract,
    };
    let (module_items, new_body) = rewrite_impl_body(body, &ctx, krate, check)?;
    let mut g = Group::new(Delimiter::Brace, new_body);
    g.set_span(body.span());
    let mut out = module_items;
    out.extend(toks[..impl_at].iter().cloned());
    if contract && !unsafe_impl {
        // Every strict contract of the trait is implemented by a strict method whose
        // certificate is checked against it (`ImplCheck::complete`), which is the
        // claim the `unsafe trait` asks of an implementation.
        out.extend([TokenTree::Ident(Ident::new("unsafe", Span::call_site()))]);
    }
    out.extend(toks[impl_at..toks.len() - 1].iter().cloned());
    out.extend([TokenTree::Group(g)]);
    Ok(out)
}

/// What `#[fip_impl]` checks of a trait impl against the trait's strict contracts
/// (`#[fip_trait]`, `<dyn Trait>::__fip_strict_<m>`).
#[derive(Clone, Copy)]
struct ImplCheck {
    /// Compare every strict method's certificate with the contract of its method:
    /// for `unsafe impl` (a trait with strict contracts is an `unsafe trait`) and for
    /// `#[fip_impl(contract)]`. A plain `impl` is not compared: the trait may have no
    /// contract, or not be dyn-compatible.
    compare: bool,
    /// `#[fip_impl(contract)]`: every method of `<dyn Trait>::__FIP_CONTRACTED` must
    /// be a strict method of this block.
    complete: bool,
}

/// `tokens` with every identifier `__FIP_<NAME>__` replaced by the tokens bound to
/// it in `subst` (in nested groups too), so paths such as `crate = $crate::x` are
/// emitted as tokens rather than re-parsed from text.
fn subst(tokens: TokenStream, subst: &[(&str, &TokenStream)]) -> TokenStream {
    let mut out = TokenStream::new();
    for t in tokens {
        match &t {
            TokenTree::Ident(id) => {
                let s = id.to_string();
                match subst.iter().find(|(k, _)| *k == s) {
                    Some((_, v)) => out.extend((*v).clone()),
                    None => out.extend([t]),
                }
            }
            TokenTree::Group(g) => {
                let mut ng = Group::new(g.delimiter(), self::subst(g.stream(), subst));
                ng.set_span(g.span());
                out.extend([TokenTree::Group(ng)]);
            }
            _ => out.extend([t]),
        }
    }
    out
}

/// Self type and trait of an impl header (`Trait for Type` / `Type`, after the
/// generics).
fn impl_ctx(
    header: &[TokenTree],
    params: Vec<String>,
    first: Span,
) -> Result<ImplCtx, (Span, String)> {
    if let Some(w) = header.iter().find(|t| is_ident(t, "where")) {
        return Err((w.span(), IMPL_BOUNDS.to_string()));
    }
    let mut depth = 0_i32;
    let mut for_at = None;
    for (k, t) in header.iter().enumerate() {
        if is_punct(t, '<') {
            depth += 1;
        } else if is_punct(t, '>') {
            depth -= 1;
        } else if depth == 0 && is_ident(t, "for") {
            for_at = Some(k);
            break;
        }
    }
    let (trait_toks, ty_toks) = match for_at {
        Some(k) => (Some(&header[..k]), &header[k + 1..]),
        None => (None, header),
    };
    let self_ty = impl_self_ty(ty_toks, &params)?;
    let trait_name = match trait_toks {
        None => None,
        Some(t) => {
            let plain = t
                .iter()
                .all(|x| matches!(x, TokenTree::Ident(_)) || is_punct(x, ':'));
            if let (true, Some(TokenTree::Ident(n))) = (plain, t.last()) {
                Some(strict::bare(&n.to_string()).to_string())
            } else {
                let sp = t.first().map_or(first, TokenTree::span);
                return Err((
                    sp,
                    "generic traits (`impl Tr<..> for Foo`) are rejected: the certificate name could not tell the impls apart".to_string(),
                ));
            }
        }
    };
    let trait_toks = trait_toks.map_or_else(Vec::new, <[TokenTree]>::to_vec);
    Ok(ImplCtx {
        self_ty,
        trait_name,
        trait_toks,
        params,
    })
}
/// Expands the strict methods of an impl body: `(module-level items, new body)`.
/// `krate` (from `#[fip_impl(crate = ..)]`) applies to methods without their own.
fn rewrite_impl_body(
    body: &Group,
    ctx: &ImplCtx,
    krate: Option<&TokenStream>,
    check: ImplCheck,
) -> Result<(TokenStream, TokenStream), (Span, String)> {
    let mut module_items = TokenStream::new();
    let mut new_body = TokenStream::new();
    let mut strict_methods: Vec<String> = Vec::new();
    let mut first_krate: Option<TokenStream> = None;
    let body_toks: Vec<TokenTree> = body.stream().into_iter().collect();
    let mut next = 0;
    while next < body_toks.len() {
        let start = next;
        // One impl item: attributes, then up to the first top-level `;` or `{ .. }`.
        let mut end = next;
        while end < body_toks.len() {
            let t = &body_toks[end];
            if is_punct(t, '#')
                && body_toks
                    .get(end + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Bracket))
            {
                end += 2;
                continue;
            }
            end += 1;
            if is_punct(t, ';') || is_group(t, Delimiter::Brace) {
                break;
            }
        }
        next = end;
        let item_toks = &body_toks[start..end];
        // Find a strict `#[fip(..)]` among the leading attributes.
        let mut strict_attr = None;
        let mut at = 0;
        while at + 1 < item_toks.len() && is_punct(&item_toks[at], '#') {
            if let TokenTree::Group(g) = &item_toks[at + 1]
                && let Some(args) = fip_attr_args(g)
            {
                let mut parsed = parse_fip_args(args)?;
                if parsed.krate.is_none() {
                    parsed.krate = krate.cloned();
                }
                if parsed.strict {
                    strict_attr = Some((at, parsed));
                    break;
                }
            }
            at += 2;
        }
        let Some((at, args)) = strict_attr else {
            new_body.extend(item_toks.iter().cloned());
            continue;
        };
        let rest: TokenStream = item_toks[..at]
            .iter()
            .chain(&item_toks[at + 2..])
            .cloned()
            .collect();
        // The attribute is consumed here; `use <its path> as _;` keeps the user's
        // import of it in use (it is not re-emitted, so no marker on the method can
        // be written by hand to skip the checks).
        module_items.extend(attr_path_use(&item_toks[at + 1]));
        match expand_parts(args.mode, Some(&args), &rest, Some(ctx)) {
            Ok((items, f)) => {
                module_items.extend(items);
                if let Some(t) = &ctx.trait_name
                    && let Ok(shape) = parse_fn(&rest.clone().into_iter().collect::<Vec<_>>())
                {
                    let m = strict::bare(&shape.name).to_string();
                    strict_methods.push(m.clone());
                    let krate_path = args.krate.clone().unwrap_or_else(strict::default_krate);
                    if first_krate.is_none() {
                        first_krate = Some(krate_path.clone());
                    }
                    if check.compare {
                        module_items.extend(contract_comparison(ctx, t, &m, &krate_path));
                    }
                }
                new_body.extend(f);
            }
            Err(errors) => {
                module_items.extend(errors);
                new_body.extend(rest);
            }
        }
    }
    if let Some(t) = &ctx.trait_name {
        // The contract comparisons below are `::core::assert!`s.
        module_items.extend(strict::std_roots_check(&["core"]));
        let krate_path = first_krate
            .or_else(|| krate.cloned())
            .unwrap_or_else(strict::default_krate);
        let tr: TokenStream = ctx.trait_toks.iter().cloned().collect();
        if !strict_methods.is_empty() {
            module_items.extend(trait_identity_items(&ctx.self_ty, t, &tr));
        }
        if check.complete {
            let names: Vec<String> = strict_methods.iter().map(|m| format!("{m:?}")).collect();
            let src = format!(
                "#[doc(hidden)] #[allow(clippy::all, clippy::pedantic)] const _: () = ::core::assert!(__FIP_KRATE__::contracted_covered(<dyn __FIP_TRAIT__>::__FIP_CONTRACTED, &[{}]), {:?});",
                names.join(", "),
                "#[fip_impl(contract)]: a method with a strict contract in the trait is not implemented in this block with `#[fip(strict = true)]`, so its contract is not checked"
            );
            module_items.extend(subst(
                ts_of(&src),
                &[("__FIP_KRATE__", &krate_path), ("__FIP_TRAIT__", &tr)],
            ));
        }
    }
    Ok((module_items, new_body))
}

fn ts_of(s: &str) -> TokenStream {
    s.parse().unwrap_or_default()
}

/// The compile-time comparison of the impl certificate of `m` with its contract,
/// mirroring the driver's `Mark::weaker_than` as far as a certificate carries it:
/// the allocation bound and panic strictness. The kind is always `fip` (no strict
/// `#[fbip]`), so there is nothing to compare; `param(..)` is not compared by the
/// driver either. A method of the trait without a strict contract reads the local
/// fallback constant instead (an inherent associated constant of `dyn Trait`, the
/// contract, takes precedence over a trait's), which any certificate satisfies.
fn contract_comparison(ctx: &ImplCtx, t: &str, m: &str, krate: &TokenStream) -> TokenStream {
    let self_ty = &ctx.self_ty;
    let impl_name = format!("{self_ty}__{t}__{m}");
    let contract_name = format!("{t}__{m}");
    let src = format!(
        "#[doc(hidden)] #[allow(non_upper_case_globals, non_snake_case, non_camel_case_types, dead_code, clippy::all, clippy::pedantic)] \
         const _: () = {{ \
         trait __FipNoContract {{ const __fip_strict_{m}: __FIP_KRATE__::Cert = unsafe {{ __FIP_KRATE__::Cert::assume({contract_name:?}, u64::MAX) }}; }} \
         impl<__FipT: ?Sized> __FipNoContract for __FipT {{}} \
         let impl_cert = __fip_strict_{impl_name}; \
         let contract_cert = <dyn __FIP_TRAIT__>::__fip_strict_{m}; \
         let impl_allocs = __FIP_KRATE__::Cert::allocs_for(impl_cert, {impl_name:?}); \
         let contract_allocs = __FIP_KRATE__::Cert::allocs_for(contract_cert, {contract_name:?}); \
         ::core::assert!(impl_allocs <= contract_allocs, {:?}); \
         ::core::assert!(!__FIP_KRATE__::Cert::no_panic_macros_for(contract_cert, {contract_name:?}) \
         || __FIP_KRATE__::Cert::no_panic_macros_for(impl_cert, {impl_name:?}), {:?}); }};",
        "#[fip_impl]: impl certificate is weaker than contract (more allocations)",
        "#[fip_impl]: impl certificate is weaker than contract (the contract has `panic_macros = false`, the implementation does not)"
    );
    let tr: TokenStream = ctx.trait_toks.iter().cloned().collect();
    subst(
        ts_of(&src),
        &[("__FIP_KRATE__", krate), ("__FIP_TRAIT__", &tr)],
    )
}

/// Items a strict caller of `<Type as path::Trait>::m` checks its trait path
/// against (`strict::TraitCheck`): `__fip_traitid_<Type>__<Trait>::<T>()` requires
/// `T:` the impl's trait, and `__fip_traitsup_<Type>__<Trait>` has it as supertrait.
fn trait_identity_items(self_ty: &str, t: &str, tr: &TokenStream) -> TokenStream {
    let key = format!("{self_ty}__{t}");
    let src = format!(
        "#[doc(hidden)] #[allow(non_snake_case, dead_code, private_bounds, private_interfaces, clippy::all, clippy::pedantic)] \
         pub fn __fip_traitid_{key}<__FipT: ?Sized + __FIP_TRAIT__>() {{}} \
         #[doc(hidden)] #[allow(non_camel_case_types, dead_code, private_bounds, clippy::all, clippy::pedantic)] \
         pub trait __fip_traitsup_{key}: __FIP_TRAIT__ {{}} \
         #[allow(clippy::all, clippy::pedantic)] \
         impl<__FipT: ?Sized + __FIP_TRAIT__> __fip_traitsup_{key} for __FipT {{}}"
    );
    subst(ts_of(&src), &[("__FIP_TRAIT__", tr)])
}

/// `const _: () = { use <path> as _; };` for the path of the attribute `#[path(..)]`,
/// so an import of the attribute macro used only inside `#[fip_impl]` stays used.
fn attr_path_use(attr: &TokenTree) -> TokenStream {
    let mut path: Vec<TokenTree> = match attr {
        TokenTree::Group(g) => g.stream().into_iter().collect(),
        _ => Vec::new(),
    };
    if path
        .last()
        .is_some_and(|t| is_group(t, Delimiter::Parenthesis))
    {
        path.pop();
    }
    let mut inner = ts_of("#[allow(unused_imports)] use");
    inner.extend(path);
    inner.extend(ts_of("as _;"));
    let mut out = ts_of("const _: () =");
    out.extend([TokenTree::Group(Group::new(Delimiter::Brace, inner))]);
    out.extend(ts_of(";"));
    out
}

/// Wraps a closure, or a function with a certificate, into a certified callable
/// implementing `fip_strict::FipFn`.
///
/// The closure body is checked with the strict rules: it may call only certified
/// functions and the audited `core` table, and contain no allocation site inside a
/// loop. Its allocation bound becomes the wrapper's `FipBound::ALLOCS`. Annotate the
/// parameter types (`|v: &u8| ..`); the wrapper does not propagate an expected
/// closure signature.
///
/// ```
/// use fip_strict::FipFn;
/// let gt1 = fip_macros::fip_fn!(|v: &u8| *v > 1);
/// assert!(gt1.call((&2,)));
/// ```
///
/// **Specifications.** Outer attributes before the closure are kept on it, so a
/// Verus specification can be attached; under Verus the value's `pre` / `post` are
/// the closure's `requires` / `ensures`. Plain builds drop the `cfg_attr`. Verus
/// needs the closure's return type (`r: T =>` or `-> T`); it rejects `with` on
/// closures. Attributes are not part of the checked body.
///
/// ```
/// use fip_strict::FipFn;
/// let inc = fip_macros::fip_fn!(
///     #[cfg_attr(verus_keep_ghost, verus_spec(r: u32 => requires x < 10, ensures r == x + 1))]
///     |x: u32| x + 1
/// );
/// assert_eq!(inc.call((5,)), 6);
/// ```
///
/// **Named functions.** `fip_fn!(path)` takes the path of a function that a strict
/// body could call: `f`, `a::f`, `f::<T>`, `Type::m` / `<Type<..>>::m` /
/// `Type::<..>::m` (a
/// `#[fip_impl]` method), `<Type as Trait>::m` (a trait-impl method), a `core` table
/// function or a std constructor. The bound is read from the function's certificate
/// as a strict call of it reads it (`Cert::allocs_for(__fip_strict_f, "f")`), so a
/// function without one does not compile (E0425 on `__fip_strict_f`, as for a strict
/// call). No `unsafe` is written at the call site, and it works in strict bodies and
/// in Verus-verified ones (the value's `pre` / `post` are the function's `requires` /
/// `ensures`). An expected type `Certified<N, fn(..) -> ..>` makes the value a
/// certified function pointer: the function item coerces at `Certified::assume`'s
/// argument, and `N` must equal the certificate's bound.
///
/// ```
/// use fip_strict::{Certified, FipFn};
/// #[fip_macros::fip(strict = true)]
/// fn flip(x: u8) -> u8 { x ^ 1 }
/// #[fip_macros::fip(strict = true)]
/// fn keep(x: u8) -> u8 { x }
/// let f = fip_macros::fip_fn!(flip);
/// assert_eq!(f.call((2,)), 3);
/// let table: [Certified<0, fn(u8) -> u8>; 2] = [fip_macros::fip_fn!(flip), fip_macros::fip_fn!(keep)];
/// assert_eq!(table[1].call((2,)), 2);
/// ```
///
/// **A bound at the creation site.** `fip_fn!(bound <= K, ..)` (an integer literal
/// `K`, before the closure or path, after `crate = ..` if any) fails to compile when
/// the computed bound exceeds `K`: "the allocation bound exceeds the declared `bound
/// <= K`". The check is in the value's type, so `cargo check` reports it, also in an
/// uncalled generic function; a callee's `param(g = K)` check runs only when the
/// callee is instantiated (not under `cargo check`). The callee's declaration stays
/// authoritative; this is an earlier, local error. A closure keeps its computed bound
/// (`Certified<N, _>`); a path becomes `Certified<K, _>`, the declared limit, so its
/// type is the same under Verus (below).
///
/// **Under Verus** (Verus's driver, `rust_verify`) the macro never reads a certificate
/// (Verus cannot evaluate them), and the value's type is the plain build's wherever the
/// plain build's bound is a literal:
///
/// | form | plain build | Verus build |
/// |---|---|---|
/// | closure | `Certified<N, _>`, `N` scanned from the body | `Certified<N, _>`, the same `N` |
/// | closure calling certified functions | `Certified<N, _>`, `N` read from certificates | rejected (no literal `N`) |
/// | `fip_fn!(bound <= K, path)` | `Certified<K, _>`, checks certificate `N <= K` | `Certified<K, _>` |
/// | `fip_fn!(path)` | `Certified<N, _>`, `N` the certificate's | `Certified<0, _>` |
///
/// Only `fip_fn!(path)` without `bound` differs between the builds, so code that names
/// the type of a certified function (a struct field, an array, a `param(g = K)`
/// argument) under Verus writes `fip_fn!(bound <= K, path)`; for a function that
/// allocates, this is required. The plain build of the same source checks every
/// certificate.
///
/// ```
/// let f = fip_macros::fip_fn!(bound <= 0, |x: u8| x ^ 1);
/// # let _ = f;
/// ```
///
/// **Panic strictness.** `fip_fn!(panic_macros = false, ..)` (after `crate = ..`,
/// before `bound <= K`) scans a closure body as `#[fip(strict = true, panic_macros =
/// false)]` does (no `assert!`, `panic!`, `unreachable!`, ..), and for a path requires
/// the function's certificate to say `panic_macros = false`
/// (`Cert::no_panic_macros_for`; a `core` table function or std constructor is
/// rejected). The value is a `Certified<N, C, true>`, whose
/// `FipBound::NO_PANIC_MACROS` is `true`; without the option it is `false`. A strict
/// callee declared `panic_macros = false` asserts `F::NO_PANIC_MACROS` for every
/// `param(..)` argument it calls, so it rejects a value that allows panicking macros
/// (post-monomorphisation, like its `param(g = K)` check). `fip_strict::Stateless`,
/// `Compose` and `Then` are panic-macro free only if every part is. As for a strict
/// function, this covers the body's macros only; panics from indexing, arithmetic
/// and callees are the driver's.
///
/// ```
/// use fip_strict::FipFn;
/// #[fip_macros::fip(strict = true, panic_macros = false, param(g = 0))]
/// fn apply<F: FipFn<(u8,), Output = u8>>(g: F) -> u8 { g.call((1,)) }
/// assert_eq!(apply(fip_macros::fip_fn!(panic_macros = false, |x: u8| x ^ 1)), 0);
/// ```
///
/// **Driver-checked mode (opt-in per use).** `fip_fn!(prelint, N, |x: T, ..| body)`
/// (an integer literal `N`, after `crate = ..` if any) certifies the closure with the
/// declared bound `N` without the strict token scan of `body`, so method calls, `use`
/// aliases and inferred types are allowed in it. Nothing in this macro checks `N`: the
/// MIR checker `fip-prelint` checks the construction (at most `N` allocations per
/// call, no free, no recursion, for the body and everything it reaches) and is the
/// trusted party for it. The mode therefore compiles only in a checking driver run
/// (`cargo fip-prelint` on the crate as a primary package); a plain build, a
/// dependency build, `cargo fip-prelint --stack` and std-summary generation fail with
/// a compile error naming `cargo fip-prelint`. Every parameter type
/// must be written (the closure has no expected signature to infer them from), and
/// `bound <= K` is not accepted (`N` is the bound). Parameter types may name type
/// parameters of an enclosing generic function, and a closure may return a borrow
/// of its one elided-reference parameter when its return type is written
/// (`|x: &T| -> &T { x }`; Rust rejects that closure without the written type). See
/// `docs/decisions/2026-11-03-fip-fn-driver-mode.md`.
///
/// ```text
/// let f = fip_macros::fip_fn!(prelint, 0, |x: u32| x.wrapping_add(1).count_ones());
/// ```
///
/// `fip_fn!(crate = path::to::fip_strict, ..)` sets the path of the `fip_strict`
/// crate in the generated code (see `crate = ..` in the crate documentation).
#[proc_macro]
pub fn fip_fn(input: TokenStream) -> TokenStream {
    let all: Vec<TokenTree> = input.into_iter().collect();
    let (krate, toks) = match all.as_slice() {
        [TokenTree::Ident(key), eq, rest @ ..]
            if key.to_string() == "crate" && is_punct(eq, '=') =>
        {
            let Some(comma) = rest.iter().position(|t| is_punct(t, ',')) else {
                return compile_error(key.span(), "fip_fn!: expected `crate = path, |args| body`");
            };
            match parse_krate(key.span(), &rest[..comma]) {
                Ok(k) => (Some(k), rest[comma + 1..].to_vec()),
                Err((sp, msg)) => return compile_error(sp, &format!("fip_fn!: {msg}")),
            }
        }
        _ => (None, all),
    };
    let (no_panic, toks) = match panic_prefix(toks) {
        Ok(v) => v,
        Err(e) => return e,
    };
    let toks = match prelint_prefix(toks) {
        PrelintPrefix::Absent(toks) => toks,
        PrelintPrefix::Present { at, .. } if no_panic => {
            return compile_error(
                at,
                "fip_fn!(panic_macros = false, prelint, ..) is not supported: the driver-checked mode does not scan the body's macros; drop `panic_macros = false` or `prelint, N,`",
            );
        }
        PrelintPrefix::Present { at, n, rest } => return fip_fn_prelint(krate, at, n, &rest),
        PrelintPrefix::Malformed(e) => return e,
    };
    let (limit, toks) = match bound_limit(toks) {
        Ok(v) => v,
        Err(e) => return e,
    };
    let (arity, body_start) = match closure_shape(&toks) {
        Ok(v) => v,
        Err(sp) => {
            if fn_path_shape(&toks) {
                return fip_fn_path(krate, toks, limit, no_panic);
            }
            return compile_error(sp, &misuse_message(&toks));
        }
    };
    let body: TokenStream = toks[body_start..].iter().cloned().collect();
    let mut scan = Scan {
        fn_name: "",
        sites: Vec::new(),
        recursion: Vec::new(),
    };
    scan.stream(body.clone(), false);
    let mut shadowed = Vec::new();
    strict::bound_names(toks[..body_start].iter().cloned().collect(), &mut shadowed);
    strict::bound_names(body.clone(), &mut shadowed);
    let mut strict_scan = strict::StrictScan {
        krate,
        no_panic_macros: no_panic,
        shadowed,
        keep_tokens: strict::under_verus(),
        std_roots: strict::std_roots_used(body.clone()),
        ..strict::StrictScan::default()
    };
    let emitted = strict_scan.stream_expr(body);
    let mut errors = TokenStream::new();
    for s in scan.sites.iter().filter(|s| s.in_loop) {
        errors.extend(compile_error(
            s.span,
            &format!("fip_fn!: allocation site {} inside a loop body", s.what),
        ));
    }
    for (sp, msg) in &strict_scan.errors {
        errors.extend(compile_error(*sp, &format!("fip_fn! strict: {msg}")));
    }
    if !errors.is_empty() {
        return errors;
    }
    if arity > MAX_FIP_FN_ARITY {
        return compile_error(
            toks.first().map_or_else(Span::call_site, TokenTree::span),
            &format!(
                "fip_fn!: at most {MAX_FIP_FN_ARITY} closure parameters (`fip_strict::MAX_ARITY`)"
            ),
        );
    }
    let local = u64::try_from(scan.sites.len()).unwrap_or(u64::MAX);
    let bound = if strict::under_verus() {
        let first = toks.first().map_or_else(Span::call_site, TokenTree::span);
        match verus_closure_bound(&strict_scan, local, limit, first) {
            Ok(b) => b,
            Err(e) => return e,
        }
    } else {
        limited(strict_scan.emit_fip_fn_bound(local), limit, false)
    };
    let mut closure: TokenStream = toks[..body_start].iter().cloned().collect();
    closure.extend(emitted);
    fip_fn_wrapper(&strict_scan.krate(), bound, closure, no_panic)
}

/// The bound of a `fip_fn!` closure under Verus's driver: the same `N` as the plain
/// build, as a literal (Verus cannot evaluate certificate reads, `Cert::allocs_for`
/// or `const` blocks of them), checked against `bound <= K` here.
fn verus_closure_bound(
    scan: &strict::StrictScan,
    local: u64,
    limit: Option<u64>,
    at: Span,
) -> Result<TokenStream, TokenStream> {
    let Some(n) = scan.literal_fip_fn_bound(local) else {
        return Err(compile_error(at, FIP_FN_VERUS_CALLS));
    };
    if let Some(k) = limit
        && n > k
    {
        return Err(compile_error(
            at,
            &format!("fip_fn!: the allocation bound exceeds the declared `bound <= {k}`"),
        ));
    }
    Ok(format!("{n}u64").parse().unwrap_or_default())
}

/// The error for a `fip_fn!` closure that calls certified functions, under Verus's
/// driver: its bound `N` is a sum of certificate reads that only the plain build
/// evaluates, so no literal `N` exists for the Verus build's `Certified<N, _>`.
const FIP_FN_VERUS_CALLS: &str = "fip_fn!: under Verus, a closure that calls certified functions (or `param(..)` callables, or trait methods) has no literal allocation bound: its bound is a sum of certificates that only the plain build evaluates, and the value's type `Certified<N, _>` must be the same in both builds; name a function instead (`fip_fn!(bound <= K, path)`, whose type is `Certified<K, _>` in both builds) or call no certified function in the closure";

/// A leading `panic_macros = false,` (after `crate = ..`): the closure body is
/// scanned with `panic_macros = false` (no panicking macro), a path must name a
/// function whose certificate says so, and the value is a
/// `Certified<N, C, true>` (`FipBound::NO_PANIC_MACROS`). `panic_macros = true` is
/// the default and accepted.
fn panic_prefix(toks: Vec<TokenTree>) -> Result<(bool, Vec<TokenTree>), TokenStream> {
    let [TokenTree::Ident(key), eq, ..] = toks.as_slice() else {
        return Ok((false, toks));
    };
    if key.to_string() != "panic_macros" || !is_punct(eq, '=') {
        return Ok((false, toks));
    }
    let bad = |sp: Span| {
        compile_error(
            sp,
            "fip_fn!: expected `panic_macros = false, ..` (or `true`, the default), then the closure or path",
        )
    };
    let (Some(v), Some(comma)) = (toks.get(2), toks.get(3)) else {
        return Err(bad(key.span()));
    };
    if !is_punct(comma, ',') {
        return Err(bad(comma.span()));
    }
    let no_panic = match v.to_string().as_str() {
        "false" => true,
        "true" => false,
        _ => return Err(bad(v.span())),
    };
    Ok((no_panic, toks[4..].to_vec()))
}

/// The message for an argument that is neither a closure nor a function path.
const FIP_FN_SHAPE: &str = "fip_fn!: expected a closure `|args| body` or the path of a function with a certificate (`f`, `a::f`, `f::<T>`, `Type::m`, `<Type<..>>::m`, `Type::<..>::m`, `<Type as Trait>::m`)";

/// [`FIP_FN_SHAPE`], specialised for common misuse.
fn misuse_message(toks: &[TokenTree]) -> String {
    let first = toks.first().map(ToString::to_string).unwrap_or_default();
    if toks.is_empty() {
        return format!("{FIP_FN_SHAPE}; got nothing");
    }
    if ["requires", "ensures", "recommends", "decreases", "returns"].contains(&first.as_str()) {
        return format!(
            "fip_fn!: `{first}` clauses are not arguments of `fip_fn!`; attach a Verus specification to the closure as an attribute: `fip_fn!(#[cfg_attr(verus_keep_ghost, verus_spec(r: T => requires .., ensures ..))] |x: U| ..)`"
        );
    }
    if first == "bound" {
        return "fip_fn!: expected `bound <= K, ..` with an integer literal `K`, then the closure or path".to_string();
    }
    if first == "#" {
        let mut i = 0;
        while toks.get(i).is_some_and(|t| is_punct(t, '#'))
            && toks
                .get(i + 1)
                .is_some_and(|t| is_group(t, Delimiter::Bracket))
        {
            i += 2;
        }
        if fn_path_shape(&toks[i..]) {
            return "fip_fn!: attributes are kept only on a closure; a named function's specification is the function's own (`verus_spec` on its declaration), so write `fip_fn!(path)` without attributes".to_string();
        }
    }
    if toks.iter().any(|t| is_punct(t, '.')) && !toks.iter().any(|t| is_punct(t, '|')) {
        return format!(
            "{FIP_FN_SHAPE}; a method of a value (`x.m`) cannot be named: name it by its type (`Type::m`, `<Type as Trait>::m`), which takes the receiver as its first argument"
        );
    }
    FIP_FN_SHAPE.to_string()
}

/// A leading `bound <= K,`: the largest allocation bound the value may have.
fn bound_limit(toks: Vec<TokenTree>) -> Result<(Option<u64>, Vec<TokenTree>), TokenStream> {
    let [TokenTree::Ident(key), lt, eq, ..] = toks.as_slice() else {
        return Ok((None, toks));
    };
    if key.to_string() != "bound" || !is_punct(lt, '<') || !is_punct(eq, '=') {
        return Ok((None, toks));
    }
    let bad = |sp: Span| {
        compile_error(
            sp,
            "fip_fn!: expected `bound <= K, ..` with an integer literal `K`, then the closure or path",
        )
    };
    let (Some(TokenTree::Literal(lit)), Some(comma)) = (toks.get(3), toks.get(4)) else {
        return Err(bad(key.span()));
    };
    if !is_punct(comma, ',') {
        return Err(bad(comma.span()));
    }
    let text = lit.to_string().replace('_', "");
    let digits = text.strip_suffix("u64").unwrap_or(&text);
    let Ok(k) = digits.parse::<u64>() else {
        return Err(bad(lit.span()));
    };
    Ok((Some(k), toks[5..].to_vec()))
}

/// The bound block `{ checks; sum }`, asserting `sum <= limit` if a limit is given.
/// Evaluated with the value's type (also by `cargo check`), where the closure or
/// function is written. The block's value is `sum`, or the limit `K` itself when
/// `to_limit` (the path form: `Certified<K, _>`, the type the Verus build names too).
fn limited(bound: TokenStream, limit: Option<u64>, to_limit: bool) -> TokenStream {
    let Some(k) = limit else {
        return bound;
    };
    let value = if to_limit {
        format!("{k}u64")
    } else {
        "__fip_fn_bound".to_string()
    };
    let mut out: TokenStream = "let __fip_fn_bound: u64 = ".parse().unwrap_or_default();
    out.extend([TokenTree::Group(Group::new(Delimiter::Brace, bound))]);
    out.extend(
        format!(
            "; ::core::assert!(__fip_fn_bound <= {k}u64, {:?}); {value}",
            format!("fip_fn!: the allocation bound exceeds the declared `bound <= {k}`")
        )
        .parse::<TokenStream>()
        .unwrap_or_default(),
    );
    out
}

/// Set by the `fip-prelint` driver in its own process, next to [`PRELINT_ENV`], only
/// when it compiles a primary package in check mode (not an exported dependency, not
/// stack mode, not std-summary generation). `fip_fn!(prelint, N, ..)` expands only when
/// both are set (`docs/decisions/2026-11-03-fip-fn-driver-mode.md`).
const CHECKS_ENV: &str = "FIP_PRELINT_CHECKS";

/// The error of `fip_fn!(prelint, N, ..)` outside a checking driver run.
const PRELINT_UNCHECKED: &str = "fip_fn!(prelint, ..) is checked only by `cargo fip-prelint`: this compilation is not a checking driver run (a plain build, a dependency, `cargo fip-prelint --stack` or std-summary generation), so the declared bound would be trusted unchecked; build this crate with `cargo fip-prelint`, or write `fip_fn!(|..| ..)`";

/// `true` when the expanding compiler is the `fip-prelint` driver checking this crate.
fn checked_by_driver() -> bool {
    std::env::var_os(PRELINT_ENV).is_some()
        && std::env::var_os(CHECKS_ENV).is_some_and(|v| v == "1")
}

/// A leading `prelint, N,` of `fip_fn!`.
enum PrelintPrefix {
    /// No `prelint` argument: the default (token-checked) `fip_fn!`.
    Absent(Vec<TokenTree>),
    /// `prelint, N, rest`: `at` is the span of `prelint`.
    Present {
        at: Span,
        n: u64,
        rest: Vec<TokenTree>,
    },
    /// `prelint` not followed by `, N,` with an integer literal `N`.
    Malformed(TokenStream),
}

fn prelint_prefix(toks: Vec<TokenTree>) -> PrelintPrefix {
    let Some(TokenTree::Ident(key)) = toks.first() else {
        return PrelintPrefix::Absent(toks);
    };
    if key.to_string() != "prelint" {
        return PrelintPrefix::Absent(toks);
    }
    let at = key.span();
    let bad = |sp: Span| {
        PrelintPrefix::Malformed(compile_error(
            sp,
            "fip_fn!: expected `prelint, N, |x: T, ..| body` with an integer literal `N` (the declared allocation bound, checked by `fip-prelint`)",
        ))
    };
    let (Some(c1), Some(TokenTree::Literal(lit)), Some(c2)) =
        (toks.get(1), toks.get(2), toks.get(3))
    else {
        return bad(at);
    };
    if !is_punct(c1, ',') {
        return bad(c1.span());
    }
    if !is_punct(c2, ',') {
        return bad(c2.span());
    }
    let text = lit.to_string().replace('_', "");
    let digits = text.strip_suffix("u64").unwrap_or(&text);
    let Ok(n) = digits.parse::<u64>() else {
        return bad(lit.span());
    };
    PrelintPrefix::Present {
        at,
        n,
        rest: toks[4..].to_vec(),
    }
}

/// Index of the closure's opening `|`: after leading outer attributes and `move`.
fn closure_open(toks: &[TokenTree]) -> usize {
    let mut i = 0;
    while toks.get(i).is_some_and(|t| is_punct(t, '#'))
        && toks
            .get(i + 1)
            .is_some_and(|t| is_group(t, Delimiter::Bracket))
    {
        i += 2;
    }
    i + usize::from(toks.get(i).is_some_and(|t| is_ident(t, "move")))
}

/// The written type of each closure parameter in `params` (the tokens between the
/// closure's `|`s), or the span of a parameter without one.
fn closure_param_types(params: &[TokenTree]) -> Result<Vec<TokenStream>, Span> {
    let mut out = Vec::new();
    let mut parts: Vec<&[TokenTree]> = Vec::new();
    let mut depth = 0_i32;
    let mut start = 0;
    for (k, t) in params.iter().enumerate() {
        if is_punct(t, '<') {
            depth += 1;
        } else if is_punct(t, '>') && !(k > 0 && is_punct(&params[k - 1], '-')) {
            depth -= 1;
        } else if depth == 0 && is_punct(t, ',') {
            parts.push(&params[start..k]);
            start = k + 1;
        }
    }
    if start < params.len() {
        parts.push(&params[start..]);
    }
    for part in parts {
        let first = part.first().map_or_else(Span::call_site, TokenTree::span);
        let mut colon = None;
        let mut k = 0;
        while k < part.len() {
            if is_punct(&part[k], ':') {
                let joint =
                    matches!(&part[k], TokenTree::Punct(p) if p.spacing() == Spacing::Joint);
                if joint && part.get(k + 1).is_some_and(|t| is_punct(t, ':')) {
                    k += 2;
                    continue;
                }
                colon = Some(k);
                break;
            }
            k += 1;
        }
        match colon {
            Some(c) if c > 0 && c + 1 < part.len() => {
                out.push(part[c + 1..].iter().cloned().collect());
            }
            _ => return Err(first),
        }
    }
    Ok(out)
}

/// `fip_fn!(prelint, N, closure)`: the closure certified with the declared bound `N`,
/// checked by `fip-prelint` at the construction instead of by this macro (no token
/// scan of the body). Outside a checking driver run (see [`checked_by_driver`]) a
/// compile error. Under it, for `|x: &T, y: U| -> &V { .. }`:
///
/// ```text
/// {
///     #[cfg(not(fip_prelint))] ::core::compile_error!("..");
///     #[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = false,
///         panic_macros = true, param(g = N)))]
///     fn __fip_prelint_checked<G: ::core::ops::Fn(&P0, A1) -> &R, P0: ?Sized, A1, R: ?Sized>(g: G) -> G { g }
///     let __fip_prelint_closure = __fip_prelint_checked(closure);
///     unsafe { <krate>::Certified::<N, _, false>::assume(__fip_prelint_closure) }
/// }
/// ```
///
/// The check function is generic only over its own parameters (see
/// [`prelint_check_generics`]), inferred from the closure at the call, so it names no
/// type parameter of an enclosing generic function (a nested item cannot: E0401).
/// The closure is its argument, so the bound `G: Fn(..)` is the closure's expected
/// signature: an elided `&` parameter is higher-ranked, and with a written return
/// type `-> &V` and exactly one such parameter the output borrows from it (rustc
/// rejects `|x: &u32| -> &u32 { x }` without an expected signature: "lifetime may not
/// live long enough"). The driver checks every analysed call of a function declaring
/// `param(g = N)`: for `g: G` it analyses the closure's `Fn*` methods at the call and
/// requires at most `N` allocations per call; for the check function (named
/// `__fip_prelint_checked`) it also forbids a free and recursion in the argument, as
/// its `fip` mark does. The checked value is the certified one.
fn fip_fn_prelint(krate: Option<TokenStream>, at: Span, n: u64, toks: &[TokenTree]) -> TokenStream {
    if toks.first().is_some_and(|t| is_ident(t, "bound"))
        && toks.get(1).is_some_and(|t| is_punct(t, '<'))
    {
        return compile_error(
            toks[0].span(),
            "fip_fn!(prelint, N, ..): `bound <= K` is not an argument here; `N` is the declared bound, checked by `fip-prelint`",
        );
    }
    let (arity, body_start) = match closure_shape(toks) {
        Ok(v) => v,
        Err(sp) => {
            let msg = if fn_path_shape(toks) {
                "fip_fn!(prelint, N, ..) takes a closure; a named function's bound is its certificate's: write `fip_fn!(path)`"
            } else {
                "fip_fn!(prelint, N, ..): expected a closure `|x: T, ..| body` after `prelint, N,`"
            };
            return compile_error(sp, msg);
        }
    };
    if arity > MAX_FIP_FN_ARITY {
        return compile_error(
            toks.first().map_or_else(Span::call_site, TokenTree::span),
            &format!(
                "fip_fn!: at most {MAX_FIP_FN_ARITY} closure parameters (`fip_strict::MAX_ARITY`)"
            ),
        );
    }
    let open = closure_open(toks);
    let types = match closure_param_types(&toks[open + 1..body_start - 1]) {
        Ok(t) => t,
        Err(sp) => {
            return compile_error(
                sp,
                "fip_fn!(prelint, N, ..): write the type of every closure parameter (`|x: T| ..`); the closure has no expected signature to infer them from",
            );
        }
    };
    if !checked_by_driver() {
        return compile_error(at, PRELINT_UNCHECKED);
    }
    let ret = toks.get(body_start..).and_then(|rest| {
        (rest.len() > 2 && is_punct(&rest[0], '-') && is_punct(&rest[1], '>'))
            .then(|| rest[2..rest.len() - 1].to_vec())
    });
    let generics = prelint_check_generics(&types, ret.as_deref());
    let parse = |src: &str| src.parse::<TokenStream>().unwrap_or_default();
    let mut out = TokenStream::new();
    out.extend(compile_error_cfg_guard());
    out.extend(parse(&format!(
        "#[cfg_attr(fip_prelint, fip::mark(kind = \"fip\", n = 0, strict = false, panic_macros = true, param(g = {n})))] fn __fip_prelint_checked<{generics}>(g: __FipG) -> __FipG {{ g }} let __fip_prelint_closure = __fip_prelint_checked"
    )));
    out.extend([TokenTree::Group(Group::new(
        Delimiter::Parenthesis,
        toks.iter().cloned().collect(),
    ))]);
    out.extend(parse(";"));
    let mut inner = strict::krate_item(&krate.unwrap_or_else(strict::default_krate), "Certified");
    inner.extend(parse(&format!(
        "::<{n}, _, false>::assume(__fip_prelint_closure)"
    )));
    out.extend(parse("unsafe"));
    out.extend([TokenTree::Group(Group::new(Delimiter::Brace, inner))]);
    TokenStream::from(TokenTree::Group(Group::new(Delimiter::Brace, out)))
}

/// Generic parameters of the driver-mode check function for a closure with parameter
/// types `types` and written return type `ret`, all fresh names (none from the
/// caller): `__FipG: Fn(..) -> ..` first, then one parameter per closure parameter. An
/// elided reference type `&T` / `&mut T` becomes `&__FipPk` / `&mut __FipPk` with
/// `__FipPk: ?Sized` (higher-ranked in the `Fn` bound, as in the closure's own
/// annotation); any other type becomes `__FipAk`. The output is `&__FipR` /
/// `&mut __FipR` (`?Sized`) when `ret` is an elided reference and exactly one
/// parameter is (Rust's elision in `Fn(..) -> ..`), otherwise `__FipR`.
fn prelint_check_generics(types: &[TokenStream], ret: Option<&[TokenTree]>) -> String {
    // `&` or `&mut` followed by a type without a lifetime: the reference prefix.
    let elided_ref = |ty: &[TokenTree]| -> Option<&'static str> {
        if !ty.first().is_some_and(|t| is_punct(t, '&')) || ty.len() < 2 {
            return None;
        }
        if is_punct(&ty[1], '\'') {
            return None;
        }
        if is_ident(&ty[1], "mut") {
            return (ty.len() > 2 && !is_punct(&ty[2], '\'')).then_some("&mut ");
        }
        Some("&")
    };
    let mut sig = Vec::new();
    let mut own = Vec::new();
    let mut refs = 0;
    for (k, ty) in types.iter().enumerate() {
        let ty: Vec<TokenTree> = ty.clone().into_iter().collect();
        if let Some(prefix) = elided_ref(&ty) {
            refs += 1;
            sig.push(format!("{prefix}__FipP{k}"));
            own.push(format!("__FipP{k}: ?::core::marker::Sized"));
        } else {
            sig.push(format!("__FipA{k}"));
            own.push(format!("__FipA{k}"));
        }
    }
    let out = match ret.and_then(elided_ref) {
        Some(prefix) if refs == 1 => {
            own.push("__FipR: ?::core::marker::Sized".to_string());
            format!("{prefix}__FipR")
        }
        _ => {
            own.push("__FipR".to_string());
            "__FipR".to_string()
        }
    };
    let mut generics = format!("__FipG: ::core::ops::Fn({}) -> {out}", sig.join(", "));
    for g in own {
        generics.push_str(", ");
        generics.push_str(&g);
    }
    generics
}

/// `#[cfg(not(fip_prelint))] ::core::compile_error!(..);`: a driver-mode expansion
/// compiled without the driver's cfg (only the environment variables forged) fails.
/// With [`strict::std_roots_check`]: a `::core` renamed by `extern crate X as core;`
/// could make `compile_error!` a no-op.
fn compile_error_cfg_guard() -> TokenStream {
    let mut out = strict::std_roots_check(&["core"]);
    out.extend(
        format!(
            "#[cfg(not(fip_prelint))] ::core::compile_error!({:?});",
            "fip_fn!(prelint, ..): `cfg(fip_prelint)` is not set, so this is not the `fip-prelint` driver; build with `cargo fip-prelint`"
        )
        .parse::<TokenStream>()
        .unwrap_or_default(),
    );
    out
}

/// `true` if `toks` looks like the path of a function: identifiers, `::`, `<..>`
/// (generic arguments, a qualified self type), ending in an identifier or a
/// turbofish's `>`. Whether it names a certified function is decided by the strict
/// callee resolution, as for a call of it.
fn fn_path_shape(toks: &[TokenTree]) -> bool {
    let Some(last) = toks.last() else {
        return false;
    };
    let mut depth = 0_i32;
    for (k, t) in toks.iter().enumerate() {
        match t {
            TokenTree::Ident(id) => {
                if depth == 0 && id.to_string() == "move" {
                    return false;
                }
            }
            TokenTree::Punct(p) => match p.as_char() {
                '<' => depth += 1,
                '>' if k > 0 && is_punct(&toks[k - 1], '-') => {}
                '>' => {
                    depth -= 1;
                    if depth < 0 {
                        return false;
                    }
                }
                ':' => {}
                ',' | '&' | '\'' | '-' | '*' | ';' | '=' if depth > 0 => {}
                _ => return false,
            },
            TokenTree::Group(_) if depth > 0 => {}
            _ => return false,
        }
    }
    depth == 0 && (matches!(last, TokenTree::Ident(_)) || is_punct(last, '>'))
}

/// `fip_fn!(path)`: the function at `path` with the bound of its certificate, read
/// as a strict call of it reads it (`Cert::allocs_for(__fip_strict_f, "f")`, the
/// `#[fip_impl]` / `#[fip_trait]` certificates for methods, the audited `core`
/// table, std constructors as allocation sites); with `bound <= K` the bound is `K`,
/// checked against the certificate's. A function without a certificate fails to
/// compile as a strict call of it does. No `unsafe` at the call site: the macro output
/// pairs the function with its own certificate's bound. Under Verus's driver no
/// certificate is read: the bound is `K`, or 0 without `bound` (see `fip_fn!`).
fn fip_fn_path(
    krate: Option<TokenStream>,
    toks: Vec<TokenTree>,
    limit: Option<u64>,
    no_panic: bool,
) -> TokenStream {
    let mut as_call: TokenStream = toks.iter().cloned().collect();
    as_call.extend([TokenTree::Group(Group::new(
        Delimiter::Parenthesis,
        TokenStream::new(),
    ))]);
    let mut scan = Scan {
        fn_name: "",
        sites: Vec::new(),
        recursion: Vec::new(),
    };
    scan.stream(as_call.clone(), false);
    let mut strict_scan = strict::StrictScan {
        krate,
        keep_tokens: true,
        ..strict::StrictScan::default()
    };
    strict_scan.stream(as_call, false);
    if let Some((sp, msg)) = strict_scan.errors.first() {
        return compile_error(*sp, &format!("fip_fn! strict: {msg}"));
    }
    if strict_scan.ctor_calls > 0 {
        // A capitalised path is accepted in a strict call only as a constructor,
        // which the rewritten call `Name { 0: .. }` proves; a path has no call to
        // rewrite, so it could name a function, `static` or `const`.
        return compile_error(
            toks.first().map_or_else(Span::call_site, TokenTree::span),
            "fip_fn!: a capitalised path (a constructor, or a function, `static` or `const` named like one) cannot be certified; wrap a constructor in a closure, e.g. `fip_fn!(|x: T| Name(x))`",
        );
    }
    if strict::under_verus() {
        // Verus's driver: `Certified<K, _>` for `bound <= K`, as in the plain build;
        // without `bound`, `Certified<0, _>` (the certificate `N` is a constant only
        // the plain build evaluates). The plain build checks the certificate.
        let k = limit.unwrap_or(0);
        return fip_fn_wrapper(
            &strict_scan.krate(),
            format!("{k}u64").parse().unwrap_or_default(),
            toks.into_iter().collect(),
            no_panic,
        );
    }
    let local = u64::try_from(scan.sites.len()).unwrap_or(u64::MAX);
    let mut bound = TokenStream::new();
    if no_panic {
        let Some(checks) = strict_scan.emit_no_panic_path_checks() else {
            return compile_error(
                toks.first().map_or_else(Span::call_site, TokenTree::span),
                "fip_fn!(panic_macros = false, path) takes a function with a certificate (`#[fip(strict = true, panic_macros = false)]`); a `core` table function or a std constructor has no certificate stating `panic_macros = false`",
            );
        };
        bound.extend(checks);
    }
    bound.extend(limited(strict_scan.emit_fip_fn_bound(local), limit, true));
    fip_fn_wrapper(
        &strict_scan.krate(),
        bound,
        toks.into_iter().collect(),
        no_panic,
    )
}

/// Must equal `fip_strict::MAX_ARITY` (the number of `FipFn` impls for
/// `Certified`; `tests/strict_accept.rs` uses arity 4, a doctest rejects 5).
const MAX_FIP_FN_ARITY: usize = 4;

/// Arity of the closure in `toks` and the index where its body starts. Leading outer
/// attributes (`#[..]`, e.g. `#[cfg_attr(verus_keep_ghost, verus_spec(..))]`) are
/// skipped here and kept on the closure in the output: they are not body tokens.
fn closure_shape(toks: &[TokenTree]) -> Result<(usize, usize), Span> {
    let first_span = toks.first().map_or_else(Span::call_site, TokenTree::span);
    let mut i = 0;
    while toks.get(i).is_some_and(|t| is_punct(t, '#'))
        && toks
            .get(i + 1)
            .is_some_and(|t| is_group(t, Delimiter::Bracket))
    {
        i += 2;
    }
    i += usize::from(toks.get(i).is_some_and(|t| is_ident(t, "move")));
    if !toks.get(i).is_some_and(|t| is_punct(t, '|')) {
        return Err(first_span);
    }
    if toks.get(i + 1).is_some_and(|t| is_punct(t, '|'))
        && matches!(&toks[i], TokenTree::Punct(p) if p.spacing() == Spacing::Joint)
    {
        return Ok((0, i + 2));
    }
    let mut j = i + 1;
    let mut depth = 0_i32;
    let mut commas = 0;
    let mut any = false;
    while j < toks.len() {
        let t = &toks[j];
        if depth == 0 && is_punct(t, '|') {
            break;
        }
        if is_punct(t, '<') {
            depth += 1;
        } else if is_punct(t, '>') {
            depth -= 1;
        } else if depth == 0 && is_punct(t, ',') {
            commas += 1;
            j += 1;
            continue;
        }
        any = true;
        j += 1;
    }
    if j >= toks.len() {
        return Err(first_span);
    }
    let trailing = is_punct(&toks[j - 1], ',');
    let arity = if any {
        commas + 1 - usize::from(trailing)
    } else {
        0
    };
    Ok((arity, j + 1))
}

/// `unsafe { <krate>::Certified::<{ checks; bound }, _, false>::assume(closure) }`,
/// or `.., true>::assume_no_panic_macros(..)` for `panic_macros = false`.
///
/// No item is declared, so the expression is also accepted inside functions verified
/// by Verus (which does not support item statements in function bodies).
fn fip_fn_wrapper(
    krate: &TokenStream,
    bound: TokenStream,
    closure: TokenStream,
    no_panic: bool,
) -> TokenStream {
    let parse = |src: &str| src.parse::<TokenStream>().unwrap_or_default();
    let mut inner = strict::krate_item(krate, "Certified");
    inner.extend(parse("::<"));
    inner.extend([TokenTree::Group(Group::new(Delimiter::Brace, bound))]);
    inner.extend(parse(if no_panic {
        ", _, true>::assume_no_panic_macros"
    } else {
        ", _, false>::assume"
    }));
    inner.extend([TokenTree::Group(Group::new(
        Delimiter::Parenthesis,
        closure,
    ))]);
    let mut out = parse("unsafe");
    out.extend([TokenTree::Group(Group::new(Delimiter::Brace, inner))]);
    TokenStream::from(TokenTree::Group(Group::new(Delimiter::Brace, out)))
}
