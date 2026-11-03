// SPDX-License-Identifier: Apache-2.0
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
//! `.insert`, `.extend`, `.reserve`, `.resize`, …), which may allocate.
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
//! Contents of `proof!`, `proof_decl!`, `proof_with!` and of attributes inside the
//! body are skipped: they are Verus ghost code and erased in normal builds. Write
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
//!     core::mem::replace(v, Vec::new())
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
//! (or `#[fip(N, strict = true)]`) under `#[fip_trait]` on the trait. `#[fip_trait]`
//! emits `<dyn Trait>::__fip_strict_<m>` and `__fip_strict_<Trait>__<m>`, which
//! strict callers use for `x.m()`, `Trait::m(x)` and `<dyn Trait>::m(x)`. Implementations
//! under `#[fip_impl]` are checked against the contract at compile time (impl
//! certificate bound ≤ contract bound).
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
//! strict contract, mirroring the driver's `Mark::weaker_than` as far as a
//! certificate (`fip_strict::Cert`, made only by `unsafe` constructors) carries it:
//! the allocation bound (impl ≤ contract) and panic strictness (a contract with
//! `panic_macros = false` needs an implementation with `panic_macros = false`). The
//! kind needs no comparison: every certificate is `fip` (`#[fbip]` has no strict
//! mode). Not compared by the macro, only by `fip-prelint`: an implementation that is
//! not strict (`#[fbip]`, `#[fip]` without `strict = true`, or no attribute) has no
//! certificate, and the impl block cannot see whether the trait method has a contract
//! (a probe through `<dyn Trait>` would break impls of traits that are not
//! dyn-compatible); the driver reports it (measured: an `#[fbip]` implementation of a
//! strict contract compiles and is a `fip-prelint` error, "the declaration is weaker
//! than the contract").
//!
//! Implementation with a certificate weaker than the trait's contract (more
//! allocations):
//! ```compile_fail
//! # // expect: #[fip_impl]: impl certificate is weaker than contract (more allocations)
//! use fip_macros::{fip, fip_impl, fip_trait};
//! #[fip_trait]
//! pub trait Shape {
//!     #[fip(strict = true)]
//!     fn area(&self) -> u32;
//! }
//! pub struct Square(pub u32);
//! #[fip_impl]
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
//! pub trait Step {
//!     #[fip(strict = true, panic_macros = false)]
//!     fn step(&self, x: u8) -> u8;
//! }
//! pub struct Id;
//! #[fip_impl]
//! impl Step for Id {
//!     #[fip(strict = true)]
//!     fn step(&self, x: u8) -> u8 { x }
//! }
//! # fn main() {}
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
//! trait T {
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
//! functions in the audited `core` table (by full `core::`/`std::` path, or
//! `<[T]>::method` for slice methods) and functions with a certificate
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
//! generic arguments in a callee path:
//! ```compile_fail
//! # // expect: generic arguments in a callee path cannot be resolved
//! pub struct W<T>(T);
//! #[fip_macros::fip_impl]
//! impl<T> W<T> {
//!     #[fip_macros::fip(strict = true)]
//!     pub fn get(w: W<T>) -> T { w.0 }
//! }
//! #[fip_macros::fip(strict = true)]
//! fn f(w: W<u8>) -> u8 { W::<u8>::get(w) }
//! # fn main() {}
//! ```
//!
//! Methods (`#[fip_impl]`, see [`macro@fip_impl`]):
//!
//! an argument other than `crate = ..`:
//! ```compile_fail
//! # // expect: the only argument is `crate = path::to::fip_strict`
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
//! `Self::m` outside `#[fip_impl]`:
//! ```compile_fail
//! # // expect: `Self` in a strict function needs `#[fip_impl]`
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
//! trait Tr { #[fip_macros::fip(strict = true)] fn m(&self) -> u8; }
//! struct S;
//! #[fip_macros::fip_impl]
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
//! trait Tr {
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

#![forbid(unsafe_code)]

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

mod context;
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
    // Left by `#[fip_impl]` on a method it has already checked and rewritten; keeps
    // the attribute's path (and so the user's `use fip_macros::fip`) in use.
    let marker: Vec<TokenTree> = attr.clone().into_iter().collect();
    if let [TokenTree::Ident(m)] = marker.as_slice()
        && m.to_string() == IMPL_CHECKED
    {
        return item;
    }
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
}

const FIP_ARGS_HELP: &str = "expected `#[fip]`, `#[fip(N)]`, `#[fip(strict = true)]`, `#[fip(N, strict = true)]`, optionally with `param(name = K, ..)`, `panic_macros = false` and `crate = path::to::fip_strict` after `strict = true`, and `requires(i < j, j < xs.len())`";

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
                if !args.strict {
                    return Err((
                        key.span(),
                        "`panic_macros = ..` requires `strict = true` before it".to_string(),
                    ));
                }
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
                if !args.strict {
                    return Err((
                        key.span(),
                        "`crate = ..` requires `strict = true` before it".to_string(),
                    ));
                }
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
    fn stream(&mut self, ts: TokenStream, in_loop: bool) {
        let toks: Vec<TokenTree> = ts.into_iter().collect();
        let texts = path_texts(&toks);
        let ptoks = path_toks(&toks, &texts);
        let mut loop_body_pending = false;
        let mut i = 0;
        while i < toks.len() {
            let t = &toks[i];
            // Attributes inside the body (e.g. Verus loop invariants): skip.
            if is_punct(t, '#')
                && toks
                    .get(i + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Bracket))
            {
                i += 2;
                continue;
            }
            if let TokenTree::Ident(id) = t {
                let s = id.to_string();
                let bang_next = toks.get(i + 1).is_some_and(|n| is_punct(n, '!'));
                // Ghost code is erased; a `fip_fn!` closure is checked by `fip_fn!` and
                // counted through the declared bound of the parameter it is passed to.
                if bang_next && (GHOST_MACROS.contains(&s.as_str()) || s == "fip_fn") {
                    i += 3; // name ! group
                    continue;
                }
                if bang_next && ALLOC_MACROS.contains(&s.as_str()) {
                    self.site(id.span(), format!("`{s}!`"), in_loop);
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
                        self.site(toks[start].span(), c.shown(), in_loop);
                    }
                }
                let call_next = toks
                    .get(i + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Parenthesis))
                    || (toks.get(i + 1).is_some_and(|n| is_punct(n, ':'))
                        && toks.get(i + 2).is_some_and(|n| is_punct(n, ':'))
                        && toks.get(i + 3).is_some_and(|n| is_punct(n, '<')));
                if prev_dot && call_next && ALLOC_METHODS.contains(&s.as_str()) {
                    self.site(id.span(), format!("`.{s}()`"), in_loop);
                }
                if s == self.fn_name
                    && toks
                        .get(i + 1)
                        .is_some_and(|n| is_group(n, Delimiter::Parenthesis))
                {
                    let prev_path = i > 0 && is_punct(&toks[i - 1], ':');
                    let via_self_path = i >= 3
                        && is_punct(&toks[i - 1], ':')
                        && is_punct(&toks[i - 2], ':')
                        && is_ident(&toks[i - 3], "Self");
                    let via_self_dot = i >= 2 && prev_dot && is_ident(&toks[i - 2], "self");
                    if (!prev_path && !prev_dot) || via_self_path || via_self_dot {
                        self.recursion.push(id.span());
                    }
                }
                if s == "loop" || s == "while" || s == "for" {
                    loop_body_pending = true;
                }
            }
            if let TokenTree::Group(g) = t {
                let body_of_loop = loop_body_pending && g.delimiter() == Delimiter::Brace;
                if body_of_loop {
                    loop_body_pending = false;
                }
                self.stream(g.stream(), in_loop || body_of_loop);
            }
            i += 1;
        }
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
}

fn extract_param_traits(
    params: Option<&Group>,
    generics: &[TokenTree],
    ctx: Option<&ImplCtx>,
) -> Vec<(String, (Vec<TokenTree>, String))> {
    let mut out = Vec::new();
    let mut type_bounds: Vec<(String, (Vec<TokenTree>, String))> = Vec::new();

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
                if let Some(c) = ctx
                    && let Some(ref t) = c.trait_name
                {
                    out.push(("self".to_string(), (Vec::new(), t.clone())));
                }
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
    out
}

/// Certificate name of a strict function: `f`, `Type__m` or `Type__Trait__m`.
fn cert_name(fn_name: &str, ctx: Option<&ImplCtx>) -> String {
    let f = strict::bare(fn_name);
    match ctx {
        None => f.to_string(),
        Some(ImplCtx {
            self_ty,
            trait_name: None,
            ..
        }) => format!("{self_ty}__{f}"),
        Some(ImplCtx {
            self_ty,
            trait_name: Some(t),
            ..
        }) => format!("{self_ty}__{t}__{f}"),
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
    scan.stream(body.stream(), false);

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
    let in_trait = strict_args.is_some()
        && ctx.is_none()
        && shape.vis.is_empty()
        && fn_keyword_span(&toks, &shape)
            .is_some_and(|sp| context::enclosing(sp, &shape.name) == context::Enclosing::Trait);
    if in_trait {
        errors.extend(compile_error(body.span(), &strict_default_body_error(&tag)));
    } else if strict_args.is_some() && ctx.is_none() && has_receiver(shape.params.as_ref()) {
        errors.extend(compile_error(
            body.span(),
            &format!(
                "{tag} strict: a method needs `#[fip_macros::fip_impl]` on its `impl` block, which names its certificate `__fip_strict_<Type>__{}` (strict mode is not available on trait method declarations, see the crate documentation)",
                shape.name
            ),
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
    if let Some(ss) = &strict_scan {
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
        let (cert_items, stmt) = ss.emit_fn(&tag, &cert_name(&shape.name, ctx), &vis, n, local);
        items.extend(cert_items);
        let mut new_body = stmt;
        new_body.extend(body.stream());
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

/// Runs the strict checks on a function body; errors are appended to `errors`.
fn run_strict_scan(
    args: &FipArgs,
    shape: &FnShape,
    body: &Group,
    tag: &str,
    ctx: Option<&ImplCtx>,
    errors: &mut TokenStream,
) -> strict::StrictScan {
    let mut ss = strict::StrictScan {
        self_ty: ctx.map(|c| c.self_ty.clone()),
        no_panic_macros: !args.panic_macros,
        krate: args.krate.clone(),
        param_traits: extract_param_traits(shape.params.as_ref(), &shape.generics, ctx),
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
    ss.stream(body.stream(), false);
    ss.check_params();
    for (sp, msg) in &ss.errors {
        errors.extend(compile_error(*sp, &format!("{tag} strict: {msg}")));
    }
    ss
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
/// ending in `fip` (`#[fip(..)]`, `#[fip_macros::fip(..)]`, `#[my_facade::fip(..)]`).
///
/// ```
/// use fip_macros::{fip, fip_impl};
/// pub struct Cell<T> { v: T }
/// #[fip_impl]
/// impl<T> Cell<T> {
///     #[fip(strict = true)]
///     pub fn put(&mut self, v: T) -> T { core::mem::replace(&mut self.v, v) }
/// }
/// #[fip(strict = true)]
/// fn put_twice(c: &mut Cell<u8>) -> u8 { Cell::put(c, 1); Cell::put(c, 2) }
/// # fn main() { let mut c = Cell { v: 0 }; assert_eq!(put_twice(&mut c), 1); }
/// ```
#[proc_macro_attribute]
pub fn fip_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
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
            let mut out = compile_error(span, &format!("#[fip_impl]: {msg}"));
            out.extend(strip_fip_attrs(item));
            return out;
        }
    };
    match fip_impl_inner(&item, krate.as_ref()) {
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
/// is emitted as `<dyn Trait>::__fip_strict_<m>` and `__fip_strict_<Trait>__<m>`:
///
/// | item | certificate | strict callers write |
/// |---|---|---|
/// | `trait Trait { fn m }` | `__fip_strict_Trait__m` | `x.m()`, `Trait::m(x)`, `<dyn Trait>::m(x)` |
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
    if toks.get(pos).is_some_and(|t| is_ident(t, "unsafe")) {
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
    })
}

fn emit_trait_method_cert(
    trait_name: &Ident,
    vis: &[TokenTree],
    shape: &FnShape,
    args: &FipArgs,
) -> Result<TokenStream, (Span, String)> {
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
    let m = &shape.name;
    let n = match args.mode {
        Mode::FipN(n) => n,
        Mode::Fip | Mode::Fbip => 0,
    };
    let krate_path = args.krate.clone().unwrap_or_else(strict::default_krate);
    let krate_str: String = krate_path.into_iter().map(|t| t.to_string()).collect();
    let cert_ty = format!("{krate_str}::Cert");
    let assume_fn = if args.panic_macros {
        format!("{krate_str}::Cert::assume")
    } else {
        format!("{krate_str}::Cert::assume_no_panic_macros")
    };
    let vis_str: String = vis.iter().map(ToString::to_string).collect();
    let attrs = "#[doc(hidden)] #[allow(non_upper_case_globals, non_snake_case, dead_code, clippy::all, clippy::pedantic)] ";

    let impl_dyn_str = format!(
        "{attrs} impl dyn {trait_name} {{ pub const __fip_strict_{m}: {cert_ty} = unsafe {{ {assume_fn}({:?}, {n}u64) }}; }}",
        format!("{trait_name}__{m}")
    );
    let const_str = format!(
        "{attrs} {vis_str} const __fip_strict_{trait_name}__{m}: {cert_ty} = <dyn {trait_name}>::__fip_strict_{m};"
    );
    let mut out = TokenStream::new();
    if let Ok(ts) = impl_dyn_str.parse::<TokenStream>() {
        out.extend(ts);
    }
    if let Ok(ts) = const_str.parse::<TokenStream>() {
        out.extend(ts);
    }
    Ok(out)
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
        let certs = emit_trait_method_cert(&header.trait_name, &header.vis, &shape, &args)?;
        module_items.extend(certs);
        new_body.extend(mark_trait_method(item_toks, at));
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
    let mark = if let Some(r) = reason {
        format!("#[cfg_attr(fip_prelint, fip::exclude(reason = {r:?}))]")
    } else {
        "#[cfg_attr(fip_prelint, fip::exclude)]".to_string()
    };
    let doc = "#[doc = \"\"] #[doc = \"# FIP\"] #[doc = \"\"] #[doc = \"Excluded from FIP aggregation (`fip-prelint`). Calls contribute no events (user assumption).\"] #[allow(dead_code)]";
    let mut out = doc.parse::<TokenStream>().unwrap_or_default();
    if let Ok(m) = mark.parse::<TokenStream>() {
        out.extend(m);
    }
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
/// Inside `#[fip_extern]`, foreign function declarations can be:
/// - certified: `#[fip_cert(evidence = "..", allocs = N)]` or `#[fip(evidence = "..")]`
///   (requires non-empty `evidence = ".."`, emits `<vis> const __fip_strict_<name>: Cert`
///   outside the block for strict callers and a driver mark for `fip-prelint`);
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
/// dependency's.
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
    krate: Option<TokenStream>,
}

fn parse_exclude_attr(attr: TokenStream) -> Result<Option<String>, (Span, String)> {
    let parts = split_commas(attr);
    if parts.is_empty() {
        return Ok(None);
    }
    match parts.as_slice() {
        [] => Ok(None),
        [part] => match part.as_slice() {
            [TokenTree::Ident(key), eq, TokenTree::Literal(l)]
                if key.to_string() == "reason" && is_punct(eq, '=') =>
            {
                let s = l.to_string();
                let reason = s
                    .strip_prefix('"')
                    .and_then(|x| x.strip_suffix('"'))
                    .unwrap_or(&s);
                Ok(Some(reason.to_string()))
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
                evidence = Some(ev.to_string());
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
    let Some(evidence) = evidence else {
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
    if toks.get(pos).is_some_and(|t| is_ident(t, "unsafe")) {
        pos += 1;
    }
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
        let mark = if let Some(r) = excl {
            format!("#[cfg_attr(fip_prelint, fip::exclude(reason = {r:?}))]")
        } else {
            "#[cfg_attr(fip_prelint, fip::exclude)]".to_string()
        };
        let doc = "#[doc = \"\"] #[doc = \"# FIP\"] #[doc = \"\"] #[doc = \"Excluded from FIP aggregation (`fip-prelint`). Calls contribute no events (user assumption).\"] #[allow(dead_code)]";
        let mut mark_ts = doc.parse::<TokenStream>().unwrap_or_default();
        mark_ts.extend(mark.parse::<TokenStream>().unwrap_or_default());
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
    let krate_str: String = krate_path.into_iter().map(|t| t.to_string()).collect();
    let cert_ty = format!("{krate_str}::Cert");
    let assume_fn = format!("{krate_str}::Cert::assume");
    let vis_str: String = shape.vis.iter().map(ToString::to_string).collect();
    let attrs = "#[doc(hidden)] #[allow(non_upper_case_globals, non_snake_case, dead_code, clippy::all, clippy::pedantic)] ";
    let cert_str = format!(
        "{attrs} {vis_str} const __fip_strict_{fn_name}: {cert_ty} = unsafe {{ {assume_fn}({fn_name:?}, {}u64) }};",
        cert.allocs
    );
    let module_items = cert_str.parse::<TokenStream>().unwrap_or_default();

    let free_part = if cert.frees { ", frees = true" } else { "" };
    let mark = format!(
        "#[cfg_attr(fip_prelint, fip::cert(kind = {:?}, n = {}, evidence = {:?}{free_part}))]",
        cert.kind, cert.allocs, cert.evidence
    );
    let doc = format!(
        "#[doc = \"\"] #[doc = \"# FIP Certificate\"] #[doc = \"\"] \
         #[doc = {:?}] #[doc = \"\"] #[doc = {:?}]",
        format!(
            "Certified {}: at most {} allocation(s).",
            cert.kind, cert.allocs
        ),
        format!("Evidence: {}", cert.evidence)
    );
    // The mark applies to every declaration of the symbol (`fip-prelint` matches by
    // link symbol), so a declaration made only to carry it is not dead code.
    let mut mark_ts = "#[allow(dead_code)]"
        .parse::<TokenStream>()
        .unwrap_or_default();
    mark_ts.extend(doc.parse::<TokenStream>().unwrap_or_default());
    mark_ts.extend(mark.parse::<TokenStream>().unwrap_or_default());

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

/// Argument `#[fip_impl]` leaves on a strict method it has expanded.
const IMPL_CHECKED: &str = "__fip_impl_checked";

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
    if toks.get(pos).is_some_and(|t| is_ident(t, "unsafe")) {
        pos += 1;
    }
    if !toks.get(pos).is_some_and(|t| is_ident(t, "impl")) {
        return Err(not_impl());
    }
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
    let ctx = impl_ctx(&toks[pos..toks.len() - 1], &params, first)?;
    let (module_items, new_body) = rewrite_impl_body(body, &ctx, krate)?;
    let mut g = Group::new(Delimiter::Brace, new_body);
    g.set_span(body.span());
    let mut out = module_items;
    out.extend(toks[..toks.len() - 1].iter().cloned());
    out.extend([TokenTree::Group(g)]);
    Ok(out)
}

/// Self type and trait of an impl header (`Trait for Type` / `Type`, after the
/// generics).
fn impl_ctx(
    header: &[TokenTree],
    params: &[String],
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
    let self_ty = impl_self_ty(ty_toks, params)?;
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
    })
}
/// Expands the strict methods of an impl body: `(module-level items, new body)`.
/// `krate` (from `#[fip_impl(crate = ..)]`) applies to methods without their own.
fn rewrite_impl_body(
    body: &Group,
    ctx: &ImplCtx,
    krate: Option<&TokenStream>,
) -> Result<(TokenStream, TokenStream), (Span, String)> {
    let mut module_items = TokenStream::new();
    let mut new_body = TokenStream::new();
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
        match expand_parts(args.mode, Some(&args), &rest, Some(ctx)) {
            Ok((items, f)) => {
                module_items.extend(items);
                if let Some(t) = &ctx.trait_name
                    && let Ok(shape) = parse_fn(&rest.clone().into_iter().collect::<Vec<_>>())
                {
                    let m = &shape.name;
                    let self_ty = &ctx.self_ty;
                    let tr_path: String = ctx.trait_toks.iter().map(ToString::to_string).collect();
                    let krate_path = args.krate.clone().unwrap_or_else(strict::default_krate);
                    let krate_str: String = krate_path.into_iter().map(|t| t.to_string()).collect();
                    // Mirrors the driver's `Mark::weaker_than` as far as a certificate
                    // carries it: the allocation bound and panic strictness. The kind
                    // is always `fip` (no strict `#[fbip]`), so there is nothing to
                    // compare; `param(..)` is not compared by the driver either.
                    let impl_name = format!("{self_ty}__{t}__{m}");
                    let contract_name = format!("{t}__{m}");
                    let check_str = format!(
                        "#[doc(hidden)] #[allow(non_upper_case_globals, non_snake_case, dead_code, clippy::all, clippy::pedantic)] \
                         const _: () = {{ let impl_cert = __fip_strict_{self_ty}__{t}__{m}; \
                         let contract_cert = <dyn {tr_path}>::__fip_strict_{m}; \
                         let impl_allocs = {krate_str}::Cert::allocs_for(impl_cert, {impl_name:?}); \
                         let contract_allocs = {krate_str}::Cert::allocs_for(contract_cert, {contract_name:?}); \
                         ::core::assert!(impl_allocs <= contract_allocs, {:?}); \
                         ::core::assert!(!{krate_str}::Cert::no_panic_macros_for(contract_cert, {contract_name:?}) \
                         || {krate_str}::Cert::no_panic_macros_for(impl_cert, {impl_name:?}), {:?}); }};",
                        "#[fip_impl]: impl certificate is weaker than contract (more allocations)",
                        "#[fip_impl]: impl certificate is weaker than contract (the contract has `panic_macros = false`, the implementation does not)"
                    );
                    if let Ok(ts) = check_str.parse::<TokenStream>() {
                        module_items.extend(ts);
                    }
                }
                new_body.extend(checked_marker(&item_toks[at], &item_toks[at + 1]));
                new_body.extend(f);
            }
            Err(errors) => {
                module_items.extend(errors);
                new_body.extend(rest);
            }
        }
    }
    Ok((module_items, new_body))
}

/// `#[<path>(__fip_impl_checked)]` with the original attribute path, so the user's
/// `use fip_macros::fip` stays in use and `#[fip]` passes the method through.
fn checked_marker(hash: &TokenTree, attr: &TokenTree) -> TokenStream {
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
    let mut inner: TokenStream = path.into_iter().collect();
    inner.extend([TokenTree::Group(Group::new(
        Delimiter::Parenthesis,
        TokenStream::from(TokenTree::Ident(Ident::new(
            IMPL_CHECKED,
            Span::call_site(),
        ))),
    ))]);
    let mut out = TokenStream::from(hash.clone());
    out.extend([TokenTree::Group(Group::new(Delimiter::Bracket, inner))]);
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
/// body could call: `f`, `a::f`, `f::<T>`, `Type::m` / `<Type<..>>::m` (a
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
/// authoritative; this is an earlier, local error.
///
/// ```
/// let f = fip_macros::fip_fn!(bound <= 0, |x: u8| x ^ 1);
/// # let _ = f;
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
    let (limit, toks) = match bound_limit(toks) {
        Ok(v) => v,
        Err(e) => return e,
    };
    let (arity, body_start) = match closure_shape(&toks) {
        Ok(v) => v,
        Err(sp) => {
            if fn_path_shape(&toks) {
                return fip_fn_path(krate, toks, limit);
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
    let mut strict_scan = strict::StrictScan {
        krate,
        ..strict::StrictScan::default()
    };
    strict_scan.stream(body, false);
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
    let closure: TokenStream = toks.into_iter().collect();
    fip_fn_wrapper(
        &strict_scan.krate(),
        limited(strict_scan.emit_fip_fn_bound(local), limit),
        closure,
    )
}

/// The message for an argument that is neither a closure nor a function path.
const FIP_FN_SHAPE: &str = "fip_fn!: expected a closure `|args| body` or the path of a function with a certificate (`f`, `a::f`, `f::<T>`, `Type::m`, `<Type<..>>::m`, `<Type as Trait>::m`)";

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
/// function is written.
fn limited(bound: TokenStream, limit: Option<u64>) -> TokenStream {
    let Some(k) = limit else {
        return bound;
    };
    let mut out: TokenStream = "let __fip_fn_bound: u64 = ".parse().unwrap_or_default();
    out.extend([TokenTree::Group(Group::new(Delimiter::Brace, bound))]);
    out.extend(
        format!(
            "; ::core::assert!(__fip_fn_bound <= {k}u64, {:?}); __fip_fn_bound",
            format!("fip_fn!: the allocation bound exceeds the declared `bound <= {k}`")
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
/// table, std constructors as allocation sites). A function without a certificate
/// fails to compile as a strict call of it does. No `unsafe` at the call site: the
/// macro output pairs the function with its own certificate's bound.
fn fip_fn_path(
    krate: Option<TokenStream>,
    toks: Vec<TokenTree>,
    limit: Option<u64>,
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
        ..strict::StrictScan::default()
    };
    strict_scan.stream(as_call, false);
    if let Some((sp, msg)) = strict_scan.errors.first() {
        return compile_error(*sp, &format!("fip_fn! strict: {msg}"));
    }
    let local = u64::try_from(scan.sites.len()).unwrap_or(u64::MAX);
    fip_fn_wrapper(
        &strict_scan.krate(),
        limited(strict_scan.emit_fip_fn_bound(local), limit),
        toks.into_iter().collect(),
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

/// `unsafe { <krate>::Certified::<{ checks; bound }, _>::assume(closure) }`.
///
/// No item is declared, so the expression is also accepted inside functions verified
/// by Verus (which does not support item statements in function bodies).
fn fip_fn_wrapper(krate: &TokenStream, bound: TokenStream, closure: TokenStream) -> TokenStream {
    let parse = |src: &str| src.parse::<TokenStream>().unwrap_or_default();
    let mut inner = strict::krate_item(krate, "Certified");
    inner.extend(parse("::<"));
    inner.extend([TokenTree::Group(Group::new(Delimiter::Brace, bound))]);
    inner.extend(parse(", _>::assume"));
    inner.extend([TokenTree::Group(Group::new(
        Delimiter::Parenthesis,
        closure,
    ))]);
    let mut out = parse("unsafe");
    out.extend([TokenTree::Group(Group::new(Delimiter::Brace, inner))]);
    TokenStream::from(TokenTree::Group(Group::new(Delimiter::Brace, out)))
}
