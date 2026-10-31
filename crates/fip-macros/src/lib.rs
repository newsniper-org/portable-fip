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
//! # fn main() { let mut v = 3; double(&mut v); assert_eq!(v, 6); }
//! ```
//!
//! Rejected:
//!
//! ```compile_fail
//! #[fip_macros::fip]
//! fn f(x: i32) -> Box<i32> { Box::new(x) }
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip]
//! fn f(x: &[u8]) -> usize { let v = vec![0u8; 4]; v.len() + x.len() }
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip]
//! fn f(x: &[u8]) -> usize { let y = x.to_vec(); y.len() }
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip]
//! fn f(n: u32) -> u32 { if n == 0 { 0 } else { f(n - 1) } }
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip(1)]
//! fn f(n: u32) -> u32 { let mut s = 0; for i in 0..n { let b = Box::new(i); s += *b; } s }
//! # fn main() {}
//! ```
//! ```compile_fail
//! #[fip_macros::fip(1)]
//! fn f(a: u8, b: u8) -> (Box<u8>, Box<u8>) { (Box::new(a), Box::new(b)) }
//! # fn main() {}
//! ```
//! ```compile_fail
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
//! async fn f() {}
//! # fn main() {}
//! ```

#![forbid(unsafe_code)]

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

const HEAP_TYPES: &[&str] = &[
    "Box",
    "Vec",
    "String",
    "Rc",
    "Arc",
    "BTreeMap",
    "BTreeSet",
    "HashMap",
    "HashSet",
    "VecDeque",
    "BinaryHeap",
    "LinkedList",
];
const HEAP_CONSTRUCTORS: &[&str] = &[
    "new",
    "pin",
    "with_capacity",
    "from",
    "from_iter",
    "new_uninit",
    "new_zeroed",
    "new_cyclic",
    "default",
];
const ALLOC_MACROS: &[&str] = &["vec", "format"];
const ALLOC_METHODS: &[&str] = &[
    "clone",
    "to_vec",
    "to_owned",
    "to_string",
    "collect",
    "push",
    "push_back",
    "push_front",
    "insert",
    "extend",
    "extend_from_slice",
    "reserve",
    "resize",
    "append",
    "repeat",
    "concat",
    "join",
    "into_boxed_slice",
];
const GHOST_MACROS: &[&str] = &["proof", "proof_decl", "proof_with"];

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
/// See the crate documentation for exactly what is checked.
#[proc_macro_attribute]
pub fn fip(attr: TokenStream, item: TokenStream) -> TokenStream {
    let toks: Vec<TokenTree> = attr.into_iter().collect();
    let mode = match toks.as_slice() {
        [] => Mode::Fip,
        [TokenTree::Literal(l)] => match l.to_string().parse::<u64>() {
            Ok(n) => Mode::FipN(n),
            Err(_) => return arg_error(l.span(), "fip", item),
        },
        [first, ..] => return arg_error(first.span(), "fip", item),
    };
    expand(mode, item)
}

/// Marks a function as functional-but-in-place: no allocation; frees and
/// recursion are allowed. See the crate documentation for exactly what is checked.
#[proc_macro_attribute]
pub fn fbip(attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Some(first) = attr.into_iter().next() {
        return arg_error(first.span(), "fbip", item);
    }
    expand(Mode::Fbip, item)
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
    name: String,
    body: Group,
}

/// Recognises `#[attr]* vis? (const|async|unsafe|safe|extern "abi"?)* fn name ... { body }`.
fn parse_fn(toks: &[TokenTree]) -> Result<FnShape, (Span, String)> {
    let first_span = toks.first().map_or_else(Span::call_site, TokenTree::span);
    let not_fn = || {
        (
            first_span,
            "FIP attributes apply only to functions with a body".to_string(),
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
    let Some(TokenTree::Group(body)) = toks.last() else {
        return Err(not_fn());
    };
    if body.delimiter() != Delimiter::Brace {
        return Err(not_fn());
    }
    Ok(FnShape {
        after_attrs,
        name: name.to_string(),
        body: body.clone(),
    })
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
                if bang_next && GHOST_MACROS.contains(&s.as_str()) {
                    i += 3; // name ! group
                    continue;
                }
                if bang_next && ALLOC_MACROS.contains(&s.as_str()) {
                    self.site(id.span(), format!("`{s}!`"), in_loop);
                }
                if HEAP_TYPES.contains(&s.as_str())
                    && toks.get(i + 1).is_some_and(|n| is_punct(n, ':'))
                    && toks.get(i + 2).is_some_and(|n| is_punct(n, ':'))
                    && let Some(TokenTree::Ident(f)) = toks.get(i + 3)
                    && HEAP_CONSTRUCTORS.contains(&f.to_string().as_str())
                {
                    self.site(id.span(), format!("`{s}::{f}`"), in_loop);
                }
                let prev_dot = i > 0 && is_punct(&toks[i - 1], '.');
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

fn expand(mode: Mode, item: TokenStream) -> TokenStream {
    let toks: Vec<TokenTree> = item.clone().into_iter().collect();
    let shape = match parse_fn(&toks) {
        Ok(s) => s,
        Err((span, msg)) => {
            let mut out = compile_error(span, &msg);
            out.extend(item);
            return out;
        }
    };
    let mut scan = Scan {
        fn_name: &shape.name,
        sites: Vec::new(),
        recursion: Vec::new(),
    };
    scan.stream(shape.body.stream(), false);

    let mut errors = TokenStream::new();
    let tag = mode.name();
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
                    "{tag}: direct recursion into `{}` (stack is not bounded); use #[fbip] or a loop",
                    shape.name
                ),
            ));
        }
    }
    if !errors.is_empty() {
        errors.extend(item);
        return errors;
    }

    let note = match mode {
        Mode::Fip => "declared `fip`: no allocation site and no direct self-recursion in the body",
        Mode::FipN(_) => {
            "declared `fip(N)`: at most N allocation sites, none in a loop, and no direct self-recursion in the body"
        }
        Mode::Fbip => {
            "declared `fbip`: no allocation site in the body (frees and recursion allowed)"
        }
    };
    let doc = format!(
        "#[doc = \"\"] #[doc = \"# FIP\"] #[doc = \"\"] #[doc = {:?}] #[doc = \"\"] \
         #[doc = \"Checked syntactically by `fip-macros`; this is a lint, not a proof. \
         Allocation behaviour is checked by `fip-testkit` tests.\"]",
        format!(
            "{note}{}",
            if let Mode::FipN(n) = mode {
                format!(" (N = {n}).")
            } else {
                ".".to_string()
            }
        )
    );
    let doc: TokenStream = doc.parse().unwrap_or_default();
    let mut out: TokenStream = toks[..shape.after_attrs].iter().cloned().collect();
    out.extend(doc);
    out.extend(toks[shape.after_attrs..].iter().cloned());
    out
}
