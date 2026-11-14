// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `strict = true`: a function may call only
//!
//! 1. functions from the table of audited `core` functions ([`CORE_TABLE`]), or
//! 2. functions that are themselves `#[fip(strict = true)]` / `#[fip(N, strict = true)]`
//!    / `#[fip(total)]` (or carry a hand-written certificate, made with `unsafe`).
//!
//! Every strict function `f` gets a certificate `__fip_strict_f: fip_strict::Cert`
//! naming `f` and carrying an upper bound on the allocations one call of `f`
//! performs. The bound is `f`'s own allocation sites plus the certificates of its
//! callees, so:
//!
//! - a call to a function without a certificate does not compile;
//! - the bound of `f` is checked at compile time (`<= N`, `N = 0` for `#[fip]`);
//! - a callee called inside a loop must have bound 0;
//! - recursion through strict functions makes the constants refer to each other,
//!   which rustc rejects as a cycle in constant evaluation.
//!
//! Certificates are named after the callee as written: `f(..)` / `a::f(..)` use
//! `__fip_strict_f`; `Type::m(..)` / `a::Type::m(..)` / `<Type<..>>::m(..)` use
//! `__fip_strict_Type__m` (module-level, emitted by `#[fip_impl]`); `<Type as Tr>::m(..)`
//! uses `__fip_strict_Type__Tr__m` (and checks that `Tr` is the impl's trait, see
//! [`TraitCheck`]); `Self` stands for the `#[fip_impl]` type; a generic parameter `T`
//! in `T::m(..)` stands for its trait's contract. Name parts must not contain `__` or
//! start or end with `_` ([`segment_error`]), so two callees never share a name. The
//! bound is read through `Cert::allocs_for("<name>")`, so a certificate imported under
//! another function's name fails constant evaluation.
//!
//! What a token-level macro cannot resolve is rejected rather than trusted, or made
//! irrelevant by rewriting the emitted body ([`StrictScan::stream`]): method calls
//! (`x.m()`, except `param(..)` and contract parameters, emitted as type-checked path
//! calls), calls through expressions (`(f)(x)`, `a[i](x)`, `{ f }(x)`, `s.0(x)`),
//! capitalised callees other than constructors (`Name(..)` is emitted as
//! `(Name { 0: .. })`), relative `core` table paths, bare calls of names bound
//! locally, item declarations in the body, `for` loops over non-ranges, generic
//! arguments inside a callee path (`Foo::<u8>::m` is read as `<Foo<u8>>::m`), generic
//! traits in a qualified path, the `?` operator, and macros outside a small allowlist
//! (panicking macros are emitted as `::core::..`; ghost-code macros are emptied). A
//! `fip_fn!(..)` argument is skipped: `fip_fn!` checks its closure itself, and a call
//! of it is bounded by the `param(..)` of the function it is passed to.

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

use crate::{GHOST_MACROS, flow, is_group, is_ident, is_punct};
use fip_lint_rules::CORE_TABLE;
use fip_lint_rules::callee::{self, Callee as Callee2};

/// Macros a strict body may invoke: the panicking macros of the shared rule set
/// (`fip_lint_rules::PANIC_MACROS`). Their arguments are still checked; what they
/// expand to on the panic path is outside the guarantee (see crate docs);
/// `panic_macros = false` rejects them.
use fip_lint_rules::PANIC_MACROS as ALLOWED_MACROS;

const KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern",
    "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub",
    "ref", "return", "self", "static", "struct", "super", "trait", "true", "type", "unsafe", "use",
    "where", "while", "yield",
];

/// A parameter of the strict function declared as a certified callable.
pub(crate) struct Param {
    pub(crate) name: String,
    /// The parameter's type: a single generic type parameter.
    pub(crate) ty: Option<Ident>,
    /// Declared bound from `param(name = K)`, if any.
    pub(crate) bound: Option<u64>,
}

/// A call to a [`Param`].
pub(crate) struct ParamCall {
    param: usize,
    span: Span,
    in_loop: bool,
}

/// A call to a function that must carry a certificate.
pub(crate) struct Call {
    /// Module path before the certificate identifier, including the trailing `::`.
    cert_prefix: Vec<TokenTree>,
    /// Certificate name: `f`, `Type__m` or `Type__Trait__m`.
    cert_name: String,
    /// If this is a call through a trait contract: `(trait_name, method_name)`.
    pub(crate) trait_target: Option<(String, String)>,
    /// The callee as written, for messages.
    shown: String,
    span: Span,
    in_loop: bool,
}

/// One pair of `ffi(dep::sym = local::sym)`: strict calls of `dep::sym` read the
/// certificate `local::__fip_strict_sym` (name checked by `Cert::allocs_for`).
#[derive(Clone)]
pub(crate) struct FfiMap {
    /// The dependency's path as identifier segments joined by `::` (a leading `::`
    /// dropped), compared with the callee path as written.
    pub(crate) dep_key: String,
    /// The dependency's path as written.
    pub(crate) dep: Vec<TokenTree>,
    /// The local declaration's path as written.
    pub(crate) local: Vec<TokenTree>,
    /// The local path before its last segment, with the trailing `::`.
    pub(crate) local_prefix: Vec<TokenTree>,
    /// The local declaration's name (the certificate's name).
    pub(crate) local_name: String,
    /// The pair's first token, for messages and the driver's check function.
    pub(crate) span: Span,
}

/// How a callee is named.
enum Callee {
    /// `a::b::name` / `name`: the path tokens before the name, with the trailing `::`.
    Path(Vec<TokenTree>),
    /// `<Ty as Tr>::name` / `<Ty>::name`: the type path without generic arguments,
    /// and the trait path as written (its last segment is the trait's name).
    Qualified {
        ty: Vec<TokenTree>,
        tr: Option<Vec<TokenTree>>,
    },
}

/// A strict call `<Type as path::Trait>::m(..)` of a trait-impl certificate
/// `__fip_strict_Type__Trait__m`: the certificate names the trait by its last
/// segment only, so the generated code also checks that the caller's trait is the
/// trait of the `#[fip_impl]` block that made the certificate.
pub(crate) struct TraitCheck {
    /// The trait path as the caller wrote it.
    caller: Vec<TokenTree>,
    /// The module path of the certificate (the type's), with the trailing `::`.
    prefix: Vec<TokenTree>,
    /// `Type__Trait`: the suffix of the impl's `__fip_traitid_` / `__fip_traitsup_`
    /// items.
    key: String,
    span: Span,
}

#[derive(Default)]
pub(crate) struct StrictScan {
    pub(crate) params: Vec<Param>,
    pub(crate) calls: Vec<Call>,
    pub(crate) param_calls: Vec<ParamCall>,
    pub(crate) errors: Vec<(Span, String)>,
    /// Name of `Self` inside a `#[fip_impl]` block.
    pub(crate) self_ty: Option<String>,
    /// The trait of the `#[fip_impl]` block (`impl Trait for Type`), for messages.
    pub(crate) impl_trait: Option<String>,
    /// `panic_macros = false`: reject the panicking macros of [`ALLOWED_MACROS`].
    pub(crate) no_panic_macros: bool,
    /// Path of the `fip_strict` crate in generated code (`crate = ..`); `None` is
    /// `::fip_strict`.
    pub(crate) krate: Option<TokenStream>,
    /// Mapping of parameter name to its trait path and trait name: `(prefix, trait_name)`.
    pub(crate) param_traits: Vec<(String, (Vec<TokenTree>, String))>,
    /// Generic type parameters of the function and of its `impl` block.
    pub(crate) generic_params: Vec<String>,
    /// The first trait bound of a generic type parameter: `(param, (prefix, trait))`.
    pub(crate) type_bounds: Vec<(String, (Vec<TokenTree>, String))>,
    /// Names bound in the parameter list or the body (`let`, patterns, closure
    /// parameters), or used as values: a bare call of such a name may call the local
    /// binding, not the function whose certificate `__fip_strict_<name>` is read.
    pub(crate) shadowed: Vec<String>,
    /// `ffi(dep::sym = local::sym, ..)`.
    pub(crate) ffi: Vec<FfiMap>,
    /// Which pairs of `ffi` a call used.
    pub(crate) ffi_used: Vec<bool>,
    /// Trait identity checks of qualified calls.
    pub(crate) trait_checks: Vec<TraitCheck>,
    /// `true` under Verus's driver: the body is emitted as written (see
    /// [`StrictScan::stream`]).
    pub(crate) keep_tokens: bool,
    /// Calls of a capitalised name accepted as constructors.
    pub(crate) ctor_calls: usize,
    /// `FipFn::call(&g, ..)`: the index of its argument group in the current list and
    /// the type of `g`, whose first argument is rewritten to `(&g as &G)`.
    pub(crate) fipfn_arg: Option<(usize, Option<Ident>)>,
    /// Absolute roots the body uses (see [`std_roots_used`]); empty means `core`
    /// only. Checked by [`std_roots_check`] in the emitted bound checks.
    pub(crate) std_roots: Vec<&'static str>,
}

/// `&g, rest..` with the leading `&g` replaced by `(&g as &ty)`.
fn rewrite_first_ref_arg(args: TokenStream, ty: &Ident) -> TokenStream {
    let toks: Vec<TokenTree> = args.into_iter().collect();
    match toks.as_slice() {
        [amp, TokenTree::Ident(r), rest @ ..] if is_punct(amp, '&') => {
            let mut out = TokenStream::from(as_param_ref(r, ty));
            out.extend(rest.iter().cloned());
            out
        }
        _ => toks.into_iter().collect(),
    }
}

/// `(&r as &ty)`.
fn as_param_ref(r: &Ident, ty: &Ident) -> TokenTree {
    let sp = r.span();
    let mut inner: TokenStream = [
        TokenTree::Punct(Punct::new('&', Spacing::Alone)),
        TokenTree::Ident(r.clone()),
        ident("as", sp),
        TokenTree::Punct(Punct::new('&', Spacing::Alone)),
        TokenTree::Ident(ty.clone()),
    ]
    .into_iter()
    .collect();
    inner = inner
        .into_iter()
        .map(|mut t| {
            t.set_span(sp);
            t
        })
        .collect();
    let mut g = Group::new(Delimiter::Parenthesis, inner);
    g.set_span(sp);
    TokenTree::Group(g)
}

fn param_index(params: &[Param], name: &str) -> Option<usize> {
    params.iter().position(|p| p.name == name)
}

pub(crate) fn upper_initial(s: &str) -> bool {
    s.chars().next().is_some_and(char::is_uppercase)
}

/// An identifier as used inside a certificate name (`r#fn` becomes `fn`).
pub(crate) fn bare(id: &str) -> &str {
    id.strip_prefix("r#").unwrap_or(id)
}

/// An identifier token for `s` (`r#..` as a raw identifier).
pub(crate) fn ident(s: &str, span: Span) -> TokenTree {
    TokenTree::Ident(match s.strip_prefix("r#") {
        Some(raw) => Ident::new_raw(raw, span),
        None => Ident::new(s, span),
    })
}

/// Why `seg` cannot be a segment of a multi-part certificate name (`Type__m`,
/// `Type__Trait__m`, `Trait__m`): parts are joined by `__`, so a part containing
/// `__` or starting or ending with `_` would make two different callees share one
/// name (`fn Foo__new` and `Foo::new`).
pub(crate) fn segment_error(seg: &str) -> Option<String> {
    let s = bare(seg);
    (s.contains("__") || s.starts_with('_') || s.ends_with('_')).then(|| {
        format!(
            "`{s}` cannot be part of a certificate name: names are joined with `__` (`Type__method`), so a type, trait or method name used by strict code must not contain `__` or start or end with `_`"
        )
    })
}

/// [`segment_error`] for the name of a free function (one part, `__fip_strict_f`):
/// it must not contain `__` after its leading underscores, or it would equal a
/// multi-part name (`fn Foo__new` and `Foo::new`).
pub(crate) fn fn_name_error(name: &str) -> Option<String> {
    let s = bare(name);
    s.trim_start_matches('_').contains("__").then(|| {
        format!(
            "`{s}` cannot be the name of a strict function: certificate names join a type and a method with `__` (`__fip_strict_Type__method`), so a function name containing `__` would share one"
        )
    })
}

/// `::a::b::` / `a::b::` before `toks[i]`: the segment names, whether the path is
/// absolute (leading `::`), and how many tokens it takes.
fn path_prefix(toks: &[TokenTree], i: usize) -> (Vec<String>, bool, usize) {
    let mut segs = Vec::new();
    let mut k = i;
    loop {
        if k >= 2 && is_punct(&toks[k - 1], ':') && is_punct(&toks[k - 2], ':') {
            if let Some(TokenTree::Ident(id)) = k.checked_sub(3).map(|j| &toks[j]) {
                segs.push(id.to_string());
                k -= 3;
                continue;
            }
            segs.reverse();
            return (segs, true, i - (k - 2));
        }
        segs.reverse();
        return (segs, false, i - k);
    }
}

/// What a ghost-code macro invocation `name!(..)` at `toks[i]` becomes outside
/// Verus: `const { name! {} };`. The contents are not scanned, so they are dropped;
/// the macro is still invoked (an import or definition of it stays used), with no
/// input and in a const block, so whatever macro of that name is in scope cannot add
/// run-time code (code that is not const-evaluable is a compile error there).
pub(crate) fn ghost_stub(toks: &[TokenTree], i: usize) -> Vec<TokenTree> {
    let sp = toks[i].span();
    let mut inner: TokenStream = [toks[i].clone(), toks[i + 1].clone()].into_iter().collect();
    let mut empty = Group::new(Delimiter::Brace, TokenStream::new());
    empty.set_span(sp);
    inner.extend([TokenTree::Group(empty)]);
    let mut block = Group::new(Delimiter::Brace, inner);
    block.set_span(sp);
    let mut out = vec![ident("const", sp), TokenTree::Group(block)];
    if !toks.get(i + 3).is_some_and(|t| is_punct(t, ';')) {
        let mut semi = Punct::new(';', Spacing::Alone);
        semi.set_span(sp);
        out.push(TokenTree::Punct(semi));
    }
    out
}

/// `::` with `span`.
fn colons(span: Span) -> [TokenTree; 2] {
    let mut a = Punct::new(':', Spacing::Joint);
    a.set_span(span);
    let mut b = Punct::new(':', Spacing::Alone);
    b.set_span(span);
    [TokenTree::Punct(a), TokenTree::Punct(b)]
}

/// `::<root>::` tokens with `span`.
fn abs_root(root: &str, span: Span) -> Vec<TokenTree> {
    let mut out = Vec::new();
    out.extend(colons(span));
    out.push(ident(root, span));
    out.extend(colons(span));
    out
}

/// Splits call arguments at top-level commas, keeping commas inside turbofish and
/// qualified-path angle brackets (`HashMap::<u8, u8>::new()`, `<T as Tr<A, B>>::f`)
/// and closure parameter lists (`|a, b| a + b`) in their argument. A wrong split is
/// a compile error in the rewritten constructor (a field that does not parse), never
/// a different program.
fn split_args(ts: TokenStream) -> Vec<Vec<TokenTree>> {
    let toks: Vec<TokenTree> = ts.into_iter().collect();
    let mut parts: Vec<Vec<TokenTree>> = vec![Vec::new()];
    let mut angle = 0_i32;
    let mut in_closure_params = false;
    for (k, t) in toks.iter().enumerate() {
        let prev = k.checked_sub(1).map(|j| &toks[j]);
        let operand_pos = match prev {
            None => true,
            Some(TokenTree::Punct(p)) => p.as_char() != '?',
            Some(TokenTree::Ident(id)) => matches!(id.to_string().as_str(), "move" | "return"),
            Some(_) => false,
        };
        if is_punct(t, '|') && angle == 0 {
            if in_closure_params {
                in_closure_params = false;
            } else if operand_pos
                && !(matches!(t, TokenTree::Punct(p) if p.spacing() == Spacing::Joint)
                    && toks.get(k + 1).is_some_and(|n| is_punct(n, '|')))
            {
                in_closure_params = true;
            }
        } else if is_punct(t, '<') {
            let turbofish = prev.is_some_and(|p| is_punct(p, ':'));
            if angle > 0 || turbofish || operand_pos {
                angle += 1;
            }
        } else if is_punct(t, '>') && angle > 0 && !prev.is_some_and(|p| is_punct(p, '-')) {
            angle -= 1;
        } else if is_punct(t, ',') && angle == 0 && !in_closure_params {
            parts.push(Vec::new());
            continue;
        }
        if let Some(last) = parts.last_mut() {
            last.push(t.clone());
        }
    }
    if parts.last().is_some_and(Vec::is_empty) {
        parts.pop();
    }
    parts
}

/// Names bound in, or used as values by, `ts`: every identifier that is not
/// called (`f(..)`), not a macro (`m!`), not a path segment before `::`, not a
/// method or field (`.f`), and not a keyword; contents of `fip_fn!` and of the ghost
/// macros are skipped, as the scan skips them.
pub(crate) fn bound_names(ts: TokenStream, out: &mut Vec<String>) {
    let toks: Vec<TokenTree> = ts.into_iter().collect();
    let mut i = 0;
    while i < toks.len() {
        match &toks[i] {
            TokenTree::Ident(id) => {
                let s = id.to_string();
                let next = toks.get(i + 1);
                if next.is_some_and(|n| is_punct(n, '!'))
                    && (s == "fip_fn" || GHOST_MACROS.contains(&s.as_str()))
                {
                    i += 3;
                    continue;
                }
                let called = next.is_some_and(|n| {
                    is_group(n, Delimiter::Parenthesis) || is_punct(n, '!') || is_punct(n, ':')
                });
                let member = i > 0 && is_punct(&toks[i - 1], '.');
                if !called && !member && !KEYWORDS.contains(&s.as_str()) && !out.contains(&s) {
                    out.push(s);
                }
            }
            TokenTree::Group(g) => bound_names(g.stream(), out),
            _ => {}
        }
        i += 1;
    }
}

/// Rebindings of the declared callable parameters `names` (`param(g = K)` and
/// parameters of a contracted trait) in a strict body, as `(span, message)` errors.
///
/// The rewrites of `g.call(..)` to `(&g as &G).call(..)` and of `x.m(..)` to
/// `Tr::m(x, ..)` stop a rebinding to an unrelated type, but not one to a type that
/// derefs to the parameter's type (`let g = W(g)` with `W<G>: Deref<Target = G>`):
/// the cast and the argument coerce through a user `deref`, which may allocate. So
/// every binding of such a name in the body is rejected: in a `let` (also `if let`,
/// `while let`, let-else) pattern, a `for` pattern, a `match` arm pattern, a closure
/// parameter list and before `@`. The check is token-level and errs on the side of
/// rejecting: a struct field pattern `S { g: x }` named like a parameter is reported
/// too. Contents of `fip_fn!` and of the ghost macros are skipped, as the scan skips
/// them.
pub(crate) fn rebinding_errors(ts: TokenStream, names: &[String]) -> Vec<(Span, String)> {
    let mut errs = Vec::new();
    if !names.is_empty() {
        rebind_list(&ts.into_iter().collect::<Vec<_>>(), names, &mut errs);
    }
    errs
}

fn rebind_message(name: &str) -> String {
    format!(
        "`{name}` is a declared callable parameter and cannot be rebound in the body (a `let`, `for`, `match` or closure pattern): a rebinding to a type that derefs to the parameter's type would make its calls run a user `deref`; use another name"
    )
}

/// Every occurrence of a name of `names` in the pattern tokens `toks` (descending
/// into groups), except a path segment (`a::g`, `g::A`).
fn rebind_pattern(toks: &[TokenTree], names: &[String], errs: &mut Vec<(Span, String)>) {
    for (k, t) in toks.iter().enumerate() {
        match t {
            TokenTree::Ident(id) => {
                let s = id.to_string();
                let joint_colon = |t: &TokenTree| matches!(t, TokenTree::Punct(p) if p.as_char() == ':' && p.spacing() == Spacing::Joint);
                let path = (k > 1 && is_punct(&toks[k - 1], ':') && joint_colon(&toks[k - 2]))
                    || toks.get(k + 1).is_some_and(joint_colon);
                if !path && names.iter().any(|n| bare(n) == bare(&s)) {
                    errs.push((id.span(), rebind_message(bare(&s))));
                }
            }
            TokenTree::Group(g) => {
                rebind_pattern(&g.stream().into_iter().collect::<Vec<_>>(), names, errs);
            }
            _ => {}
        }
    }
}

/// `=` that is not part of `==`, `=>`, `<=`, `>=`, `!=`, `+=`, ..: an assignment or
/// the `=` of a `let`.
fn lone_eq(toks: &[TokenTree], k: usize) -> bool {
    let joint_before =
        k > 0 && matches!(&toks[k - 1], TokenTree::Punct(p) if p.spacing() == Spacing::Joint);
    matches!(&toks[k], TokenTree::Punct(p) if p.as_char() == '=' && p.spacing() == Spacing::Alone)
        && !joint_before
}

/// A `|` that opens a closure parameter list: at the start of the list, or after a
/// punctuation token or a keyword (`move`, `return`, ..), not after an operand
/// (`a | b`, `(x) | y`, `1 | 2`).
fn closure_bar(toks: &[TokenTree], k: usize) -> bool {
    is_punct(&toks[k], '|')
        && match k.checked_sub(1).map(|p| &toks[p]) {
            None | Some(TokenTree::Punct(_)) => true,
            Some(TokenTree::Ident(id)) => KEYWORDS.contains(&id.to_string().as_str()),
            Some(_) => false,
        }
}

fn rebind_list(toks: &[TokenTree], names: &[String], errs: &mut Vec<(Span, String)>) {
    let mut i = 0;
    while i < toks.len() {
        let t = &toks[i];
        if let TokenTree::Ident(id) = t {
            let s = id.to_string();
            if toks.get(i + 1).is_some_and(|n| is_punct(n, '!'))
                && (s == "fip_fn" || GHOST_MACROS.contains(&s.as_str()))
            {
                i += 3;
                continue;
            }
            if toks.get(i + 1).is_some_and(|n| is_punct(n, '@'))
                && names.iter().any(|n| bare(n) == bare(&s))
            {
                errs.push((id.span(), rebind_message(bare(&s))));
            }
            if s == "let" {
                // The pattern (and type) up to the `=` or the end of the statement.
                let end = (i + 1..toks.len())
                    .find(|&k| lone_eq(toks, k) || is_punct(&toks[k], ';'))
                    .unwrap_or(toks.len());
                rebind_pattern(&toks[i + 1..end], names, errs);
                i = end;
                continue;
            }
            if s == "for" {
                let end = (i + 1..toks.len())
                    .find(|&k| is_ident(&toks[k], "in"))
                    .unwrap_or(toks.len());
                rebind_pattern(&toks[i + 1..end], names, errs);
                i = end;
                continue;
            }
            if s == "match"
                && let Some(b) = (i + 1..toks.len()).find(|&k| is_group(&toks[k], Delimiter::Brace))
            {
                rebind_list(&toks[i + 1..b], names, errs);
                if let TokenTree::Group(g) = &toks[b] {
                    rebind_arms(&g.stream().into_iter().collect::<Vec<_>>(), names, errs);
                }
                i = b + 1;
                continue;
            }
        }
        if closure_bar(toks, i) {
            let end = (i + 1..toks.len())
                .find(|&k| is_punct(&toks[k], '|'))
                .unwrap_or(toks.len());
            rebind_pattern(&toks[i + 1..end], names, errs);
            i = end + 1;
            continue;
        }
        if let TokenTree::Group(g) = t {
            rebind_list(&g.stream().into_iter().collect::<Vec<_>>(), names, errs);
        }
        i += 1;
    }
}

/// The arms of a `match` body: each pattern (up to its guard `if` or its `=>`) is
/// checked as a pattern; guards and arm bodies as code.
fn rebind_arms(toks: &[TokenTree], names: &[String], errs: &mut Vec<(Span, String)>) {
    let mut i = 0;
    while i < toks.len() {
        let arrow = (i..toks.len()).find(|&k| {
            is_punct(&toks[k], '=')
                && matches!(&toks[k], TokenTree::Punct(p) if p.spacing() == Spacing::Joint)
                && toks.get(k + 1).is_some_and(|n| is_punct(n, '>'))
        });
        let Some(arrow) = arrow else {
            // No further arm: check the rest as a pattern (fail closed).
            rebind_pattern(&toks[i..], names, errs);
            return;
        };
        let guard = (i..arrow)
            .find(|&k| is_ident(&toks[k], "if"))
            .unwrap_or(arrow);
        rebind_pattern(&toks[i..guard], names, errs);
        rebind_list(&toks[guard..arrow], names, errs);
        let body = arrow + 2;
        let end = if toks
            .get(body)
            .is_some_and(|t| is_group(t, Delimiter::Brace))
        {
            body + 1
        } else {
            (body..toks.len())
                .find(|&k| is_punct(&toks[k], ','))
                .unwrap_or(toks.len())
        };
        rebind_list(
            &toks[body.min(toks.len())..end.min(toks.len())],
            names,
            errs,
        );
        i = end;
        if toks.get(i).is_some_and(|t| is_punct(t, ',')) {
            i += 1;
        }
    }
}

/// Item keywords rejected in a strict body: an item or `use` inside the body can
/// shadow the name of a certified callee for the body while the certificate is read
/// at module level.
const ITEM_KEYWORDS: &[&str] = &[
    "enum", "extern", "impl", "mod", "static", "struct", "trait", "type", "use",
];

impl StrictScan {
    /// Scans a strict body and returns it as emitted. Outside Verus's driver
    /// (`keep_tokens` false) the body is rewritten so that what compiles is what was
    /// checked:
    ///
    /// - a call of a capitalised name `Name(a, b)` (a tuple struct or tuple variant
    ///   constructor) becomes `(Name { 0: a, 1: b })`, which rustc accepts only for a
    ///   constructor: a function, `static`, `const` or local named `Name` is a compile
    ///   error instead of an unchecked call (also in patterns, where both forms mean
    ///   the same);
    /// - a bare panicking macro (`assert!`) becomes `::core::assert!`, so a local
    ///   `macro_rules! assert` is not what runs;
    /// - a bare ghost-code macro (`proof!`, ..) is removed: its contents are not
    ///   scanned, so they must not be compiled;
    /// - `g.call(args)` / `FipFn::call(&g, args)` on a `param(g = K)` parameter become
    ///   `(&g as &G).call(args)` / `FipFn::call((&g as &G), args)`, and `x.m(args)` on
    ///   a parameter of a contracted trait `Tr` becomes `Tr::m(x, args)`. These
    ///   rewrites alone do not stop a rebinding (`let g = W(g)` with `W<G>: Deref<Target
    ///   = G>` coerces through a user `deref`), so [`rebinding_errors`] rejects every
    ///   rebinding of such a parameter in the body.
    pub(crate) fn stream(&mut self, ts: TokenStream, in_loop: bool) -> TokenStream {
        self.stream_list(ts, in_loop, true)
    }

    /// [`StrictScan::stream`] for an expression (a closure body): no token starts a
    /// statement, so `{ f }(x)` is a call through an expression.
    pub(crate) fn stream_expr(&mut self, ts: TokenStream) -> TokenStream {
        self.stream_list(ts, false, false)
    }

    fn stream_list(&mut self, ts: TokenStream, in_loop: bool, stmts: bool) -> TokenStream {
        let toks: Vec<TokenTree> = ts.into_iter().collect();
        let loops = flow::loop_regions(&toks);
        let ends = if stmts {
            flow::stmt_block_ends(&toks)
        } else {
            vec![false; toks.len()]
        };
        self.check_for_loops(&toks);
        let mut out: Vec<TokenTree> = Vec::with_capacity(toks.len());
        let mut i = 0;
        while i < toks.len() {
            let t = &toks[i];
            let here = in_loop || loops[i];
            if is_punct(t, '#')
                && toks
                    .get(i + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Bracket))
            {
                out.extend(toks[i..i + 2].iter().cloned());
                i += 2;
                continue;
            }
            if is_punct(t, '?') {
                self.err(
                    t.span(),
                    "the `?` operator may call `From::from`, which cannot be checked; match explicitly",
                );
            }
            let call_next = toks
                .get(i + 1)
                .is_some_and(|n| is_group(n, Delimiter::Parenthesis));
            match t {
                TokenTree::Group(g) => {
                    let through_expr = match g.delimiter() {
                        Delimiter::Brace => !ends[i],
                        _ => true,
                    };
                    if call_next && through_expr {
                        self.err(
                            g.span(),
                            "call through an expression cannot be checked; call a named function",
                        );
                    }
                    let mut inner =
                        self.stream_list(g.stream(), here, g.delimiter() == Delimiter::Brace);
                    if let Some((at, ty)) = self.fipfn_arg.take() {
                        if at == i
                            && !self.keep_tokens
                            && let Some(ty) = ty
                        {
                            inner = rewrite_first_ref_arg(inner, &ty);
                        } else if at != i {
                            self.fipfn_arg = Some((at, ty));
                        }
                    }
                    let mut ng = Group::new(g.delimiter(), inner);
                    ng.set_span(g.span());
                    out.push(TokenTree::Group(ng));
                    i += 1;
                }
                TokenTree::Literal(l) => {
                    if call_next {
                        self.err(
                            l.span(),
                            "call through a tuple field or literal cannot be checked; call a named function",
                        );
                    }
                    out.push(t.clone());
                    i += 1;
                }
                TokenTree::Ident(id) => {
                    self.check_item(&toks, i, id);
                    i += self.on_ident(&toks, i, id, here, &mut out);
                }
                TokenTree::Punct(_) => {
                    out.push(t.clone());
                    i += 1;
                }
            }
        }
        out.into_iter().collect()
    }

    /// Rejects item declarations (see [`ITEM_KEYWORDS`]), nested `fn` items and
    /// `const` items.
    fn check_item(&mut self, toks: &[TokenTree], i: usize, id: &Ident) {
        let s = id.to_string();
        let next_ident = matches!(toks.get(i + 1), Some(TokenTree::Ident(_)));
        let item = ITEM_KEYWORDS.contains(&s.as_str())
            || (s == "fn" && next_ident)
            || (s == "const"
                && next_ident
                && !toks.get(i + 1).is_some_and(|t| is_ident(t, "fn"))
                && toks.get(i + 2).is_some_and(|t| is_punct(t, ':')))
            || (s == "macro_rules" && toks.get(i + 1).is_some_and(|t| is_punct(t, '!')));
        if item {
            self.err(
                id.span(),
                &format!(
                    "`{s}` declares an item inside a strict body, which is rejected: an item or `use` there can shadow the name of a certified function for the body, while its certificate is read at module level; move it out of the function"
                ),
            );
        }
    }

    /// A strict `for` loop must iterate over a range (`a..b`, `a..=b`): any other
    /// iterable calls `IntoIterator::into_iter` and `Iterator::next` of a type the
    /// token-level check cannot see (a user iterator's `next` may allocate). A range of
    /// integers steps through `core`'s `Step`, which user types cannot implement on
    /// stable Rust.
    fn check_for_loops(&mut self, toks: &[TokenTree]) {
        for (i, t) in toks.iter().enumerate() {
            let prev_dot = i > 0 && is_punct(&toks[i - 1], '.');
            if !is_ident(t, "for") || prev_dot || toks.get(i + 1).is_some_and(|n| is_punct(n, '<'))
            {
                continue;
            }
            let in_at = (i + 1..toks.len()).find(|&k| is_ident(&toks[k], "in"));
            let body = in_at.and_then(|k| flow::body_index(toks, k + 1));
            let range = match (in_at, body) {
                (Some(k), Some(b)) => (k + 1..b).any(|j| {
                    matches!(&toks[j], TokenTree::Punct(p) if p.as_char() == '.' && p.spacing() == Spacing::Joint)
                        && toks.get(j + 1).is_some_and(|n| is_punct(n, '.'))
                }),
                _ => false,
            };
            if !range {
                self.err(
                    t.span(),
                    "a strict `for` loop must iterate over a range (`a..b`, `a..=b`): another iterable calls `IntoIterator::into_iter` and `Iterator::next` of a type the check cannot see; use a `while` loop over indices",
                );
            }
        }
    }

    /// Handles the identifier at `toks[i]`, pushing what it consumed (possibly
    /// rewritten) to `out`; returns how many tokens it consumed.
    fn on_ident(
        &mut self,
        toks: &[TokenTree],
        i: usize,
        id: &Ident,
        in_loop: bool,
        out: &mut Vec<TokenTree>,
    ) -> usize {
        let s = id.to_string();
        // Macro invocation `name!(..)` / `name![..]` / `name!{..}`.
        if toks.get(i + 1).is_some_and(|n| is_punct(n, '!'))
            && let Some(TokenTree::Group(mg)) = toks.get(i + 2)
        {
            return self.on_macro(toks, i, id, mg, out);
        }
        let Some(paren) = call_position(toks, i) else {
            out.push(toks[i].clone());
            return 1;
        };
        if i > 0 && is_punct(&toks[i - 1], '.') {
            return self.on_method_call(toks, i, id, in_loop, out);
        }
        if self.on_std_callee(toks, i, in_loop) || KEYWORDS.contains(&s.as_str()) || s == "Self" {
            // A std heap constructor or trait function (any spelling), control flow,
            // or the `Self(..)` constructor of a tuple struct.
            out.push(toks[i].clone());
            return 1;
        }
        if upper_initial(&s) {
            return self.on_ctor(toks, i, paren, id, in_loop, out);
        }
        if slice_qualified(toks, i) {
            if !CORE_TABLE.contains(&format!("slice::{s}").as_str()) {
                self.err(
                    id.span(),
                    &format!("`<[T]>::{s}` is not in the audited `core` table"),
                );
            }
        } else {
            match callee_path(toks, i) {
                Err((sp, msg)) => self.err(sp, &msg),
                Ok(Callee::Path(prefix)) => {
                    self.on_path_call(toks, paren, prefix, id, in_loop);
                }
                Ok(Callee::Qualified { ty, tr }) => {
                    self.on_qualified_call(&ty, tr.as_deref(), id, in_loop);
                }
            }
        }
        out.push(toks[i].clone());
        1
    }

    /// A macro invocation at `toks[i]` (`name!` followed by `mg`); see
    /// [`StrictScan::stream`] for what is accepted and how it is rewritten.
    fn on_macro(
        &mut self,
        toks: &[TokenTree],
        i: usize,
        id: &Ident,
        mg: &Group,
        out: &mut Vec<TokenTree>,
    ) -> usize {
        let s = id.to_string();
        let (segs, absolute, _) = path_prefix(toks, i);
        let bare_name = segs.is_empty();
        // `fip_fn!` closures are checked by `fip_fn!` itself and their calls are
        // bounded through the callee's `param(..)`.
        if s == "fip_fn" {
            out.extend(toks[i..i + 3].iter().cloned());
            return 3;
        }
        // Ghost code: skipped, and emptied outside Verus (`ghost_stub`).
        if bare_name && GHOST_MACROS.contains(&s.as_str()) {
            if self.keep_tokens {
                out.extend(toks[i..i + 3].iter().cloned());
            } else {
                out.extend(ghost_stub(toks, i));
            }
            return 3;
        }
        let mut shown = String::new();
        for x in &segs {
            shown.push_str(x);
            shown.push_str("::");
        }
        shown.push_str(&s);
        let std_root =
            |roots: &[&str]| absolute && segs.len() == 1 && roots.contains(&segs[0].as_str());
        if ALLOWED_MACROS.contains(&s.as_str()) {
            if self.no_panic_macros {
                self.err(
                    id.span(),
                    &format!(
                        "`{s}!` may panic, and `panic_macros = false` rejects panicking macros"
                    ),
                );
            }
            if bare_name {
                if !self.keep_tokens {
                    out.extend(abs_root("core", id.span()));
                }
            } else if !std_root(&["core", "std"]) {
                self.err(
                    id.span(),
                    &format!(
                        "macro `{shown}!` is not the `core` macro: write `{s}!` or `::core::{s}!`"
                    ),
                );
            }
        } else if s == "vec" {
            if !std_root(&["std", "alloc"]) {
                self.err(
                    id.span(),
                    "write `vec!` as `::std::vec!` or `::alloc::vec!` in a strict body: a local `vec!` macro could shadow the standard one",
                );
            }
            if mg.stream().into_iter().any(|t| is_punct(&t, ';')) {
                self.err(
                    id.span(),
                    "`vec![e; n]` clones `e` n - 1 times, which may call user code (the element's `Clone`); strict mode cannot bound it: list the elements",
                );
            }
        } else if s == "format" {
            self.err(
                id.span(),
                "`format!` calls the arguments' `Display` / `Debug` code and may grow its buffer any number of times; strict mode cannot bound it",
            );
        } else {
            self.err(
                id.span(),
                &format!("macro `{shown}!` cannot be checked (its expansion is not visible)"),
            );
        }
        // `!` and the arguments are scanned when they are reached.
        out.push(toks[i].clone());
        1
    }

    /// `Name(..)` with a capitalised `Name`: accepted only as a tuple struct or tuple
    /// variant constructor, rewritten to `(Name { 0: .., 1: .. })` (see
    /// [`StrictScan::stream`]). The `Fn*` traits in type position (`dyn Fn(u8)`) are
    /// left alone.
    fn on_ctor(
        &mut self,
        toks: &[TokenTree],
        i: usize,
        paren: usize,
        id: &Ident,
        in_loop: bool,
        out: &mut Vec<TokenTree>,
    ) -> usize {
        let s = id.to_string();
        let prev = i.checked_sub(1).map(|k| &toks[k]);
        let type_position = matches!(s.as_str(), "Fn" | "FnMut" | "FnOnce")
            && prev.is_some_and(|p| is_ident(p, "dyn") || is_ident(p, "impl") || is_punct(p, '+'));
        if type_position {
            out.push(toks[i].clone());
            return 1;
        }
        self.ctor_calls += 1;
        if paren != i + 1 {
            self.err(
                id.span(),
                &format!(
                    "`{s}::<..>(..)`: generic arguments on a capitalised callee are rejected; strict mode accepts it only as a constructor, written without them"
                ),
            );
            out.push(toks[i].clone());
            return 1;
        }
        let Ok(Callee::Path(prefix)) = callee_path(toks, i) else {
            self.err(
                id.span(),
                &format!(
                    "`{s}(..)` through a qualified path: strict mode accepts a capitalised callee only as a constructor written by path (`Name(..)`, `Enum::Variant(..)`)"
                ),
            );
            out.push(toks[i].clone());
            return 1;
        };
        let TokenTree::Group(args) = &toks[paren] else {
            out.push(toks[i].clone());
            return 1;
        };
        let scanned = self.stream_list(args.stream(), in_loop, false);
        if self.keep_tokens {
            out.push(toks[i].clone());
            let mut g = Group::new(Delimiter::Parenthesis, scanned);
            g.set_span(args.span());
            out.push(TokenTree::Group(g));
            return 2;
        }
        let n = prefix.len().min(out.len());
        let mut path = out.split_off(out.len() - n);
        path.push(toks[i].clone());
        let parts = split_args(scanned);
        let last = parts.len().saturating_sub(1);
        let mut fields = TokenStream::new();
        for (k, part) in parts.into_iter().enumerate() {
            let rest = part.len() == 2
                && matches!(&part[0], TokenTree::Punct(p) if p.as_char() == '.' && p.spacing() == Spacing::Joint)
                && is_punct(&part[1], '.');
            if rest {
                if k != last {
                    self.err(
                        part[0].span(),
                        "`..` before the last field of a capitalised call: strict mode rewrites `Name(a, ..)` to `Name { 0: a, .. }`; write the pattern with numbered fields, e.g. `Name { 0: a, 2: c, .. }`",
                    );
                }
                fields.extend(part);
                continue;
            }
            // Generated tokens: the macro's context at the user's location, so lints
            // on hand-written code (`clippy::init_numbered_fields`) skip them.
            let sp = Span::call_site()
                .located_at(part.first().map_or_else(|| args.span(), TokenTree::span));
            let mut lit = Literal::usize_unsuffixed(k);
            lit.set_span(sp);
            fields.extend([TokenTree::Literal(lit)]);
            let mut colon = Punct::new(':', Spacing::Alone);
            colon.set_span(sp);
            fields.extend([TokenTree::Punct(colon)]);
            fields.extend(part);
            let mut comma = Punct::new(',', Spacing::Alone);
            comma.set_span(sp);
            fields.extend([TokenTree::Punct(comma)]);
        }
        let mut body = Group::new(Delimiter::Brace, fields);
        body.set_span(Span::call_site().located_at(args.span()));
        let mut inner: TokenStream = path.into_iter().collect();
        inner.extend([TokenTree::Group(body)]);
        let mut wrapped = Group::new(Delimiter::Parenthesis, inner);
        // The macro's context: `unused_parens` does not fire on macro output.
        wrapped.set_span(Span::call_site().located_at(id.span()));
        out.push(TokenTree::Group(wrapped));
        2
    }

    /// A call whose callee path (any spelling, normalised by
    /// `fip_lint_rules::callee`) is a std heap constructor or a constructor-like std
    /// trait function. Returns `true` if it was decided here:
    /// - a heap constructor needs no certificate: an allocating one is an allocation
    ///   site of this body (counted by the base scan), an audited non-allocating one
    ///   counts 0 (like the `core` table);
    /// - an allocating method called by path (`Vec::clone(&v)`, `<[T]>::to_vec(x)`)
    ///   is rejected: it may call user code (the element's `Clone`);
    /// - a trait function whose type is inferred (`Default::default()`) is rejected:
    ///   the tokens cannot tell what it builds.
    fn on_std_callee(&mut self, toks: &[TokenTree], i: usize, _in_loop: bool) -> bool {
        let texts = crate::path_texts(toks);
        let ptoks = crate::path_toks(toks, &texts);
        let start = callee::path_start(&ptoks, i);
        let c = callee::classify(&ptoks[start..=i]);
        let span = toks[start].span();
        match &c {
            Callee2::Alloc { method: false, .. } | Callee2::NonAllocating { .. } => true,
            Callee2::Alloc { method: true, .. } => {
                self.err(
                    span,
                    &format!(
                        "{}: an allocating method called by path may call user code (e.g. the element type's `Clone`), which strict mode cannot check",
                        c.shown()
                    ),
                );
                true
            }
            Callee2::Inferred { tr, f } => {
                self.err(
                    span,
                    &format!(
                        "{}: the type it builds is inferred, so the token-level check cannot tell whether it allocates; name the type, e.g. `Vec::<T>::{f}(..)` or `<Vec<T> as {tr}>::{f}(..)`",
                        c.shown()
                    ),
                );
                true
            }
            Callee2::Other => false,
        }
    }

    /// The receiver of `recv.name(..)` at `toks[i]`: a plain identifier (not a field
    /// `a.b.name()`, not a path).
    fn plain_receiver(toks: &[TokenTree], i: usize) -> Option<Ident> {
        match toks.get(i.checked_sub(2)?) {
            Some(TokenTree::Ident(r))
                if !(i >= 3 && (is_punct(&toks[i - 3], '.') || is_punct(&toks[i - 3], ':'))) =>
            {
                Some(r.clone())
            }
            _ => None,
        }
    }

    /// `recv.name(..)`: allowed as `param.call(..)` on a declared `FipFn` parameter
    /// or on a parameter whose type implements a contracted trait; rewritten to a
    /// path call that only type-checks for that parameter's type.
    fn on_method_call(
        &mut self,
        toks: &[TokenTree],
        i: usize,
        id: &Ident,
        in_loop: bool,
        out: &mut Vec<TokenTree>,
    ) -> usize {
        let s = id.to_string();
        let recv = Self::plain_receiver(toks, i);
        let direct = toks
            .get(i + 1)
            .is_some_and(|n| is_group(n, Delimiter::Parenthesis));
        if s == "call"
            && let Some(r) = &recv
            && let Some(p) = param_index(&self.params, &r.to_string())
        {
            self.param_calls.push(ParamCall {
                param: p,
                span: id.span(),
                in_loop,
            });
            if !self.keep_tokens
                && let Some(ty) = self.params[p].ty.clone()
            {
                // `(&g as &G).call(..)` names `G`'s `call`. This is not what keeps a
                // rebinding of `g` out (`let g = W(g)` with `W<G>: Deref<Target = G>`
                // coerces through `W::deref`): `rebinding_errors` rejects those.
                out.truncate(out.len().saturating_sub(2));
                out.push(as_param_ref(r, &ty));
                out.push(toks[i - 1].clone());
            }
            out.push(toks[i].clone());
            return 1;
        }
        if let Some(r) = &recv {
            let recv_str = r.to_string();
            if let Some((_, (prefix, trait_name))) =
                self.param_traits.iter().find(|(name, _)| name == &recv_str)
            {
                let (prefix, trait_name) = (prefix.clone(), trait_name.clone());
                for seg in [trait_name.as_str(), s.as_str()] {
                    if let Some(e) = segment_error(seg) {
                        self.err(id.span(), &e);
                    }
                }
                self.calls.push(Call {
                    cert_prefix: prefix.clone(),
                    cert_name: format!("{}__{}", bare(&trait_name), bare(&s)),
                    trait_target: Some((trait_name.clone(), s.clone())),
                    shown: format!("{recv_str}.{s}"),
                    span: id.span(),
                    in_loop,
                });
                if !self.keep_tokens
                    && direct
                    && let Some(TokenTree::Group(args)) = toks.get(i + 1)
                {
                    // `Tr::m(x, args)`.
                    out.truncate(out.len().saturating_sub(2));
                    out.extend(prefix);
                    out.push(ident(&trait_name, id.span()));
                    out.extend(colons(id.span()));
                    out.push(toks[i].clone());
                    let mut new_args: TokenStream = TokenStream::from(TokenTree::Ident(r.clone()));
                    let scanned = self.stream_list(args.stream(), in_loop, false);
                    if !scanned.is_empty() {
                        new_args.extend([TokenTree::Punct(Punct::new(',', Spacing::Alone))]);
                        new_args.extend(scanned);
                    }
                    let mut g = Group::new(Delimiter::Parenthesis, new_args);
                    g.set_span(args.span());
                    out.push(TokenTree::Group(g));
                    return 2;
                }
                out.push(toks[i].clone());
                return 1;
            }
        }
        if recv.as_ref().is_some_and(|r| r.to_string() == "self")
            && let Some(t) = &self.impl_trait
        {
            self.err(
                id.span(),
                &format!(
                    "method call `self.{s}(..)` in a trait impl cannot be resolved (an inherent method `{s}` would be called first): write `<Self as {t}>::{s}(self, ..)`"
                ),
            );
        } else {
            self.err(
                id.span(),
                &format!(
                    "method call `.{s}(..)` cannot be resolved; call it by path, e.g. `Type::{s}(x, ..)`"
                ),
            );
        }
        out.push(toks[i].clone());
        1
    }

    /// The name of the type `ty` (the last path segment), with `Self` resolved.
    fn type_name(&mut self, ty: &Ident, callee: &str) -> Option<String> {
        let t = ty.to_string();
        if t != "Self" {
            return Some(bare(&t).to_string());
        }
        if self.self_ty.is_none() {
            self.err(
                ty.span(),
                &format!(
                    "`{callee}`: `Self` in a strict function needs `#[fip_impl]` on the `impl` block (certificates are named after the type)"
                ),
            );
        }
        self.self_ty.clone()
    }

    /// A call through the contract of `trait_name` (at `prefix`) for `m`.
    fn contract_call(
        &mut self,
        prefix: Vec<TokenTree>,
        trait_name: &str,
        m: &str,
        shown: String,
        id: &Ident,
        in_loop: bool,
    ) {
        for seg in [trait_name, m] {
            if let Some(e) = segment_error(seg) {
                self.err(id.span(), &e);
            }
        }
        self.calls.push(Call {
            cert_prefix: prefix,
            cert_name: format!("{}__{}", bare(trait_name), bare(m)),
            trait_target: Some((trait_name.to_string(), m.to_string())),
            shown,
            span: id.span(),
            in_loop,
        });
    }

    /// A type segment naming a generic parameter of the function or `impl`: its
    /// first trait bound's contract, or an error (the certificate `T__m` would be
    /// read from whatever type is named `T` in scope).
    fn generic_param_call(
        &mut self,
        t: &str,
        tr: Option<&[TokenTree]>,
        id: &Ident,
        shown: &str,
        in_loop: bool,
    ) {
        let m = id.to_string();
        if let Some(tr) = tr
            && let Some((TokenTree::Ident(last), module)) = tr.split_last()
        {
            self.contract_call(
                module.to_vec(),
                &last.to_string(),
                &m,
                shown.to_string(),
                id,
                in_loop,
            );
            return;
        }
        if let Some((_, (prefix, trait_name))) = self.type_bounds.iter().find(|(p, _)| p == t) {
            let (prefix, trait_name) = (prefix.clone(), trait_name.clone());
            self.contract_call(prefix, &trait_name, &m, shown.to_string(), id, in_loop);
            return;
        }
        self.err(
            id.span(),
            &format!(
                "`{shown}`: `{t}` is a generic parameter, so no certificate names the function this calls; bound `{t}` by a trait with a strict contract (`#[fip_trait]`)"
            ),
        );
    }

    /// `<Ty as Tr>::name(..)` / `<Ty>::name(..)`.
    fn on_qualified_call(
        &mut self,
        ty: &[TokenTree],
        tr: Option<&[TokenTree]>,
        id: &Ident,
        in_loop: bool,
    ) {
        let s = id.to_string();
        if ty.first().is_some_and(|t| is_ident(t, "dyn")) {
            let after_dyn = &ty[1..];
            let Some((TokenTree::Ident(last), module)) = after_dyn.split_last() else {
                self.err(id.span(), "expected a trait path in `<dyn Trait>::f`");
                return;
            };
            let shown = format!("<dyn {last}>::{s}");
            self.contract_call(module.to_vec(), &last.to_string(), &s, shown, id, in_loop);
            return;
        }
        let Some((TokenTree::Ident(last), module)) = ty.split_last() else {
            self.err(id.span(), "expected a type path in `<Type as Trait>::f`");
            return;
        };
        let tr_last = tr.and_then(|t| match t.last() {
            Some(TokenTree::Ident(x)) => Some(x.clone()),
            _ => None,
        });
        let shown = match &tr_last {
            Some(t) => format!("<{last} as {t}>::{s}"),
            None => format!("<{last}>::{s}"),
        };
        if module.is_empty() && self.generic_params.contains(&last.to_string()) {
            self.generic_param_call(&last.to_string(), tr, id, &shown, in_loop);
            return;
        }
        let Some(ty_name) = self.type_name(last, &shown) else {
            return;
        };
        let mut parts = vec![ty_name.clone()];
        if let Some(t) = &tr_last {
            parts.push(bare(&t.to_string()).to_string());
        }
        parts.push(bare(&s).to_string());
        for seg in &parts {
            if let Some(e) = segment_error(seg) {
                self.err(id.span(), &e);
            }
        }
        if let (Some(t), Some(tr)) = (&tr_last, tr) {
            self.trait_checks.push(TraitCheck {
                caller: tr.to_vec(),
                prefix: module.to_vec(),
                key: format!("{ty_name}__{}", bare(&t.to_string())),
                span: id.span(),
            });
        }
        self.calls.push(Call {
            cert_prefix: module.to_vec(),
            cert_name: parts.join("__"),
            trait_target: None,
            shown,
            span: id.span(),
            in_loop,
        });
    }

    /// `path::name(..)` / `name(..)`.
    fn on_path_call(
        &mut self,
        toks: &[TokenTree],
        paren: usize,
        prefix: Vec<TokenTree>,
        id: &Ident,
        in_loop: bool,
    ) {
        let s = id.to_string();
        if prefix.is_empty() && param_index(&self.params, &s).is_some() {
            self.err(
                id.span(),
                &format!(
                    "call the parameter through `FipFn::call(&{s}, (..))` or `{s}.call((..))`"
                ),
            );
            return;
        }
        if s == "call"
            && prefix
                .iter()
                .rev()
                .nth(2)
                .is_some_and(|t| is_ident(t, "FipFn"))
        {
            self.on_fipfn_call(toks, paren, id, in_loop);
            return;
        }
        if prefix.is_empty() && self.shadowed.contains(&s) {
            self.err(
                id.span(),
                &format!(
                    "`{s}` is also bound in this function (a parameter, `let`, pattern or closure parameter, or a value named `{s}`), so `{s}(..)` may call that binding rather than the function whose certificate is read; rename the binding"
                ),
            );
            return;
        }
        let segs: Vec<String> = prefix
            .iter()
            .filter_map(|t| match t {
                TokenTree::Ident(x) => Some(x.to_string()),
                _ => None,
            })
            .collect();
        let shown: String = prefix
            .iter()
            .map(ToString::to_string)
            .chain([s.clone()])
            .collect();
        // Std heap constructors were decided before (`on_std_callee`).
        if in_core_table(&segs, &s) {
            if !prefix.first().is_some_and(|t| is_punct(t, ':')) {
                self.err(
                    id.span(),
                    &format!(
                        "write the `core` table function with an absolute path, `::{shown}`: a local module named `{}` (or `use .. as {0}`) would be called instead of the audited function",
                        segs[0]
                    ),
                );
            }
            return;
        }
        // `ffi(dep::sym = local::sym)`: a call of `dep::sym` reads `local::sym`'s
        // certificate (the driver checks that both name one foreign function).
        let key = segs
            .iter()
            .cloned()
            .chain([s.clone()])
            .collect::<Vec<_>>()
            .join("::");
        if let Some(k) = self.ffi.iter().position(|m| m.dep_key == key) {
            if let Some(u) = self.ffi_used.get_mut(k) {
                *u = true;
            }
            let m = &self.ffi[k];
            self.calls.push(Call {
                cert_prefix: m.local_prefix.clone(),
                cert_name: m.local_name.clone(),
                trait_target: None,
                shown,
                span: id.span(),
                in_loop,
            });
            return;
        }
        self.path_cert(prefix, id, shown, in_loop);
    }

    /// The certificate of `prefix::name(..)`: `Type::m` / `Self::m` read
    /// `__fip_strict_Type__m` next to the type's module path, `a::f` reads
    /// `a::__fip_strict_f`.
    fn path_cert(&mut self, prefix: Vec<TokenTree>, id: &Ident, shown: String, in_loop: bool) {
        let s = id.to_string();
        let type_seg = match prefix.len().checked_sub(3).map(|k| &prefix[k]) {
            Some(TokenTree::Ident(t)) if upper_initial(&t.to_string()) => Some(t.clone()),
            _ => None,
        };
        let (cert_prefix, cert_name) = if let Some(t) = type_seg {
            {
                if prefix.len() == 3 && self.generic_params.contains(&t.to_string()) {
                    self.generic_param_call(&t.to_string(), None, id, &shown, in_loop);
                    return;
                }
                let Some(ty_name) = self.type_name(&t, &shown) else {
                    return;
                };
                for seg in [ty_name.as_str(), s.as_str()] {
                    if let Some(e) = segment_error(seg) {
                        self.err(id.span(), &e);
                    }
                }
                (
                    prefix[..prefix.len() - 3].to_vec(),
                    format!("{ty_name}__{}", bare(&s)),
                )
            }
        } else {
            if let Some(e) = fn_name_error(&s) {
                self.err(id.span(), &e);
            }
            (prefix, bare(&s).to_string())
        };
        self.calls.push(Call {
            cert_prefix,
            cert_name,
            trait_target: None,
            shown,
            span: id.span(),
            in_loop,
        });
    }

    /// `FipFn::call(&param, (..))`, rewritten to `<G as FipFn<_>>::call(&param, (..))`.
    fn on_fipfn_call(&mut self, toks: &[TokenTree], paren: usize, id: &Ident, in_loop: bool) {
        let arg0: Vec<TokenTree> = match toks.get(paren) {
            Some(TokenTree::Group(g)) => g.stream().into_iter().take(2).collect(),
            _ => Vec::new(),
        };
        let param = match arg0.as_slice() {
            [amp, TokenTree::Ident(recv)] if is_punct(amp, '&') => {
                param_index(&self.params, &recv.to_string())
            }
            _ => None,
        };
        match param {
            Some(p) => {
                self.param_calls.push(ParamCall {
                    param: p,
                    span: id.span(),
                    in_loop,
                });
                self.fipfn_arg = Some((paren, self.params[p].ty.clone()));
            }
            None => self.err(
                id.span(),
                "`FipFn::call` must be applied to `&param` of a parameter declared with `param(name = K)`",
            ),
        }
    }

    fn err(&mut self, span: Span, msg: &str) {
        self.errors.push((span, msg.to_string()));
    }
}

/// If `toks[i]` is followed by a call (`(..)`, or `::<..>(..)`), returns the index of
/// the argument group.
fn call_position(toks: &[TokenTree], i: usize) -> Option<usize> {
    if toks
        .get(i + 1)
        .is_some_and(|n| is_group(n, Delimiter::Parenthesis))
    {
        return Some(i + 1);
    }
    if toks.get(i + 1).is_some_and(|n| is_punct(n, ':'))
        && toks.get(i + 2).is_some_and(|n| is_punct(n, ':'))
        && toks.get(i + 3).is_some_and(|n| is_punct(n, '<'))
    {
        let mut depth = 0_i32;
        let mut j = i + 3;
        while j < toks.len() {
            if is_punct(&toks[j], '<') {
                depth += 1;
            } else if is_punct(&toks[j], '>') {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            j += 1;
        }
        if toks
            .get(j + 1)
            .is_some_and(|n| is_group(n, Delimiter::Parenthesis))
        {
            return Some(j + 1);
        }
    }
    None
}

/// `true` if `toks[..i]` ends with `<[ .. ]>::`: a slice inherent method
/// (`<[T]>::len(xs)`), which names the method unambiguously.
fn slice_qualified(toks: &[TokenTree], i: usize) -> bool {
    i >= 5
        && is_punct(&toks[i - 1], ':')
        && is_punct(&toks[i - 2], ':')
        && is_punct(&toks[i - 3], '>')
        && is_group(&toks[i - 4], Delimiter::Bracket)
        && is_punct(&toks[i - 5], '<')
}

/// How the callee at `toks[i]` is named: `a::b::f` (path tokens before it, with a
/// leading `::` if any), or `<Ty as Tr>::f`; `a::Ty::<..>::f` is `<a::Ty<..>>::f`.
fn callee_path(toks: &[TokenTree], i: usize) -> Result<Callee, (Span, String)> {
    let mut start = i;
    loop {
        if start >= 2 && is_punct(&toks[start - 1], ':') && is_punct(&toks[start - 2], ':') {
            match toks.get(start.wrapping_sub(3)) {
                Some(TokenTree::Ident(_)) if start >= 3 => start -= 3,
                Some(t) if start >= 3 && is_punct(t, '>') => {
                    if start != i {
                        return Err((t.span(), GENERIC_PATH.to_string()));
                    }
                    return qualified(toks, start - 3);
                }
                _ => {
                    // Leading `::` (absolute path).
                    start -= 2;
                    break;
                }
            }
        } else {
            break;
        }
    }
    Ok(Callee::Path(toks[start..i].to_vec()))
}

const GENERIC_PATH: &str = "generic arguments in a callee path cannot be resolved; write `Type::f(..)` or `<Type<..>>::f(..)`";

/// `<Ty as Tr>` / `<Ty>` ending with the `>` at `toks[gt]`.
fn qualified(toks: &[TokenTree], gt: usize) -> Result<Callee, (Span, String)> {
    let gt_span = toks[gt].span();
    let mut depth = 0_i32;
    let mut lt = None;
    for k in (0..=gt).rev() {
        let arrow = k > 0 && is_punct(&toks[k - 1], '-');
        if is_punct(&toks[k], '>') && !arrow {
            depth += 1;
        } else if is_punct(&toks[k], '<') {
            depth -= 1;
            if depth == 0 {
                lt = Some(k);
                break;
            }
        }
    }
    let Some(lt) = lt else {
        return Err((gt_span, GENERIC_PATH.to_string()));
    };
    if lt > 0 {
        let prev = &toks[lt - 1];
        if is_punct(prev, ':') && lt >= 2 && is_punct(&toks[lt - 2], ':') {
            // `a::Type::<..>::m`: the generic arguments of the type, as in
            // `<a::Type<..>>::m`.
            return turbofish_type(toks, lt - 2, gt_span);
        }
        let path_like = is_punct(prev, ':')
            || matches!(prev, TokenTree::Ident(id) if !KEYWORDS.contains(&id.to_string().as_str()));
        if path_like {
            return Err((gt_span, GENERIC_PATH.to_string()));
        }
    }
    let inner = &toks[lt + 1..gt];
    let as_at = {
        let mut d = 0_i32;
        let mut found = None;
        for (k, t) in inner.iter().enumerate() {
            if is_punct(t, '<') {
                d += 1;
            } else if is_punct(t, '>') {
                d -= 1;
            } else if d == 0 && is_ident(t, "as") {
                found = Some(k);
                break;
            }
        }
        found
    };
    let (ty_part, trait_part) = match as_at {
        Some(k) => (&inner[..k], Some(&inner[k + 1..])),
        None => (inner, None),
    };
    // The type: a path, optionally followed by one `<..>` argument list.
    let path_end = ty_part
        .iter()
        .position(|t| is_punct(t, '<'))
        .unwrap_or(ty_part.len());
    let plain_path = |ts: &[TokenTree]| {
        !ts.is_empty()
            && matches!(ts.last(), Some(TokenTree::Ident(_)))
            && ts
                .iter()
                .all(|t| matches!(t, TokenTree::Ident(_)) || is_punct(t, ':'))
    };
    let args_ok = path_end == ty_part.len()
        || (is_punct(&ty_part[path_end], '<') && ty_part.last().is_some_and(|t| is_punct(t, '>')));
    if !plain_path(&ty_part[..path_end]) || !args_ok {
        return Err((
            gt_span,
            "the type in a qualified callee path must be a named type (`<Type as Trait>::f`, `<Type<..>>::f`)".to_string(),
        ));
    }
    let tr = match trait_part {
        None => None,
        Some(t) if plain_path(t) => Some(t.to_vec()),
        Some(_) => {
            return Err((
                gt_span,
                "a generic trait in `<Type as Trait<..>>::f` cannot be resolved to one impl; strict calls support traits without generic arguments".to_string(),
            ));
        }
    };
    Ok(Callee::Qualified {
        ty: ty_part[..path_end].to_vec(),
        tr,
    })
}

/// `a::Type::<..>::m` with the `::` before `<` starting at `toks[colon]`: the type
/// path `a::Type` (identifiers and `::`, optionally a leading `::`), as the type of
/// `<a::Type<..>>::m`. Generic arguments on an earlier segment are rejected.
fn turbofish_type(
    toks: &[TokenTree],
    colon: usize,
    gt_span: Span,
) -> Result<Callee, (Span, String)> {
    let mut start = colon;
    loop {
        if !(start >= 1 && matches!(toks[start - 1], TokenTree::Ident(_))) {
            return Err((gt_span, GENERIC_PATH.to_string()));
        }
        start -= 1;
        if start >= 2 && is_punct(&toks[start - 1], ':') && is_punct(&toks[start - 2], ':') {
            match toks.get(start.wrapping_sub(3)) {
                Some(TokenTree::Ident(_)) if start >= 3 => start -= 2,
                Some(t) if start >= 3 && is_punct(t, '>') => {
                    return Err((t.span(), GENERIC_PATH.to_string()));
                }
                _ => {
                    start -= 2;
                    break;
                }
            }
        } else {
            break;
        }
    }
    Ok(Callee::Qualified {
        ty: toks[start..colon].to_vec(),
        tr: None,
    })
}

fn in_core_table(segs: &[String], name: &str) -> bool {
    let Some((root, rest)) = segs.split_first() else {
        return false;
    };
    let rest: Vec<&str> = rest.iter().map(String::as_str).collect();
    fip_lint_rules::in_core_table(root, &rest, name)
}

fn ts(s: &str) -> TokenStream {
    s.parse().unwrap_or_default()
}

fn paren(inner: TokenStream) -> TokenTree {
    TokenTree::Group(Group::new(Delimiter::Parenthesis, inner))
}

fn brace(inner: TokenStream) -> TokenTree {
    TokenTree::Group(Group::new(Delimiter::Brace, inner))
}

/// `<krate>::Cert::allocs_for(prefix::__fip_strict_name, "name")`, with the call's
/// span so a missing certificate is reported at the call site. Called through the
/// `Cert` type, not as a method, so a constant of another type with an `allocs_for`
/// method is not accepted as a certificate.
fn term(c: &Call, krate: &TokenStream) -> TokenStream {
    cert_read(c, krate, "Cert::allocs_for")
}

/// `<krate>::<read>(<the callee's certificate>, "name")`.
fn cert_read(c: &Call, krate: &TokenStream, read: &str) -> TokenStream {
    let mut arg: TokenStream = if let Some((tr_path, m)) = &c.trait_target {
        // `<dyn prefix::Trait>::__fip_strict_<m>`, from tokens (a raw identifier
        // `r#type` names the constant `__fip_strict_type`).
        let mut a = TokenStream::from(TokenTree::Punct(Punct::new('<', Spacing::Alone)));
        a.extend([ident("dyn", c.span)]);
        a.extend(c.cert_prefix.iter().cloned());
        a.extend([ident(tr_path, c.span)]);
        a.extend([TokenTree::Punct(Punct::new('>', Spacing::Alone))]);
        a.extend(colons(c.span));
        a.extend([TokenTree::Ident(Ident::new(
            &format!("__fip_strict_{}", bare(m)),
            c.span,
        ))]);
        a
    } else {
        let mut a: TokenStream = c.cert_prefix.iter().cloned().collect();
        a.extend([TokenTree::Ident(Ident::new(
            &format!("__fip_strict_{}", c.cert_name),
            c.span,
        ))]);
        a
    };
    arg.extend(ts(&format!(", {:?}", c.cert_name)));
    let mut out = krate_item(krate, read);
    out.extend([paren(arg)]);
    out
}

/// The default path of the `fip_strict` crate.
pub(crate) fn default_krate() -> TokenStream {
    ts("::fip_strict")
}

/// `<krate>::<item>`. The appended segments take the span of the path's last token,
/// so an item missing under a `crate = ..` path is reported at that argument.
pub(crate) fn krate_item(krate: &TokenStream, item: &str) -> TokenStream {
    let span = krate
        .clone()
        .into_iter()
        .last()
        .map_or_else(Span::call_site, |t| t.span());
    let mut out = krate.clone();
    out.extend(ts(&format!("::{item}")).into_iter().map(|mut t| {
        t.set_span(span);
        t
    }));
    out
}

impl StrictScan {
    /// Driver-only check functions of `ffi(dep::sym = local::sym, ..)`, one per pair:
    /// `#[cfg_attr(fip_prelint, fip::ffi_map)] fn __fip_ffi_map_K() { let _ =
    /// (dep::sym as *const (), local::sym as *const ()); }`. `fip-prelint` reads the
    /// two foreign functions it names and reports a pair whose link symbols or ABIs
    /// differ. Emitted only under the driver (like `fip::mark`), as items at the start
    /// of the strict body, so the paths resolve as the body's calls do.
    pub(crate) fn emit_ffi_checks(&self) -> TokenStream {
        let mut out = TokenStream::new();
        for (k, m) in self.ffi.iter().enumerate() {
            let respan = |t: TokenStream| -> TokenStream {
                t.into_iter()
                    .map(|mut t| {
                        t.set_span(m.span);
                        t
                    })
                    .collect()
            };
            out.extend(respan(ts(&format!(
                "#[cfg_attr(fip_prelint, fip::ffi_map)] #[doc(hidden)] #[allow(dead_code, non_snake_case, clippy::all, clippy::pedantic)] fn __fip_ffi_map_{k}()"
            ))));
            let mut pair: TokenStream = m.dep.iter().cloned().collect();
            pair.extend(respan(ts("as *const (),")));
            pair.extend(m.local.iter().cloned());
            pair.extend(respan(ts("as *const ()")));
            let mut body = respan(ts("let _ ="));
            body.extend([paren(pair)]);
            body.extend(respan(ts(";")));
            let mut b = Group::new(Delimiter::Brace, body);
            b.set_span(m.span);
            out.extend([TokenTree::Group(b)]);
        }
        out
    }

    /// Path of the `fip_strict` crate in generated code.
    pub(crate) fn krate(&self) -> TokenStream {
        self.krate.clone().unwrap_or_else(default_krate)
    }

    /// `<krate>::<item>`, see [`krate_item`].
    pub(crate) fn krate_item(&self, item: &str) -> TokenStream {
        krate_item(&self.krate(), item)
    }

    /// Errors that need the declared parameter bounds.
    pub(crate) fn check_params(&mut self) {
        let mut errs = Vec::new();
        for pc in &self.param_calls {
            let p = &self.params[pc.param];
            match (p.bound, &p.ty) {
                (None, _) => errs.push((
                    pc.span,
                    format!("declare the bound of `{0}`: `#[fip(.., strict = true, param({0} = K))]`", p.name),
                )),
                (_, None) => errs.push((
                    pc.span,
                    format!("`{}` must have a named generic type `F` with `F: FipFn<..>` (not `impl FipFn`)", p.name),
                )),
                (Some(k), Some(_)) if pc.in_loop && k > 0 => errs.push((
                    pc.span,
                    format!("`{}` is called in a loop, so its declared bound must be 0 (is {k})", p.name),
                )),
                _ => {}
            }
        }
        self.errors.extend(errs);
    }

    /// `local + Σ cert(callee) + Σ declared(param)` over calls outside loops.
    fn sum_expr(&self, local: u64) -> TokenStream {
        let krate = self.krate();
        let mut out = ts(&format!("{local}u64"));
        for c in self.calls.iter().filter(|c| !c.in_loop) {
            out.extend(ts("+"));
            out.extend(term(c, &krate));
        }
        for pc in self.param_calls.iter().filter(|c| !c.in_loop) {
            let k = self.params[pc.param].bound.unwrap_or(0);
            out.extend(ts(&format!("+ {k}u64")));
        }
        out
    }

    /// Items checking each [`TraitCheck`]: the caller's trait implies the impl's
    /// (`__fip_traitid_<Type>__<Trait>::<T>()` for `T: CallerTrait`) and the impl's
    /// implies the caller's (a `T: __fip_traitsup_<Type>__<Trait>` satisfies
    /// `CallerTrait`). Two distinct traits cannot imply each other both ways through
    /// supertraits (a cycle), so the two traits are one.
    fn trait_check_items(&self) -> TokenStream {
        let mut out = TokenStream::new();
        for (k, tc) in self.trait_checks.iter().enumerate() {
            let respan = |t: TokenStream| -> TokenStream {
                t.into_iter()
                    .map(|mut t| {
                        t.set_span(tc.span);
                        t
                    })
                    .collect()
            };
            let caller: TokenStream = tc.caller.iter().cloned().collect();
            let prefix: TokenStream = tc.prefix.iter().cloned().collect();
            let key = &tc.key;
            out.extend(respan(ts(&format!(
                "#[allow(non_snake_case, dead_code)] fn __fip_trait_check_{k}<__FipT: ?Sized +"
            ))));
            out.extend(caller.clone());
            out.extend(respan(ts(">()")));
            let mut b = prefix.clone();
            b.extend(respan(ts(&format!("__fip_traitid_{key}::<__FipT>();"))));
            out.extend([brace(b)]);
            out.extend(respan(ts(&format!(
                "#[allow(non_snake_case, dead_code)] fn __fip_trait_check_back_{k}<__FipT: ?Sized +"
            ))));
            out.extend(prefix);
            out.extend(respan(ts(&format!("__fip_traitsup_{key}>()"))));
            let mut b = respan(ts("fn __fip_need<__FipX: ?Sized +"));
            b.extend(caller);
            b.extend(respan(ts(">() {} __fip_need::<__FipT>();")));
            out.extend([brace(b)]);
        }
        out
    }

    /// The roots the emitted code relies on: `::core` always, `::std` / `::alloc`
    /// when the body names them.
    fn roots(&self) -> &[&'static str] {
        if self.std_roots.is_empty() {
            &["core"]
        } else {
            &self.std_roots
        }
    }

    /// Statements asserting the bound and the loop rule (and, at module level,
    /// [`std_roots_check`]).
    fn checks(&self, tag: &str, n: u64, local: u64, with_params: bool) -> TokenStream {
        let mut body = self.trait_check_items();
        if !with_params {
            body.extend(std_roots_check(self.roots()));
        }
        // `n == u64::MAX` (a `fip_fn!` closure): no total to check.
        if n < u64::MAX {
            let mut a = self.sum_expr(local);
            a.extend(ts(&format!(
                " <= {n}u64, {:?}",
                format!("{tag}: the callees may allocate more than {n} times in total")
            )));
            body.extend(ts("::core::assert!"));
            body.extend([paren(a)]);
            body.extend(ts(";"));
        }
        for c in self.calls.iter().filter(|c| c.in_loop) {
            let mut a = term(c, &self.krate());
            a.extend(ts(&format!(
                " == 0u64, {:?}",
                format!("{tag}: `{}` is called in a loop and may allocate", c.shown)
            )));
            body.extend(ts("::core::assert!"));
            body.extend([paren(a)]);
            body.extend(ts(";"));
        }
        if with_params {
            for p in &self.params {
                if let (Some(k), Some(ty)) = (p.bound, &p.ty)
                    && self
                        .param_calls
                        .iter()
                        .any(|c| self.params[c.param].name == p.name)
                {
                    let bound_of = |item: &str| {
                        let mut a =
                            TokenStream::from(TokenTree::Punct(Punct::new('<', Spacing::Alone)));
                        a.extend([TokenTree::Ident(ty.clone())]);
                        a.extend(ts(" as "));
                        a.extend(self.krate_item("FipBound"));
                        a.extend(ts(&format!(">::{item}")));
                        a
                    };
                    let mut a = bound_of("ALLOCS");
                    a.extend(ts(&format!(
                        " <= {k}u64, {:?}",
                        format!("{tag}: the argument passed as `{}` may allocate more than its declared bound {k}", p.name)
                    )));
                    body.extend(ts("::core::assert!"));
                    body.extend([paren(a)]);
                    body.extend(ts(";"));
                    // `panic_macros = false` covers the callables it calls: their
                    // bodies must have been checked the same way.
                    if self.no_panic_macros {
                        let mut a = bound_of("NO_PANIC_MACROS");
                        a.extend(ts(&format!(
                            ", {:?}",
                            format!("{tag}: the argument passed as `{}` is not certified with `panic_macros = false` (`fip_fn!(panic_macros = false, ..)`), which this function's `panic_macros = false` requires", p.name)
                        )));
                        body.extend(ts("::core::assert!"));
                        body.extend([paren(a)]);
                        body.extend(ts(";"));
                    }
                }
            }
        }
        body
    }

    /// Items emitted before a strict function (or, for `#[fip_impl]`, before its
    /// `impl` block), and the statement inserted at the start of its body.
    /// `cert_name` is `f`, `Type__m` or `Type__Trait__m`.
    pub(crate) fn emit_fn(
        &self,
        tag: &str,
        cert_name: &str,
        vis: &[TokenTree],
        n: u64,
        local: u64,
    ) -> (TokenStream, TokenStream) {
        let attrs = "#[doc(hidden)] #[allow(non_upper_case_globals, non_snake_case, dead_code, clippy::all, clippy::pedantic)]";
        let mut items = ts(attrs);
        items.extend(vis.iter().cloned());
        items.extend(ts(&format!("const __fip_strict_{cert_name}: ")));
        items.extend(self.krate_item("Cert"));
        items.extend(ts("= unsafe"));
        // A body checked with `panic_macros = false` says so in its certificate, so
        // `#[fip_impl]` can compare it with a contract's (`Cert::no_panic_macros_for`).
        let mut ctor = self.krate_item(if self.no_panic_macros {
            "Cert::assume_no_panic_macros"
        } else {
            "Cert::assume"
        });
        let mut args = ts(&format!("{cert_name:?},"));
        args.extend(self.sum_expr(local));
        ctor.extend([paren(args)]);
        items.extend([brace(ctor)]);
        items.extend(ts(";"));
        // Evaluated eagerly at module level (also by `cargo check`); the checks on
        // generic parameters are in the body (post-monomorphisation).
        items.extend(ts(attrs));
        items.extend(ts(&format!("const __fip_check_{cert_name}: () = ")));
        items.extend([brace(self.checks(tag, n, local, false))]);
        items.extend(ts(";"));

        // Verus does not take the inline-const statement in a verified body, so under
        // Verus's driver it is left out of the `verus_keep_ghost` pass. The cfg is
        // emitted only there: in any other build it would be an undeclared cfg, an
        // `unexpected_cfgs` warning in every crate without
        // `check-cfg = ["cfg(verus_keep_ghost)"]` (measured: 5 in a facade consumer;
        // `#[allow(unexpected_cfgs)]` on the statement does not silence it), and
        // outside Verus it is never set, so the statement is kept as before.
        let mut stmt = if under_verus() {
            ts("#[cfg(not(verus_keep_ghost))]")
        } else {
            TokenStream::new()
        };
        stmt.extend(ts(
            "#[allow(clippy::all, clippy::pedantic)] let () = const ",
        ));
        stmt.extend([brace(self.checks(tag, n, local, true))]);
        stmt.extend(ts(";"));
        (items, stmt)
    }

    /// The bound of a `fip_fn!` closure as a literal: `local` when the body calls no
    /// certified function and no `param(..)` callable (no certificate to read), else
    /// `None`. Under Verus's driver this literal is the value's `ALLOCS`, the same
    /// number the plain build's constant evaluation of [`Self::emit_fip_fn_bound`]
    /// yields.
    pub(crate) fn literal_fip_fn_bound(&self, local: u64) -> Option<u64> {
        (self.calls.is_empty() && self.param_calls.is_empty() && self.trait_checks.is_empty())
            .then_some(local)
    }

    /// `checks; sum`: the body of the const argument giving a `fip_fn!` closure's bound.
    pub(crate) fn emit_fip_fn_bound(&self, local: u64) -> TokenStream {
        let mut body = self.checks("fip_fn!", u64::MAX, local, false);
        body.extend(self.sum_expr(local));
        body
    }

    /// Statements for `fip_fn!(panic_macros = false, path)`: the function's
    /// certificate must say that its body was checked with `panic_macros = false`
    /// (`Cert::no_panic_macros_for`). `None` if the path has no certificate to read
    /// (a `core` table function, a std constructor).
    pub(crate) fn emit_no_panic_path_checks(&self) -> Option<TokenStream> {
        if self.calls.is_empty() {
            return None;
        }
        let krate = self.krate();
        let mut body = std_roots_check(self.roots());
        for c in &self.calls {
            let mut a = cert_read(c, &krate, "Cert::no_panic_macros_for");
            a.extend(ts(&format!(
                ", {:?}",
                format!(
                    "fip_fn!(panic_macros = false, ..): `{}` is not certified with `panic_macros = false`",
                    c.shown
                )
            )));
            body.extend(ts("::core::assert!"));
            body.extend([paren(a)]);
            body.extend(ts(";"));
        }
        Some(body)
    }
}

/// An item that fails to compile (E0659, "`__fip_extern_crate_renames_<root>` is
/// ambiguous") unless each of `roots` (`core`, `std`, `alloc`) names the standard
/// crate of that name.
///
/// The absolute paths strict mode audits by spelling (`::core::mem::swap`), the
/// `::core::assert!` it emits for a bare `assert!`, and the `::core::assert!` of
/// its own bound checks all go through the extern prelude, which `extern crate X as
/// core;` at the crate root fills with `X` (re-audit N2: cert 0, measured 1 through
/// `X::mem::swap`; a no-op `X::assert!` would disable the bound checks). An attribute
/// macro cannot see the crate root, so the check is a name-resolution fact instead:
/// module `a` imports `::<root>` (the extern prelude's), module `b` declares
/// `extern crate <root>`, which loads the crate named `<root>` (the sysroot's, not the
/// alias), and a glob import of both is ambiguous exactly when they differ. A
/// plain `extern crate core;` or `extern crate alloc;` passes. Not covered: a Cargo
/// dependency renamed to `core` / `std` / `alloc` in `Cargo.toml` (`--extern core=..`
/// changes both), a manifest-level choice outside the source.
///
/// Left out under Verus's driver (whose expansion is not what runs).
pub(crate) fn std_roots_check(roots: &[&str]) -> TokenStream {
    if under_verus() || roots.is_empty() {
        return TokenStream::new();
    }
    let (mut a, mut b, mut uses) = (String::new(), String::new(), String::new());
    for r in roots {
        let name = format!("__fip_extern_crate_renames_{r}");
        a.push_str("pub(super) use ::");
        a.push_str(r);
        a.push_str(" as ");
        a.push_str(&name);
        a.push_str("; ");
        b.push_str("pub(super) extern crate ");
        b.push_str(r);
        b.push_str(" as ");
        b.push_str(&name);
        b.push_str("; ");
        uses.push_str("use ");
        uses.push_str(&name);
        uses.push_str(" as _; ");
    }
    ts(&format!(
        "#[doc(hidden)] #[allow(unused_imports, unused_extern_crates, clippy::all, clippy::pedantic)] \
         const _: () = {{ mod __fip_root_prelude {{ {a}}} mod __fip_root_crate {{ {b}}} \
         use __fip_root_prelude::*; use __fip_root_crate::*; {uses}}};"
    ))
}

/// The roots of absolute paths `::std::..` / `::alloc::..` in `ts` (descending into
/// groups), with `core` always first: every strict expansion uses `::core`.
pub(crate) fn std_roots_used(ts: TokenStream) -> Vec<&'static str> {
    fn walk(ts: TokenStream, out: &mut Vec<&'static str>) {
        let toks: Vec<TokenTree> = ts.into_iter().collect();
        for (k, t) in toks.iter().enumerate() {
            if let TokenTree::Group(g) = t {
                walk(g.stream(), out);
                continue;
            }
            // `::root` at the start of a path: not after `a::`, `<T>::` or `(..)::`.
            let after_segment = k >= 3
                && (matches!(&toks[k - 3], TokenTree::Ident(_) | TokenTree::Group(_))
                    || is_punct(&toks[k - 3], '>'));
            let leading = k >= 2
                && is_punct(&toks[k - 1], ':')
                && is_punct(&toks[k - 2], ':')
                && !after_segment;
            for root in ["std", "alloc"] {
                if leading && is_ident(t, root) && !out.contains(&root) {
                    out.push(root);
                }
            }
        }
    }
    let mut out = vec!["core"];
    walk(ts, &mut out);
    out
}

/// `true` when the expanding compiler is Verus's driver: proc macros run in the
/// compiler's process, whose executable is `rust_verify` for the upstream `verus`
/// launcher and for a source build (measured: `argv[0]` of both). Verus passes
/// `--cfg verus_keep_ghost` to rustc through its driver API, not in `argv`.
///
/// The executable is read from `argv[0]` and, when the process has no arguments, from
/// `std::env::current_exe()`: on a musl host `std::env::args_os()` is empty inside a proc
/// macro (std gets the arguments of a dynamic library only through glibc's `.init_array`
/// extension; measured with rustc 1.100.0-beta.10 on `x86_64-unknown-linux-musl`:
/// `argc = 0`, `current_exe()` = `.../bin/rustc`; on glibc `argc = 25`, `argv[0]` = `rustc`),
/// so the `argv[0]` test alone made every strict expansion the plain one under Verus there
/// (fip-core: 6 errors, "Verus does not currently support const block expressions").
/// A Verus driver under another executable name still fails visibly, as before
/// (`TODOs/strict-open-items.md`, item 12).
pub(crate) fn under_verus() -> bool {
    let argv0 = std::env::args_os().next();
    let exe = match argv0 {
        Some(a) => Some(std::path::PathBuf::from(a)),
        None => std::env::current_exe().ok(),
    };
    exe.is_some_and(|p| is_verus_driver(&p))
}

/// `true` for the path of Verus's rustc driver executable, `rust_verify`.
fn is_verus_driver(exe: &std::path::Path) -> bool {
    exe.file_stem().is_some_and(|s| s == "rust_verify")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_table_roots() {
        let s = |v: &[&str]| v.iter().map(ToString::to_string).collect::<Vec<_>>();
        assert!(in_core_table(&s(&["core", "mem"]), "swap"));
        assert!(in_core_table(&s(&["std", "mem"]), "replace"));
        assert!(!in_core_table(&s(&["alloc", "mem"]), "swap"));
        assert!(!in_core_table(&s(&["core", "mem"]), "take"));
        assert!(!in_core_table(&s(&["mem"]), "swap"));
    }

    #[test]
    fn verus_driver_is_recognised_by_its_executable() {
        use std::path::Path;
        assert!(is_verus_driver(Path::new("rust_verify")));
        assert!(is_verus_driver(Path::new(
            "/opt/verus/source/target-verus/release/rust_verify"
        )));
        assert!(is_verus_driver(Path::new("C:/verus/rust_verify.exe")));
        assert!(!is_verus_driver(Path::new(
            "/home/u/.rustup/toolchains/beta/bin/rustc"
        )));
        assert!(!is_verus_driver(Path::new("rust_verify_test")));
        assert!(!is_verus_driver(Path::new("")));
        // This test binary is not Verus's driver, by either source of the executable name.
        assert!(!under_verus());
    }

    #[test]
    fn keyword_list_is_sorted_and_lowercase() {
        assert!(KEYWORDS.windows(2).all(|w| w[0] < w[1]));
        let _ = is_ident;
    }
}
