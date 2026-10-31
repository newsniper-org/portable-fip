// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `strict = true`: a function may call only
//!
//! 1. functions from the table of audited `core` functions ([`CORE_TABLE`]), or
//! 2. functions that are themselves `#[fip(strict = true)]` / `#[fip(N, strict = true)]`
//!    (or carry a hand-written certificate, as `fip-core` and `fip-alloc` do via
//!    `fip_strict::certs`).
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
//! uses `__fip_strict_Type__Tr__m`; `Self` stands for the `#[fip_impl]` type. The bound
//! is read through `Cert::allocs_for("<name>")`, so a certificate imported under
//! another function's name fails constant evaluation.
//!
//! What a token-level macro cannot resolve is rejected rather than trusted: method
//! calls (`x.m()`), calls through expressions (`(f)(x)`, `a[i](x)`), generic arguments
//! inside a callee path (`Foo::<u8>::m`; write `<Foo<u8>>::m`), generic traits in a
//! qualified path, the `?` operator, and macros outside a small allowlist. A
//! `fip_fn!(..)` argument is skipped: `fip_fn!` checks its closure itself, and a call
//! of it is bounded by the `param(..)` of the function it is passed to.

use proc_macro::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};

use crate::{GHOST_MACROS, HEAP_CONSTRUCTORS, HEAP_TYPES, is_group, is_ident, is_punct};
use fip_lint_rules::CORE_TABLE;

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
    /// The callee as written, for messages.
    shown: String,
    span: Span,
    in_loop: bool,
}

/// How a callee is named.
enum Callee {
    /// `a::b::name` / `name`: the path tokens before the name, with the trailing `::`.
    Path(Vec<TokenTree>),
    /// `<Ty as Tr>::name` / `<Ty>::name`: the type path without generic arguments,
    /// and the trait's last segment.
    Qualified {
        ty: Vec<TokenTree>,
        tr: Option<Ident>,
    },
}

#[derive(Default)]
pub(crate) struct StrictScan {
    pub(crate) params: Vec<Param>,
    pub(crate) calls: Vec<Call>,
    pub(crate) param_calls: Vec<ParamCall>,
    pub(crate) errors: Vec<(Span, String)>,
    /// Name of `Self` inside a `#[fip_impl]` block.
    pub(crate) self_ty: Option<String>,
    /// `panic_macros = false`: reject the panicking macros of [`ALLOWED_MACROS`].
    pub(crate) no_panic_macros: bool,
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

impl StrictScan {
    pub(crate) fn stream(&mut self, ts: TokenStream, in_loop: bool) {
        let toks: Vec<TokenTree> = ts.into_iter().collect();
        let mut loop_body_pending = false;
        let mut i = 0;
        while i < toks.len() {
            let t = &toks[i];
            if is_punct(t, '#')
                && toks
                    .get(i + 1)
                    .is_some_and(|n| is_group(n, Delimiter::Bracket))
            {
                i += 2;
                continue;
            }
            if is_punct(t, '?') {
                self.err(
                    t.span(),
                    "the `?` operator may call `From::from`, which cannot be checked; match explicitly",
                );
            }
            if let TokenTree::Group(g) = t {
                if matches!(g.delimiter(), Delimiter::Parenthesis | Delimiter::Bracket)
                    && toks
                        .get(i + 1)
                        .is_some_and(|n| is_group(n, Delimiter::Parenthesis))
                {
                    self.err(
                        g.span(),
                        "call through an expression cannot be checked; call a named function",
                    );
                }
                let body_of_loop = loop_body_pending && g.delimiter() == Delimiter::Brace;
                if body_of_loop {
                    loop_body_pending = false;
                }
                self.stream(g.stream(), in_loop || body_of_loop);
            } else if let TokenTree::Ident(id) = t {
                let s = id.to_string();
                if s == "loop" || s == "while" || s == "for" {
                    loop_body_pending = true;
                }
                i += self.on_ident(&toks, i, id, in_loop);
                continue;
            }
            i += 1;
        }
    }

    /// Handles the identifier at `toks[i]`; returns how many tokens to advance.
    fn on_ident(&mut self, toks: &[TokenTree], i: usize, id: &Ident, in_loop: bool) -> usize {
        let s = id.to_string();
        // Macro invocation `name!(..)` / `name![..]` / `name!{..}`.
        if toks.get(i + 1).is_some_and(|n| is_punct(n, '!'))
            && toks
                .get(i + 2)
                .is_some_and(|n| matches!(n, TokenTree::Group(_)))
        {
            // Ghost code, and `fip_fn!` closures: those are checked by `fip_fn!` itself
            // and their calls are bounded through the callee's `param(..)`.
            if GHOST_MACROS.contains(&s.as_str()) || s == "fip_fn" {
                return 3;
            }
            let panicking = ALLOWED_MACROS.contains(&s.as_str());
            if !panicking && s != "vec" && s != "format" {
                self.err(
                    id.span(),
                    &format!("macro `{s}!` cannot be checked (its expansion is not visible)"),
                );
            } else if panicking && self.no_panic_macros {
                self.err(
                    id.span(),
                    &format!(
                        "`{s}!` may panic, and `panic_macros = false` rejects panicking macros"
                    ),
                );
            }
            // Arguments are scanned when the group is reached.
            return 2;
        }
        let Some(paren) = call_position(toks, i) else {
            return 1;
        };
        if i > 0 && is_punct(&toks[i - 1], '.') {
            self.on_method_call(toks, i, id, in_loop);
        } else if KEYWORDS.contains(&s.as_str()) || upper_initial(&s) {
            // Control flow, or a tuple-struct / enum-variant constructor.
        } else if slice_qualified(toks, i) {
            if !CORE_TABLE.contains(&format!("slice::{s}").as_str()) {
                self.err(
                    id.span(),
                    &format!("`<[T]>::{s}` is not in the audited `core` table"),
                );
            }
        } else {
            match callee_path(toks, i) {
                Err((sp, msg)) => self.err(sp, &msg),
                Ok(Callee::Path(prefix)) => self.on_path_call(toks, paren, prefix, id, in_loop),
                Ok(Callee::Qualified { ty, tr }) => {
                    self.on_qualified_call(&ty, tr.as_ref(), id, in_loop);
                }
            }
        }
        1
    }

    /// `recv.name(..)`: allowed only as `param.call(..)` on a declared `FipFn` parameter.
    fn on_method_call(&mut self, toks: &[TokenTree], i: usize, id: &Ident, in_loop: bool) {
        let s = id.to_string();
        if s == "call"
            && i >= 2
            && let TokenTree::Ident(recv) = &toks[i - 2]
            && !(i >= 3 && is_punct(&toks[i - 3], '.'))
            && let Some(p) = param_index(&self.params, &recv.to_string())
        {
            self.param_calls.push(ParamCall {
                param: p,
                span: id.span(),
                in_loop,
            });
            return;
        }
        self.err(
            id.span(),
            &format!(
                "method call `.{s}(..)` cannot be resolved; call it by path, e.g. `Type::{s}(x, ..)`"
            ),
        );
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

    /// `<Ty as Tr>::name(..)` / `<Ty>::name(..)`.
    fn on_qualified_call(
        &mut self,
        ty: &[TokenTree],
        tr: Option<&Ident>,
        id: &Ident,
        in_loop: bool,
    ) {
        let s = id.to_string();
        let Some((TokenTree::Ident(last), module)) = ty.split_last() else {
            self.err(id.span(), "expected a type path in `<Type as Trait>::f`");
            return;
        };
        let shown = match tr {
            Some(t) => format!("<{last} as {t}>::{s}"),
            None => format!("<{last}>::{s}"),
        };
        let Some(ty_name) = self.type_name(last, &shown) else {
            return;
        };
        let cert_name = match tr {
            Some(t) => format!("{ty_name}__{}__{}", bare(&t.to_string()), bare(&s)),
            None => format!("{ty_name}__{}", bare(&s)),
        };
        self.calls.push(Call {
            cert_prefix: module.to_vec(),
            cert_name,
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
        let segs: Vec<String> = prefix
            .iter()
            .filter_map(|t| match t {
                TokenTree::Ident(x) => Some(x.to_string()),
                _ => None,
            })
            .collect();
        let heap_ctor = segs
            .last()
            .is_some_and(|l| HEAP_TYPES.contains(&l.as_str()))
            && HEAP_CONSTRUCTORS.contains(&s.as_str());
        if heap_ctor || in_core_table(&segs, &s) {
            return;
        }
        let shown: String = prefix
            .iter()
            .map(ToString::to_string)
            .chain([s.clone()])
            .collect();
        // `Type::m` / `Self::m`: the certificate sits next to the type's module path.
        let type_seg = match prefix.len().checked_sub(3).map(|k| &prefix[k]) {
            Some(TokenTree::Ident(t)) if upper_initial(&t.to_string()) => Some(t.clone()),
            _ => None,
        };
        let (cert_prefix, cert_name) = match type_seg {
            Some(t) => {
                let Some(ty_name) = self.type_name(&t, &shown) else {
                    return;
                };
                (
                    prefix[..prefix.len() - 3].to_vec(),
                    format!("{ty_name}__{}", bare(&s)),
                )
            }
            None => (prefix, bare(&s).to_string()),
        };
        self.calls.push(Call {
            cert_prefix,
            cert_name,
            shown,
            span: id.span(),
            in_loop,
        });
    }

    /// `FipFn::call(&param, (..))`.
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
            Some(p) => self.param_calls.push(ParamCall {
                param: p,
                span: id.span(),
                in_loop,
            }),
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
/// leading `::` if any), or `<Ty as Tr>::f`.
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
        let path_like = is_punct(prev, ':')
            || matches!(prev, TokenTree::Ident(id) if !KEYWORDS.contains(&id.to_string().as_str()));
        if path_like {
            // `Foo::<u8>::f`: generic arguments inside a path.
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
        Some(t) if plain_path(t) => match t.last() {
            Some(TokenTree::Ident(id)) => Some(id.clone()),
            _ => None,
        },
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

/// `prefix::__fip_strict_name.allocs_for("name")`, with the call's span so a missing
/// certificate is reported at the call site.
fn term(c: &Call) -> TokenStream {
    let mut out: TokenStream = c.cert_prefix.iter().cloned().collect();
    out.extend([TokenTree::Ident(Ident::new(
        &format!("__fip_strict_{}", c.cert_name),
        c.span,
    ))]);
    out.extend(ts(&format!(".allocs_for({:?})", c.cert_name)));
    out
}

impl StrictScan {
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
        let mut out = ts(&format!("{local}u64"));
        for c in self.calls.iter().filter(|c| !c.in_loop) {
            out.extend(ts("+"));
            out.extend(term(c));
        }
        for pc in self.param_calls.iter().filter(|c| !c.in_loop) {
            let k = self.params[pc.param].bound.unwrap_or(0);
            out.extend(ts(&format!("+ {k}u64")));
        }
        out
    }

    /// Statements asserting the bound and the loop rule.
    fn checks(&self, tag: &str, n: u64, local: u64, with_params: bool) -> TokenStream {
        let mut body = TokenStream::new();
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
            let mut a = term(c);
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
                    let mut a =
                        TokenStream::from(TokenTree::Punct(Punct::new('<', Spacing::Alone)));
                    a.extend([TokenTree::Ident(ty.clone())]);
                    a.extend(ts(&format!(
                        " as ::fip_strict::FipBound>::ALLOCS <= {k}u64, {:?}",
                        format!("{tag}: the argument passed as `{}` may allocate more than its declared bound {k}", p.name)
                    )));
                    body.extend(ts("::core::assert!"));
                    body.extend([paren(a)]);
                    body.extend(ts(";"));
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
        items.extend(ts(&format!(
            "const __fip_strict_{cert_name}: ::fip_strict::Cert = unsafe"
        )));
        let mut ctor = ts("::fip_strict::Cert::assume");
        let mut args = ts(&format!("{cert_name:?},"));
        args.extend(self.sum_expr(local));
        ctor.extend([paren(args)]);
        items.extend([brace(ctor)]);
        items.extend(ts(";"));
        // Evaluated eagerly at module level (also by `cargo check`); the checks on
        // generic parameters are in the body (post-monomorphisation).
        items.extend(ts(attrs));
        items.extend(ts(&format!("const __fip_strict_check_{cert_name}: () = ")));
        items.extend([brace(self.checks(tag, n, local, false))]);
        items.extend(ts(";"));

        let mut stmt = ts(
            "#[cfg(not(verus_keep_ghost))] #[allow(clippy::all, clippy::pedantic)] let () = const ",
        );
        stmt.extend([brace(self.checks(tag, n, local, true))]);
        stmt.extend(ts(";"));
        (items, stmt)
    }

    /// `checks; sum`: the body of the const argument giving a `fip_fn!` closure's bound.
    pub(crate) fn emit_fip_fn_bound(&self, local: u64) -> TokenStream {
        let mut body = self.checks("fip_fn!", u64::MAX, local, false);
        body.extend(self.sum_expr(local));
        body
    }
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
    fn keyword_list_is_sorted_and_lowercase() {
        assert!(KEYWORDS.windows(2).all(|w| w[0] < w[1]));
        let _ = is_ident;
    }
}
