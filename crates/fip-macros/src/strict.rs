// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `strict = true`: a function may call only
//!
//! 1. functions from the table of audited `core` functions ([`CORE_TABLE`]), or
//! 2. functions that are themselves `#[fip(strict = true)]` / `#[fip(N, strict = true)]`
//!    (or carry a hand-written certificate, as `fip-core` and `fip-alloc` do via
//!    `fip_strict::certs`).
//!
//! Every strict function `f` gets a companion constant `__fip_strict_f: u64`: an upper
//! bound on the allocations one call of `f` performs. It is defined as `f`'s own
//! allocation sites plus the companion constants of its callees, so:
//!
//! - a call to a function without a companion constant does not compile;
//! - the bound of `f` is checked at compile time (`<= N`, `N = 0` for `#[fip]`);
//! - a callee called inside a loop must have bound 0;
//! - recursion through strict functions makes the constants refer to each other,
//!   which rustc rejects as a cycle in constant evaluation.
//!
//! What a token-level macro cannot resolve is rejected rather than trusted: method
//! calls (`x.m()`), calls through expressions (`(f)(x)`, `a[i](x)`), qualified paths
//! (`<T as Tr>::f`), generic arguments inside a callee path, the `?` operator, and
//! macros outside a small allowlist.

use proc_macro::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};

use crate::{GHOST_MACROS, HEAP_CONSTRUCTORS, HEAP_TYPES, is_group, is_ident, is_punct};
use fip_lint_rules::CORE_TABLE;

/// Macros a strict body may invoke. Their arguments are still checked; what they
/// expand to on the panic path is outside the guarantee (see crate docs).
const ALLOWED_MACROS: &[&str] = &[
    "assert",
    "assert_eq",
    "assert_ne",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_ne",
    "unreachable",
    "panic",
];

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

/// A call to a function that must carry a companion constant.
pub(crate) struct Call {
    /// Path tokens before the function name, including the trailing `::`.
    prefix: Vec<TokenTree>,
    name: Ident,
    in_loop: bool,
}

#[derive(Default)]
pub(crate) struct StrictScan {
    pub(crate) params: Vec<Param>,
    pub(crate) calls: Vec<Call>,
    pub(crate) param_calls: Vec<ParamCall>,
    pub(crate) errors: Vec<(Span, String)>,
}

fn param_index(params: &[Param], name: &str) -> Option<usize> {
    params.iter().position(|p| p.name == name)
}

fn upper_initial(s: &str) -> bool {
    s.chars().next().is_some_and(char::is_uppercase)
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
            if GHOST_MACROS.contains(&s.as_str()) {
                return 3;
            }
            if !ALLOWED_MACROS.contains(&s.as_str()) && s != "vec" && s != "format" {
                self.err(
                    id.span(),
                    &format!("macro `{s}!` cannot be checked (its expansion is not visible)"),
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
            match path_prefix(toks, i) {
                Err((sp, msg)) => self.err(sp, &msg),
                Ok(prefix) => self.on_path_call(toks, paren, prefix, id, in_loop),
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
            // `FipFn::call(&param, (..))`
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
        if !heap_ctor && !in_core_table(&segs, &s) {
            self.calls.push(Call {
                prefix,
                name: id.clone(),
                in_loop,
            });
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

/// Path tokens before `toks[i]` (`a::b::` in `a::b::f`), with a leading `::` if any.
fn path_prefix(toks: &[TokenTree], i: usize) -> Result<Vec<TokenTree>, (Span, String)> {
    let mut start = i;
    loop {
        if start >= 2 && is_punct(&toks[start - 1], ':') && is_punct(&toks[start - 2], ':') {
            match toks.get(start.wrapping_sub(3)) {
                Some(TokenTree::Ident(_)) if start >= 3 => start -= 3,
                Some(t) if start >= 3 && is_punct(t, '>') => {
                    return Err((
                        t.span(),
                        "generic arguments or a qualified path (`<T as Tr>::f`) in a callee path cannot be resolved; name the function by a plain path".to_string(),
                    ));
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
    Ok(toks[start..i].to_vec())
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

fn marker_ident(name: &str, span: Span) -> Ident {
    Ident::new(&format!("__fip_strict_{name}"), span)
}

/// `prefix::__fip_strict_name.allocs()`, with the call's spans so a missing
/// certificate is reported at the call site.
fn term(c: &Call) -> TokenStream {
    let mut out: TokenStream = c.prefix.iter().cloned().collect();
    out.extend([TokenTree::Ident(marker_ident(
        &c.name.to_string(),
        c.name.span(),
    ))]);
    out.extend(ts(".allocs()"));
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
        let mut a = self.sum_expr(local);
        a.extend(ts(&format!(
            " <= {n}u64, {:?}",
            format!("{tag}: the callees may allocate more than {n} times in total")
        )));
        body.extend(ts("::core::assert!"));
        body.extend([paren(a)]);
        body.extend(ts(";"));
        for c in self.calls.iter().filter(|c| c.in_loop) {
            let mut a = term(c);
            a.extend(ts(&format!(
                " == 0u64, {:?}",
                format!("{tag}: `{}` is called in a loop and may allocate", c.name)
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

    /// Items emitted before a strict function, and the statement inserted at the
    /// start of its body.
    pub(crate) fn emit_fn(
        &self,
        tag: &str,
        fn_name: &str,
        vis: &[TokenTree],
        n: u64,
        local: u64,
    ) -> (TokenStream, TokenStream) {
        let attrs = "#[doc(hidden)] #[allow(non_upper_case_globals, dead_code, clippy::all, clippy::pedantic)]";
        let mut items = ts(attrs);
        items.extend(vis.iter().cloned());
        items.extend(ts(&format!(
            "const __fip_strict_{fn_name}: ::fip_strict::Cert = unsafe"
        )));
        let mut ctor = ts("::fip_strict::Cert::assume");
        ctor.extend([paren(self.sum_expr(local))]);
        items.extend([brace(ctor)]);
        items.extend(ts(";"));
        // Evaluated eagerly at module level (also by `cargo check`); inside an `impl`
        // an associated constant is lazy, so the checks are repeated in the body,
        // together with the checks on generic parameters (post-monomorphisation).
        items.extend(ts(attrs));
        items.extend(ts(&format!("const __fip_strict_check_{fn_name}: () = ")));
        items.extend([brace(self.checks(tag, n, local, false))]);
        items.extend(ts(";"));

        let mut stmt = ts(
            "#[cfg(not(verus_keep_ghost))] #[allow(clippy::all, clippy::pedantic)] let () = const ",
        );
        stmt.extend([brace(self.checks(tag, n, local, true))]);
        stmt.extend(ts(";"));
        (items, stmt)
    }

    /// `const ALLOCS: u64 = { checks; sum };` for a `fip_fn!` wrapper.
    pub(crate) fn emit_allocs_const(&self, local: u64) -> TokenStream {
        let mut body = self.checks("fip_fn!", u64::MAX, local, false);
        body.extend(self.sum_expr(local));
        let mut out = ts("#[allow(clippy::all, clippy::pedantic)] const ALLOCS: u64 = ");
        out.extend([brace(body)]);
        out.extend(ts(";"));
        out
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
