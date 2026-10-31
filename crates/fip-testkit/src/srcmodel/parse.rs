// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Item parser and body scanner: functions with their module path, `impl` owner,
//! marks, parameters and the events of their bodies (calls, allocation sites, loop
//! context, closures).

use std::collections::{BTreeMap, BTreeSet};

use fip_lint_rules::{
    ALLOC_FREE_MACROS, ALLOC_MACROS, ALLOC_METHODS, FN_TRAITS, GHOST_MACROS, HEAP_CONSTRUCTORS,
    HEAP_TYPES, PANIC_MACROS,
};

use super::lex::{
    Kind, Tok, adjacent, angle_end, group_end, group_start, id, is_close, is_id, is_open, is_p,
    lit, sep, split_top,
};
use super::{Arg, Ev, Event, FnDef, Mark, MarkKind, Param, Res, Uses};

/// Keywords that never start a call or value path (`crate`, `self`, `Self`, `super`
/// start paths and are handled separately).
const KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "dyn", "else", "enum", "extern", "false",
    "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref",
    "return", "static", "struct", "trait", "true", "type", "unsafe", "use", "where", "while",
    "yield",
];

/// Where an item lives.
#[derive(Clone, Debug)]
pub(super) struct Scope {
    pub(super) unit: usize,
    pub(super) module: Vec<String>,
    pub(super) owner: Option<String>,
    pub(super) generics: Vec<String>,
}

/// Names visible in a body.
#[derive(Clone, Debug)]
struct FnCtx {
    /// Function (or closure) receiving the events.
    fid: usize,
    /// Parameters of callable type of the enclosing named function.
    callable: BTreeSet<String>,
    /// Other parameters and `let`-bound locals.
    locals: BTreeSet<String>,
    /// Locals bound to a closure literal.
    closures: BTreeMap<String, usize>,
    scope: Scope,
    /// `macro_rules!` names being expanded (recursion guard).
    expanding: Vec<String>,
}

/// Parsed attribute.
#[derive(Default)]
pub(super) struct Attr {
    pub(super) mark: Mark,
    pub(super) path: Option<String>,
}

pub(super) struct Builder<'a> {
    pub(super) toks: &'a [Vec<Tok>],
    /// `macro_rules!` name → transcriber bodies (file, start, end).
    pub(super) macros: &'a BTreeMap<String, Vec<(usize, usize, usize)>>,
    pub(super) fns: Vec<FnDef>,
    pub(super) modules: BTreeSet<(usize, Vec<String>)>,
    pub(super) uses: Uses,
    pub(super) globs: BTreeMap<(usize, Vec<String>), Vec<Vec<String>>>,
}

/// Parses `#[..]` contents `t[a..b]`: FIP marks (also inside `cfg_attr`) and `path`.
pub(super) fn attr(t: &[Tok], from: usize, to: usize) -> Attr {
    let mut k = from;
    let mut last = None;
    while k < to {
        let Some(s) = id(t, k) else { break };
        last = Some(s);
        if sep(t, k + 1) {
            k += 3;
        } else {
            k += 1;
            break;
        }
    }
    let mut out = Attr::default();
    match last {
        Some("fip") => out.mark = fip_args(t, k),
        Some("fbip") => out.mark.kind = MarkKind::Fbip,
        Some("cfg_attr") if is_p(t, k, '(') => {
            // `cfg_attr(pred, attrs..)`: marked under any predicate (conservative).
            let e = group_end(t, k);
            for &(x, y) in split_top(t, k + 1, e - 1, false).iter().skip(1) {
                let inner = attr(t, x, y);
                if inner.mark.kind != MarkKind::None {
                    out.mark = inner.mark;
                }
                if inner.path.is_some() {
                    out.path = inner.path;
                }
            }
        }
        Some("path") if is_p(t, k, '=') => out.path = lit(t, k + 1).map(str::to_string),
        _ => {}
    }
    out
}

/// `fip` arguments starting at `t[k]` (`(N, strict = true, param(g = K))`, or none).
fn fip_args(t: &[Tok], k: usize) -> Mark {
    let mut m = Mark {
        kind: MarkKind::Fip,
        ..Mark::default()
    };
    if !is_p(t, k, '(') {
        return m;
    }
    let e = group_end(t, k);
    for (x, y) in split_top(t, k + 1, e - 1, false) {
        if y == x + 1
            && let Some(n) = lit(t, x).and_then(int)
        {
            m.n = n;
        } else if is_id(t, x, "param") && is_p(t, x + 1, '(') {
            let pe = group_end(t, x + 1);
            for (p, q) in split_top(t, x + 2, pe - 1, false) {
                if q == p + 3
                    && is_p(t, p + 1, '=')
                    && let (Some(name), Some(n)) = (id(t, p), lit(t, p + 2).and_then(int))
                {
                    m.params.push((name.to_string(), n));
                }
            }
        }
    }
    m
}

/// Integer literal value (`2`, `1_000`, `3u64`).
pub(super) fn int(s: &str) -> Option<u64> {
    let digits: String = s
        .chars()
        .take_while(|c| c.is_ascii_digit() || *c == '_')
        .filter(|c| *c != '_')
        .collect();
    digits.parse().ok()
}

/// Tokens between attributes and `fn` that keep a pending mark.
fn keeps_mark(t: &[Tok], i: usize) -> bool {
    matches!(
        id(t, i),
        Some(
            "pub"
                | "const"
                | "async"
                | "unsafe"
                | "safe"
                | "extern"
                | "crate"
                | "super"
                | "self"
                | "in"
                | "default"
        )
    ) || is_p(t, i, '(')
        || is_p(t, i, ')')
        || lit(t, i).is_some()
}

/// `const NAME: T = ..;` / `static [mut] NAME: T = ..;` (not `const fn`).
fn is_value_item(t: &[Tok], i: usize) -> bool {
    let k = if is_id(t, i + 1, "mut") { i + 2 } else { i + 1 };
    id(t, k).is_some_and(|n| !KEYWORDS.contains(&n)) && is_p(t, k + 1, ':') && !sep(t, k + 1)
}

/// Any identifier of a trait in [`FN_TRAITS`] in `t[a..b]`.
fn mentions_fn_trait(t: &[Tok], a: usize, b: usize) -> bool {
    (a..b).any(|q| id(t, q).is_some_and(|s| FN_TRAITS.contains(&s)))
}

/// A parameter type that is a callable value: `impl Fn..`, `&dyn FnMut..`,
/// `Box<dyn Fn..>`, `fn(..)`, or a generic parameter bounded by a callable trait.
fn type_callable(t: &[Tok], a: usize, b: usize, callable_generics: &BTreeSet<String>) -> bool {
    let dyn_or_impl = (a..b).any(|q| is_id(t, q, "impl") || is_id(t, q, "dyn"));
    if dyn_or_impl && mentions_fn_trait(t, a, b) {
        return true;
    }
    if (a..b).any(|q| is_id(t, q, "fn") && is_p(t, q + 1, '(')) {
        return true;
    }
    let mut q = a;
    while q < b && (is_p(t, q, '&') || is_id(t, q, "mut")) {
        q += 1;
    }
    q + 1 == b && id(t, q).is_some_and(|g| callable_generics.contains(g))
}

/// Signature facts of `fn name<..>(..) -> R where ..` in `t[a..j]` (`a` just after
/// the name).
struct Sig {
    generics: Vec<String>,
    params: Vec<Param>,
    has_self: bool,
}

fn signature(t: &[Tok], from: usize, stop: usize) -> Sig {
    let mut k = from;
    let mut generics = Vec::new();
    let mut callable_g = BTreeSet::new();
    if is_p(t, k, '<') {
        let e = angle_end(t, k, stop);
        for (lo, hi) in split_top(t, k + 1, e.saturating_sub(1), true) {
            let lo = if is_id(t, lo, "const") { lo + 1 } else { lo };
            if let Some(g) = id(t, lo) {
                generics.push(g.to_string());
                if mentions_fn_trait(t, lo + 1, hi) {
                    callable_g.insert(g.to_string());
                }
            }
        }
        k = e;
    }
    let params_at = k;
    let params_end = if is_p(t, k, '(') { group_end(t, k) } else { k };
    if let Some(w) = (params_end..stop).find(|&q| is_id(t, q, "where")) {
        for (lo, hi) in split_top(t, w + 1, stop, true) {
            if let Some(g) = id(t, lo)
                && generics.iter().any(|n| n == g)
                && mentions_fn_trait(t, lo + 1, hi)
            {
                callable_g.insert(g.to_string());
            }
        }
    }
    let mut params = Vec::new();
    let mut has_self = false;
    if is_p(t, params_at, '(') {
        for (n, (lo, hi)) in split_top(t, params_at + 1, params_end - 1, true)
            .into_iter()
            .enumerate()
        {
            let mut q = lo;
            while is_p(t, q, '&') || is_id(t, q, "mut") {
                q += 1;
            }
            if n == 0 && is_id(t, q, "self") {
                has_self = true;
                continue;
            }
            let q = if is_id(t, lo, "mut") { lo + 1 } else { lo };
            match id(t, q) {
                Some(name) if is_p(t, q + 1, ':') && !sep(t, q + 1) => params.push(Param {
                    name: name.to_string(),
                    callable: type_callable(t, q + 2, hi, &callable_g),
                }),
                _ => params.push(Param {
                    name: "_".to_string(),
                    callable: false,
                }),
            }
        }
    }
    Sig {
        generics,
        params,
        has_self,
    }
}

/// Last identifier of the self type of an `impl` header (`Foo<T>` → `Foo`,
/// `&'a mut S` → `S`).
fn last_type_ident(t: &[Tok], from: usize, to: usize) -> Option<String> {
    let mut d = 0_i32;
    let mut last = None;
    let mut q = from;
    while q < to {
        if is_open(t, q) {
            q = group_end(t, q);
            continue;
        }
        if is_p(t, q, '<') {
            d += 1;
        } else if is_p(t, q, '>') && !is_p(t, q.wrapping_sub(1), '-') {
            d -= 1;
        } else if d == 0
            && let Some(s) = id(t, q)
            && !matches!(s, "dyn" | "mut" | "impl" | "for" | "const" | "unsafe")
        {
            last = Some(s.to_string());
        }
        q += 1;
    }
    last
}

/// Index of the first `t[k]` in `a..b` at delimiter depth 0 matching `f`.
fn find_top(t: &[Tok], from: usize, to: usize, f: impl Fn(usize) -> bool) -> Option<usize> {
    let mut q = from;
    while q < to {
        if f(q) {
            return Some(q);
        }
        if is_open(t, q) {
            q = group_end(t, q);
        } else {
            q += 1;
        }
    }
    None
}

/// An `=` that is an assignment, not part of `==`, `<=`, `=>`, `+=`, ...
fn is_assign(t: &[Tok], q: usize) -> bool {
    is_p(t, q, '=')
        && !(is_p(t, q + 1, '=') && adjacent(t, q, q + 1))
        && !(is_p(t, q + 1, '>') && adjacent(t, q, q + 1))
        && !(q > 0
            && adjacent(t, q - 1, q)
            && matches!(
                t[q - 1].kind,
                Kind::Punct('=' | '<' | '>' | '!' | '+' | '-' | '*' | '/' | '%' | '^' | '&' | '|')
            ))
}

/// `t[i]` is a `|` that starts a closure (expression position).
fn closure_start(t: &[Tok], i: usize, start: usize) -> bool {
    if !is_p(t, i, '|') {
        return false;
    }
    if i == start {
        return true;
    }
    let p = i - 1;
    match &t[p].kind {
        Kind::Punct('(' | ',' | '{' | ';' | '[' | ':' | '!') => true,
        Kind::Punct('=') => !(p > 0 && is_p(t, p - 1, '=') && adjacent(t, p - 1, p)),
        Kind::Punct('>') => p > 0 && is_p(t, p - 1, '=') && adjacent(t, p - 1, p),
        Kind::Ident(s) => matches!(s.as_str(), "move" | "return" | "in" | "else"),
        _ => false,
    }
}

/// `t[i]` is `<` opening a qualified path `<T as Tr>::f` / `<[T]>::f` in expression
/// position.
fn qualified_start(t: &[Tok], i: usize, start: usize, end: usize) -> Option<usize> {
    if !is_p(t, i, '<') {
        return None;
    }
    let expr_pos = i == start
        || match &t[i - 1].kind {
            Kind::Punct(c) => !matches!(c, ')' | ']'),
            Kind::Ident(s) => KEYWORDS.contains(&s.as_str()),
            Kind::Lit(_) => false,
        };
    let e = angle_end(t, i, end);
    (expr_pos && e > i + 1 && sep(t, e)).then_some(e)
}

/// End of an expression starting at `k` (closure body without braces): the first
/// top-level `,` or `;`, an unmatched closer, or `end`.
fn expr_end(t: &[Tok], k: usize, end: usize) -> usize {
    let mut j = k;
    while j < end {
        if is_open(t, j) {
            j = group_end(t, j);
            continue;
        }
        if is_p(t, j, ',') || is_p(t, j, ';') || is_close(t, j) {
            break;
        }
        j += 1;
    }
    j.min(end)
}

/// Lowercase identifiers bound by a pattern in `t[a..b]`.
fn pattern_names(t: &[Tok], a: usize, b: usize) -> Vec<String> {
    (a..b)
        .filter_map(|q| {
            let s = id(t, q)?;
            let lower = s.starts_with(|c: char| c.is_lowercase() || c == '_');
            let binds = !(is_p(t, q + 1, '(') || is_p(t, q + 1, '{') || sep(t, q + 1));
            (lower && binds && !KEYWORDS.contains(&s) && s != "self").then(|| s.to_string())
        })
        .collect()
}

impl<'a> Builder<'a> {
    fn new_fn(&mut self, f: FnDef) -> usize {
        self.fns.push(f);
        self.fns.len() - 1
    }

    fn push(&mut self, cx: &FnCtx, ev: Ev, tok: &Tok, in_loop: bool) {
        self.fns[cx.fid].events.push(Event {
            ev,
            file: tok.file,
            line: tok.line,
            in_loop,
        });
    }

    /// Items in `t[start..end]`.
    pub(super) fn items(&mut self, t: &'a [Tok], start: usize, end: usize, sc: &Scope) {
        let mut i = start;
        let mut mark = Mark::default();
        let mut pending = false;
        while i < end {
            if is_p(t, i, '#') && is_p(t, i + 1, '!') && is_p(t, i + 2, '[') {
                i = group_end(t, i + 2);
                continue;
            }
            if is_p(t, i, '#') && is_p(t, i + 1, '[') {
                let e = group_end(t, i + 1);
                let a = attr(t, i + 2, e - 1);
                if a.mark.kind != MarkKind::None {
                    mark = a.mark;
                }
                pending = true;
                i = e;
                continue;
            }
            if is_p(t, i, '{') {
                let e = group_end(t, i);
                if i > start && (is_id(t, i - 1, "extern") || lit(t, i - 1).is_some()) {
                    self.items(t, i + 1, e - 1, sc);
                }
                i = e;
                mark = Mark::default();
                pending = false;
                continue;
            }
            if let Some(next) = self.item(t, i, end, sc, &mut mark) {
                i = next;
                mark = Mark::default();
                pending = false;
                continue;
            }
            if !(keeps_mark(t, i) || (pending && is_p(t, i, ':'))) {
                mark = Mark::default();
                pending = false;
            }
            i += 1;
        }
    }

    /// The item starting at `t[i]`, if any; returns the index after it.
    fn item(
        &mut self,
        t: &'a [Tok],
        i: usize,
        end: usize,
        sc: &Scope,
        mark: &mut Mark,
    ) -> Option<usize> {
        let s = id(t, i)?;
        match s {
            "fn" if id(t, i + 1).is_some() => Some(self.fn_item(t, i, sc, std::mem::take(mark))),
            "mod" if id(t, i + 1).is_some() && is_p(t, i + 2, '{') => {
                let e = group_end(t, i + 2);
                let mut module = sc.module.clone();
                module.push(id(t, i + 1).unwrap_or_default().to_string());
                self.modules.insert((sc.unit, module.clone()));
                let inner = Scope {
                    unit: sc.unit,
                    module,
                    owner: None,
                    generics: Vec::new(),
                };
                self.items(t, i + 3, e - 1, &inner);
                Some(e)
            }
            "impl" => Some(self.impl_item(t, i, end, sc)),
            "trait" if id(t, i + 1).is_some() => Some(self.trait_item(t, i, end, sc)),
            "macro_rules" if is_p(t, i + 1, '!') => Some(group_end(t, i + 3)),
            "use" => Some(self.use_item(t, i, end, sc)),
            "const" | "static" if is_value_item(t, i) => Some(self.value_item(t, i, end, sc)),
            _ if is_p(t, i + 1, '!') && is_open(t, i + 2) && !GHOST_MACROS.contains(&s) => {
                // item-level macro invocation (e.g. `verus! { .. }`): parse as items
                let e = group_end(t, i + 2);
                self.items(t, i + 3, e - 1, sc);
                Some(e)
            }
            _ => None,
        }
    }

    fn fn_item(&mut self, t: &'a [Tok], i: usize, sc: &Scope, mark: Mark) -> usize {
        let name = id(t, i + 1).unwrap_or_default().to_string();
        let mut j = i + 2;
        let mut depth = 0_i32;
        while j < t.len() {
            match &t[j].kind {
                Kind::Punct('(' | '[' | '<') => depth += 1,
                Kind::Punct(')' | ']') => depth -= 1,
                Kind::Punct('>') if !is_p(t, j - 1, '-') && !is_p(t, j - 1, '=') => depth -= 1,
                Kind::Punct(';' | '{') if depth <= 0 => break,
                _ => {}
            }
            j += 1;
        }
        if !is_p(t, j, '{') {
            return j + 1;
        }
        let sig = signature(t, i + 2, j);
        let mut generics = sc.generics.clone();
        generics.extend(sig.generics);
        let callable: BTreeSet<String> = sig
            .params
            .iter()
            .filter(|p| p.callable)
            .map(|p| p.name.clone())
            .collect();
        let locals: BTreeSet<String> = sig
            .params
            .iter()
            .filter(|p| !p.callable)
            .map(|p| p.name.clone())
            .collect();
        let fid = self.new_fn(FnDef {
            name,
            display: String::new(),
            unit: sc.unit,
            module: sc.module.clone(),
            owner: sc.owner.clone(),
            generics: generics.clone(),
            mark,
            has_self: sig.has_self,
            params: sig.params,
            closure_of: None,
            item_init: false,
            file: t[i].file,
            line: t[i].line,
            events: Vec::new(),
        });
        let body_end = group_end(t, j);
        let mut cx = FnCtx {
            fid,
            callable,
            locals,
            closures: BTreeMap::new(),
            scope: Scope {
                unit: sc.unit,
                module: sc.module.clone(),
                owner: None,
                generics,
            },
            expanding: Vec::new(),
        };
        self.scan(t, j + 1, body_end - 1, false, &mut cx);
        body_end
    }

    fn impl_item(&mut self, t: &'a [Tok], i: usize, end: usize, sc: &Scope) -> usize {
        let mut k = i + 1;
        let mut generics = sc.generics.clone();
        if is_p(t, k, '<') {
            let close = angle_end(t, k, end);
            for (x, _) in split_top(t, k + 1, close.saturating_sub(1), true) {
                let x = if is_id(t, x, "const") { x + 1 } else { x };
                if let Some(g) = id(t, x) {
                    generics.push(g.to_string());
                }
            }
            k = close;
        }
        let Some(body) = find_top(t, k, end, |q| is_p(t, q, '{') || is_p(t, q, ';')) else {
            return end;
        };
        if !is_p(t, body, '{') {
            return body + 1;
        }
        let hdr_end = (k..body).find(|&q| is_id(t, q, "where")).unwrap_or(body);
        let for_at = (k..hdr_end).find(|&q| is_id(t, q, "for") && !is_p(t, q + 1, '<'));
        let ty_start = for_at.map_or(k, |f| f + 1);
        let owner = last_type_ident(t, ty_start, hdr_end).unwrap_or_else(|| "_".to_string());
        let close = group_end(t, body);
        let inner = Scope {
            unit: sc.unit,
            module: sc.module.clone(),
            owner: Some(owner),
            generics,
        };
        self.items(t, body + 1, close - 1, &inner);
        close
    }

    fn trait_item(&mut self, t: &'a [Tok], i: usize, end: usize, sc: &Scope) -> usize {
        let name = id(t, i + 1).unwrap_or_default().to_string();
        let mut generics = sc.generics.clone();
        if is_p(t, i + 2, '<') {
            let e = angle_end(t, i + 2, end);
            for (x, _) in split_top(t, i + 3, e.saturating_sub(1), true) {
                if let Some(g) = id(t, x) {
                    generics.push(g.to_string());
                }
            }
        }
        let Some(b) = find_top(t, i + 2, end, |q| is_p(t, q, '{') || is_p(t, q, ';')) else {
            return end;
        };
        if !is_p(t, b, '{') {
            return b + 1;
        }
        let e = group_end(t, b);
        let inner = Scope {
            unit: sc.unit,
            module: sc.module.clone(),
            owner: Some(name),
            generics,
        };
        self.items(t, b + 1, e - 1, &inner);
        e
    }

    fn use_item(&mut self, t: &'a [Tok], i: usize, end: usize, sc: &Scope) -> usize {
        let semi = find_top(t, i, end, |q| is_p(t, q, ';')).unwrap_or(end);
        let mut uses = Vec::new();
        let mut globs = Vec::new();
        use_tree(t, i + 1, semi, &[], &mut uses, &mut globs);
        let key = (sc.unit, sc.module.clone());
        self.uses.entry(key.clone()).or_default().extend(uses);
        self.globs.entry(key).or_default().extend(globs);
        semi + 1
    }

    /// `const` / `static` initializer: scanned for functions used as values.
    fn value_item(&mut self, t: &'a [Tok], i: usize, end: usize, sc: &Scope) -> usize {
        let semi = find_top(t, i, end, |q| is_p(t, q, ';')).unwrap_or(end);
        if let Some(eq) = find_top(t, i, semi, |q| is_assign(t, q)) {
            let fid = self.new_fn(FnDef {
                name: "{item}".to_string(),
                display: String::new(),
                unit: sc.unit,
                module: sc.module.clone(),
                owner: sc.owner.clone(),
                generics: sc.generics.clone(),
                mark: Mark::default(),
                has_self: false,
                params: Vec::new(),
                closure_of: None,
                item_init: true,
                file: t[i].file,
                line: t[i].line,
                events: Vec::new(),
            });
            let mut cx = FnCtx {
                fid,
                callable: BTreeSet::new(),
                locals: BTreeSet::new(),
                closures: BTreeMap::new(),
                scope: sc.clone(),
                expanding: Vec::new(),
            };
            self.scan(t, eq + 1, semi, false, &mut cx);
        }
        semi + 1
    }

    // ---- bodies ----

    fn scan(&mut self, t: &'a [Tok], start: usize, end: usize, lp: bool, cx: &mut FnCtx) {
        let mut i = start;
        while i < end {
            i = self.step(t, i, start, end, lp, cx).max(i + 1);
        }
    }

    fn step(
        &mut self,
        t: &'a [Tok],
        i: usize,
        start: usize,
        end: usize,
        lp: bool,
        cx: &mut FnCtx,
    ) -> usize {
        match &t[i].kind {
            Kind::Punct('#') if is_p(t, i + 1, '[') => group_end(t, i + 1),
            Kind::Punct('#') if is_p(t, i + 1, '!') && is_p(t, i + 2, '[') => group_end(t, i + 2),
            // macro metavariable `$x` (but `$crate` starts a path)
            Kind::Punct('$') if id(t, i + 1).is_some_and(|s| s != "crate") => i + 2,
            Kind::Punct('|') if closure_start(t, i, start) => {
                let (cid, e) = self.closure(t, i, end, cx);
                self.push(cx, Ev::Escape(cid), &t[i], lp);
                e
            }
            Kind::Punct('(') if i > start && (is_p(t, i - 1, ')') || is_p(t, i - 1, ']')) => {
                self.expr_call(t, i, lp, cx)
            }
            Kind::Punct('<') => match qualified_start(t, i, start, end) {
                Some(e) => self.qualified(t, i, e, lp, cx),
                None => i + 1,
            },
            Kind::Punct('?') if !is_id(t, i + 1, "Sized") => {
                self.push(
                    cx,
                    Ev::Unknown("`?` operator (calls `From::from` on the error path)".to_string()),
                    &t[i],
                    lp,
                );
                i + 1
            }
            Kind::Ident(_) if i > start && is_p(t, i - 1, '.') => self.method(t, i, lp, cx),
            Kind::Ident(s) => self.ident(t, i, s, end, lp, cx),
            _ => i + 1,
        }
    }

    fn ident(
        &mut self,
        t: &'a [Tok],
        i: usize,
        s: &str,
        end: usize,
        lp: bool,
        cx: &mut FnCtx,
    ) -> usize {
        match s {
            "fn" if id(t, i + 1).is_some() => {
                let sc = cx.scope.clone();
                return self.fn_item(t, i, &sc, Mark::default());
            }
            "impl" => {
                let sc = cx.scope.clone();
                return self.impl_item(t, i, end, &sc);
            }
            "trait" if id(t, i + 1).is_some() => {
                let sc = cx.scope.clone();
                return self.trait_item(t, i, end, &sc);
            }
            "mod" if id(t, i + 1).is_some() && is_p(t, i + 2, '{') => {
                let sc = cx.scope.clone();
                let mut mark = Mark::default();
                return self.item(t, i, end, &sc, &mut mark).unwrap_or(i + 1);
            }
            "macro_rules" if is_p(t, i + 1, '!') => return group_end(t, i + 3),
            "use" => {
                let sc = cx.scope.clone();
                return self.use_item(t, i, end, &sc);
            }
            "let" => return self.let_stmt(t, i, end, cx),
            "loop" if is_p(t, i + 1, '{') => {
                let e = group_end(t, i + 1);
                self.scan(t, i + 2, e - 1, true, cx);
                return e;
            }
            "while" => return self.while_loop(t, i, end, cx),
            "for" if !is_p(t, i + 1, '<') => return self.for_loop(t, i, end, lp, cx),
            "self" if is_p(t, i + 1, '(') => {
                self.push(cx, Ev::Indirect, &t[i], lp);
                let (args, e) = self.call_args(t, i + 1, lp, cx);
                self.escape_closures(cx, &args, &t[i], lp);
                return e;
            }
            _ => {}
        }
        if KEYWORDS.contains(&s) {
            return i + 1;
        }
        self.path_expr(t, i, end, lp, cx)
    }

    fn let_stmt(&mut self, t: &'a [Tok], i: usize, end: usize, cx: &mut FnCtx) -> usize {
        let Some(stop) = find_top(t, i + 1, end, |q| {
            is_p(t, q, ';') || is_assign(t, q) || is_close(t, q)
        }) else {
            return i + 1;
        };
        let pat_end = find_top(t, i + 1, stop, |q| is_p(t, q, ':') && !sep(t, q)).unwrap_or(stop);
        let k = if is_id(t, i + 1, "mut") { i + 2 } else { i + 1 };
        let simple = (k + 1 == pat_end).then(|| id(t, k)).flatten();
        if is_assign(t, stop)
            && let Some(name) = simple
        {
            let name = name.to_string();
            if let Some((cid, e)) = self.closure_expr(t, stop + 1, end, cx) {
                cx.locals.remove(&name);
                cx.closures.insert(name, cid);
                return e;
            }
            cx.closures.remove(&name);
            cx.locals.insert(name);
        } else {
            for n in pattern_names(t, i + 1, pat_end) {
                cx.closures.remove(&n);
                cx.locals.insert(n);
            }
        }
        if is_assign(t, stop) { stop + 1 } else { stop }
    }

    fn while_loop(&mut self, t: &'a [Tok], i: usize, end: usize, cx: &mut FnCtx) -> usize {
        let Some(b) = find_top(t, i + 1, end, |q| is_p(t, q, '{')) else {
            return i + 1;
        };
        // the condition runs on every iteration
        self.scan(t, i + 1, b, true, cx);
        let e = group_end(t, b);
        self.scan(t, b + 1, e - 1, true, cx);
        e
    }

    fn for_loop(&mut self, t: &'a [Tok], i: usize, end: usize, lp: bool, cx: &mut FnCtx) -> usize {
        let Some(b) = find_top(t, i + 1, end, |q| is_p(t, q, '{')) else {
            return i + 1;
        };
        let Some(inn) = (i + 1..b).find(|&q| is_id(t, q, "in")) else {
            return i + 1;
        };
        for n in pattern_names(t, i + 1, inn) {
            cx.closures.remove(&n);
            cx.locals.insert(n);
        }
        self.scan(t, inn + 1, b, lp, cx);
        // `for` calls `IntoIterator::into_iter` and `Iterator::next` implicitly; over a
        // range literal those are `core`'s, otherwise they are method calls by name
        let range = find_top(t, inn + 1, b, |q| {
            is_p(t, q, '.') && is_p(t, q + 1, '.') && adjacent(t, q, q + 1)
        })
        .is_some();
        if !range {
            for name in ["into_iter", "next"] {
                let ev = Ev::Method {
                    name: name.to_string(),
                    args: Vec::new(),
                    site: false,
                    qualified: false,
                    res: Res::Pending,
                };
                self.push(cx, ev, &t[i], name == "next" || lp);
            }
        }
        let e = group_end(t, b);
        self.scan(t, b + 1, e - 1, true, cx);
        e
    }

    /// A closure-valued expression at `t[k]`: a closure literal or `fip_fn!(..)`.
    /// Creates the closure; returns it and the index after the expression.
    fn closure_expr(
        &mut self,
        t: &'a [Tok],
        k: usize,
        end: usize,
        cx: &FnCtx,
    ) -> Option<(usize, usize)> {
        let bar = if is_id(t, k, "move") { k + 1 } else { k };
        if is_p(t, bar, '|') {
            return Some(self.closure(t, bar, end, cx));
        }
        // `fip_fn!(..)`, `fip_macros::fip_fn!(..)`
        let mut q = k;
        while id(t, q).is_some() && sep(t, q + 1) {
            q += 3;
        }
        if is_id(t, q, "fip_fn") && is_p(t, q + 1, '!') && is_open(t, q + 2) {
            let ge = group_end(t, q + 2);
            let inner = if is_id(t, q + 3, "move") {
                q + 4
            } else {
                q + 3
            };
            if is_p(t, inner, '|') {
                let (cid, _) = self.closure(t, inner, ge - 1, cx);
                return Some((cid, ge));
            }
        }
        None
    }

    /// Closure literal whose first `|` is `t[bar]`.
    fn closure(&mut self, t: &'a [Tok], bar: usize, end: usize, cx: &FnCtx) -> (usize, usize) {
        let params_end = if is_p(t, bar + 1, '|') {
            bar + 1
        } else {
            find_top(t, bar + 1, end, |q| is_p(t, q, '|')).unwrap_or(end)
        };
        let names = pattern_names(t, bar + 1, params_end);
        let mut k = params_end + 1;
        if is_p(t, k, '-') && is_p(t, k + 1, '>') {
            k = find_top(t, k + 2, end, |q| is_p(t, q, '{')).unwrap_or(end);
        }
        let (body_start, body_end, e) = if is_p(t, k, '{') {
            let ge = group_end(t, k);
            (k + 1, ge - 1, ge)
        } else {
            let ee = expr_end(t, k, end);
            (k, ee, ee)
        };
        let parent = &self.fns[cx.fid];
        let def = FnDef {
            name: "{closure}".to_string(),
            display: String::new(),
            unit: parent.unit,
            module: parent.module.clone(),
            owner: parent.owner.clone(),
            generics: parent.generics.clone(),
            mark: Mark::default(),
            has_self: false,
            params: Vec::new(),
            closure_of: Some(cx.fid),
            item_init: false,
            file: t[bar].file,
            line: t[bar].line,
            events: Vec::new(),
        };
        let cid = self.new_fn(def);
        let mut inner = cx.clone();
        inner.fid = cid;
        for n in names {
            inner.callable.remove(&n);
            inner.closures.remove(&n);
            inner.locals.insert(n);
        }
        self.scan(t, body_start, body_end.min(end), false, &mut inner);
        (cid, e.max(bar + 1))
    }

    /// Arguments of the call group at `t[open]`; scans them. Returns the arguments and
    /// the index after the group.
    fn call_args(
        &mut self,
        t: &'a [Tok],
        open: usize,
        lp: bool,
        cx: &mut FnCtx,
    ) -> (Vec<Arg>, usize) {
        let close = group_end(t, open);
        let mut args = Vec::new();
        for (a, b) in split_top(t, open + 1, close - 1, false) {
            if let Some((cid, e)) = self.closure_expr(t, a, b, cx) {
                args.push(Arg::Closure(cid));
                if e < b {
                    self.scan(t, e, b, lp, cx);
                }
                continue;
            }
            let mut x = a;
            while x < b && (is_p(t, x, '&') || is_id(t, x, "mut") || is_p(t, x, '*')) {
                x += 1;
            }
            let arg = classify_path(t, x, b, cx);
            if !matches!(arg, Arg::Param(_) | Arg::Closure(_)) {
                self.scan(t, a, b, lp, cx);
            }
            args.push(arg);
        }
        (args, close)
    }

    fn escape_closures(&mut self, cx: &FnCtx, args: &[Arg], tok: &Tok, lp: bool) {
        for a in args {
            if let Arg::Closure(c) = a {
                self.push(cx, Ev::Escape(*c), tok, lp);
            }
        }
    }

    /// `(expr)(..)` / `a[i](..)`: a call through an expression.
    fn expr_call(&mut self, t: &'a [Tok], i: usize, lp: bool, cx: &mut FnCtx) -> usize {
        let open = group_start(t, i - 1);
        let mut x = open + 1;
        while x < i - 1 && (is_p(t, x, '&') || is_p(t, x, '*')) {
            x += 1;
        }
        let ev = match (is_p(t, open, '(') && x + 2 == i)
            .then(|| id(t, x))
            .flatten()
        {
            Some(n) if cx.callable.contains(n) => Ev::ParamCall(n.to_string()),
            Some(n) if cx.closures.contains_key(n) => Ev::ClosureCall(cx.closures[n]),
            _ => Ev::Indirect,
        };
        self.push(cx, ev, &t[i], lp);
        let (args, e) = self.call_args(t, i, lp, cx);
        self.escape_closures(cx, &args, &t[i], lp);
        e
    }

    /// `<T as Tr>::name(..)` / `<[T]>::name(..)`, treated as a method call `name`.
    fn qualified(&mut self, t: &'a [Tok], i: usize, e: usize, lp: bool, cx: &mut FnCtx) -> usize {
        let Some(name) = id(t, e + 2) else {
            return e;
        };
        let mut j = e + 3;
        if sep(t, j) && is_p(t, j + 2, '<') {
            j = angle_end(t, j + 2, t.len());
        }
        if !is_p(t, j, '(') {
            return j;
        }
        let (args, end) = self.call_args(t, j, lp, cx);
        let ev = Ev::Method {
            name: name.to_string(),
            args,
            site: ALLOC_METHODS.contains(&name),
            qualified: true,
            res: Res::Pending,
        };
        self.push(cx, ev, &t[i], lp);
        end
    }

    /// `.name(..)` / `.name::<..>(..)`; other `.name` (fields, `.await`) are skipped.
    fn method(&mut self, t: &'a [Tok], i: usize, lp: bool, cx: &mut FnCtx) -> usize {
        let name = id(t, i).unwrap_or_default();
        let mut j = i + 1;
        if sep(t, j) && is_p(t, j + 2, '<') {
            j = angle_end(t, j + 2, t.len());
        }
        if !is_p(t, j, '(') {
            return j;
        }
        let recv = (i >= 2 && !(i >= 3 && (is_p(t, i - 3, '.') || is_p(t, i - 3, ':'))))
            .then(|| id(t, i - 2))
            .flatten();
        if matches!(name, "call" | "call_mut" | "call_once")
            && let Some(r) = recv
        {
            let ev = if cx.callable.contains(r) {
                Some(Ev::ParamCall(r.to_string()))
            } else {
                cx.closures.get(r).map(|&c| Ev::ClosureCall(c))
            };
            if let Some(ev) = ev {
                self.push(cx, ev, &t[i], lp);
                let (args, e) = self.call_args(t, j, lp, cx);
                self.escape_closures(cx, &args, &t[i], lp);
                return e;
            }
        }
        let (args, e) = self.call_args(t, j, lp, cx);
        let ev = Ev::Method {
            name: name.to_string(),
            args,
            site: ALLOC_METHODS.contains(&name),
            qualified: false,
            res: Res::Pending,
        };
        self.push(cx, ev, &t[i], lp);
        e
    }

    /// A path expression starting at `t[i]`: call, macro, allocation site or value.
    fn path_expr(&mut self, t: &'a [Tok], i: usize, end: usize, lp: bool, cx: &mut FnCtx) -> usize {
        let mut segs = vec![id(t, i).unwrap_or_default().to_string()];
        let mut j = i + 1;
        while sep(t, j) {
            if is_p(t, j + 2, '<') {
                j = angle_end(t, j + 2, end);
            } else if let Some(n) = id(t, j + 2) {
                segs.push(n.to_string());
                j += 3;
            } else {
                break;
            }
        }
        if i > 0 && is_p(t, i - 1, '$') && segs[0] == "crate" {
            segs[0] = "$crate".to_string();
        }
        let name = segs.pop().unwrap_or_default();
        if is_p(t, j, '!') && !is_p(t, j + 1, '=') && is_open(t, j + 1) {
            return self.macro_call(t, i, &name, j + 1, lp, cx);
        }
        if segs
            .last()
            .is_some_and(|s| HEAP_TYPES.contains(&s.as_str()))
            && HEAP_CONSTRUCTORS.contains(&name.as_str())
        {
            let ty = segs.last().cloned().unwrap_or_default();
            self.push(cx, Ev::Site(format!("`{ty}::{name}`")), &t[i], lp);
            return j;
        }
        if is_p(t, j, '(') {
            return self.call(t, i, (segs, name), j, lp, cx);
        }
        let label = is_p(t, j, ':') && !sep(t, j);
        let struct_lit = is_p(t, j, '{') && name.starts_with(char::is_uppercase);
        if label || struct_lit || matches!(name.as_str(), "self" | "Self" | "crate" | "super") {
            return j;
        }
        if segs.is_empty() {
            if cx.locals.contains(&name) || cx.callable.contains(&name) {
                return j;
            }
            if let Some(&cid) = cx.closures.get(&name) {
                self.push(cx, Ev::Escape(cid), &t[i], lp);
                return j;
            }
        }
        self.push(
            cx,
            Ev::Value {
                segs,
                name,
                res: Res::Pending,
            },
            &t[i],
            lp,
        );
        j
    }

    fn call(
        &mut self,
        t: &'a [Tok],
        i: usize,
        (segs, name): (Vec<String>, String),
        open: usize,
        lp: bool,
        cx: &mut FnCtx,
    ) -> usize {
        if segs.is_empty() {
            let local = if let Some(&cid) = cx.closures.get(&name) {
                Some(Ev::ClosureCall(cid))
            } else if cx.callable.contains(&name) {
                Some(Ev::ParamCall(name.clone()))
            } else if cx.locals.contains(&name) {
                Some(Ev::Indirect)
            } else {
                None
            };
            if let Some(ev) = local {
                self.push(cx, ev, &t[i], lp);
                let (args, e) = self.call_args(t, open, lp, cx);
                self.escape_closures(cx, &args, &t[i], lp);
                return e;
            }
        }
        let (args, e) = self.call_args(t, open, lp, cx);
        if matches!(name.as_str(), "call" | "call_mut" | "call_once")
            && segs.last().is_some_and(|s| FN_TRAITS.contains(&s.as_str()))
        {
            // `FipFn::call(&g, ..)`, `Fn::call(&g, ..)`
            let ev = match args.first() {
                Some(Arg::Param(p)) => Ev::ParamCall(p.clone()),
                Some(Arg::Closure(c)) => Ev::ClosureCall(*c),
                _ => Ev::Indirect,
            };
            self.push(cx, ev, &t[i], lp);
            return e;
        }
        let ev = Ev::Call {
            segs,
            name,
            args,
            res: Res::Pending,
        };
        self.push(cx, ev, &t[i], lp);
        e
    }

    fn macro_call(
        &mut self,
        t: &'a [Tok],
        i: usize,
        name: &str,
        g: usize,
        lp: bool,
        cx: &mut FnCtx,
    ) -> usize {
        let ge = group_end(t, g);
        let (macros, toks) = (self.macros, self.toks);
        if GHOST_MACROS.contains(&name) {
            return ge;
        }
        if name == "fip_fn" {
            let inner = if is_id(t, g + 1, "move") {
                g + 2
            } else {
                g + 1
            };
            if is_p(t, inner, '|') {
                let (cid, _) = self.closure(t, inner, ge - 1, cx);
                self.push(cx, Ev::Escape(cid), &t[i], lp);
            }
            return ge;
        }
        if name == "include" {
            self.push(
                cx,
                Ev::Unknown("`include!` whose file could not be read".to_string()),
                &t[i],
                lp,
            );
            return ge;
        }
        if ALLOC_MACROS.contains(&name) {
            self.push(cx, Ev::Site(format!("`{name}!`")), &t[i], lp);
        } else if let Some(bodies) = macros.get(name)
            && !cx.expanding.iter().any(|m| m == name)
        {
            cx.expanding.push(name.to_string());
            for &(f, a, b) in bodies {
                self.scan(&toks[f], a, b, lp, cx);
            }
            cx.expanding.pop();
        } else if !PANIC_MACROS.contains(&name)
            && !ALLOC_FREE_MACROS.contains(&name)
            && !cx.expanding.iter().any(|m| m == name)
        {
            self.push(
                cx,
                Ev::Unknown(format!("macro `{name}!` (its expansion is not visible)")),
                &t[i],
                lp,
            );
        }
        self.scan(t, g + 1, ge - 1, lp, cx);
        ge
    }
}

/// Classifies a call argument `t[x..b]` (after `&`, `mut`, `*`).
fn classify_path(t: &[Tok], x: usize, b: usize, cx: &FnCtx) -> Arg {
    let mut segs = Vec::new();
    let mut q = x;
    while let Some(s) = id(t, q) {
        segs.push(s.to_string());
        if sep(t, q + 1) {
            q += 3;
        } else {
            q += 1;
            break;
        }
    }
    if segs.is_empty() || q != b {
        return Arg::Other;
    }
    let name = segs.pop().unwrap_or_default();
    if segs.is_empty() {
        if cx.callable.contains(&name) {
            return Arg::Param(name);
        }
        if let Some(&c) = cx.closures.get(&name) {
            return Arg::Closure(c);
        }
        if cx.locals.contains(&name) || KEYWORDS.contains(&name.as_str()) || name == "self" {
            return Arg::Other;
        }
    }
    Arg::Named {
        segs,
        name,
        res: Res::Pending,
    }
}

/// `use` tree `t[a..b]` under `prefix`.
fn use_tree(
    t: &[Tok],
    from: usize,
    to: usize,
    prefix: &[String],
    uses: &mut Vec<(String, Vec<String>)>,
    globs: &mut Vec<Vec<String>>,
) {
    let mut segs = prefix.to_vec();
    let mut k = from;
    if sep(t, k) {
        k += 2;
    }
    while k < to {
        if is_p(t, k, '*') {
            globs.push(segs);
            return;
        }
        if is_p(t, k, '{') {
            let e = group_end(t, k);
            for (x, y) in split_top(t, k + 1, e - 1, false) {
                use_tree(t, x, y, &segs, uses, globs);
            }
            return;
        }
        let Some(s) = id(t, k) else { return };
        segs.push(s.to_string());
        if sep(t, k + 1) {
            k += 3;
            continue;
        }
        if is_id(t, k + 1, "as") {
            if let Some(alias) = id(t, k + 2)
                && alias != "_"
            {
                uses.push((alias.to_string(), segs));
            }
            return;
        }
        if s == "self" {
            segs.pop();
        }
        if let Some(last) = segs.last().cloned() {
            uses.push((last, segs));
        }
        return;
    }
}
