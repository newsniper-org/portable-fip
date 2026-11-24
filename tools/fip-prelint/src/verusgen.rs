// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Generator of the Verus sidecar (top plan T13.4), `cargo fip-prelint
//! --verus-sidecar`: runs Verus with `--output-json --log vir`, refuses anything but
//! a successful `--no-cheating` run over the entire crate, and lists the exec
//! functions of the crate that Verus verified (from the VIR log: mode `Exec`, a body,
//! not `external_body`; `#[verifier::external]` items are not in the VIR at all),
//! with their item hashes ([`crate::verus::item_hash`]).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

use crate::verus::{self, ALLOC_CHECK, Entry, NO_CHEATING, Sidecar};

/// Flags that restrict or weaken what Verus checks: a run with one of them is never
/// recorded.
pub const REFUSED_FLAGS: &[&str] = &[
    "--no-verify",
    "--no-lifetime",
    "--verify-root",
    "--verify-module",
    "--verify-only-module",
    "--verify-function",
    "--no-builtin",
    "--no-vstd",
    "--no-erasure-check",
    "--no-trait-conflicts",
    // `verus::STD_CRATE_FLAGS` (the fork audit, 2026-11-09): the crate verified as
    // vstd, core or std.
    "--is-vstd",
    "--is-core",
    "--is-stdlib-outside-of-core",
];

// ---------------------------------------------------------------------------------
// A minimal JSON reader (the `--output-json` result).

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(kv) => kv.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn path(&self, keys: &[&str]) -> Option<&Json> {
        keys.iter().try_fold(self, |j, k| j.get(k))
    }
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Json::Bool(b) => Some(*b),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            Json::Num(n) if *n >= 0.0 && n.fract() == 0.0 => Some(*n as u64),
            _ => None,
        }
    }
}

pub fn parse_json(text: &str) -> Result<Json, String> {
    let b = text.as_bytes();
    let mut i = 0;
    let v = json_value(b, &mut i)?;
    json_ws(b, &mut i);
    if i != b.len() {
        return Err(format!("trailing data at byte {i}"));
    }
    Ok(v)
}

fn json_ws(b: &[u8], i: &mut usize) {
    while *i < b.len() && b[*i].is_ascii_whitespace() {
        *i += 1;
    }
}

fn json_value(b: &[u8], i: &mut usize) -> Result<Json, String> {
    json_ws(b, i);
    let err = |i: usize| format!("unexpected input at byte {i}");
    match b.get(*i) {
        Some(b'{') => {
            *i += 1;
            let mut kv = Vec::new();
            json_ws(b, i);
            if b.get(*i) == Some(&b'}') {
                *i += 1;
                return Ok(Json::Obj(kv));
            }
            loop {
                json_ws(b, i);
                let Json::Str(k) = json_value(b, i)? else {
                    return Err(err(*i));
                };
                json_ws(b, i);
                if b.get(*i) != Some(&b':') {
                    return Err(err(*i));
                }
                *i += 1;
                let v = json_value(b, i)?;
                kv.push((k, v));
                json_ws(b, i);
                match b.get(*i) {
                    Some(b',') => *i += 1,
                    Some(b'}') => {
                        *i += 1;
                        return Ok(Json::Obj(kv));
                    }
                    _ => return Err(err(*i)),
                }
            }
        }
        Some(b'[') => {
            *i += 1;
            let mut v = Vec::new();
            json_ws(b, i);
            if b.get(*i) == Some(&b']') {
                *i += 1;
                return Ok(Json::Arr(v));
            }
            loop {
                v.push(json_value(b, i)?);
                json_ws(b, i);
                match b.get(*i) {
                    Some(b',') => *i += 1,
                    Some(b']') => {
                        *i += 1;
                        return Ok(Json::Arr(v));
                    }
                    _ => return Err(err(*i)),
                }
            }
        }
        Some(b'"') => {
            *i += 1;
            let mut s = Vec::new();
            while let Some(&c) = b.get(*i) {
                *i += 1;
                match c {
                    b'"' => {
                        return String::from_utf8(s)
                            .map(Json::Str)
                            .map_err(|e| e.to_string());
                    }
                    b'\\' => {
                        let e = *b.get(*i).ok_or_else(|| err(*i))?;
                        *i += 1;
                        match e {
                            b'n' => s.push(b'\n'),
                            b't' => s.push(b'\t'),
                            b'r' => s.push(b'\r'),
                            b'b' => s.push(8),
                            b'f' => s.push(12),
                            b'u' => {
                                let hex = b.get(*i..*i + 4).ok_or_else(|| err(*i))?;
                                let code = u32::from_str_radix(
                                    std::str::from_utf8(hex).map_err(|e| e.to_string())?,
                                    16,
                                )
                                .map_err(|e| e.to_string())?;
                                *i += 4;
                                let ch = char::from_u32(code).unwrap_or('\u{fffd}');
                                let mut buf = [0u8; 4];
                                s.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                            }
                            other => s.push(other),
                        }
                    }
                    c => s.push(c),
                }
            }
            Err("unterminated string".to_string())
        }
        Some(b't') if b[*i..].starts_with(b"true") => {
            *i += 4;
            Ok(Json::Bool(true))
        }
        Some(b'f') if b[*i..].starts_with(b"false") => {
            *i += 5;
            Ok(Json::Bool(false))
        }
        Some(b'n') if b[*i..].starts_with(b"null") => {
            *i += 4;
            Ok(Json::Null)
        }
        Some(c) if *c == b'-' || c.is_ascii_digit() => {
            let start = *i;
            while *i < b.len() && (b[*i].is_ascii_digit() || b"+-.eE".contains(&b[*i])) {
                *i += 1;
            }
            std::str::from_utf8(&b[start..*i])
                .ok()
                .and_then(|s| s.parse().ok())
                .map(Json::Num)
                .ok_or_else(|| err(start))
        }
        _ => Err(err(*i)),
    }
}

// ---------------------------------------------------------------------------------
// The VIR log (`--log vir`): top-level `(@ "<span>" (Function ..))` records.

/// `true` when the S-expression text `s` is a list whose head symbol is `sym`: `(`,
/// optional whitespace (Verus's printer may break the line there), `sym`, then whitespace
/// or `)`.
fn head_is(s: &str, sym: &str) -> bool {
    s.strip_prefix('(')
        .map(str::trim_start)
        .and_then(|r| r.strip_prefix(sym))
        .is_some_and(|r| r.starts_with(|c: char| c.is_ascii_whitespace() || c == ')'))
}

/// A span as Verus prints it: `<file>:<line>:<col>: <line>:<col> (#n)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSpan {
    pub file: String,
    pub lo: (usize, usize),
    pub hi: (usize, usize),
}

pub fn parse_span(s: &str) -> Option<VirSpan> {
    let s = s.split(" (#").next()?;
    let (left, right) = s.rsplit_once(": ")?;
    let mut l = left.rsplitn(3, ':');
    let lcol = l.next()?.parse().ok()?;
    let lline = l.next()?.parse().ok()?;
    let file = l.next()?.to_string();
    let (rline, rcol) = right.split_once(':')?;
    Some(VirSpan {
        file,
        lo: (lline, lcol),
        hi: (rline.parse().ok()?, rcol.parse().ok()?),
    })
}

/// One function of the VIR log.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirFn {
    pub path: String,
    /// The function's span (its signature).
    pub span: VirSpan,
    pub mode: String,
    pub external_body: bool,
    /// The span of the body, if it has one.
    pub body: Option<VirSpan>,
    pub requires: bool,
    /// The function's span comes from a macro expansion (its syntax context is not
    /// `#0`): one text for every expansion.
    pub expanded: bool,
    /// Every other function its record names (`(Fun :path ..)`: call targets, also
    /// resolved trait methods and functions named in its specification).
    pub calls: Vec<String>,
    /// Its proved `allocates` bound ([`alloc_bound`] of the `:allocates` field).
    pub allocates: verus::AllocBound,
    /// Its `deallocates` bound ([`alloc_bound`] of the `:deallocations` field, fork
    /// `83fd42f3b`).
    pub deallocates: verus::AllocBound,
    /// `:encapsulates_alloc true` in its attributes (`encapsulates alloc(a, d)`).
    pub encapsulates: bool,
    /// The first segments of the paths in its record: the crates whose functions,
    /// types, traits and constants it uses (as Verus resolved them, so through
    /// re-exports too).
    pub mentions: Vec<String>,
}

/// End of the balanced s-expression starting at `open` (a `(`), strings skipped.
fn sexp_end(t: &[u8], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut j = open;
    let mut in_str = false;
    while j < t.len() {
        let c = t[j];
        if in_str {
            if c == b'\\' {
                j += 1;
            } else if c == b'"' {
                in_str = false;
            }
        } else if c == b'"' {
            in_str = true;
        } else if c == b'(' {
            depth += 1;
        } else if c == b')' {
            depth -= 1;
            if depth == 0 {
                return Some(j + 1);
            }
        }
        j += 1;
    }
    None
}

/// The direct children of the field `key` (e.g. `:body`) of a record: its text up to
/// the next field of the same record, as a substring of `rec`.
fn field<'r>(rec: &'r str, key: &str) -> Option<&'r str> {
    // Fields are found at nesting depth 1 of the `(Function ..)` record.
    let t = rec.as_bytes();
    let mut depth = 0usize;
    let mut in_str = false;
    let mut j = 0;
    let mut start = None;
    while j < t.len() {
        let c = t[j];
        if in_str {
            if c == b'\\' {
                j += 1;
            } else if c == b'"' {
                in_str = false;
            }
        } else if c == b'"' {
            in_str = true;
        } else if c == b'(' {
            depth += 1;
        } else if c == b')' {
            depth = depth.saturating_sub(1);
            if depth == 0 && start.is_some() {
                return start.map(|s| &rec[s..j]);
            }
        } else if depth == 1 && c == b':' {
            if let Some(s) = start {
                return Some(&rec[s..j]);
            }
            // The key, then whitespace (Verus wraps long records at any space).
            if rec[j..].starts_with(key)
                && rec[j + key.len()..].starts_with(|c: char| c.is_ascii_whitespace())
            {
                start = Some(j + key.len());
                j += key.len();
                continue;
            }
        }
        j += 1;
    }
    start.map(|s| &rec[s..])
}

pub fn vir_functions(text: &str) -> Result<Vec<VirFn>, String> {
    let t = text.as_bytes();
    let mut out = Vec::new();
    let marker = "(@ \"";
    let mut from = 0;
    while let Some(rel) = text[from..].find(marker) {
        let at = from + rel;
        // Only top-level records: at the start of a line.
        if at != 0 && t[at - 1] != b'\n' {
            from = at + marker.len();
            continue;
        }
        let end = sexp_end(t, at).ok_or("unbalanced VIR log")?;
        from = end;
        let rec = &text[at..end];
        let Some(q) = rec[marker.len()..].find('"') else {
            continue;
        };
        let span_text = &rec[marker.len()..marker.len() + q];
        // The record's payload `(Function ..)`. Verus wraps long lines at any space and
        // also right after an opening parenthesis: with a long source path in the span
        // the head is printed as `(` + newline + `Function` (measured: a crate under
        // `~/.cargo/git/checkouts/..`, whose trait method declaration was then dropped
        // from the sidecar's `skip` lines).
        let payload_at = marker.len() + q + 1;
        let lead = rec[payload_at..].len() - rec[payload_at..].trim_start().len();
        let fstart = payload_at + lead;
        if !head_is(&rec[fstart..], "Function") {
            continue;
        }
        let Some(fend) = sexp_end(t, at + fstart) else {
            continue;
        };
        let func = &text[at + fstart..fend];
        let span = parse_span(span_text).ok_or_else(|| format!("bad span `{span_text}`"))?;
        let name = field(func, ":name").ok_or("function without :name")?;
        let path = name
            .split(":path")
            .nth(1)
            .and_then(|p| p.split_whitespace().next())
            .map(|p| vir_path(p.trim_end_matches(')')))
            .ok_or_else(|| format!("bad :name `{name}`"))?;
        let mode = field(func, ":mode")
            .map(|m| m.split_whitespace().next().unwrap_or("").to_string())
            .ok_or_else(|| format!("`{path}`: no :mode"))?;
        let attrs = field(func, ":attrs").ok_or_else(|| format!("`{path}`: no :attrs"))?;
        let external_body = attrs
            .split(":is_external_body")
            .nth(1)
            .map(|r| r.trim_start().starts_with("true"))
            .ok_or_else(|| format!("`{path}`: no :is_external_body"))?;
        let body_text = field(func, ":body").ok_or_else(|| format!("`{path}`: no :body"))?;
        let body_text = body_text.trim();
        let body = if body_text.starts_with("None") {
            None
        } else {
            let q = body_text
                .strip_prefix('(')
                .map(str::trim_start)
                .and_then(|r| r.strip_prefix("@@"))
                .map(str::trim_start)
                .and_then(|r| r.strip_prefix('"'))
                .and_then(|r| r.split('"').next())
                .ok_or_else(|| format!("`{path}`: unrecognised :body"))?;
            Some(parse_span(q).ok_or_else(|| format!("`{path}`: bad body span `{q}`"))?)
        };
        let req = field(func, ":require").ok_or_else(|| format!("`{path}`: no :require"))?;
        let requires = req.trim() != "()";
        let mut calls: Vec<String> = Vec::new();
        for part in func.split("(Fun :path ").skip(1) {
            let p = part
                .split(|c: char| c.is_whitespace() || c == ')')
                .next()
                .unwrap_or("");
            let p = vir_path(p);
            if !p.is_empty() && p != path && !calls.contains(&p) {
                calls.push(p);
            }
        }
        // The fork's `:allocates` field (absent before 0.2026.11: nothing proved).
        let allocates = field(func, ":allocates").map_or(verus::AllocBound::None, alloc_bound);
        let deallocates =
            field(func, ":deallocations").map_or(verus::AllocBound::None, alloc_bound);
        // (absent before the fork `e93729c25`)
        let encapsulates = attrs
            .split(":encapsulates_alloc")
            .nth(1)
            .is_some_and(|r| r.trim_start().starts_with("true"));
        // `#[verifier::fip]` (`:fip true`; `fip(strict)` sets it too): the fork proves
        // that a normal return deallocates nothing and admits no `deallocates` clause
        // beside it, so its `:deallocations` is `None`. It is `deallocates 0`. Not for
        // a function with `encapsulates`, whose body the fork does not check.
        let fip = attrs
            .split(":fip ")
            .nth(1)
            .is_some_and(|r| r.trim_start().starts_with("true"));
        let deallocates = if fip && !encapsulates && deallocates == verus::AllocBound::None {
            verus::AllocBound::Linear(0, Vec::new())
        } else {
            deallocates
        };
        out.push(VirFn {
            mentions: path_roots(func),
            path,
            span,
            mode,
            external_body,
            body,
            requires,
            expanded: !span_text.ends_with(" (#0)"),
            calls,
            allocates,
            deallocates,
            encapsulates,
        });
    }
    Ok(out)
}

/// The identifiers that start a path (`root::..`) in `text`, sorted, each once.
fn path_roots(text: &str) -> Vec<String> {
    let b = text.as_bytes();
    let ident = |c: u8| c == b'_' || c.is_ascii_alphanumeric();
    let mut out = BTreeSet::new();
    let mut i = 0;
    while i + 1 < b.len() {
        if b[i] == b':' && b[i + 1] == b':' {
            let mut j = i;
            while j > 0 && ident(b[j - 1]) {
                j -= 1;
            }
            // (the first segment: nothing of a path in front of it)
            let first = j == 0 || !(b[j - 1] == b':' || b[j - 1] == b'%' || b[j - 1] == b'&');
            if j < i && first && !b[j].is_ascii_digit() {
                out.insert(text[j..i].to_string());
            }
            i += 2;
        } else {
            i += 1;
        }
    }
    out.into_iter().collect()
}

/// An s-expression of the VIR log: an atom (a string literal keeps its quotes) or a
/// list.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    fn atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(a) => Some(a),
            Sexp::List(_) => None,
        }
    }
    fn list(&self) -> &[Sexp] {
        match self {
            Sexp::List(l) => l,
            Sexp::Atom(_) => &[],
        }
    }
    /// The list's first element is the atom `head`.
    fn is(&self, head: &str) -> bool {
        self.list().first().and_then(Sexp::atom) == Some(head)
    }
    /// The text without spans (`"<file>:<line>.."` strings after `@@`/`@`) and without
    /// `:id <n>` pairs: stable under moves of the source text.
    fn stable_text(&self, out: &mut String) {
        match self {
            Sexp::Atom(a) => out.push_str(a),
            Sexp::List(l) => {
                out.push('(');
                let mut k = 0;
                while k < l.len() {
                    let head = l[k].atom();
                    if k == 1
                        && matches!(l[0].atom(), Some("@@" | "@"))
                        && head.is_some_and(|a| a.starts_with('"'))
                    {
                        k += 1;
                        continue;
                    }
                    if head == Some(":id") {
                        k += 2;
                        continue;
                    }
                    if !out.ends_with('(') {
                        out.push(' ');
                    }
                    l[k].stable_text(out);
                    k += 1;
                }
                out.push(')');
            }
        }
    }
}

/// Parses the s-expressions of `text` (the value of a record field).
fn parse_sexps(text: &str) -> Option<Vec<Sexp>> {
    fn one(b: &[u8], i: &mut usize, text: &str) -> Option<Sexp> {
        while *i < b.len() && b[*i].is_ascii_whitespace() {
            *i += 1;
        }
        match b.get(*i)? {
            b'(' => {
                *i += 1;
                let mut items = Vec::new();
                loop {
                    while *i < b.len() && b[*i].is_ascii_whitespace() {
                        *i += 1;
                    }
                    match b.get(*i)? {
                        b')' => {
                            *i += 1;
                            return Some(Sexp::List(items));
                        }
                        _ => items.push(one(b, i, text)?),
                    }
                }
            }
            b')' => None,
            b'"' => {
                let start = *i;
                *i += 1;
                while *i < b.len() && b[*i] != b'"' {
                    if b[*i] == b'\\' {
                        *i += 1;
                    }
                    *i += 1;
                }
                *i += 1;
                Some(Sexp::Atom(text.get(start..(*i).min(b.len()))?.to_string()))
            }
            _ => {
                let start = *i;
                while *i < b.len() && !b[*i].is_ascii_whitespace() && b[*i] != b'(' && b[*i] != b')'
                {
                    *i += 1;
                }
                Some(Sexp::Atom(text[start..*i].to_string()))
            }
        }
    }
    let b = text.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    loop {
        while i < b.len() && b[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= b.len() {
            return Some(out);
        }
        out.push(one(b, &mut i, text)?);
    }
}

/// A linear form `c + Σ kᵢ·pᵢ` (parameter → coefficient).
type Linear = (u64, BTreeMap<String, u64>);

/// The linear form of a VIR expression `(@@ "<span>" (> <expr>) <type>)`, if it is
/// one: an integer constant (`Const (Constant Int K)`, `0 <= K < 2^64`), a read of a
/// local of an unsigned integer type or `nat` (in an `allocates` clause only the
/// parameters are in scope; a cast `n as nat` of an unsigned `n` is not in the VIR),
/// or `+` and `*` (one side constant) over `int`/`nat`, which cannot wrap.
fn linear(e: &Sexp) -> Option<Linear> {
    let l = e.list();
    if !(e.is("@@") && l.len() == 4 && l[2].is(">")) {
        return None;
    }
    let ex = &l[2].list()[1..];
    let unbounded = |t: &Sexp| {
        let mut s = String::new();
        t.stable_text(&mut s);
        s.contains("(IntRange Int)") || s.contains("(IntRange Nat)")
    };
    match ex.first()?.atom()? {
        "Const" => {
            let c = ex.get(1)?;
            let cl = c.list();
            if c.is("Constant") && cl.len() == 3 && cl[1].atom() == Some("Int") {
                let k: u64 = cl[2].atom()?.parse().ok()?;
                return Some((k, BTreeMap::new()));
            }
            None
        }
        "ReadPlace" => {
            let place = ex.get(1)?;
            let pl = place.list();
            if !(place.is("@@") && pl.len() == 4 && pl[2].is("Place")) {
                return None;
            }
            let p = pl[2].list();
            if p.get(1)?.atom()? != "Local" || !p.get(2)?.is("VarIdent") {
                return None;
            }
            let name = p[2].list().get(1)?.atom()?;
            let name = name.strip_prefix('"')?.strip_suffix('"')?;
            let ty = {
                let mut s = String::new();
                l[3].stable_text(&mut s);
                s
            };
            let unsigned = ty.starts_with("(Typ Int (IntRange U ")
                || ty == "(Typ Int (IntRange USize))"
                || ty == "(Typ Int (IntRange Nat))";
            let ident = name
                .bytes()
                .next()
                .is_some_and(|b| b == b'_' || b.is_ascii_alphabetic())
                && name.bytes().all(|b| b == b'_' || b.is_ascii_alphanumeric());
            if !(unsigned && ident) {
                return None;
            }
            Some((0, BTreeMap::from([(name.to_string(), 1)])))
        }
        "Binary" => {
            let op = ex.get(1)?;
            // `(BinaryOp Arith (ArithOp Add|Mul (OverflowBehavior .. (IntRange Int|Nat))))`
            let arith = op.list().get(2)?;
            let kind = arith.list().get(1)?.atom()?;
            if !(op.list().get(1)?.atom()? == "Arith" && arith.is("ArithOp") && unbounded(arith)) {
                return None;
            }
            let (a, b) = (linear(ex.get(2)?)?, linear(ex.get(3)?)?);
            match kind {
                "Add" => {
                    let mut t = a.1;
                    for (p, k) in b.1 {
                        let e = t.entry(p).or_insert(0);
                        *e = e.checked_add(k)?;
                    }
                    Some((a.0.checked_add(b.0)?, t))
                }
                "Mul" => {
                    let (c, (k0, terms)) = if a.1.is_empty() {
                        (a.0, b)
                    } else if b.1.is_empty() {
                        (b.0, a)
                    } else {
                        return None;
                    };
                    let mut t = BTreeMap::new();
                    for (p, k) in terms {
                        let k = k.checked_mul(c)?;
                        if k > 0 {
                            t.insert(p, k);
                        }
                    }
                    Some((k0.checked_mul(c)?, t))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The proved bound of a function from the text of its `:allocates` field (fork
/// `0.2026.11.05.ca33b04`: `None`, or `(@@ "<span>" (> <expr>) <type>)`): a linear form
/// ([`linear`]) or, for anything else, the SHA-256 of the expression's text without
/// spans and ids ([`verus::AllocBound::Opaque`]).
pub fn alloc_bound(field_text: &str) -> verus::AllocBound {
    let t = field_text.trim();
    if t == "None" {
        return verus::AllocBound::None;
    }
    let opaque = |t: &str| verus::AllocBound::Opaque(verus::sha256_hex(t.as_bytes()));
    let Some(sexps) = parse_sexps(t) else {
        return opaque(t);
    };
    let [e] = &sexps[..] else {
        return opaque(t);
    };
    match linear(e) {
        Some((c, terms)) => {
            verus::AllocBound::Linear(c, terms.into_iter().filter(|(_, k)| *k > 0).collect())
        }
        None => {
            let mut s = String::new();
            e.stable_text(&mut s);
            opaque(&s)
        }
    }
}

// ---------------------------------------------------------------------------------
// Generation.

/// `path` relative to `base` (both made absolute against the current directory and
/// normalised lexically; symlinks are resolved where the paths exist).
pub fn relative(path: &Path, base: &Path) -> String {
    let abs = |p: &Path| -> Vec<String> {
        let p = std::fs::canonicalize(p).unwrap_or_else(|_| {
            std::env::current_dir()
                .map(|d| d.join(p))
                .unwrap_or_else(|_| p.to_path_buf())
        });
        let mut v: Vec<String> = Vec::new();
        for c in p.components() {
            match c {
                Component::ParentDir => {
                    v.pop();
                }
                Component::Normal(s) => v.push(s.to_string_lossy().into_owned()),
                _ => {}
            }
        }
        v
    };
    let (p, b) = (abs(path), abs(base));
    let common = p.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let mut parts: Vec<String> = vec!["..".to_string(); b.len() - common];
    parts.extend(p[common..].iter().cloned());
    parts.join("/")
}

/// The run's provenance, read from Verus's `--output-json` result.
pub struct RunInfo {
    pub version: String,
    pub commit: String,
    pub toolchain: String,
    pub verified: u64,
    /// Target triple and cargo features of the run ([`run_cfg`]).
    pub target: String,
    pub features: Vec<String>,
    /// Edition of the run ([`run_cfg`]).
    pub edition: String,
    /// The crates the run imported: name, SHA-256 of the sidecar given for it by
    /// `--import-sidecar`, that sidecar's edition (the sidecar's `import` lines).
    pub imports: Vec<(String, String, String)>,
    /// Functions the run's `--import-sidecar`s skipped because their code may differ
    /// between the builds ([`imported_cfg_skips`]).
    pub imported_skips: Vec<String>,
    /// Traits the run's `--import-sidecar`s record as divergent (their `divergent`
    /// lines): a function naming one of their methods is skipped.
    pub imported_divergent: Vec<String>,
    /// [`verus::Gated::names`] of the sources of the imported crates that use
    /// `verus_keep_ghost` for more than [`verus::gate_violation`] admits.
    pub imported_gated: Vec<String>,
    /// The names of those crates: a function that uses anything of one is not listed.
    pub imported_nonconforming: Vec<String>,
}

/// Checks the `--output-json` result: success, no errors, the entire crate.
pub fn run_info(json: &Json) -> Result<RunInfo, String> {
    let r = |k: &str| json.path(&["verification-results", k]);
    let flag = |k: &str| r(k).and_then(Json::as_bool);
    if flag("success") != Some(true) {
        return Err("Verus reported no success".to_string());
    }
    if flag("encountered-error") != Some(false) || flag("encountered-vir-error") != Some(false) {
        return Err("Verus encountered an error".to_string());
    }
    if r("errors").and_then(Json::as_u64) != Some(0) {
        return Err("Verus reported errors".to_string());
    }
    if flag("is-verifying-entire-crate") != Some(true) {
        return Err("Verus did not verify the entire crate".to_string());
    }
    let s = |k: &str| {
        json.path(&["verus", k])
            .and_then(Json::as_str)
            .map(str::to_string)
            .ok_or_else(|| format!("no `verus.{k}` in the JSON result"))
    };
    Ok(RunInfo {
        version: s("version")?,
        commit: s("commit")?,
        toolchain: s("toolchain")?,
        verified: r("verified").and_then(Json::as_u64).unwrap_or(0),
        target: String::new(),
        features: Vec::new(),
        edition: String::new(),
        imports: Vec::new(),
        imported_skips: Vec::new(),
        imported_divergent: Vec::new(),
        imported_gated: Vec::new(),
        imported_nonconforming: Vec::new(),
    })
}

/// The target, the cargo features and the edition of a Verus command line: `--target
/// <t>` (else `host`), every `--cfg feature="x"`, and `--edition <e>`. Any other
/// `--cfg` is refused: the driver could not compare it with its own build. A run
/// without `--edition` is refused too: Verus's default edition is not cargo's, so the
/// crate would be verified as written for another edition than it is compiled for.
pub fn run_cfg(flags: &[String], host: &str) -> Result<(String, Vec<String>, String), String> {
    let mut target = host.to_string();
    let mut features = Vec::new();
    let mut edition: Option<String> = None;
    let mut k = 0;
    while k < flags.len() {
        let f = &flags[k];
        let mut value = |name: &str| -> Option<String> {
            if f == name {
                k += 1;
                flags.get(k).cloned()
            } else {
                f.strip_prefix(&format!("{name}=")).map(str::to_string)
            }
        };
        if let Some(t) = value("--target") {
            target = t;
        } else if let Some(e) = value("--edition") {
            if !verus::EDITIONS.contains(&e.as_str()) {
                return Err(format!("refused `--edition {e}`: not an edition of rustc"));
            }
            if edition.as_ref().is_some_and(|old| *old != e) {
                return Err("refused: `--edition` is given twice with different values".to_string());
            }
            edition = Some(e);
        } else if let Some(c) = value("--cfg") {
            let feature = c
                .strip_prefix("feature=\"")
                .and_then(|r| r.strip_suffix('"'))
                .filter(|v| !v.is_empty() && !v.contains([',', ' ', '"']));
            match feature {
                Some(v) => features.push(v.to_string()),
                None => {
                    return Err(format!(
                        "refused `--cfg {c}`: only cargo features (`feature=\"x\"`) are recorded and compared by the driver"
                    ));
                }
            }
        }
        k += 1;
    }
    features.sort();
    features.dedup();
    let edition = edition.ok_or_else(|| {
        "refused: the Verus run names no `--edition`; Verus's default is not the edition cargo compiles the crate for, so the sidecar would describe another program (pass the crate's edition, e.g. `--edition 2024`)"
            .to_string()
    })?;
    Ok((target, features, edition))
}

/// `Err` naming the first source file under `crate_dir/src` whose `cfg` predicates
/// or macros may make the driver's build differ from Verus's
/// ([`verus::crate_cfg_conflict`]). Run before Verus; [`build`] checks every source
/// of the run the same way.
pub fn crate_cfg_check(crate_dir: &Path) -> Result<(), String> {
    let mut files = Vec::new();
    let mut stack = vec![crate_dir.join("src")];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "rs") {
                files.push(p);
            }
        }
    }
    files.sort();
    cfg_check_files(crate_dir, &files)
}

/// [`verus::crate_cfg_conflict`] on each of `files`, with the `macro_rules!` names
/// of all of them.
pub fn cfg_check_files(crate_dir: &Path, files: &[PathBuf]) -> Result<(), String> {
    let mut texts = Vec::new();
    for f in files {
        let src = std::fs::read_to_string(f).map_err(|e| format!("{}: {e}", f.display()))?;
        texts.push((f, src));
    }
    let local: Vec<String> = texts
        .iter()
        .flat_map(|(_, src)| verus::macro_rules_names(src))
        .collect();
    for (f, src) in &texts {
        if let Some(line) = verus::verus_internal_use(src) {
            return Err(format!(
                "{}:{line}: the identifier `internal`: `verus::internal(..)` are the attributes Verus's own macros write for the verifier, and written by hand (in any spelling, or put together by a macro) they state what Verus did not check, so no sidecar is written",
                relative(f, crate_dir)
            ));
        }
        if let Some(c) = verus::crate_cfg_conflict(src, &local) {
            return Err(format!(
                "{}: {c}: the driver compiles the crate with other cfgs and environment than Verus (`fip_prelint`, the profile, `test`, cargo's variables), so no sidecar is written",
                relative(f, crate_dir)
            ));
        }
    }
    Ok(())
}

/// Paths of the functions an `--import-sidecar` skipped because their item text
/// differs between the builds ([`cfg_skip_reason`]), with impl segments as
/// [`verus::impl_key`] writes them.
pub fn imported_cfg_skips(sidecar: &Sidecar) -> Vec<String> {
    sidecar
        .skipped
        .iter()
        .filter(|(_, why)| cfg_skip_reason(why))
        .map(|(p, _)| verus::impl_key(p))
        .collect()
}

/// `true` for a skip reason saying the function's code may differ between the
/// driver's build and Verus's (a cfg in its text, Verus-only, or a caller of such a
/// function): its `ensures` may not hold for the code the driver analyses.
pub fn cfg_skip_reason(why: &str) -> bool {
    why.starts_with(SKIP_CFG_ITEM)
        || why.starts_with(SKIP_GHOST_ONLY)
        || why.starts_with(SKIP_TAINTED)
        || why.starts_with(SKIP_GATE)
        || why.starts_with(SKIP_DEP)
}

const SKIP_CFG_ITEM: &str = "the item text has ";
const SKIP_GHOST_ONLY: &str = "only in the Verus build";
const SKIP_TAINTED: &str = "relies on the specification of ";
/// The crate uses `verus_keep_ghost` for more than [`verus::gate_violation`] admits.
const SKIP_GATE: &str = "the crate has code for one build only: ";
/// The function uses something of an imported crate that does.
const SKIP_DEP: &str = "uses the crate ";

/// The `--import <name>=<file.vir>` arguments of a Verus command line.
pub fn imports(flags: &[String]) -> Vec<(String, PathBuf)> {
    let mut out = Vec::new();
    for (k, f) in flags.iter().enumerate() {
        let v = if f == "--import" {
            flags.get(k + 1).map(String::as_str)
        } else {
            f.strip_prefix("--import=")
        };
        if let Some((name, path)) = v.and_then(|v| v.split_once('=')) {
            out.push((name.to_string(), PathBuf::from(path)));
        }
    }
    out
}

/// The `--export <file.vir>` of a Verus command line.
pub fn export(flags: &[String]) -> Option<PathBuf> {
    flags.iter().enumerate().find_map(|(k, f)| {
        if f == "--export" {
            flags.get(k + 1).map(PathBuf::from)
        } else {
            f.strip_prefix("--export=").map(PathBuf::from)
        }
    })
}

/// The record written next to an exported VIR file (`<file.vir>.fip-run`) by a
/// generator run, which only succeeds with `--no-cheating`: the crate and the
/// SHA-256 of the VIR file.
pub fn export_record(krate: &str, vir: &[u8]) -> String {
    format!(
        "fip-prelint verus export\ncrate {krate}\nflags {NO_CHEATING}\nvir {}\n",
        verus::sha256_hex(vir)
    )
}

/// Checks an `--import name=vir` of a generator run (2026-11-04): the VIR file was
/// exported by a generator run (`--no-cheating`) of crate `name` (its
/// `<vir>.fip-run` record matches the file), and `sidecar`, that crate's committed
/// sidecar, has the trusted stamp with `--no-cheating` and every source file it lists
/// has its recorded SHA-256. Else the importing run proves its callers' panic freedom
/// on top of specifications nobody verified, and no sidecar is written.
pub fn check_import(
    name: &str,
    vir: &Path,
    sidecar: &Path,
    trusted: &verus::Trusted,
) -> Result<(), String> {
    let text = std::fs::read_to_string(sidecar)
        .map_err(|e| format!("sidecar `{}` of `{name}`: {e}", sidecar.display()))?;
    let sc = Sidecar::parse(&text)
        .map_err(|e| format!("sidecar `{}` of `{name}`: {e}", sidecar.display()))?;
    if sc.krate != name {
        return Err(format!(
            "sidecar `{}` is for crate `{}`, not `{name}`",
            sidecar.display(),
            sc.krate
        ));
    }
    sc.check_stamp(trusted)
        .map_err(|e| format!("sidecar `{}` of `{name}`: {e}", sidecar.display()))?;
    let dir = sidecar.parent().unwrap_or(Path::new("."));
    for (file, hash) in &sc.sources {
        let bytes = std::fs::read(dir.join(file)).map_err(|_| {
            format!(
                "sidecar `{}`: source `{file}` is missing",
                sidecar.display()
            )
        })?;
        if verus::sha256_hex(&bytes) != *hash {
            return Err(format!(
                "sidecar `{}`: source `{file}` changed since its verification run",
                sidecar.display()
            ));
        }
    }
    let record_path = PathBuf::from(format!("{}.fip-run", vir.display()));
    let record = std::fs::read_to_string(&record_path).map_err(|_| {
        format!(
            "`{}` was not exported by a generator run (`cargo fip-prelint --verus-sidecar`, which requires `{NO_CHEATING}`): no `{}`",
            vir.display(),
            record_path.display()
        )
    })?;
    let bytes = std::fs::read(vir).map_err(|e| format!("`{}`: {e}", vir.display()))?;
    if record != export_record(name, &bytes) {
        return Err(format!(
            "`{}` does not match its record `{}` (another crate, or exported by another run)",
            vir.display(),
            record_path.display()
        ));
    }
    Ok(())
}

/// A VIR path as the driver spells it: Verus 0.2026.11 marks the namespace of a
/// module or type segment with a one-letter prefix (`fip_core::t%slice::compact`,
/// `fip_strict::t%FipFn::call`; measured on the fork `0.2026.11.05.ca33b04`; 10.18
/// wrote `fip_core::slice::compact`). `%` is not part of a Rust identifier, so dropping
/// `<letter>%` before an identifier is unambiguous; `impl&%N` segments are kept.
pub fn vir_path(p: &str) -> String {
    p.split("::")
        .map(|seg| {
            let b = seg.as_bytes();
            if b.len() > 2
                && b[0].is_ascii_lowercase()
                && b[1] == b'%'
                && (b[2].is_ascii_alphabetic() || b[2] == b'_')
            {
                &seg[2..]
            } else {
                seg
            }
        })
        .collect::<Vec<_>>()
        .join("::")
}

/// `true` if a Verus command line uses `-V alloc-check` (spelled `-V alloc-check`,
/// `-Valloc-check` or `-V=alloc-check`): required since sidecar format 5.
pub fn uses_alloc_check(flags: &[String]) -> bool {
    verus::has_alloc_check(&trust_flags(flags))
}

/// The flags of a run that the sidecar's `flags` line records: `--no-cheating`, then
/// any of `verus::STD_CRATE_FLAGS` the run used (the generator refuses such a run;
/// recorded so that the driver refuses the sidecar should one be written anyway),
/// then `-V alloc-check` if the run used it (spelled `-V alloc-check`, `-Valloc-check`
/// or `-V=alloc-check`), each once.
pub fn trust_flags(flags: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    if flags.iter().any(|f| f == NO_CHEATING) {
        out.push(NO_CHEATING.to_string());
    }
    for s in verus::STD_CRATE_FLAGS {
        if flags.iter().any(|f| f == s) {
            out.push((*s).to_string());
        }
    }
    let alloc_check = flags.iter().enumerate().any(|(k, f)| {
        (f == "-V" && flags.get(k + 1).is_some_and(|v| v == ALLOC_CHECK))
            || f.strip_prefix("-V")
                .is_some_and(|v| v.trim_start_matches('=') == ALLOC_CHECK)
    });
    if alloc_check {
        out.extend(["-V".to_string(), ALLOC_CHECK.to_string()]);
    }
    out
}

/// Builds the sidecar of crate `krate` (its directory `crate_dir`, where the sidecar
/// is committed; paths are relative to it) from the functions of the VIR log.
/// Paths in VIR spans are relative to `root`, the directory Verus ran in.
pub fn build(
    root: &Path,
    krate: &str,
    crate_dir: &Path,
    info: &RunInfo,
    z3: &str,
    flags: &[String],
    fns: &[VirFn],
) -> Result<Sidecar, String> {
    let mut sources: BTreeSet<String> = BTreeSet::new();
    let mut add_source = |file: &Path| {
        if file.is_file() {
            sources.insert(relative(file, crate_dir));
        }
    };
    // Every workspace file the run read (spans of this crate and of imported crates),
    // and every source file of the crate.
    for f in fns {
        let p = Path::new(&f.span.file);
        if p.is_relative() && !f.span.file.starts_with("vstd/") {
            add_source(&root.join(p));
        }
    }
    let mut stack = vec![crate_dir.join("src")];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "rs") {
                add_source(&p);
            }
        }
    }
    // Every source of the run, also one outside `src/` (a `#[path]` module) or of an
    // imported crate (re-audit N4: `#[path = "../../shared.rs"]` escaped the scan of
    // `src/`); an imported crate's sources passed the same scan in its own run.
    let files: Vec<PathBuf> = sources.iter().map(|s| crate_dir.join(s)).collect();
    cfg_check_files(crate_dir, &files)?;
    // Names the two builds may give different meanings (amendment 2026-11-24 (4)).
    let mut texts: Vec<(String, String)> = Vec::new();
    for s in &sources {
        let text = std::fs::read_to_string(crate_dir.join(s))
            .map_err(|e| format!("{s}: cannot read: {e}"))?;
        texts.push((s.clone(), text));
    }
    let mut gated = verus::gated_names(&texts);
    // What the crate puts under `verus_keep_ghost` beyond what cannot change exec code:
    // then none of its functions is listed (amendment 2026-11-25).
    // (the crate's own sources: an imported crate answers for its own, through the
    // functions its sidecar skips and the names it gates)
    let own: Vec<(String, String)> = texts
        .iter()
        .filter(|(p, _)| !Path::new(p).starts_with(".."))
        .cloned()
        .collect();
    let gate = verus::gate_violation(&own);
    // In a crate that keeps to the list no definition is under the gate: the names
    // that count are those of the imported crates that do not keep to it.
    gated.names = info.imported_gated.iter().cloned().collect();
    let mut source_hashes = Vec::new();
    // Traits implemented or declared differently in the two builds (phase 4 of
    // decision 2026-11-06-redesign-verus-allocates): in any source of the run, or
    // recorded by an imported crate's sidecar.
    let mut divergent: Vec<(String, String, usize)> = Vec::new();
    for s in &sources {
        let bytes =
            std::fs::read(crate_dir.join(s)).map_err(|e| format!("{s}: cannot read: {e}"))?;
        source_hashes.push((s.clone(), verus::sha256_hex(&bytes)));
        let text = String::from_utf8_lossy(&bytes);
        for (t, at) in verus::divergent_traits(&text) {
            divergent.push((t, s.clone(), verus::line_of(&text, at)));
        }
    }
    divergent.sort();
    divergent.dedup();
    let divergent_names: BTreeSet<String> = divergent
        .iter()
        .map(|(t, _, _)| t.clone())
        .chain(info.imported_divergent.iter().cloned())
        .collect();
    // A function naming a method of a divergent trait (a call, also through a type
    // parameter, or a spec function in its specification).
    let names_divergent =
        |c: &str| verus::trait_segment(c).is_some_and(|t| divergent_names.contains(t));
    let prefix = format!("{krate}::");
    let mut entries: Vec<(Entry, &VirFn)> = Vec::new();
    let mut skipped = Vec::new();
    // Functions whose code may differ between the two builds (impl segments as
    // `impl_key`): their `ensures` were proved for Verus's build only.
    let mut tainted: BTreeSet<String> = info.imported_skips.iter().cloned().collect();
    for f in fns {
        if !f.path.starts_with(&prefix) || f.mode != "Exec" {
            continue;
        }
        if let Some(v) = &gate {
            skipped.push((f.path.clone(), format!("{SKIP_GATE}{v}")));
            tainted.insert(verus::impl_key(&f.path));
            continue;
        }
        // Anything of a crate whose exec code is not the same in the two builds: a
        // function, a type, a trait, a constant, as Verus resolved the names.
        if let Some(dep) = f
            .mentions
            .iter()
            .find(|m| info.imported_nonconforming.contains(m))
        {
            skipped.push((
                f.path.clone(),
                format!("{SKIP_DEP}`{dep}`, which has code for one build only"),
            ));
            tainted.insert(verus::impl_key(&f.path));
            continue;
        }
        let why = if f.external_body {
            Some("external_body (not verified)".to_string())
        } else if f.expanded {
            Some("generated by a macro expansion (one item text for every expansion)".to_string())
        } else {
            None
        };
        if let Some(why) = why {
            skipped.push((f.path.clone(), why));
            continue;
        }
        let Some(body) = &f.body else {
            skipped.push((f.path.clone(), "no body".to_string()));
            continue;
        };
        if body.file != f.span.file {
            skipped.push((
                f.path.clone(),
                "body in another file than the signature".to_string(),
            ));
            continue;
        }
        let file = root.join(&f.span.file);
        let src = std::fs::read_to_string(&file)
            .map_err(|e| format!("{}: cannot read: {e}", f.span.file))?;
        let (Some(start), Some(end)) = (
            verus::offset_of(&src, f.span.lo.0, f.span.lo.1),
            verus::offset_of(&src, body.hi.0, body.hi.1),
        ) else {
            skipped.push((f.path.clone(), "span outside its file".to_string()));
            continue;
        };
        let Some((lo, hi)) = verus::item_region(&src, start, end) else {
            skipped.push((f.path.clone(), "item text not found".to_string()));
            continue;
        };
        if verus::ghost_only_regions(&src)
            .iter()
            .any(|&(a, b)| a <= lo && hi <= b)
            || verus::in_gated_item(&src, lo, hi)
            || gated.files.contains(&relative(&file, crate_dir))
        {
            skipped.push((
                f.path.clone(),
                format!("{SKIP_GHOST_ONLY} (inside `#[cfg(verus_keep_ghost)]`)"),
            ));
            tainted.insert(verus::impl_key(&f.path));
            continue;
        }
        if let Some(c) = verus::cfg_conflict(&src[lo..hi]) {
            skipped.push((
                f.path.clone(),
                format!("{SKIP_CFG_ITEM}{c}: the driver's build and Verus's may differ"),
            ));
            tainted.insert(verus::impl_key(&f.path));
            continue;
        }
        if let Some(n) = verus::gated_name_use(&src[lo..hi], &gated, &divergent_names) {
            skipped.push((
                f.path.clone(),
                format!(
                    "{SKIP_CFG_ITEM}the name `{n}`, which is defined under a `cfg` (or by a definition that names one that is): the driver's build and Verus's may differ"
                ),
            ));
            tainted.insert(verus::impl_key(&f.path));
            continue;
        }
        entries.push((
            Entry {
                path: verus::impl_key(&f.path),
                file: relative(&file, crate_dir),
                line: verus::line_of(&src, lo),
                hash: verus::sha256_hex(&src.as_bytes()[lo..hi]),
                requires: f.requires,
                allocates: f.allocates.clone(),
                deallocates: f.deallocates.clone(),
                encapsulates: f.encapsulates,
            },
            f,
        ));
    }
    // Re-audit N4: a caller verified against the `ensures` of a function whose code
    // differs in the driver's build (`shared::on`, `ensures !r`, returning
    // `cfg!(fip_prelint)`) is not verified for the driver's code. Every function
    // naming a tainted one is tainted, to a fixpoint (a verified but unlisted
    // function passes its callees' assumptions on through its own `ensures`).
    //
    // Phase 4 (decision 2026-11-06-redesign-verus-allocates): a function naming a
    // method of a divergent trait is tainted as well. Verus proved it against the
    // trait's specification, assumed for every implementation, also those the driver's
    // build has and Verus never compiled (a plain-only twin impl).
    let mut why_tainted: BTreeMap<String, String> = BTreeMap::new();
    loop {
        let mut changed = false;
        for f in fns {
            let key = verus::impl_key(&f.path);
            if tainted.contains(&key) {
                continue;
            }
            let why = if let Some(c) = f
                .calls
                .iter()
                .find(|c| tainted.contains(&verus::impl_key(c)))
            {
                Some(format!(
                    "`{}`, whose code may differ in the driver's build",
                    verus::impl_key(c)
                ))
            } else {
                f.calls.iter().find(|c| names_divergent(c)).map(|c| {
                    format!(
                        "`{}`, a method of trait `{}`, which has an implementation or declaration in only one of the builds",
                        verus::impl_key(c),
                        verus::trait_segment(c).unwrap_or("")
                    )
                })
            };
            if let Some(why) = why {
                why_tainted.insert(key.clone(), why);
                tainted.insert(key);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let entries: Vec<Entry> = entries
        .into_iter()
        .filter_map(|(e, f)| {
            if !tainted.contains(&e.path) {
                return Some(e);
            }
            // Named through a tainted function, or sharing its path (another impl
            // block's method of that name: `{impl}` paths do not tell them apart).
            let why = why_tainted.get(&e.path).cloned().unwrap_or_else(|| {
                format!("`{}`, whose code may differ in the driver's build", e.path)
            });
            skipped.push((f.path.clone(), format!("{SKIP_TAINTED}{why}")));
            None
        })
        .collect();
    let mut entries = entries;
    entries.sort_by(|a, b| (&a.path, &a.file, a.line).cmp(&(&b.path, &b.file, b.line)));
    // Two entries with one path, file and line would be ambiguous: neither is listed.
    let key = |e: &Entry| (e.path.clone(), e.file.clone(), e.line);
    let dups: BTreeSet<(String, String, usize)> = entries
        .windows(2)
        .filter(|w| key(&w[0]) == key(&w[1]))
        .map(|w| key(&w[0]))
        .collect();
    entries.retain(|e| !dups.contains(&key(e)));
    skipped.extend(
        dups.into_iter()
            .map(|(p, f, l)| (p, format!("several functions with this path at {f}:{l}"))),
    );
    skipped.sort();
    skipped.dedup();
    let flags_kept = trust_flags(flags);
    Ok(Sidecar {
        format: verus::FORMAT,
        krate: krate.to_string(),
        verus_version: info.version.clone(),
        verus_commit: info.commit.clone(),
        z3: z3.to_string(),
        toolchain: info.toolchain.clone(),
        flags: flags_kept,
        target: info.target.clone(),
        features: info.features.clone(),
        edition: info.edition.clone(),
        verified: info.verified,
        sources: source_hashes,
        imports: info.imports.clone(),
        fns: entries,
        skipped,
        divergent,
    })
}

/// The Z3 that `verus` uses: `VERUS_Z3_PATH`, else `z3` next to the (resolved) Verus
/// binary.
pub fn z3_path(verus: &str) -> PathBuf {
    if let Some(p) = std::env::var_os("VERUS_Z3_PATH") {
        return PathBuf::from(p);
    }
    let exe = if verus.contains('/') {
        PathBuf::from(verus)
    } else {
        std::env::var_os("PATH")
            .and_then(|paths| {
                std::env::split_paths(&paths)
                    .map(|d| d.join(verus))
                    .find(|p| p.is_file())
            })
            .unwrap_or_else(|| PathBuf::from(verus))
    };
    let exe = std::fs::canonicalize(&exe).unwrap_or(exe);
    exe.with_file_name("z3")
}

/// `X.Y.Z` from `Z3 version X.Y.Z - 64 bit`.
pub fn z3_version(output: &str) -> Option<String> {
    let rest = output.split("Z3 version ").nth(1)?;
    let v = rest.split_whitespace().next()?;
    v.chars()
        .all(|c| c.is_ascii_digit() || c == '.')
        .then(|| v.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Trimmed from a real `--log vir` of Verus 0.2026.10.18 (crate `t`, run without
    /// `--no-cheating`): an exec function with a body and `requires`, one with
    /// `#[verifier::external_body]`, and a spec function.
    const VIR: &str = r#"(@ "src/lib.rs:3:1: 3:30 (#0)" (Function
  :name (Fun :path t::f) :proxy None :kind (FunctionKind Static) :owning_module t :mode
  Exec :typ_params () :params () :ret (@ "x" (Param :name "r" :mode Exec)) :require (
   (@ "src/lib.rs:4:14: 4:20 (#0)" (> Const (Bool true)))
  ) :ensure (() ()) :decrease () :attrs (FunctionAttrs :uses_ghost_blocks true :is_external_body false :is_unsafe false
  ) :body (@@ "src/lib.rs:5:1: 7:2 (#0)" (> Block ()))
  :extra_dependencies ()))

(@ "src/lib.rs:10:1: 10:20 (#0)" (Function
  :name (Fun :path t::ext) :proxy None :mode Exec :require () :attrs (FunctionAttrs :is_external_body true
  ) :body None :extra_dependencies ()))

(@ "src/lib.rs:12:1: 12:20 (#0)" (Function
  :name (Fun :path t::s) :proxy None :mode Spec :require () :attrs (FunctionAttrs :is_external_body false
  ) :body (@@ "src/lib.rs:12:21: 12:30 (#0)" (> Block ())) :extra_dependencies ()))
"#;

    /// Verus's printer wraps a long record right after an opening parenthesis: the head
    /// `(Function` and a body span `(@@` are then split over two lines (measured with a
    /// long source path in the span, `~/.cargo/git/checkouts/..`). Such records must be
    /// read like the unwrapped ones; before, they were skipped without a word.
    #[test]
    fn records_wrapped_after_a_parenthesis_are_read() {
        let wrapped = VIR
            .replace("(Function", "(\n  Function")
            .replace("(@@ ", "(\n   @@ ");
        assert_ne!(wrapped, VIR);
        let key = |fns: &[VirFn]| -> Vec<(String, String, bool, Option<String>)> {
            fns.iter()
                .map(|f| {
                    (
                        f.path.clone(),
                        f.mode.clone(),
                        f.external_body,
                        f.body.as_ref().map(|b| b.file.clone()),
                    )
                })
                .collect()
        };
        let plain = vir_functions(VIR).unwrap();
        assert!(plain.len() >= 3);
        assert_eq!(key(&vir_functions(&wrapped).unwrap()), key(&plain));
        assert!(head_is("(\n  Function :name x)", "Function"));
        assert!(head_is("(Function)", "Function"));
        assert!(!head_is("(FunctionX :name x)", "Function"));
        assert!(!head_is("(Datatype :name x)", "Function"));
    }

    #[test]
    fn vir_records() {
        let fns = vir_functions(VIR).unwrap();
        assert_eq!(fns.len(), 3);
        assert_eq!(fns[0].path, "t::f");
        assert_eq!(fns[0].mode, "Exec");
        assert!(!fns[0].external_body);
        assert!(fns[0].requires);
        assert_eq!(
            fns[0].body,
            Some(VirSpan {
                file: "src/lib.rs".to_string(),
                lo: (5, 1),
                hi: (7, 2)
            })
        );
        assert_eq!(fns[1].path, "t::ext");
        assert!(fns[1].external_body);
        assert!(!fns[1].requires);
        assert_eq!(fns[1].body, None);
        assert_eq!(fns[2].mode, "Spec");
    }

    #[test]
    fn external_body_is_never_listed() {
        let dir = std::env::temp_dir().join(format!("fip-verusgen-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        let src = "// line 1\n\npub fn f(a: u8) -> u8\n    requires true\n{\n    a\n}\n\n#[verifier::external_body]\npub fn ext() -> u8 { 1 }\n\nspec fn s() -> u8 { 1 }\n";
        std::fs::write(dir.join("src/lib.rs"), src).unwrap();
        let info = RunInfo {
            version: "v".to_string(),
            commit: "c".to_string(),
            toolchain: "t".to_string(),
            verified: 2,
            target: "x86_64-unknown-linux-gnu".to_string(),
            features: Vec::new(),
            edition: "2024".to_string(),
            imports: Vec::new(),
            imported_skips: Vec::new(),
            imported_divergent: Vec::new(),
            imported_gated: Vec::new(),
            imported_nonconforming: Vec::new(),
        };
        let fns = vir_functions(VIR).unwrap();
        let s = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap();
        assert_eq!(s.fns.len(), 1, "{s:?}");
        assert_eq!(s.fns[0].path, "t::f");
        assert!(s.fns[0].requires);
        assert_eq!(s.fns[0].file, "src/lib.rs");
        assert!(
            s.skipped
                .iter()
                .any(|(p, why)| p == "t::ext" && why.contains("external_body"))
        );
        assert!(s.flags.is_empty());
        assert_eq!(s.sources.len(), 1);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Re-audit N4 (2026-11-04): a caller verified against the `ensures` of a function
    /// skipped for a cfg in its text is skipped too, transitively, and so is a caller
    /// of a function an imported crate skipped for that reason.
    #[test]
    fn callers_of_cfg_skipped_functions_are_not_listed() {
        let dir = std::env::temp_dir().join(format!("fip-verusgen-taint-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        let src = "pub fn on() -> bool {\n    #[cfg(feature = \"x\")]\n    return true;\n    false\n}\n\npub fn g(a: u32, b: u32) -> u32 {\n    if on() { a / b } else { 0 }\n}\n\npub fn h(a: u32, b: u32) -> u32 {\n    g(a, b)\n}\n\npub fn k() -> u32 { 1 }\n\npub fn d() -> u32 { 2 }\n";
        std::fs::write(dir.join("src/lib.rs"), src).unwrap();
        let sp = |a: (usize, usize), b: (usize, usize)| VirSpan {
            file: "src/lib.rs".to_string(),
            lo: a,
            hi: b,
        };
        let f = |path: &str,
                 sig: (usize, usize),
                 body: ((usize, usize), (usize, usize)),
                 calls: &[&str]| VirFn {
            path: path.to_string(),
            span: sp(sig, sig),
            mode: "Exec".to_string(),
            external_body: false,
            body: Some(sp(body.0, body.1)),
            requires: false,
            expanded: false,
            calls: calls.iter().map(ToString::to_string).collect(),
            allocates: verus::AllocBound::None,
            deallocates: verus::AllocBound::None,
            encapsulates: false,
            mentions: Vec::new(),
        };
        let fns = vec![
            f("t::on", (1, 1), ((1, 21), (5, 2)), &[]),
            f("t::g", (7, 1), ((7, 33), (9, 2)), &["t::on"]),
            f("t::h", (11, 1), ((11, 33), (13, 2)), &["t::g"]),
            f("t::k", (15, 1), ((15, 19), (15, 24)), &[]),
            f("t::d", (17, 1), ((17, 19), (17, 24)), &["dep::impl&%2::x"]),
        ];
        let info = RunInfo {
            version: "v".to_string(),
            commit: "c".to_string(),
            toolchain: "t".to_string(),
            verified: 5,
            target: "x86_64-unknown-linux-gnu".to_string(),
            features: Vec::new(),
            edition: "2024".to_string(),
            imports: Vec::new(),
            imported_skips: Vec::new(),
            imported_divergent: Vec::new(),
            imported_gated: Vec::new(),
            imported_nonconforming: Vec::new(),
        };
        let info = RunInfo {
            imported_skips: vec!["dep::{impl}::x".to_string()],
            ..info
        };
        let s = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap();
        let listed: Vec<&str> = s.fns.iter().map(|e| e.path.as_str()).collect();
        assert_eq!(listed, vec!["t::k"], "{s:?}");
        let why = |p: &str| {
            s.skipped
                .iter()
                .find(|(q, _)| q == p)
                .map(|(_, w)| w.clone())
                .unwrap_or_default()
        };
        assert!(why("t::on").starts_with(SKIP_CFG_ITEM), "{s:?}");
        assert!(why("t::g").contains("`t::on`"), "{s:?}");
        assert!(why("t::h").contains("`t::g`"), "{s:?}");
        assert!(why("t::d").contains("`dep::{impl}::x`"), "{s:?}");
        assert_eq!(
            imported_cfg_skips(&s),
            vec![
                "t::d".to_string(),
                "t::g".to_string(),
                "t::h".to_string(),
                "t::on".to_string()
            ]
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Phase 4: `allocates` clauses as the fork `0.2026.11.05.ca33b04` writes them into
    /// the VIR log (taken from a `--log vir` run): constants, unsigned parameters
    /// (`n as nat` leaves no cast), `+` and constant `*` over `nat`/`int` normalise;
    /// a callback's `call_allocations`, a sequence length, a fixed-width operation or a
    /// non-constant product are opaque (hashed without spans and ids).
    #[test]
    fn allocates_bounds_normalised() {
        assert_eq!(alloc_bound("None"), verus::AllocBound::None);
        let c0 =
            "(@@ \"lib.rs:4:51: 4:52 (#0)\" (> Const (Constant Int 0)) (Typ Int (IntRange Int)))";
        assert_eq!(alloc_bound(c0), verus::AllocBound::Linear(0, Vec::new()));
        let c2 = "(@@ \"lib.rs:7:51: 7:52 (#0)\" (> Const (Constant Int 2))\n   (Typ Int (IntRange Int)))";
        assert_eq!(alloc_bound(c2), verus::AllocBound::Linear(2, Vec::new()));
        let n = "(@@ \"lib.rs:18:15: 18:16 (#0)\" (> ReadPlace (@@ \"lib.rs:18:15: 18:16 (#0)\" (Place Local (VarIdent \"n\" (VarIdentDisambiguate RustcId 2)) ) (Typ Int (IntRange U 32)) ) (UnfinalizedReadKind :preliminary_kind (ReadKind Copy) :id 5) ) (Typ Int (IntRange U 32)) )";
        assert_eq!(
            alloc_bound(n),
            verus::AllocBound::Linear(0, vec![("n".to_string(), 1)])
        );
        let lin = "(@@ \"lib.rs:24:38: 24:56 (#0)\" (> Binary (BinaryOp Arith (ArithOp Add (OverflowBehavior Truncate (IntRange Nat))) ) (@@ \"lib.rs:24:38: 24:52 (#0)\" (> Binary (BinaryOp Arith (ArithOp Mul (OverflowBehavior Truncate (IntRange Nat)))) (@@ \"lib.rs:24:38: 24:39 (#0)\" (> Const (Constant Int 2)) (Typ Int (IntRange Nat)) ) (@@ \"lib.rs:24:43: 24:44 (#0)\" (> ReadPlace (@@ \"lib.rs:24:43: 24:44 (#0)\" (Place Local (VarIdent \"n\" (VarIdentDisambiguate RustcId 2)) ) (Typ Int (IntRange U 32)) ) (UnfinalizedReadKind :preliminary_kind (ReadKind Copy) :id 16) ) (Typ Int (IntRange U 32))) ) (Typ Int (IntRange Nat)) ) (@@ \"lib.rs:24:55: 24:56 (#0)\" (> Const (Constant Int 1)) (Typ Int (IntRange Nat))) ) (Typ Int (IntRange Nat)) )";
        assert_eq!(
            alloc_bound(lin),
            verus::AllocBound::Linear(1, vec![("n".to_string(), 2)])
        );
        assert_eq!(
            verus::AllocBound::Linear(1, vec![("n".to_string(), 2)]).render(),
            "1+2*n"
        );
        // Fixed-width arithmetic could wrap; a signed parameter could be negative.
        let wrap = lin.replace("(IntRange Nat)", "(IntRange U 64)");
        assert!(matches!(alloc_bound(&wrap), verus::AllocBound::Opaque(_)));
        let signed = n.replace("(IntRange U 32)", "(IntRange I 32)");
        assert!(matches!(alloc_bound(&signed), verus::AllocBound::Opaque(_)));
        let closure = "(@@ \"lib.rs:28:86: 28:111 (#0)\" (> Call :target (CallTarget BuiltinSpecFun (BuiltinSpecFun ClosureAlloc) ((Typ TypParam \"F\") (Typ Datatype (Dt Tuple 1) ((Typ Int (IntRange U 8))) ())) () ) :args ((@@ \"lib.rs:28:101: 28:102 (#0)\" (> ReadPlace (@@ \"lib.rs:28:101: 28:102 (#0)\" (Place Local (VarIdent \"f\" (VarIdentDisambiguate RustcId 2)) ) (Typ TypParam \"F\") ) (UnfinalizedReadKind :preliminary_kind (ReadKind Copy) :id 21) ) (Typ TypParam \"F\") )) :post_args None :body None ) (Typ Int (IntRange Int)) )";
        let verus::AllocBound::Opaque(h) = alloc_bound(closure) else {
            panic!("a closure's bound is opaque");
        };
        // Stable under moves of the text (spans) and of VIR ids.
        let moved = closure
            .replace("lib.rs:28:", "lib.rs:90:")
            .replace(":id 21", ":id 7");
        assert_eq!(alloc_bound(&moved), verus::AllocBound::Opaque(h.clone()));
        let other = closure.replace("\"f\"", "\"g\"");
        assert_ne!(alloc_bound(&other), verus::AllocBound::Opaque(h));
        // A product of two parameters, a negative constant, garbage: opaque.
        let nn = lin.replace("(Constant Int 2)", "(Constant Int -2)");
        assert!(matches!(alloc_bound(&nn), verus::AllocBound::Opaque(_)));
        assert!(matches!(
            alloc_bound("(@@ \"x\" (> Const"),
            verus::AllocBound::Opaque(_)
        ));
        // `vir_functions` reads the field.
        let rec = format!(
            "(@ \"src/lib.rs:1:1: 1:20 (#0)\" (Function :name (Fun :path t::f) :mode Exec :attrs (FunctionAttrs :is_external_body false) :require () :unwind_spec None :allocates {c2} :item_kind (ItemKind Function) :body (@@ \"src/lib.rs:1:15: 1:20 (#0)\" (Block))))\n"
        );
        let fns = vir_functions(&rec).unwrap();
        assert_eq!(fns[0].allocates, verus::AllocBound::Linear(2, Vec::new()));
        assert_eq!(fns[0].deallocates, verus::AllocBound::None);
        // `:fip true` is `deallocates 0` (the fork writes no `:deallocations` for it);
        // `:fip_strict` alone is not read, nor `:fip true` beside `encapsulates`.
        let with = |attrs: &str| {
            let r = rec.replace(":is_external_body false", attrs);
            assert_ne!(r, rec);
            vir_functions(&r).unwrap()[0].deallocates.clone()
        };
        assert_eq!(
            with(":is_external_body false :fip true :fip_strict false"),
            verus::AllocBound::Linear(0, Vec::new())
        );
        assert_eq!(
            with(":is_external_body false :fip false :fip_strict true"),
            verus::AllocBound::None
        );
        assert_eq!(
            with(":is_external_body false :fip true :encapsulates_alloc true"),
            verus::AllocBound::None
        );
    }

    /// Phase 4 (cfg twins, decision 2026-11-06-redesign-verus-allocates): a function
    /// naming a method of a trait with a plain-only implementation (the probe: `run`
    /// through a type parameter, `direct` on a concrete type) is skipped, so is its
    /// caller, and the trait is recorded as `divergent`; a trait an imported sidecar
    /// records taints this run's callers too.
    #[test]
    fn callers_of_divergent_trait_methods_are_not_listed() {
        let dir = std::env::temp_dir().join(format!("fip-verusgen-twin-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        let src = "pub trait Step { fn step(&self) -> u32; }\n#[cfg(not(verus_keep_ghost))]\nimpl Step for S { fn step(&self) -> u32 { 0 } }\npub fn run<T: Step>(t: &T, a: u32) -> u32 {\n    a / t.step()\n}\npub fn run_s(a: u32) -> u32 {\n    run(&S, a)\n}\npub fn direct(a: u32) -> u32 {\n    a / S.step()\n}\npub fn other(a: u32) -> u32 {\n    dep::Tick::tick(a)\n}\npub fn k() -> u32 { 1 }\n";
        std::fs::write(dir.join("src/lib.rs"), src).unwrap();
        let sp = |a: (usize, usize), b: (usize, usize)| VirSpan {
            file: "src/lib.rs".to_string(),
            lo: a,
            hi: b,
        };
        let f = |path: &str, line: usize, end: (usize, usize), calls: &[&str]| VirFn {
            path: path.to_string(),
            span: sp((line, 1), (line, 1)),
            mode: "Exec".to_string(),
            external_body: false,
            body: Some(sp((line, 1), end)),
            requires: false,
            expanded: false,
            calls: calls.iter().map(ToString::to_string).collect(),
            allocates: verus::AllocBound::None,
            deallocates: verus::AllocBound::None,
            encapsulates: false,
            mentions: Vec::new(),
        };
        let fns = vec![
            f("t::run", 4, (6, 2), &["t::Step::step"]),
            f("t::run_s", 7, (9, 2), &["t::run"]),
            f("t::direct", 10, (12, 2), &["t::Step::step"]),
            f("t::other", 13, (15, 2), &["dep::Tick::tick"]),
            f("t::k", 16, (16, 24), &[]),
        ];
        let info = RunInfo {
            version: "v".to_string(),
            commit: "c".to_string(),
            toolchain: "t".to_string(),
            verified: 5,
            target: "x86_64-unknown-linux-gnu".to_string(),
            features: Vec::new(),
            edition: "2024".to_string(),
            imports: Vec::new(),
            imported_skips: Vec::new(),
            imported_divergent: vec!["Tick".to_string()],
            imported_gated: Vec::new(),
            imported_nonconforming: Vec::new(),
        };
        // The impl of plain builds only is more than the gate may hold: no function of
        // the crate is listed (amendment 2026-11-25 (2)); the trait is recorded, and
        // importers take every function as differing between the builds.
        let s = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap();
        assert!(s.fns.is_empty(), "{s:?}");
        assert!(
            s.skipped
                .iter()
                .all(|(_, why)| why.starts_with(SKIP_GATE) && why.contains("src/lib.rs:2: ")),
            "{s:?}"
        );
        assert_eq!(
            s.divergent,
            vec![("Step".to_string(), "src/lib.rs".to_string(), 3)]
        );
        assert!(imported_cfg_skips(&s).contains(&"t::run".to_string()));
        // The same crate with the impl in both builds, and the trait divergent in a
        // crate it imports: the callers of the trait's methods are tainted.
        std::fs::write(
            dir.join("src/lib.rs"),
            src.replace("#[cfg(not(verus_keep_ghost))]\n", "// (in both builds)\n"),
        )
        .unwrap();
        let info = RunInfo {
            imported_divergent: vec!["Tick".to_string(), "Step".to_string()],
            ..info
        };
        let s = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap();
        let listed: Vec<&str> = s.fns.iter().map(|e| e.path.as_str()).collect();
        assert_eq!(listed, vec!["t::k"], "{s:?}");
        let why = |p: &str| {
            s.skipped
                .iter()
                .find(|(q, _)| q == p)
                .map(|(_, w)| w.clone())
                .unwrap_or_default()
        };
        assert!(
            why("t::run").contains("`t::Step::step`, a method of trait `Step`"),
            "{s:?}"
        );
        assert!(why("t::direct").contains("trait `Step`"), "{s:?}");
        assert!(why("t::run_s").contains("`t::run`"), "{s:?}");
        assert!(why("t::other").contains("trait `Tick`"), "{s:?}");
        assert!(s.divergent.is_empty(), "{s:?}");
        // Importers taint their callers of these.
        assert!(imported_cfg_skips(&s).contains(&"t::run".to_string()));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Re-audit N4 (2026-11-04): a source of the run outside `src/` (a `#[path]`
    /// module) is scanned like the crate's own: before, `shared.rs` testing
    /// `cfg!(fip_prelint)` escaped the scan of `src/`.
    #[test]
    fn every_source_of_the_run_is_scanned() {
        let dir = std::env::temp_dir().join(format!("fip-verusgen-path-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(
            dir.join("src/lib.rs"),
            "#[path = \"../shared.rs\"]\npub mod shared;\n",
        )
        .unwrap();
        std::fs::write(
            dir.join("shared.rs"),
            "pub fn on() -> bool {\n    cfg!(fip_prelint)\n}\n",
        )
        .unwrap();
        assert_eq!(crate_cfg_check(&dir), Ok(()));
        let span = VirSpan {
            file: "shared.rs".to_string(),
            lo: (1, 1),
            hi: (1, 21),
        };
        let fns = vec![VirFn {
            path: "t::shared::on".to_string(),
            span: span.clone(),
            mode: "Exec".to_string(),
            external_body: false,
            body: Some(VirSpan {
                lo: (1, 21),
                hi: (3, 2),
                ..span
            }),
            requires: false,
            expanded: false,
            calls: Vec::new(),
            allocates: verus::AllocBound::None,
            deallocates: verus::AllocBound::None,
            encapsulates: false,
            mentions: Vec::new(),
        }];
        let info = RunInfo {
            version: "v".to_string(),
            commit: "c".to_string(),
            toolchain: "t".to_string(),
            verified: 1,
            target: "x86_64-unknown-linux-gnu".to_string(),
            features: Vec::new(),
            edition: "2024".to_string(),
            imports: Vec::new(),
            imported_skips: Vec::new(),
            imported_divergent: Vec::new(),
            imported_gated: Vec::new(),
            imported_nonconforming: Vec::new(),
        };
        let e = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap_err();
        assert!(
            e.starts_with("shared.rs: `cfg!(fip_prelint)` tests `fip_prelint`"),
            "{e}"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Impl methods (top plan item 8): listed as `{impl}` with their line; a method
    /// inside `#[cfg(verus_keep_ghost)]` (no plain twin at that place) and one whose
    /// span comes from a macro expansion are skipped.
    #[test]
    fn impl_methods() {
        let vir = r#"(@ "src/lib.rs:3:5: 3:26 (#0)" (Function
  :name (Fun :path t::impl&%3::m) :proxy None :mode Exec :require () :attrs (FunctionAttrs :is_external_body false
  ) :body (@@ "src/lib.rs:3:27: 5:6 (#0)" (> Block ())) :extra_dependencies ()))

(@ "src/lib.rs:10:5: 10:26 (#0)" (Function
  :name (Fun :path t::impl&%1::g) :proxy None :mode Exec :require () :attrs (FunctionAttrs :is_external_body false
  ) :body (@@ "src/lib.rs:10:27: 12:6 (#0)" (> Block ())) :extra_dependencies ()))

(@ "src/lib.rs:15:40: 15:60 (#4)" (Function
  :name (Fun :path t::impl&%7::e) :proxy None :mode Exec :require () :attrs (FunctionAttrs :is_external_body false
  ) :body (@@ "src/lib.rs:15:60: 15:65 (#4)" (> Block ())) :extra_dependencies ()))
"#;
        let dir = std::env::temp_dir().join(format!("fip-verusgen-impl-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        let src = "pub struct S;\nimpl S {\n    pub fn m(&self) -> u8 {\n        1\n    }\n}\n#[cfg(verus_keep_ghost)]\nverus! {\nimpl S {\n    pub fn g(&self) -> u8 {\n        2\n    }\n}\n}\nmacro_rules! mk { () => { impl S { pub fn e(&self) -> u8 { 3 } } } }\n";
        std::fs::write(dir.join("src/lib.rs"), src).unwrap();
        let info = RunInfo {
            version: "v".to_string(),
            commit: "c".to_string(),
            toolchain: "t".to_string(),
            verified: 3,
            target: "x86_64-unknown-linux-gnu".to_string(),
            features: Vec::new(),
            edition: "2024".to_string(),
            imports: Vec::new(),
            imported_skips: Vec::new(),
            imported_divergent: Vec::new(),
            imported_gated: Vec::new(),
            imported_nonconforming: Vec::new(),
        };
        let fns = vir_functions(vir).unwrap();
        assert!(!fns[0].expanded && fns[2].expanded);
        // An exec method of Verus's build only: no function of the crate is listed
        // (amendment 2026-11-25).
        let s = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap();
        assert!(s.fns.is_empty(), "{s:?}");
        assert!(
            s.skipped.len() == 3
                && s.skipped.iter().all(|(_, why)| why.starts_with(SKIP_GATE)
                    && why.contains("the exec function `g` under `#[cfg(verus_keep_ghost)]`")),
            "{s:?}"
        );
        assert_eq!(imported_cfg_skips(&s).len(), 3);
        // Without the gate (same lines): both methods are listed, by one path.
        std::fs::write(
            dir.join("src/lib.rs"),
            src.replace(
                "#[cfg(verus_keep_ghost)]\nverus! {",
                "// (no gate)\nverus! {",
            ),
        )
        .unwrap();
        let s = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap();
        assert_eq!(s.fns.len(), 2, "{s:?}");
        assert!(
            s.fns
                .iter()
                .all(|e| e.path == "t::{impl}::g" || e.path == "t::{impl}::m")
        );
        let m = s.fns.iter().find(|e| e.path == "t::{impl}::m").unwrap();
        assert_eq!((m.file.as_str(), m.line), ("src/lib.rs", 3));
        assert!(
            s.skipped
                .iter()
                .any(|(p, why)| p == "t::impl&%7::e" && why.contains("macro expansion"))
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn json_and_run_info() {
        let ok = r#"{"verification-results": {"encountered-error": false, "encountered-vir-error": false, "success": true, "verified": 7, "errors": 0, "is-verifying-entire-crate": true}, "verus": {"version": "0.1", "commit": "abc", "toolchain": "1.99.1"}}"#;
        let j = parse_json(ok).unwrap();
        let i = run_info(&j).unwrap();
        assert_eq!((i.version.as_str(), i.verified), ("0.1", 7));
        let partial = ok.replace(
            "\"is-verifying-entire-crate\": true",
            "\"is-verifying-entire-crate\": false",
        );
        assert!(run_info(&parse_json(&partial).unwrap()).is_err());
        let failed = ok.replace("\"errors\": 0", "\"errors\": 1");
        assert!(run_info(&parse_json(&failed).unwrap()).is_err());
    }

    #[test]
    fn spans_and_versions() {
        assert_eq!(
            parse_span("crates/a/src/x.rs:280:1: 283:11 (#0)"),
            Some(VirSpan {
                file: "crates/a/src/x.rs".to_string(),
                lo: (280, 1),
                hi: (283, 11)
            })
        );
        assert_eq!(
            z3_version("Z3 version 4.16.0 - 64 bit\n").as_deref(),
            Some("4.16.0")
        );
        assert_eq!(
            relative(Path::new("/a/b/c.rs"), Path::new("/a/d")),
            "../b/c.rs"
        );
    }

    #[test]
    fn vir_paths_drop_namespace_marks() {
        assert_eq!(
            vir_path("fip_core::t%slice::compact"),
            "fip_core::slice::compact"
        );
        assert_eq!(
            vir_path("fip_strict::t%FipFn::call"),
            "fip_strict::FipFn::call"
        );
        assert_eq!(vir_path("c::t%m::impl&%3::f"), "c::m::impl&%3::f");
        assert_eq!(vir_path("c::f"), "c::f");
        assert_eq!(vir_path("c::t%"), "c::t%");
        assert_eq!(vir_path("c::impl&%0::add"), "c::impl&%0::add");
    }

    #[test]
    fn trust_flags_keep_no_cheating_and_alloc_check() {
        let v = |a: &[&str]| a.iter().map(|s| (*s).to_string()).collect::<Vec<_>>();
        assert_eq!(
            trust_flags(&v(&["--crate-type=lib", "--no-cheating", "x.rs"])),
            v(&["--no-cheating"])
        );
        for spelling in [
            &["-V", "alloc-check"][..],
            &["-Valloc-check"],
            &["-V=alloc-check"],
        ] {
            let mut f = v(&["--no-cheating", "--no-cheating"]);
            f.extend(v(spelling));
            assert_eq!(trust_flags(&f), v(&["--no-cheating", "-V", "alloc-check"]));
        }
        assert_eq!(
            trust_flags(&v(&["--no-cheating", "-V", "alloc-check-strict"])),
            v(&["--no-cheating"])
        );
        assert!(trust_flags(&v(&["-V", "alloc-check"])).starts_with(&v(&["-V"])));
        // A standard-library crate run is recorded (the driver refuses its sidecar).
        assert_eq!(
            trust_flags(&v(&["--is-vstd", "--no-cheating", "-V", "alloc-check"])),
            v(&["--no-cheating", "--is-vstd", "-V", "alloc-check"])
        );
        for f in verus::STD_CRATE_FLAGS {
            assert!(REFUSED_FLAGS.contains(f), "{f}");
        }
    }

    #[test]
    fn run_cfg_and_imports() {
        let v = |a: &[&str]| a.iter().map(|s| (*s).to_string()).collect::<Vec<_>>();
        assert_eq!(
            run_cfg(
                &v(&["--crate-type=lib", "--no-cheating", "--edition", "2024"]),
                "h"
            ),
            Ok(("h".to_string(), Vec::new(), "2024".to_string()))
        );
        // The edition is required, must be one of rustc's, and is not given twice.
        assert!(run_cfg(&v(&["--crate-type=lib", "--no-cheating"]), "h").is_err());
        assert!(run_cfg(&v(&["--edition=2023"]), "h").is_err());
        assert!(run_cfg(&v(&["--edition", "2021", "--edition=2024"]), "h").is_err());
        assert_eq!(
            run_cfg(&v(&["--edition=2021"]), "h"),
            Ok(("h".to_string(), Vec::new(), "2021".to_string()))
        );
        assert_eq!(
            run_cfg(
                &v(&[
                    "--target",
                    "t",
                    "--cfg",
                    "feature=\"b\"",
                    "--cfg=feature=\"a\"",
                    "--edition",
                    "2024"
                ]),
                "h"
            ),
            Ok((
                "t".to_string(),
                vec!["a".to_string(), "b".to_string()],
                "2024".to_string()
            ))
        );
        assert!(run_cfg(&v(&["--edition=2024", "--cfg", "fip_prelint"]), "h").is_err());
        assert!(run_cfg(&v(&["--edition=2024", "--cfg=test"]), "h").is_err());
        assert_eq!(
            imports(&v(&[
                "--import",
                "a=x/a.vir",
                "--import=b=b.vir",
                "--extern",
                "c=c.rlib"
            ])),
            vec![
                ("a".to_string(), PathBuf::from("x/a.vir")),
                ("b".to_string(), PathBuf::from("b.vir"))
            ]
        );
        assert_eq!(
            export(&v(&["--export", "o.vir"])),
            Some(PathBuf::from("o.vir"))
        );
        assert_eq!(export(&v(&["--compile"])), None);
    }

    /// The audit's import probe (2026-11-04): a VIR file exported by a run without
    /// `--no-cheating` (no generator record), a record for another crate or another
    /// file, a committed sidecar with a changed source or without `--no-cheating`: each
    /// refused; the record and sidecar of a generator run: accepted.
    #[test]
    fn imports_need_a_no_cheating_generator_run() {
        let dir = std::env::temp_dir().join(format!("fip-verusgen-imp-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(dir.join("src/lib.rs"), "pub fn hint() -> usize { 1 }\n").unwrap();
        let trusted = verus::Trusted {
            verus_version: "v".to_string(),
            verus_commit: "c".to_string(),
            z3: "4.16.0".to_string(),
        };
        let sc = Sidecar {
            format: verus::FORMAT,
            krate: "dep".to_string(),
            verus_version: "v".to_string(),
            verus_commit: "c".to_string(),
            z3: "4.16.0".to_string(),
            toolchain: "t".to_string(),
            flags: vec![
                NO_CHEATING.to_string(),
                "-V".to_string(),
                ALLOC_CHECK.to_string(),
            ],
            target: "x".to_string(),
            features: Vec::new(),
            edition: "2024".to_string(),
            verified: 1,
            sources: vec![(
                "src/lib.rs".to_string(),
                verus::sha256_hex(b"pub fn hint() -> usize { 1 }\n"),
            )],
            imports: Vec::new(),
            fns: Vec::new(),
            skipped: Vec::new(),
            divergent: Vec::new(),
        };
        let side = dir.join("verus-verified.txt");
        std::fs::write(&side, sc.render()).unwrap();
        let vir = dir.join("dep.vir");
        std::fs::write(&vir, b"(vir)").unwrap();
        // Exported by a plain Verus run: no record.
        let e = check_import("dep", &vir, &side, &trusted).unwrap_err();
        assert!(e.contains("not exported by a generator run"), "{e}");
        // A record of another crate, or of other contents.
        std::fs::write(
            format!("{}.fip-run", vir.display()),
            export_record("other", b"(vir)"),
        )
        .unwrap();
        assert!(check_import("dep", &vir, &side, &trusted).is_err());
        std::fs::write(
            format!("{}.fip-run", vir.display()),
            export_record("dep", b"(old)"),
        )
        .unwrap();
        assert!(check_import("dep", &vir, &side, &trusted).is_err());
        std::fs::write(
            format!("{}.fip-run", vir.display()),
            export_record("dep", b"(vir)"),
        )
        .unwrap();
        assert_eq!(check_import("dep", &vir, &side, &trusted), Ok(()));
        // The committed sidecar: another crate, without --no-cheating, a changed source.
        assert!(check_import("dap", &vir, &side, &trusted).is_err());
        let cheat = Sidecar {
            flags: Vec::new(),
            ..sc.clone()
        };
        std::fs::write(&side, cheat.render()).unwrap();
        assert!(check_import("dep", &vir, &side, &trusted).is_err());
        std::fs::write(&side, sc.render()).unwrap();
        std::fs::write(
            dir.join("src/lib.rs"),
            "pub fn hint() -> usize { proof! { assume(false); } 99 }\n",
        )
        .unwrap();
        let e = check_import("dep", &vir, &side, &trusted).unwrap_err();
        assert!(e.contains("changed"), "{e}");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
