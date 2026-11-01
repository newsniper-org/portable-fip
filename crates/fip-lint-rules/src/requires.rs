// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The grammar of `fip::requires(..)` (declared preconditions, limits plan L1), shared
//! by `fip-macros` (which emits and checks the mark) and `fip-prelint` (which assumes
//! it in the function and checks it at every call site).
//!
//! A precondition is a comma-separated list of chained comparisons, each a
//! conjunction: `i < j < xs.len()` is `i < j` and `j < xs.len()`. A side is a term
//! plus or minus integer literals; a term is an integer parameter `i`, the length
//! `xs.len()` of a slice parameter `xs`, or an integer literal (suffixes such as
//! `usize` are accepted). Relations: `<`, `<=`, `>`, `>=`, `==`. Anything else is a
//! parse error: a precondition is never silently weakened by the parser.
//!
//! [`from_verus`] translates the fitting subset of a Verus `requires` clause
//! (`old(xs)@.len()` and `xs@.len()` become `xs.len()`, chains are split); clauses that
//! do not fit are left out, which assumes less.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

/// A term of a precondition.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    /// An integer parameter.
    Param(String),
    /// The length of a slice parameter, `xs.len()`.
    Len(String),
    /// The constant 0 (a literal is `Zero` plus an offset).
    Zero,
}

/// `term + offset`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Side {
    /// The term.
    pub term: Term,
    /// The constant added to it.
    pub offset: i128,
}

/// `<` or `<=` (`>` and `>=` are written with the sides swapped), or `==`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Rel {
    /// `a < b`.
    Lt,
    /// `a <= b`.
    Le,
    /// `a == b`.
    Eq,
}

/// One comparison `a rel b`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Conjunct {
    /// Left side.
    pub a: Side,
    /// Relation.
    pub rel: Rel,
    /// Right side.
    pub b: Side,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Int(i128),
    Punct(&'static str),
}

/// Splits `s` into identifiers, integer literals and punctuation; whitespace is
/// ignored. Unknown characters are errors, or with `lenient` (Verus text, which has
/// `#[trigger]`, `==>` and more) the punctuation `?`, which no comparison contains.
fn tokens(s: &str, lenient: bool) -> Result<Vec<Tok>, String> {
    const PUNCT: &[&str] = &[
        "<=", ">=", "==", "!=", "&&", "<", ">", "+", "-", ".", "(", ")", ",", "@", "!", "&", "|",
        "*", "/", "%", "[", "]", "{", "}", ":", ";", "=",
    ];
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let ch = bytes[i];
        if ch.is_ascii_whitespace() {
            i += 1;
        } else if ch.is_ascii_alphabetic() || ch == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            out.push(Tok::Ident(s[start..i].to_string()));
        } else if ch.is_ascii_digit() {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
                i += 1;
            }
            let digits: String = s[start..i].chars().filter(|c| *c != '_').collect();
            let value: i128 = digits
                .parse()
                .map_err(|_| format!("integer literal `{}` out of range", &s[start..i]))?;
            // An integer suffix (`usize`, `u8`, ..) belongs to the literal.
            if i < bytes.len() && (bytes[i] == b'u' || bytes[i] == b'i') {
                let s0 = i;
                while i < bytes.len() && bytes[i].is_ascii_alphanumeric() {
                    i += 1;
                }
                let suffix = &s[s0..i];
                if !matches!(
                    suffix,
                    "u8" | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "usize"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "isize"
                ) {
                    return Err(format!("unknown integer suffix `{suffix}`"));
                }
            }
            out.push(Tok::Int(value));
        } else {
            let found = PUNCT.iter().find(|p| s[i..].starts_with(**p));
            if found.is_none() && lenient {
                out.push(Tok::Punct("?"));
                i += s[i..].chars().next().map_or(1, char::len_utf8);
                continue;
            }
            let punct = found.ok_or_else(|| {
                format!(
                    "unexpected character `{}`",
                    s[i..].chars().next().unwrap_or(' ')
                )
            })?;
            out.push(Tok::Punct(punct));
            i += punct.len();
        }
    }
    Ok(out)
}

/// `term (± literal)*`.
fn side(t: &[Tok], i: &mut usize) -> Result<Side, String> {
    let term = match t.get(*i) {
        Some(Tok::Int(v)) => {
            *i += 1;
            Side {
                term: Term::Zero,
                offset: *v,
            }
        }
        Some(Tok::Ident(name)) => {
            *i += 1;
            let is_len = matches!(
                t.get(*i..*i + 4),
                Some([Tok::Punct("."), Tok::Ident(l), Tok::Punct("("), Tok::Punct(")")]) if l == "len"
            );
            if is_len {
                *i += 4;
                Side {
                    term: Term::Len(name.clone()),
                    offset: 0,
                }
            } else {
                Side {
                    term: Term::Param(name.clone()),
                    offset: 0,
                }
            }
        }
        other => {
            return Err(format!(
                "expected a parameter, `p.len()` or an integer literal, found {}",
                describe(other)
            ));
        }
    };
    let mut s = term;
    loop {
        let sign = match t.get(*i) {
            Some(Tok::Punct("+")) => 1,
            Some(Tok::Punct("-")) => -1,
            _ => return Ok(s),
        };
        *i += 1;
        let Some(Tok::Int(v)) = t.get(*i) else {
            return Err(format!(
                "only integer literals may be added or subtracted, found {}",
                describe(t.get(*i))
            ));
        };
        *i += 1;
        s.offset = s
            .offset
            .checked_add(sign * v)
            .ok_or_else(|| "offset out of range".to_string())?;
    }
}

fn describe(t: Option<&Tok>) -> String {
    match t {
        None => "the end".to_string(),
        Some(Tok::Ident(s)) => format!("`{s}`"),
        Some(Tok::Int(v)) => format!("`{v}`"),
        Some(Tok::Punct(p)) => format!("`{p}`"),
    }
}

fn rel(t: Option<&Tok>) -> Option<(Rel, bool)> {
    match t {
        Some(Tok::Punct("<")) => Some((Rel::Lt, false)),
        Some(Tok::Punct("<=")) => Some((Rel::Le, false)),
        Some(Tok::Punct(">")) => Some((Rel::Lt, true)),
        Some(Tok::Punct(">=")) => Some((Rel::Le, true)),
        Some(Tok::Punct("==")) => Some((Rel::Eq, false)),
        _ => None,
    }
}

/// One chained comparison (tokens of one comma-separated part).
fn chain(t: &[Tok]) -> Result<Vec<Conjunct>, String> {
    let mut i = 0;
    let mut out = Vec::new();
    let mut a = side(t, &mut i)?;
    while let Some((r, swap)) = rel(t.get(i)) {
        i += 1;
        let b = side(t, &mut i)?;
        out.push(if swap {
            Conjunct {
                a: b.clone(),
                rel: r,
                b: a,
            }
        } else {
            Conjunct {
                a,
                rel: r,
                b: b.clone(),
            }
        });
        a = b;
    }
    if i < t.len() {
        return Err(format!("unexpected {} in a comparison", describe(t.get(i))));
    }
    if out.is_empty() {
        return Err("expected a comparison (`<`, `<=`, `>`, `>=`, `==`)".to_string());
    }
    Ok(out)
}

/// Splits tokens at top-level commas.
fn split_commas(t: &[Tok]) -> Vec<&[Tok]> {
    let mut parts = Vec::new();
    let mut depth = 0_i32;
    let mut start = 0;
    for (k, tok) in t.iter().enumerate() {
        match tok {
            Tok::Punct("(" | "[" | "{") => depth += 1,
            Tok::Punct(")" | "]" | "}") => depth -= 1,
            Tok::Punct(",") if depth == 0 => {
                parts.push(&t[start..k]);
                start = k + 1;
            }
            _ => {}
        }
    }
    if start < t.len() {
        parts.push(&t[start..]);
    }
    parts
}

/// Parses the argument list of `fip::requires(..)` (without the parentheses).
///
/// # Errors
///
/// Anything outside the grammar (see the module documentation), and an empty list.
pub fn parse(text: &str) -> Result<Vec<Conjunct>, String> {
    let t = tokens(text, false)?;
    let mut out = Vec::new();
    for part in split_commas(&t) {
        if part.is_empty() {
            return Err("empty comparison between commas".to_string());
        }
        out.extend(chain(part)?);
    }
    if out.is_empty() {
        return Err("`fip::requires(..)` needs at least one comparison".to_string());
    }
    Ok(out)
}

fn show_side(s: &Side) -> String {
    let base = match &s.term {
        Term::Param(p) => p.clone(),
        Term::Len(p) => format!("{p}.len()"),
        Term::Zero => return format!("{}", s.offset),
    };
    match s.offset {
        0 => base,
        o if o > 0 => format!("{base} + {o}"),
        o => format!("{base} - {}", o.unsigned_abs()),
    }
}

/// `a rel b` as written in `fip::requires(..)`.
#[must_use]
pub fn display(c: &Conjunct) -> String {
    let r = match c.rel {
        Rel::Lt => "<",
        Rel::Le => "<=",
        Rel::Eq => "==",
    };
    format!("{} {r} {}", show_side(&c.a), show_side(&c.b))
}

/// The conjuncts as one `fip::requires(..)` argument list.
#[must_use]
pub fn display_all(cs: &[Conjunct]) -> String {
    cs.iter().map(display).collect::<Vec<_>>().join(", ")
}

/// Verus clause keywords that end a `requires` clause.
const VERUS_CLAUSES: &[&str] = &[
    "ensures",
    "returns",
    "decreases",
    "recommends",
    "invariant",
    "invariant_except_break",
    "invariant_ensures",
    "opens_invariants",
    "no_unwind",
    "with",
];

/// The conjuncts of the `requires` clause in the text of a Verus `verus_spec(..)` or
/// `requires ..` that fit the grammar: `old(p)@.len()`, `p@.len()` and `old(p).len()`
/// become `p.len()`, `old(i)` becomes `i`, chains are split. Clauses that do not fit
/// (quantifiers, sequences, calls, `!=`, ..) are left out.
#[must_use]
pub fn from_verus(spec: &str) -> Vec<Conjunct> {
    let Ok(t) = tokens(spec, true) else {
        return Vec::new();
    };
    let Some(start) = t
        .iter()
        .position(|x| matches!(x, Tok::Ident(s) if s == "requires"))
    else {
        return Vec::new();
    };
    let mut depth = 0_i32;
    let mut end = t.len();
    for (k, x) in t.iter().enumerate().skip(start + 1) {
        match x {
            Tok::Punct("(" | "[" | "{") => depth += 1,
            Tok::Punct(")" | "]" | "}") => depth -= 1,
            Tok::Ident(s) if depth == 0 && VERUS_CLAUSES.contains(&s.as_str()) => {
                end = k;
                break;
            }
            _ => {}
        }
    }
    let clause = rewrite_verus(&t[start + 1..end]);
    let mut out = Vec::new();
    for part in split_commas(&clause) {
        if let Ok(cs) = chain(part) {
            out.extend(cs);
        }
    }
    out
}

/// `old(p)` → `p`, `p@.len()` → `p.len()`.
fn rewrite_verus(t: &[Tok]) -> Vec<Tok> {
    let mut out: Vec<Tok> = Vec::new();
    let mut i = 0;
    while i < t.len() {
        if let (
            Some(Tok::Ident(o)),
            Some(Tok::Punct("(")),
            Some(Tok::Ident(p)),
            Some(Tok::Punct(")")),
        ) = (t.get(i), t.get(i + 1), t.get(i + 2), t.get(i + 3))
            && o == "old"
        {
            out.push(Tok::Ident(p.clone()));
            i += 4;
            continue;
        }
        if matches!(t.get(i), Some(Tok::Punct("@"))) {
            i += 1;
            continue;
        }
        out.push(t[i].clone());
        i += 1;
    }
    out
}

/// The conjuncts of `fip` that are not among those of `verus` (a drift between the
/// hand-written precondition and the verified one).
#[must_use]
pub fn not_in<'a>(fip: &'a [Conjunct], verus: &[Conjunct]) -> Vec<&'a Conjunct> {
    fip.iter().filter(|c| !verus.contains(c)).collect()
}
