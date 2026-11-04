// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! One normaliser for the spellings of a callee path, shared by `#[fip]` (strict and
//! non-strict) and `fip_testkit::srcmodel`.
//!
//! A heap constructor can be written `Box::new`, `Box::<u8>::new`, `<Box<u8>>::new`,
//! `alloc::boxed::Box::new`, `::std::boxed::Box::new`, `<Box<u8> as Default>::default`
//! and more; an allocating method can be called by path (`Vec::clone(&v)`,
//! `<[u8]>::to_vec(x)`, `Clone::clone(&v)`). [`classify`] reduces each spelling to the
//! type's last path segment (generic arguments dropped), the trait of a qualified path
//! and the function, and decides with the tables of the crate root:
//!
//! | callee | result |
//! |---|---|
//! | a [`crate::HEAP_TYPES`] type with a [`crate::NON_ALLOCATING_CONSTRUCTORS`] function | [`Callee::NonAllocating`] |
//! | a [`crate::HEAP_TYPES`] type with a [`crate::HEAP_CONSTRUCTORS`] or [`crate::ALLOC_METHODS`] function | [`Callee::Alloc`] |
//! | a [`CTOR_TRAITS`] trait (`Clone::clone`, `<_ as ToOwned>::to_owned`, ..) or a slice/`str` type with an [`crate::ALLOC_METHODS`] function | [`Callee::Alloc`] (as `.f()` is) |
//! | any other [`CTOR_TRAITS`] function without a type (`Default::default`, `From::from`, `<_ as Default>::default`) | [`Callee::Inferred`]: the type is inferred, tokens cannot tell |
//! | everything else | [`Callee::Other`] |
//!
//! Not resolvable by tokens, as before: type aliases (`type V = Vec<u8>; V::new()`)
//! and `use` renames (`use std::boxed::Box as B;`), generic parameters (`T::default()`
//! for `T = Vec<u8>`). `fip-prelint` (MIR) sees the resolved callee in all of these.

use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::{ALLOC_METHODS, HEAP_CONSTRUCTORS, HEAP_TYPES, is_non_allocating_constructor};

/// One token of a callee path as both checkers see it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tok<'a> {
    /// An identifier (also `_`).
    Ident(&'a str),
    /// One punctuation character (`::` is two `:`).
    Punct(char),
    /// A delimited group or a literal (e.g. `[u8]`, `(..)`).
    Other,
    /// A bracketed group `[..]`: a slice type in a qualified path `<[T]>::f`.
    Slice,
}

/// What a callee path is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    /// May allocate: shown as `ty::f`.
    Alloc {
        /// The type's last segment, or the trait for a trait path.
        ty: String,
        /// The function.
        f: String,
        /// `true` for an allocating method called by path ([`crate::ALLOC_METHODS`]:
        /// it may call user code, e.g. the element's `Clone`), `false` for a
        /// [`crate::HEAP_CONSTRUCTORS`] constructor.
        method: bool,
    },
    /// An audited non-allocating constructor.
    NonAllocating {
        /// The type's last segment.
        ty: String,
        /// The function.
        f: String,
    },
    /// A constructor-like trait function whose type is inferred (`Default::default()`).
    Inferred {
        /// The trait.
        tr: String,
        /// The function.
        f: String,
    },
    /// Anything else.
    Other,
}

/// Standard traits whose functions build a value of an inferred type.
pub const CTOR_TRAITS: &[&str] = &[
    "Default",
    "From",
    "Into",
    "TryFrom",
    "TryInto",
    "FromIterator",
    "Clone",
    "ToOwned",
    "ToString",
    "Extend",
];

/// The last identifier of a type, skipping generic arguments, references and `dyn`:
/// `std::vec::Vec<u8>` → `Vec`, `&str` → `str`, `[u8]` → `[]`, `_` → `_`.
fn type_last(toks: &[Tok]) -> Option<String> {
    let mut depth = 0i32;
    let mut last = None;
    let mut prev = None;
    for t in toks {
        match *t {
            Tok::Punct('<') => depth += 1,
            Tok::Punct('>') if prev != Some(Tok::Punct('-')) => depth -= 1,
            Tok::Ident(s) if depth == 0 && s != "dyn" && s != "mut" => last = Some(s.to_string()),
            Tok::Punct('_') if depth == 0 => last = Some("_".to_string()),
            Tok::Slice if depth == 0 => last = Some("[]".to_string()),
            _ => {}
        }
        prev = Some(*t);
    }
    last
}

/// Index of the `>` matching the `<` at `open` (`->` is not a bracket).
fn angle_close(toks: &[Tok], open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (k, t) in toks.iter().enumerate().skip(open) {
        match t {
            Tok::Punct('<') => depth += 1,
            Tok::Punct('>') if !(k > 0 && toks[k - 1] == Tok::Punct('-')) => {
                depth -= 1;
                if depth == 0 {
                    return Some(k);
                }
            }
            _ => {}
        }
    }
    None
}

/// Index of the `<` matching the `>` at `close`, searching backwards.
fn angle_open(toks: &[Tok], close: usize) -> Option<usize> {
    let mut depth = 0i32;
    let mut k = close + 1;
    while k > 0 {
        k -= 1;
        match toks[k] {
            Tok::Punct('>') if !(k > 0 && toks[k - 1] == Tok::Punct('-')) => depth += 1,
            Tok::Punct('<') => {
                depth -= 1;
                if depth == 0 {
                    return Some(k);
                }
            }
            _ => {}
        }
    }
    None
}

fn is_sep(toks: &[Tok], k: usize) -> bool {
    toks.get(k) == Some(&Tok::Punct(':')) && toks.get(k + 1) == Some(&Tok::Punct(':'))
}

/// Start of the callee path whose last segment is the identifier `toks[end]`:
/// back over `::`, identifiers, turbofish arguments `::<..>`, a qualified self
/// `<T as Tr>` / `<T>`, and a leading `::`.
#[must_use]
pub fn path_start(toks: &[Tok], end: usize) -> usize {
    let mut k = end;
    loop {
        if k < 2 || !is_sep(toks, k - 2) {
            return k;
        }
        let colon = k - 2;
        if colon == 0 {
            return 0;
        }
        match toks[colon - 1] {
            Tok::Ident(_) => k = colon - 1,
            Tok::Punct('>') => {
                let Some(lt) = angle_open(toks, colon - 1) else {
                    return colon;
                };
                // `Seg::<G>::` (turbofish) continues the path; otherwise `<..>` is
                // the qualified self, the start.
                if lt >= 3 && is_sep(toks, lt - 2) && matches!(toks[lt - 3], Tok::Ident(_)) {
                    k = lt - 3;
                } else {
                    return lt;
                }
            }
            _ => return colon,
        }
    }
}

/// A parsed callee path: the qualified self's type and trait, if any, and the
/// segments after it (turbofish arguments dropped).
type Parsed<'a> = (Option<(Option<String>, Option<String>)>, Vec<&'a str>);

/// Parses a callee path; `None` if `toks` is not exactly one.
fn parse<'a>(toks: &[Tok<'a>]) -> Option<Parsed<'a>> {
    let mut i = 0;
    if is_sep(toks, 0) {
        i = 2;
    }
    // Qualified self `<T as Tr>` / `<T>`.
    let mut qself: Option<(Option<String>, Option<String>)> = None;
    if toks.get(i) == Some(&Tok::Punct('<')) {
        let close = angle_close(toks, i)?;
        let inner = &toks[i + 1..close];
        let mut depth = 0i32;
        let mut as_at = None;
        for (k, t) in inner.iter().enumerate() {
            match t {
                Tok::Punct('<') => depth += 1,
                Tok::Punct('>') if !(k > 0 && inner[k - 1] == Tok::Punct('-')) => depth -= 1,
                Tok::Ident("as") if depth == 0 => {
                    as_at = Some(k);
                    break;
                }
                _ => {}
            }
        }
        let (ty, tr) = match as_at {
            Some(a) => (type_last(&inner[..a]), type_last(&inner[a + 1..])),
            None => (type_last(inner), None),
        };
        qself = Some((ty, tr));
        i = close + 1;
        if !is_sep(toks, i) {
            return None;
        }
        i += 2;
    }
    // Segments, with turbofish arguments dropped.
    let mut segs: Vec<&str> = Vec::new();
    while let Some(Tok::Ident(s)) = toks.get(i) {
        segs.push(s);
        i += 1;
        if !is_sep(toks, i) {
            break;
        }
        i += 2;
        if toks.get(i) == Some(&Tok::Punct('<')) {
            let close = angle_close(toks, i)?;
            i = close + 1;
            if !is_sep(toks, i) {
                break;
            }
            i += 2;
        }
    }
    (i == toks.len()).then_some((qself, segs))
}

/// Classifies the callee path `toks` (from [`path_start`] to the function name).
#[must_use]
pub fn classify(toks: &[Tok]) -> Callee {
    let Some((qself, segs)) = parse(toks) else {
        return Callee::Other;
    };
    let Some(&f) = segs.last() else {
        return Callee::Other;
    };
    let (ty, tr) = match qself {
        Some((ty, tr)) if segs.len() == 1 => (ty, tr),
        Some(_) => return Callee::Other,
        None => match segs.len().checked_sub(2).map(|k| segs[k]) {
            Some(q) if CTOR_TRAITS.contains(&q) => (None, Some(q.to_string())),
            Some(q) => (Some(q.to_string()), None),
            None => (None, None),
        },
    };
    let f_s = f.to_string();
    if let Some(ty) = &ty
        && HEAP_TYPES.contains(&ty.as_str())
    {
        if is_non_allocating_constructor(ty, f) {
            return Callee::NonAllocating {
                ty: ty.clone(),
                f: f_s,
            };
        }
        if HEAP_CONSTRUCTORS.contains(&f) || ALLOC_METHODS.contains(&f) {
            return Callee::Alloc {
                ty: ty.clone(),
                f: f_s,
                method: !HEAP_CONSTRUCTORS.contains(&f),
            };
        }
        return Callee::Other;
    }
    let slice_or_str = ty.as_deref().is_some_and(|t| t == "[]" || t == "str");
    let ctor_trait = tr.as_deref().is_some_and(|t| CTOR_TRAITS.contains(&t));
    if ALLOC_METHODS.contains(&f) && (slice_or_str || ctor_trait) {
        let shown = match (&ty, &tr) {
            (Some(t), _) if t == "[]" => "<[T]>".to_string(),
            (Some(t), _) if t != "_" => t.clone(),
            (_, Some(t)) => t.clone(),
            _ => "_".to_string(),
        };
        return Callee::Alloc {
            ty: shown,
            f: f_s,
            method: true,
        };
    }
    if ctor_trait && ty.as_deref().is_none_or(|t| t == "_") {
        return Callee::Inferred {
            tr: tr.unwrap_or_default(),
            f: f_s,
        };
    }
    Callee::Other
}

/// The spellings the checkers are tested on: `(expression, type, expected)`, used as
/// `let _x: type = expression;` (no annotation when `type` is empty) in a function
/// with parameters `v: Vec<u8>, mut a: u8, b: u8`; `expected` is one of
/// `alloc Ty::f`, `ok` (an audited non-allocating constructor), `inferred` or
/// `other`. Shared by this crate's tests, `fip_testkit`'s and `fip-macros`'
/// (`verify/ctor_spellings.py`).
pub const SPELLINGS: &[(&str, &str, &str)] = &[
    ("Box::new(1u8)", "", "alloc Box::new"),
    ("Box::<u8>::new(1)", "", "alloc Box::new"),
    ("<Box<u8>>::new(1)", "", "alloc Box::new"),
    ("alloc::boxed::Box::new(1u8)", "", "alloc Box::new"),
    ("std::boxed::Box::<u8>::new(1)", "", "alloc Box::new"),
    ("::std::boxed::Box::new(1u8)", "", "alloc Box::new"),
    ("<std::boxed::Box<u8>>::new(1)", "", "alloc Box::new"),
    ("<Box<u8> as Default>::default()", "", "alloc Box::default"),
    (
        "<std::boxed::Box<u8> as core::default::Default>::default()",
        "",
        "alloc Box::default",
    ),
    ("Box::<u8>::default()", "", "alloc Box::default"),
    (
        "Vec::<u8>::with_capacity(4)",
        "",
        "alloc Vec::with_capacity",
    ),
    (
        "<Vec<u8>>::with_capacity(4)",
        "",
        "alloc Vec::with_capacity",
    ),
    (
        "<Vec<u8> as FromIterator<u8>>::from_iter([1u8])",
        "",
        "alloc Vec::from_iter",
    ),
    ("String::from(\"x\")", "", "alloc String::from"),
    (
        "<String as From<&str>>::from(\"x\")",
        "",
        "alloc String::from",
    ),
    ("Vec::clone(&v)", "", "alloc Vec::clone"),
    ("<Vec<u8> as Clone>::clone(&v)", "", "alloc Vec::clone"),
    ("Clone::clone(&v)", "", "alloc Clone::clone"),
    ("<[u8]>::to_vec(&v)", "", "alloc <[T]>::to_vec"),
    ("str::to_owned(\"x\")", "", "alloc str::to_owned"),
    ("<str>::to_owned(\"x\")", "", "alloc str::to_owned"),
    ("ToOwned::to_owned(\"x\")", "", "alloc ToOwned::to_owned"),
    ("HashMap::<u8, u8>::new()", "", "alloc HashMap::new"),
    ("Rc::<u8>::new(1)", "", "alloc Rc::new"),
    ("Some(1u8).map(Box::new)", "", "alloc Box::new"),
    ("Vec::new()", "Vec<u8>", "ok"),
    ("Vec::<u8>::new()", "", "ok"),
    ("<Vec<u8>>::new()", "", "ok"),
    ("std::vec::Vec::new()", "Vec<u8>", "ok"),
    ("alloc::vec::Vec::<u8>::new()", "", "ok"),
    ("::std::vec::Vec::<u8>::new()", "", "ok"),
    ("Vec::default()", "Vec<u8>", "ok"),
    ("Vec::<u8>::default()", "", "ok"),
    ("<Vec<u8> as Default>::default()", "", "ok"),
    ("<Vec<u8>>::default()", "", "ok"),
    ("String::new()", "", "ok"),
    ("<String as Default>::default()", "", "ok"),
    ("std::string::String::default()", "", "ok"),
    ("VecDeque::<u8>::new()", "", "ok"),
    ("<BTreeMap<u8, u8> as Default>::default()", "", "ok"),
    ("std::collections::BTreeSet::<u8>::new()", "", "ok"),
    ("LinkedList::<u8>::new()", "", "ok"),
    ("<BinaryHeap<u8>>::new()", "", "ok"),
    ("Default::default()", "Box<u8>", "inferred"),
    ("<_ as Default>::default()", "Box<u8>", "inferred"),
    ("core::default::Default::default()", "Box<u8>", "inferred"),
    ("From::from(1u8)", "Box<u8>", "inferred"),
    ("FromIterator::from_iter([1u8])", "Vec<u8>", "inferred"),
    ("<u8 as Default>::default()", "", "other"),
    ("u8::default()", "", "other"),
    ("core::mem::replace(&mut a, b)", "", "other"),
    ("Foo::new()", "", "other"),
];

impl Callee {
    /// How a checker shows the callee: `` `Ty::f` ``.
    #[must_use]
    pub fn shown(&self) -> String {
        match self {
            Callee::Alloc { ty, f, .. } | Callee::NonAllocating { ty, f } => {
                alloc::format!("`{ty}::{f}`")
            }
            Callee::Inferred { tr, f } => alloc::format!("`{tr}::{f}`"),
            Callee::Other => String::new(),
        }
    }
}

/// `expected` of [`SPELLINGS`] for a classification.
#[must_use]
pub fn expected_label(c: &Callee) -> String {
    match c {
        Callee::Alloc { ty, f, .. } => alloc::format!("alloc {ty}::{f}"),
        Callee::NonAllocating { .. } => "ok".to_string(),
        Callee::Inferred { .. } => "inferred".to_string(),
        Callee::Other => "other".to_string(),
    }
}

/// The most significant classification over every path in `toks` (an allocating
/// one first, then a non-allocating constructor, then an inferred one): the result
/// for a whole expression. A path is classified at its last identifier, one not
/// followed by `::` and not a method name after `.`.
#[must_use]
pub fn classify_all(toks: &[Tok]) -> Callee {
    let mut best = Callee::Other;
    let rank = |c: &Callee| match c {
        Callee::Alloc { .. } => 3,
        Callee::NonAllocating { .. } => 2,
        Callee::Inferred { .. } => 1,
        Callee::Other => 0,
    };
    for (k, t) in toks.iter().enumerate() {
        if !matches!(t, Tok::Ident(_)) || is_sep(toks, k + 1) {
            continue;
        }
        if k > 0 && toks[k - 1] == Tok::Punct('.') {
            continue;
        }
        let c = classify(&toks[path_start(toks, k)..=k]);
        if rank(&c) > rank(&best) {
            best = c;
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::{SPELLINGS, Tok, classify_all, expected_label, path_start};
    use alloc::vec::Vec;

    /// A flat token list of `src`: identifiers, punctuation, `[..]` after `<` as one
    /// [`Tok::Slice`], literals and parentheses as [`Tok::Other`].
    fn lex(src: &str) -> Vec<Tok<'_>> {
        let b = src.as_bytes();
        let mut out = Vec::new();
        let mut i = 0;
        while i < b.len() {
            let c = b[i];
            if c.is_ascii_whitespace() {
                i += 1;
            } else if c.is_ascii_alphabetic() || c == b'_' {
                let s = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
                out.push(Tok::Ident(&src[s..i]));
            } else if c.is_ascii_digit() {
                while i < b.len() && b[i].is_ascii_alphanumeric() {
                    i += 1;
                }
                out.push(Tok::Other);
            } else if c == b'"' {
                i += 1;
                while i < b.len() && b[i] != b'"' {
                    i += 1;
                }
                i += 1;
                out.push(Tok::Other);
            } else if c == b'[' && out.last() == Some(&Tok::Punct('<')) {
                while i < b.len() && b[i] != b']' {
                    i += 1;
                }
                i += 1;
                out.push(Tok::Slice);
            } else if matches!(c, b'(' | b')' | b'[' | b']') {
                i += 1;
                out.push(Tok::Other);
            } else {
                out.push(Tok::Punct(char::from(c)));
                i += 1;
            }
        }
        out
    }

    #[test]
    fn every_spelling_is_classified_as_expected() {
        for (src, _, want) in SPELLINGS {
            let got = expected_label(&classify_all(&lex(src)));
            assert_eq!(&got, want, "{src}");
        }
    }

    #[test]
    fn path_start_walks_back_over_every_form() {
        let t = lex("x = <std::vec::Vec<u8> as Default>::default");
        assert_eq!(path_start(&t, t.len() - 1), 2);
        let t = lex("a + ::std::boxed::Box::<u8>::new");
        assert_eq!(path_start(&t, t.len() - 1), 2);
        let t = lex("f(Vec::<Box<dyn Fn(u8) -> u8>>::new");
        assert_eq!(path_start(&t, t.len() - 1), 2);
    }
}
