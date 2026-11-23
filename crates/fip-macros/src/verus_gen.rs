// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The Verus contract of a `strict`/`total` function (decision
//! 2026-11-06-redesign-verus-allocates, section 7): from `#[fip(N, strict,
//! requires(..))]` and an optional hand-written `verus_spec(..)` (which keeps the
//! functional clauses: `ensures`, ..), the attributes emitted in a Verus build.
//!
//! Pure string functions, so the rules are unit-tested without a compiler:
//!
//! - `requires(..)` of the attribute becomes the `requires` clause (the grammar of
//!   `fip_lint_rules::requires`, translated: `xs.len()` of a `&mut` parameter is
//!   `old(xs)@.len()`, of any other `xs@.len()`); a hand-written `requires` next to it
//!   is an error (two sources of one precondition);
//! - `allocates N` (the declared bound) is generated; a hand-written `allocates` is an
//!   error, except for a function with callable parameters, whose bound is relative to
//!   its callbacks (`f.allocs()`, `call_allocations(..)`) and must be written by hand
//!   (section 7.3), and is then required;
//! - `total`: `no_unwind` (a hand-written one is an error) and
//!   `#[verifier::fip(strict)]` (no free on a normal return and constant stack; plain
//!   `#[verifier::fip]` until fork `c716c2bfd`, whose strict check accepts std calls that
//!   drop nothing with a non-`Copy` `T`); `total` with callable parameters is an error (measured
//!   2026-11-09 on the fork `6f6975af2`: a closure call is never `no_unwind`);
//! - never `decreases` (a hand-written function-level `decreases` is an error: the
//!   surface gate forbids recursion in the verified crates, section 7.2);
//! - [`UPSTREAM_ENV`] (honoured by the caller only under Verus's driver): the
//!   fork-only parts (`allocates`, `#[verifier::fip(strict)]`) are left out, `requires` and
//!   `no_unwind` (an upstream clause, accepted by upstream 0.2026.11.02, measured
//!   2026-11-09) stay, so the strip gate `just verify-upstream` can run upstream Verus
//!   on the macro's output.

use fip_lint_rules::requires::{Conjunct, Rel, Side, Step, Term};

/// Expansion-time switch of the strip gate (`just verify-upstream`): set to `1`, a
/// Verus build gets no fork-only clause from the macro.
pub(crate) const UPSTREAM_ENV: &str = "FIP_MACROS_UPSTREAM";

/// Verus signature clause keywords recognised at the top level of a hand-written
/// `verus_spec(..)`.
pub(crate) const CLAUSES: &[&str] = &[
    "requires",
    "recommends",
    "ensures",
    "returns",
    "decreases",
    "opens_invariants",
    "no_unwind",
    "unwind",
    "allocates",
    "deallocates",
    "invariant",
    "invariant_except_break",
    "invariant_ensures",
];

/// What the generator needs to know about one function.
#[allow(
    clippy::struct_excessive_bools,
    reason = "four independent facts about one function, each read once"
)]
pub(crate) struct Input<'a> {
    /// `requires(..)` of the attribute.
    pub(crate) requires: Option<&'a [Conjunct]>,
    /// Parameters of type `&mut ..`.
    pub(crate) mut_params: &'a [String],
    /// The inner text of the hand-written `verus_spec(..)`, if any.
    pub(crate) hand: Option<&'a str>,
    /// The declared allocation bound.
    pub(crate) bound: u64,
    /// `total`.
    pub(crate) total: bool,
    /// The function has callable parameters (`Fn*`, `FipFn`, function pointers,
    /// `dyn`).
    pub(crate) callable: bool,
    /// [`UPSTREAM_ENV`] is set (and honoured).
    pub(crate) upstream: bool,
    /// The function carries a hand-written `verifier::fip` attribute (which states that
    /// it frees nothing, and admits no `deallocates` clause).
    pub(crate) hand_fip: bool,
}

/// The top-level clause keywords of a `verus_spec(..)` text, in order, and where the
/// clauses start (after a return pattern `r =>`, `(r: T) =>`, if any).
fn clauses(text: &str) -> (usize, Vec<String>) {
    let bytes = text.as_bytes();
    let is_word = |ch: u8| ch.is_ascii_alphanumeric() || ch == b'_';
    let mut depth = 0_i32;
    let mut found: Vec<String> = Vec::new();
    let mut start = 0usize;
    let mut pos = 0usize;
    let mut in_str = false;
    while pos < bytes.len() {
        let ch = bytes[pos];
        if in_str {
            if ch == b'\\' {
                pos += 2;
                continue;
            }
            if ch == b'"' {
                in_str = false;
            }
            pos += 1;
            continue;
        }
        match ch {
            b'"' => in_str = true,
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'=' if depth == 0
                && found.is_empty()
                && bytes.get(pos + 1) == Some(&b'>')
                && (pos == 0 || bytes[pos - 1] != b'=') =>
            {
                start = pos + 2;
            }
            first if depth == 0 && (first.is_ascii_alphabetic() || first == b'_') => {
                let word_start = pos;
                while pos < bytes.len() && is_word(bytes[pos]) {
                    pos += 1;
                }
                let prev_ok = word_start == 0 || !is_word(bytes[word_start - 1]);
                let word = &text[word_start..pos];
                if prev_ok && CLAUSES.contains(&word) {
                    found.push(word.to_string());
                }
                continue;
            }
            _ => {}
        }
        pos += 1;
    }
    (start, found)
}

fn show_path(p: &str, steps: &[Step]) -> Result<String, String> {
    let mut out = p.to_string();
    for st in steps {
        match st {
            Step::Field(f) => {
                out.push('.');
                out.push_str(f);
            }
            Step::Index(_) => {
                return Err(
                    "an element access (`p[c]`) in `requires(..)` is not translated to Verus by the generator; state that precondition by hand without `requires(..)` in the attribute".to_string(),
                );
            }
        }
    }
    Ok(out)
}

fn side(s: &Side, mut_params: &[String]) -> Result<String, String> {
    let len = |p: &str| {
        if mut_params.iter().any(|m| m == p) {
            format!("old({p})@.len()")
        } else {
            format!("{p}@.len()")
        }
    };
    let base = match &s.term {
        Term::Param(p) => p.clone(),
        Term::Len(p) => len(p),
        Term::Path(p, steps) => show_path(p, steps)?,
        Term::PathLen(p, steps) => format!("{}@.len()", show_path(p, steps)?),
        Term::Zero => return Ok(format!("{}", s.offset)),
    };
    Ok(match s.offset {
        0 => base,
        o if o > 0 => format!("{base} + {o}"),
        o => format!("{base} - {}", o.unsigned_abs()),
    })
}

/// The Verus `requires` conjuncts of `cs`, comma-separated.
pub(crate) fn requires_text(cs: &[Conjunct], mut_params: &[String]) -> Result<String, String> {
    let mut parts = Vec::new();
    for c in cs {
        let r = match c.rel {
            Rel::Lt => "<",
            Rel::Le => "<=",
            Rel::Eq => "==",
        };
        parts.push(format!(
            "{} {r} {}",
            side(&c.a, mut_params)?,
            side(&c.b, mut_params)?
        ));
    }
    Ok(parts.join(", "))
}

/// Errors of the hand-written spec against the attribute, in every build (the
/// macro sees the `cfg_attr` in plain builds too).
pub(crate) fn conflicts(inp: &Input<'_>) -> Vec<String> {
    let mut errors = Vec::new();
    let Some(hand) = inp.hand else {
        return errors;
    };
    let (_, found) = clauses(hand);
    let has = |k: &str| found.iter().any(|f| f == k);
    if has("decreases") {
        errors.push("`strict`/`total`: the hand-written `verus_spec` has a function-level `decreases`; the generator never emits one, and the verified crates' surface gate forbids recursion (decision 2026-11-06-redesign-verus-allocates, 7.2)".to_string());
    }
    if inp.requires.is_some() && has("requires") {
        errors.push("`strict`/`total`: `requires(..)` is given in the attribute and in the hand-written `verus_spec`; the Verus `requires` is generated from the attribute, so remove it from `verus_spec`".to_string());
    }
    if has("allocates") && !inp.callable {
        errors.push(format!(
            "`strict`/`total`: the hand-written `verus_spec` has `allocates`; it is generated from the declared bound (`allocates {}`), so remove it from `verus_spec` (only a function with callable parameters writes its callback-relative bound by hand)",
            inp.bound
        ));
    }
    if has("deallocates") && !inp.callable {
        errors.push("`strict`/`total`: the hand-written `verus_spec` has `deallocates`; a strict function frees nothing, and the clause is generated (`deallocates 0`; `total` states it through `#[verifier::fip(strict)]`), so remove it from `verus_spec` (only a function with callable parameters writes its own, e.g. the drop of the callable it takes by value)".to_string());
    }
    if inp.total && (has("no_unwind") || has("unwind")) {
        errors.push("`total`: the hand-written `verus_spec` has an unwinding clause; `total` generates `no_unwind`, so remove it from `verus_spec`".to_string());
    }
    errors
}

/// Errors in every build: the hand-written spec against the attribute, and `total`
/// with callable parameters.
pub(crate) fn plain_errors(inp: &Input<'_>) -> Vec<String> {
    let mut errors = conflicts(inp);
    if inp.total && inp.callable {
        errors.push("`total` with callable parameters: Verus cannot state that a callback does not unwind (measured on the fork: a closure call is never `no_unwind`), so a combinator is at most `strict` with a callback-relative bound (decision 2026-11-06-redesign-verus-allocates, 7.3)".to_string());
    }
    errors
}

/// The generated pieces of a Verus build: the attributes before the spec, the
/// `requires` conjuncts (inserted after the return pattern of the hand-written spec)
/// and the clauses appended after it.
pub(crate) struct Parts {
    /// Whole attributes emitted before the spec (`#[cfg_attr(verus_keep_ghost,
    /// verifier::fip(strict))]`).
    pub(crate) attrs: Vec<String>,
    /// `requires <conjuncts>,`.
    pub(crate) requires: Option<String>,
    /// `no_unwind`, `allocates N` (possibly empty).
    pub(crate) tail: String,
}

/// The generated pieces, or the errors (Verus build).
pub(crate) fn parts(inp: &Input<'_>) -> Result<Parts, Vec<String>> {
    let mut errors = plain_errors(inp);
    let (_, found) = clauses(inp.hand.unwrap_or(""));
    // Under the strip switch the hand-written bound is stripped from the source with
    // the rest of the allocation layer (`verify/strip_alloc.py`).
    if inp.callable && !inp.total && !inp.upstream && !found.iter().any(|f| f == "allocates") {
        errors.push("`strict` with callable parameters under Verus: write the callback-relative bound (`allocates f.allocs()`, `allocates call_allocations(f, ..)`, ..) in the hand-written `verus_spec`; the generator states only literal bounds".to_string());
    }
    let requires = match inp.requires {
        Some(cs) => match requires_text(cs, inp.mut_params) {
            Ok(t) => Some(format!("requires {t},")),
            Err(e) => {
                errors.push(format!("`requires(..)`: {e}"));
                None
            }
        },
        None => None,
    };
    if !errors.is_empty() {
        return Err(errors);
    }
    let mut tail = Vec::new();
    if inp.total {
        tail.push("no_unwind".to_string());
    }
    if !inp.callable && !inp.upstream {
        tail.push(format!("allocates {}", inp.bound));
        // A strict function is `fip`: it frees nothing (2026-11-22; `FipFn::call` is
        // `deallocates 0`, so a certified function must state it). `total` states it
        // through `#[verifier::fip(strict)]`, which admits no `deallocates` clause.
        if !inp.total && !inp.hand_fip {
            tail.push("deallocates 0".to_string());
        }
    }
    let mut attrs = Vec::new();
    if inp.total && !inp.upstream {
        attrs.push("#[cfg_attr(verus_keep_ghost, verifier::fip(strict))]".to_string());
    }
    Ok(Parts {
        attrs,
        requires,
        tail: tail.join(" "),
    })
}

/// The attributes of a Verus build as text (the token form in `lib.rs` assembles the
/// same [`Parts`] around the hand-written tokens, keeping their spans), or the errors.
#[cfg(test)]
pub(crate) fn generate(inp: &Input<'_>) -> Result<Vec<String>, Vec<String>> {
    let p = parts(inp)?;
    let hand = inp.hand.unwrap_or("");
    let (start, _) = clauses(hand);
    let (prefix, rest) = hand.split_at(start.min(hand.len()));
    let mut spec: Vec<&str> = Vec::new();
    for piece in [
        prefix.trim(),
        p.requires.as_deref().unwrap_or(""),
        rest.trim(),
        p.tail.as_str(),
    ] {
        if !piece.is_empty() {
            spec.push(piece);
        }
    }
    let mut attrs = p.attrs;
    attrs.push(format!(
        "#[cfg_attr(verus_keep_ghost, verus_spec({}))]",
        spec.join(" ")
    ));
    Ok(attrs)
}

/// The `verifier::<name>` attributes in `attrs` (for the surface test).
#[cfg(test)]
fn verifier_names(attrs: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for a in attrs {
        let mut rest = a.as_str();
        while let Some(i) = rest.find("verifier::") {
            let tail = &rest[i + "verifier::".len()..];
            let name: String = tail
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            out.push(name);
            rest = tail;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use fip_lint_rules::requires::parse;

    fn input<'a>(
        requires: Option<&'a [Conjunct]>,
        mut_params: &'a [String],
        hand: Option<&'a str>,
        total: bool,
        callable: bool,
        upstream: bool,
    ) -> Input<'a> {
        Input {
            requires,
            mut_params,
            hand,
            bound: 0,
            total,
            callable,
            upstream,
            hand_fip: false,
        }
    }

    #[test]
    fn total_with_requires_and_ensures() {
        let cs = parse("i < j, j < xs.len()").unwrap();
        let m = vec!["xs".to_string()];
        let a = generate(&input(
            Some(&cs),
            &m,
            Some("r => ensures r == 1,"),
            true,
            false,
            false,
        ))
        .unwrap();
        assert_eq!(
            a,
            vec![
                "#[cfg_attr(verus_keep_ghost, verifier::fip(strict))]".to_string(),
                "#[cfg_attr(verus_keep_ghost, verus_spec(r => requires i < j, j < old(xs)@.len(), ensures r == 1, no_unwind allocates 0))]".to_string(),
            ]
        );
    }

    #[test]
    fn strict_without_hand_spec() {
        let cs = parse("i < xs.len()").unwrap();
        let a = generate(&Input {
            bound: 3,
            ..input(Some(&cs), &[], None, false, false, false)
        })
        .unwrap();
        assert_eq!(
            a,
            vec![
                "#[cfg_attr(verus_keep_ghost, verus_spec(requires i < xs@.len(), allocates 3 deallocates 0))]"
                    .to_string()
            ]
        );
    }

    #[test]
    fn upstream_keeps_requires_and_no_unwind() {
        let cs = parse("i + 1 < xs.len(), 0 <= i").unwrap();
        for total in [false, true] {
            let a = generate(&input(
                Some(&cs),
                &[],
                Some("ensures true"),
                total,
                false,
                true,
            ))
            .unwrap();
            let all = a.join(" ");
            assert!(all.contains("requires i + 1 < xs@.len(), 0 <= i,"), "{all}");
            assert!(!all.contains("allocates"), "{all}");
            assert!(!all.contains("verifier::fip"), "{all}");
            assert_eq!(all.contains("no_unwind"), total, "{all}");
        }
    }

    #[test]
    fn upstream_never_drops_requires() {
        // Every grammar form the generator translates keeps its `requires` under the
        // switch: the switch removes only fork-only clauses.
        for text in [
            "i < j",
            "i <= xs.len()",
            "w.n == 3",
            "w.b.len() > 0",
            "i + 2 < j - 1",
        ] {
            let cs = parse(text).unwrap();
            let on = generate(&input(Some(&cs), &[], None, true, false, true)).unwrap();
            let off = generate(&input(Some(&cs), &[], None, true, false, false)).unwrap();
            let req = |v: &[String]| {
                v.iter()
                    .find_map(|a| {
                        a.find("requires ").map(|i| {
                            let t = &a[i..];
                            t[..t.find(',').unwrap()].to_string()
                        })
                    })
                    .unwrap()
            };
            assert_eq!(req(&on), req(&off), "{text}");
        }
    }

    #[test]
    fn emitted_verifier_attributes_are_allowed_and_never_decreases() {
        let cs = parse("i < xs.len()").unwrap();
        let m = vec!["xs".to_string()];
        let hands = [
            None,
            Some("r => ensures r == 1"),
            Some("ensures true,"),
            Some("(r: u8) => ensures r == 0, r >= 0"),
        ];
        for hand in hands {
            for (total, upstream) in [(false, false), (true, false), (false, true), (true, true)] {
                for req in [None, Some(cs.as_slice())] {
                    let a = generate(&input(req, &m, hand, total, false, upstream)).unwrap();
                    for n in verifier_names(&a) {
                        assert!(
                            fip_testkit::surface::VERIFIER_ALLOWED.contains(&n.as_str()),
                            "emitted `verifier::{n}` is not in VERIFIER_ALLOWED: {a:?}"
                        );
                    }
                    for x in &a {
                        assert!(!clauses(x).1.iter().any(|c| c == "decreases"), "{x}");
                        assert!(!x.contains("decreases"), "{x}");
                    }
                }
            }
        }
    }

    #[test]
    fn conflicts_are_errors() {
        let cs = parse("i < 3").unwrap();
        let e = generate(&input(
            Some(&cs),
            &[],
            Some("requires i < 3"),
            false,
            false,
            false,
        ));
        assert!(e.unwrap_err()[0].contains("in the hand-written `verus_spec`"));
        let e = generate(&input(
            None,
            &[],
            Some("ensures true, allocates 0"),
            false,
            false,
            false,
        ));
        assert!(e.unwrap_err()[0].contains("has `allocates`"));
        let e = generate(&input(
            None,
            &[],
            Some("ensures true no_unwind"),
            true,
            false,
            false,
        ));
        assert!(e.unwrap_err()[0].contains("unwinding clause"));
        let e = generate(&input(None, &[], Some("decreases n"), false, false, false));
        assert!(e.unwrap_err()[0].contains("`decreases`"));
        let e = generate(&input(None, &[], Some("ensures true"), true, true, false));
        assert!(
            e.unwrap_err()
                .iter()
                .any(|m| m.contains("callable parameters"))
        );
        let e = generate(&input(None, &[], Some("ensures true"), false, true, false));
        assert!(e.unwrap_err()[0].contains("callback-relative"));
        let ok = generate(&input(
            None,
            &[],
            Some("r => ensures true, allocates f.allocs()"),
            false,
            true,
            false,
        ))
        .unwrap();
        assert_eq!(
            ok,
            vec!["#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures true, allocates f.allocs()))]".to_string()]
        );
        // `==>` in an `ensures` is not a return pattern.
        let (start, found) = clauses("ensures a ==> b, allocates 0");
        assert_eq!(start, 0);
        assert_eq!(found, vec!["ensures".to_string(), "allocates".to_string()]);
        // `call_allocations(..)` is not the clause `allocates`.
        let (_, found) = clauses("r => ensures call_allocations(f, (x,)) == 0");
        assert_eq!(found, vec!["ensures".to_string()]);
        let e = generate(&input(
            Some(&parse("xs[0] < 3").unwrap()),
            &[],
            None,
            false,
            false,
            false,
        ));
        assert!(e.unwrap_err()[0].contains("element access"));
    }
}
