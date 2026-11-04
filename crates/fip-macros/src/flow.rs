// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Control-flow regions of one token list, shared by the base scan and the strict
//! scan: which tokens run repeatedly (loop headers and bodies, closure bodies) and
//! which brace groups end a statement.
//!
//! The parser is a token-level approximation of rustc's. Where it cannot decide
//! (a header with a nested `if`/`match`/loop), it answers conservatively: the rest
//! of the list counts as repeated, and no brace group counts as a statement end.

use proc_macro::{Delimiter, Spacing, TokenTree};

use crate::{is_group, is_ident, is_punct};

/// Index of the body `{ .. }` of a loop or `if`/`match` whose header expression
/// starts at `toks[start]`, or `None` if the header cannot be parsed.
///
/// The header is an expression without struct literals (as rustc parses it): a brace
/// group where an operand is expected is a block operand (`while { c } { .. }`,
/// `for i in { 0..n } { .. }`); the first brace group after a complete operand, or
/// after an open range `a..`, is the body.
pub(crate) fn body_index(toks: &[TokenTree], start: usize) -> Option<usize> {
    let mut expect = true;
    let mut after_range = false;
    let mut j = start;
    while j < toks.len() {
        match &toks[j] {
            TokenTree::Group(g) if g.delimiter() == Delimiter::Brace => {
                if expect && !after_range {
                    expect = false;
                } else {
                    return Some(j);
                }
                after_range = false;
            }
            TokenTree::Group(_) | TokenTree::Literal(_) => {
                expect = false;
                after_range = false;
            }
            TokenTree::Ident(id) => {
                let s = id.to_string();
                match s.as_str() {
                    "if" | "match" | "loop" | "while" | "for" | "unsafe" | "async" | "move"
                    | "const" => return None,
                    "as" | "let" | "in" => expect = true,
                    _ => expect = false,
                }
                after_range = false;
            }
            TokenTree::Punct(p) => {
                let c = p.as_char();
                if c == '?' {
                    expect = false;
                    after_range = false;
                } else if c == '|' {
                    // A closure in a loop header.
                    return None;
                } else if c == '.'
                    && p.spacing() == Spacing::Joint
                    && toks.get(j + 1).is_some_and(|n| is_punct(n, '.'))
                {
                    j += 1;
                    if toks.get(j + 1).is_some_and(|n| is_punct(n, '=')) {
                        j += 1;
                    }
                    expect = true;
                    after_range = true;
                } else {
                    expect = true;
                    after_range = false;
                }
            }
        }
        j += 1;
    }
    None
}

/// `true` if the `|` at `toks[i]` opens a closure: it stands where an operand is
/// expected (start of the list, after an operator or `,`, after `move`, `return`,
/// `break`, `in`, `=>`), not between two operands (`a | b`, `A | B` patterns).
fn closure_opens(toks: &[TokenTree], i: usize) -> bool {
    let Some(prev) = i.checked_sub(1).map(|k| &toks[k]) else {
        return true;
    };
    match prev {
        TokenTree::Punct(p) => p.as_char() != '?',
        TokenTree::Ident(id) => matches!(
            id.to_string().as_str(),
            "move" | "return" | "break" | "in" | "yield" | "else"
        ),
        TokenTree::Group(_) | TokenTree::Literal(_) => false,
    }
}

/// Index just past a closure opened at `toks[i]` (`|..|` or `||`): the next `,` or
/// `;` of this list after its parameters, or the end of the list.
fn closure_end(toks: &[TokenTree], i: usize) -> usize {
    let empty = matches!(&toks[i], TokenTree::Punct(p) if p.spacing() == Spacing::Joint)
        && toks.get(i + 1).is_some_and(|n| is_punct(n, '|'));
    let mut j = if empty {
        i + 2
    } else {
        let mut k = i + 1;
        while k < toks.len() && !is_punct(&toks[k], '|') {
            k += 1;
        }
        k + 1
    };
    while j < toks.len() && !is_punct(&toks[j], ',') && !is_punct(&toks[j], ';') {
        j += 1;
    }
    j
}

/// For each token of `toks`: `true` if it runs repeatedly within one execution of
/// the list. Marked: the header and body of `while` (the condition is evaluated on
/// every iteration), the body of `loop` and `for` (not the `for` iterator
/// expression, evaluated once), and everything from a closure's `|` to the end of
/// the closure (a closure may be called any number of times, e.g. by an iterator
/// adaptor). A header that cannot be parsed marks the rest of the list.
pub(crate) fn loop_regions(toks: &[TokenTree]) -> Vec<bool> {
    let n = toks.len();
    let mut r = vec![false; n];
    let mark = |r: &mut Vec<bool>, from: usize, to: usize| {
        for x in r.iter_mut().take(to.min(n)).skip(from) {
            *x = true;
        }
    };
    let mut i = 0;
    while i < n {
        if is_punct(&toks[i], '|') && closure_opens(toks, i) {
            let end = closure_end(toks, i);
            mark(&mut r, i, end);
            i = end;
            continue;
        }
        if let TokenTree::Ident(id) = &toks[i] {
            let prev_dot = i > 0 && is_punct(&toks[i - 1], '.');
            match id.to_string().as_str() {
                "loop" if !prev_dot => {
                    if toks
                        .get(i + 1)
                        .is_some_and(|t| is_group(t, Delimiter::Brace))
                    {
                        r[i + 1] = true;
                    }
                }
                "while" if !prev_dot => match body_index(toks, i + 1) {
                    Some(b) => mark(&mut r, i + 1, b + 1),
                    None => mark(&mut r, i + 1, n),
                },
                "for" if !prev_dot && !toks.get(i + 1).is_some_and(|t| is_punct(t, '<')) => {
                    let in_at = (i + 1..n).find(|&k| is_ident(&toks[k], "in"));
                    match in_at.and_then(|k| body_index(toks, k + 1)) {
                        Some(b) => r[b] = true,
                        None => mark(&mut r, i + 1, n),
                    }
                }
                _ => {}
            }
        }
        i += 1;
    }
    r
}

/// For each token of a statement list (a block's contents): `true` for a brace group
/// that ends a statement-level block-like expression (`{ .. }`, `unsafe { .. }`,
/// `loop`, `while`, `for`, `match`, `if .. else ..`). Rustc ends such a statement at
/// that `}`, so a following `( .. )` is a new expression, not a call. Brace groups in
/// expression position (`let r = { f }(x);`) are not marked.
pub(crate) fn stmt_block_ends(toks: &[TokenTree]) -> Vec<bool> {
    let n = toks.len();
    let mut ends = vec![false; n];
    let mut at_start = true;
    let mut i = 0;
    while i < n {
        if !at_start {
            if is_punct(&toks[i], ';') || is_punct(&toks[i], ',') {
                at_start = true;
            } else if is_punct(&toks[i], '=') && toks.get(i + 1).is_some_and(|t| is_punct(t, '>')) {
                at_start = true;
                i += 1;
            }
            i += 1;
            continue;
        }
        if is_punct(&toks[i], '#')
            && toks
                .get(i + 1)
                .is_some_and(|t| is_group(t, Delimiter::Bracket))
        {
            i += 2;
            continue;
        }
        // A label `'a:`.
        if is_punct(&toks[i], '\'')
            && matches!(toks.get(i + 1), Some(TokenTree::Ident(_)))
            && toks.get(i + 2).is_some_and(|t| is_punct(t, ':'))
        {
            i += 3;
            continue;
        }
        let end = match &toks[i] {
            TokenTree::Group(g) if g.delimiter() == Delimiter::Brace => Some(i),
            TokenTree::Ident(id) => match id.to_string().as_str() {
                "unsafe" | "loop" => toks
                    .get(i + 1)
                    .is_some_and(|t| is_group(t, Delimiter::Brace))
                    .then_some(i + 1),
                "while" | "match" => body_index(toks, i + 1),
                "for" => (i + 1..n)
                    .find(|&k| is_ident(&toks[k], "in"))
                    .and_then(|k| body_index(toks, k + 1)),
                "if" => if_end(toks, i),
                _ => {
                    at_start = false;
                    i += 1;
                    continue;
                }
            },
            _ => {
                at_start = false;
                i += 1;
                continue;
            }
        };
        let Some(e) = end else {
            // Undecided: no later brace group of this list counts as a statement end.
            break;
        };
        ends[e] = true;
        i = e + 1;
    }
    ends
}

/// The last brace group of the `if .. else if .. else ..` chain at `toks[i]`.
fn if_end(toks: &[TokenTree], mut i: usize) -> Option<usize> {
    loop {
        let b = body_index(toks, i + 1)?;
        if !toks.get(b + 1).is_some_and(|t| is_ident(t, "else")) {
            return Some(b);
        }
        match toks.get(b + 2) {
            Some(t) if is_ident(t, "if") => i = b + 2,
            Some(t) if is_group(t, Delimiter::Brace) => return Some(b + 2),
            _ => return None,
        }
    }
}
