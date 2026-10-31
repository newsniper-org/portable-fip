// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Minimal Rust lexer: identifiers, punctuation and literals, each with its file and
//! line. Comments and lifetimes are dropped.

/// Token kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Ident(String),
    Punct(char),
    /// A literal: the body of a string literal, the text of a number, empty for
    /// characters and bytes.
    Lit(String),
}

/// One token with its source position.
#[derive(Clone, Debug)]
pub(crate) struct Tok {
    pub(crate) kind: Kind,
    pub(crate) file: usize,
    pub(crate) line: u32,
    /// Character offset in its file (adjacency of `|` `|`, `=` after `<`, ...).
    pub(crate) pos: usize,
}

/// Lexes `src`, tagging every token with `file`.
pub(crate) fn lex(src: &str, file: usize) -> Vec<Tok> {
    let c: Vec<char> = src.chars().collect();
    let mut lines = Vec::with_capacity(c.len() + 1);
    let mut line = 1_u32;
    for &ch in &c {
        lines.push(line);
        if ch == '\n' {
            line += 1;
        }
    }
    lines.push(line);
    let mut lx = Lexer {
        c: &c,
        lines: &lines,
        file,
        out: Vec::new(),
    };
    let mut i = 0;
    while i < c.len() {
        i = lx.step(i);
    }
    lx.out
}

struct Lexer<'a> {
    c: &'a [char],
    lines: &'a [u32],
    file: usize,
    out: Vec<Tok>,
}

impl Lexer<'_> {
    fn push(&mut self, kind: Kind, pos: usize) {
        let line = self.lines[pos.min(self.lines.len() - 1)];
        self.out.push(Tok {
            kind,
            file: self.file,
            line,
            pos,
        });
    }

    fn step(&mut self, i: usize) -> usize {
        let c = self.c;
        let ch = c[i];
        if ch.is_whitespace() {
            i + 1
        } else if ch == '/' && c.get(i + 1) == Some(&'/') {
            let mut j = i;
            while j < c.len() && c[j] != '\n' {
                j += 1;
            }
            j
        } else if ch == '/' && c.get(i + 1) == Some(&'*') {
            block_comment_end(c, i)
        } else if ch == '"' {
            let end = skip_quoted(c, i, '"');
            self.push(Kind::Lit(text(c, i + 1, end.saturating_sub(1))), i);
            end
        } else if ch == '\'' {
            self.quote(i)
        } else if ch.is_alphabetic() || ch == '_' {
            self.word(i)
        } else if ch.is_ascii_digit() {
            let mut j = i;
            while j < c.len() && (is_ident_continue(c[j]) || c[j] == '.') {
                if c[j] == '.' && !c.get(j + 1).is_some_and(char::is_ascii_digit) {
                    break;
                }
                j += 1;
            }
            self.push(Kind::Lit(text(c, i, j)), i);
            j
        } else {
            self.push(Kind::Punct(ch), i);
            i + 1
        }
    }

    /// Character literal `'x'` / `'\n'`, or a lifetime `'a` (dropped).
    fn quote(&mut self, i: usize) -> usize {
        let c = self.c;
        if c.get(i + 1) == Some(&'\\') {
            self.push(Kind::Lit(String::new()), i);
            skip_quoted(c, i, '\'')
        } else if c.get(i + 2) == Some(&'\'') {
            self.push(Kind::Lit(String::new()), i);
            i + 3
        } else {
            let mut j = i + 1;
            while j < c.len() && is_ident_continue(c[j]) {
                j += 1;
            }
            j
        }
    }

    /// Identifier, raw identifier `r#name`, or a prefixed literal (`b"…"`, `r#"…"#`).
    fn word(&mut self, i: usize) -> usize {
        let c = self.c;
        let mut j = i;
        while j < c.len() && is_ident_continue(c[j]) {
            j += 1;
        }
        let word = text(c, i, j);
        if let Some((end, body)) = literal_after_prefix(c, &word, j) {
            self.push(Kind::Lit(body), i);
            end
        } else if word == "r"
            && c.get(j) == Some(&'#')
            && c.get(j + 1).is_some_and(|&n| n.is_alphabetic() || n == '_')
        {
            // raw identifier `r#name`: the identifier is `name`
            let start = j + 1;
            let mut stop = start;
            while stop < c.len() && is_ident_continue(c[stop]) {
                stop += 1;
            }
            self.push(Kind::Ident(text(c, start, stop)), i);
            stop
        } else {
            self.push(Kind::Ident(word), i);
            j
        }
    }
}

fn text(c: &[char], a: usize, b: usize) -> String {
    let b = b.min(c.len());
    c[a.min(b)..b].iter().collect()
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_'
}

fn block_comment_end(c: &[char], i: usize) -> usize {
    let mut depth = 1;
    let mut j = i + 2;
    while j < c.len() && depth > 0 {
        if c[j] == '/' && c.get(j + 1) == Some(&'*') {
            depth += 1;
            j += 2;
        } else if c[j] == '*' && c.get(j + 1) == Some(&'/') {
            depth -= 1;
            j += 2;
        } else {
            j += 1;
        }
    }
    j
}

/// If `word` (ending at `c[i]`) is a literal prefix and a literal follows, the index
/// just past that literal and its body. Prefixes: `r`, `br`, `cr` (raw strings, `#`s
/// allowed), `b`, `c` (strings), `b` (byte character `b'x'`).
fn literal_after_prefix(c: &[char], word: &str, i: usize) -> Option<(usize, String)> {
    match (word, c.get(i)) {
        ("r" | "br" | "cr", Some('"' | '#')) => raw_string(c, i),
        ("b" | "c", Some('"')) => {
            let end = skip_quoted(c, i, '"');
            Some((end, text(c, i + 1, end.saturating_sub(1))))
        }
        ("b", Some('\'')) => Some((skip_quoted(c, i, '\''), String::new())),
        _ => None,
    }
}

/// `c[i]` is the opening quote; returns the index past the closing one, honouring
/// backslash escapes.
fn skip_quoted(c: &[char], i: usize, quote: char) -> usize {
    let mut j = i + 1;
    while j < c.len() && c[j] != quote {
        if c[j] == '\\' {
            j += 1;
        }
        j += 1;
    }
    j + 1
}

/// `c[i]` is the first `#` or the `"` of a raw string; returns the index past the
/// closing `"##..` and the body, or `None` if this is not a raw string (`r#ident`).
fn raw_string(c: &[char], i: usize) -> Option<(usize, String)> {
    let mut j = i;
    let mut hashes = 0;
    while c.get(j) == Some(&'#') {
        hashes += 1;
        j += 1;
    }
    if c.get(j) != Some(&'"') {
        return None;
    }
    let body = j + 1;
    let mut k = body;
    while k < c.len() {
        if c[k] == '"' && (0..hashes).all(|h| c.get(k + 1 + h) == Some(&'#')) {
            return Some((k + 1 + hashes, text(c, body, k)));
        }
        k += 1;
    }
    Some((k, text(c, body, k)))
}

// ---- token-slice helpers ----

pub(crate) fn id(t: &[Tok], i: usize) -> Option<&str> {
    match t.get(i).map(|x| &x.kind) {
        Some(Kind::Ident(s)) => Some(s),
        _ => None,
    }
}

pub(crate) fn is_id(t: &[Tok], i: usize, s: &str) -> bool {
    id(t, i) == Some(s)
}

pub(crate) fn lit(t: &[Tok], i: usize) -> Option<&str> {
    match t.get(i).map(|x| &x.kind) {
        Some(Kind::Lit(s)) => Some(s),
        _ => None,
    }
}

pub(crate) fn is_p(t: &[Tok], i: usize, c: char) -> bool {
    matches!(t.get(i).map(|x| &x.kind), Some(Kind::Punct(p)) if *p == c)
}

/// `t[i]` and `t[i + 1]` are `::`.
pub(crate) fn sep(t: &[Tok], i: usize) -> bool {
    is_p(t, i, ':') && is_p(t, i + 1, ':')
}

/// `t[j]` directly follows `t[i]` in the source (no whitespace between).
pub(crate) fn adjacent(t: &[Tok], i: usize, j: usize) -> bool {
    match (t.get(i), t.get(j)) {
        (Some(first), Some(second)) => first.file == second.file && first.pos + 1 == second.pos,
        _ => false,
    }
}

pub(crate) fn is_open(t: &[Tok], i: usize) -> bool {
    is_p(t, i, '(') || is_p(t, i, '[') || is_p(t, i, '{')
}

pub(crate) fn is_close(t: &[Tok], i: usize) -> bool {
    is_p(t, i, ')') || is_p(t, i, ']') || is_p(t, i, '}')
}

/// Index just past the delimiter group starting at `i` (which must be the opener).
pub(crate) fn group_end(t: &[Tok], i: usize) -> usize {
    if !is_open(t, i) {
        return i + 1;
    }
    let mut d = 0_i32;
    let mut j = i;
    while j < t.len() {
        if is_open(t, j) {
            d += 1;
        } else if is_close(t, j) {
            d -= 1;
            if d == 0 {
                return j + 1;
            }
        }
        j += 1;
    }
    j
}

/// Index of the opener of the group whose closer is `t[c]`.
pub(crate) fn group_start(t: &[Tok], c: usize) -> usize {
    let mut d = 0_i32;
    let mut j = c + 1;
    while j > 0 {
        j -= 1;
        if is_close(t, j) {
            d += 1;
        } else if is_open(t, j) {
            d -= 1;
            if d == 0 {
                return j;
            }
        }
    }
    c
}

/// `t[i]` is `<`: index past the matching `>` (`->` and `=>` do not close), skipping
/// delimiter groups; `i + 1` if there is none before `end` or a `;`.
pub(crate) fn angle_end(t: &[Tok], i: usize, end: usize) -> usize {
    let mut d = 0_i32;
    let mut j = i;
    while j < end {
        if is_open(t, j) {
            j = group_end(t, j);
            continue;
        }
        if is_p(t, j, ';') || is_close(t, j) {
            break;
        }
        if is_p(t, j, '<') {
            d += 1;
        } else if is_p(t, j, '>') && !(j > 0 && (is_p(t, j - 1, '-') || is_p(t, j - 1, '='))) {
            d -= 1;
            if d == 0 {
                return j + 1;
            }
        }
        j += 1;
    }
    i + 1
}

/// Splits `t[a..b]` at top-level commas (delimiter groups skipped; with `angles`,
/// also commas inside `<..>`).
pub(crate) fn split_top(t: &[Tok], from: usize, to: usize, angles: bool) -> Vec<(usize, usize)> {
    let mut parts = Vec::new();
    let mut s = from;
    let mut j = from;
    let mut d = 0_i32;
    while j < to {
        if is_open(t, j) {
            j = group_end(t, j);
            continue;
        }
        if angles && is_p(t, j, '<') {
            d += 1;
        } else if angles
            && is_p(t, j, '>')
            && !(j > 0 && (is_p(t, j - 1, '-') || is_p(t, j - 1, '=')))
        {
            d -= 1;
        } else if d <= 0 && is_p(t, j, ',') {
            parts.push((s, j));
            s = j + 1;
        }
        j += 1;
    }
    if s < to {
        parts.push((s, to));
    }
    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<Kind> {
        lex(src, 0).into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn lines_and_literals() {
        let t = lex("fn a() {\n  include!(\"x.rs\"); 12u8 'c' '\\'' 'a\n}", 0);
        assert_eq!(t[0].line, 1);
        let inc = t
            .iter()
            .position(|x| x.kind == Kind::Ident("include".into()));
        assert_eq!(inc.map(|k| t[k].line), Some(2));
        assert!(t.iter().any(|x| x.kind == Kind::Lit("x.rs".into())));
        assert!(t.iter().any(|x| x.kind == Kind::Lit("12u8".into())));
        assert!(
            !t.iter()
                .any(|x| x.kind == Kind::Ident("a".into()) && x.line == 2)
        );
    }

    #[test]
    fn raw_strings_keep_their_body() {
        assert_eq!(kinds("r#\"a\"b\"#"), vec![Kind::Lit("a\"b".into())]);
        assert_eq!(kinds("r#x"), vec![Kind::Ident("x".into())]);
    }
}
