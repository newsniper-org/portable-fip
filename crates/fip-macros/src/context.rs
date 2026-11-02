// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The block an attributed item sits in, read from its source file.
//!
//! An attribute macro sees only its item: a bodiless `fn f();` is a trait method
//! declaration or a foreign function, and a body without receiver is a free function
//! or a trait method's default body. The tokens cannot tell them apart. The item's
//! span can: `Span::local_file`, `Span::line` and `Span::column` (stable on the
//! MSRV, 1.99.1) locate it in its file, and the innermost `{` still open before it
//! belongs to a `trait`, an `extern` block or something else.
//!
//! Used only where the item is rejected anyway (by rustc, or by `fip-prelint`), to
//! reject it at expansion with a precise message, and only when the file at that
//! position holds the item's own `fn <name>` (so a span whose line and column refer to
//! other text, e.g. a doctest's, is not used) and the header of the enclosing block is
//! recognised exactly. [`Enclosing::Unknown`] (no local file, an unreadable file,
//! other text at the position, or a header that is neither) changes nothing.

use proc_macro::Span;

/// What the innermost enclosing block is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Enclosing {
    /// `[pub ..] [unsafe] [auto] trait Name .. {`
    Trait,
    /// `[unsafe] extern ["abi"] {`
    Extern,
    /// Anything else, or not determined.
    Unknown,
}

/// The block enclosing the `fn` keyword at `span` of the function `name`, from the
/// span's source file.
pub(crate) fn enclosing(span: Span, name: &str) -> Enclosing {
    let Some(path) = span.local_file() else {
        return Enclosing::Unknown;
    };
    let Ok(src) = std::fs::read_to_string(path) else {
        return Enclosing::Unknown;
    };
    match offset_of(&src, span.line(), span.column()) {
        Some(offset) if is_fn_named(&src[offset..], name) => enclosing_at(&src, offset),
        _ => Enclosing::Unknown,
    }
}

/// `true` if `text` starts with `fn <name>` (and `name` ends there).
fn is_fn_named(text: &str, name: &str) -> bool {
    let Some(rest) = text.strip_prefix("fn") else {
        return false;
    };
    let trimmed = rest.trim_start();
    trimmed.len() < rest.len()
        && trimmed
            .strip_prefix(name)
            .is_some_and(|after| !after.starts_with(|c: char| c.is_alphanumeric() || c == '_'))
}

/// Byte offset of 1-based `line` and 1-based `column` (in characters).
fn offset_of(src: &str, line: usize, column: usize) -> Option<usize> {
    let start = if line <= 1 {
        0
    } else {
        src.match_indices('\n').nth(line - 2).map(|(i, _)| i + 1)?
    };
    let rest = &src[start..];
    let col = column.checked_sub(1)?;
    rest.char_indices().nth(col).map(|(i, _)| start + i)
}

/// The block enclosing byte `offset` of `src`: comments, strings and character
/// literals are skipped; the header of a `{` is the text since the last `;`, `{` or
/// `}` at block level, with comments removed.
pub(crate) fn enclosing_at(src: &str, offset: usize) -> Enclosing {
    let b = src.as_bytes();
    let end = offset.min(b.len());
    // `clean`: the scanned text with comments blanked and literals emptied.
    let mut clean: Vec<u8> = Vec::with_capacity(end);
    // Open `{`, `(`, `[`: the bracket and, for `{`, where its header starts in `clean`.
    let mut stack: Vec<(u8, usize, usize)> = Vec::new();
    let mut boundary = 0usize;
    let mut i = 0usize;
    while i < end {
        let c = b[i];
        let next = b.get(i + 1).copied();
        if c == b'/' && next == Some(b'/') {
            while i < end && b[i] != b'\n' {
                i += 1;
            }
            clean.push(b' ');
            continue;
        }
        if c == b'/' && next == Some(b'*') {
            let mut depth = 0usize;
            while i < end {
                if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
                    depth += 1;
                    i += 2;
                } else if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            clean.push(b' ');
            continue;
        }
        if let Some(after) = raw_string_end(b, i) {
            i = after;
            clean.extend_from_slice(b"\"\"");
            continue;
        }
        if c == b'"' {
            i += 1;
            while i < end && b[i] != b'"' {
                i += if b[i] == b'\\' { 2 } else { 1 };
            }
            i += 1;
            clean.extend_from_slice(b"\"\"");
            continue;
        }
        if c == b'\'' {
            // A character literal (`'x'`, `'\n'`, `'\u{..}'`) or a lifetime (`'a`).
            if next == Some(b'\\') {
                i += 2;
                while i < end && b[i] != b'\'' {
                    i += 1;
                }
                i += 1;
                clean.extend_from_slice(b"' '");
                continue;
            }
            let ch_len = src[i + 1..].chars().next().map_or(1, char::len_utf8);
            if b.get(i + 1 + ch_len) == Some(&b'\'') {
                i += ch_len + 2;
                clean.extend_from_slice(b"' '");
                continue;
            }
        }
        let at_block = stack.last().is_none_or(|(k, _, _)| *k == b'{');
        match c {
            b'{' => {
                stack.push((b'{', clean.len(), boundary));
                clean.push(c);
                boundary = clean.len();
            }
            b'(' | b'[' => {
                stack.push((c, clean.len(), 0));
                clean.push(c);
            }
            b'}' | b')' | b']' => {
                stack.pop();
                clean.push(c);
                if c == b'}' && stack.last().is_none_or(|(k, _, _)| *k == b'{') {
                    boundary = clean.len();
                }
            }
            b';' if at_block => {
                clean.push(c);
                boundary = clean.len();
            }
            _ => clean.push(c),
        }
        i += 1;
    }
    let Some(&(_, open, header_start)) = stack.iter().rev().find(|(k, _, _)| *k == b'{') else {
        return Enclosing::Unknown;
    };
    let header = String::from_utf8_lossy(&clean[header_start..open]).into_owned();
    classify(&header)
}

/// End of a raw string literal (`r"..."`, `r#"..."#`, `br#".."#`) starting at `i`.
fn raw_string_end(b: &[u8], i: usize) -> Option<usize> {
    let prev_ident = i > 0 && (b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_');
    if prev_ident {
        return None;
    }
    let mut j = i;
    if b.get(j) == Some(&b'b') || b.get(j) == Some(&b'c') {
        j += 1;
    }
    if b.get(j) != Some(&b'r') {
        return None;
    }
    j += 1;
    let mut hashes = 0usize;
    while b.get(j) == Some(&b'#') {
        hashes += 1;
        j += 1;
    }
    if b.get(j) != Some(&b'"') {
        return None;
    }
    j += 1;
    while j < b.len() {
        if b[j] == b'"'
            && b[j + 1..]
                .iter()
                .take(hashes)
                .filter(|&&h| h == b'#')
                .count()
                == hashes
        {
            return Some(j + 1 + hashes);
        }
        j += 1;
    }
    Some(b.len())
}

/// Classifies a block header (outer attributes allowed in front).
fn classify(header: &str) -> Enclosing {
    let mut h = header.trim_start();
    // Outer attributes `#[..]` (balanced brackets; literals are already empty).
    while let Some(rest) = h.strip_prefix('#') {
        let rest = rest.trim_start();
        let Some(inner) = rest.strip_prefix('[') else {
            return Enclosing::Unknown;
        };
        let mut depth = 1usize;
        let mut cut = None;
        for (k, ch) in inner.char_indices() {
            match ch {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        cut = Some(k + 1);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(cut) = cut else {
            return Enclosing::Unknown;
        };
        h = inner[cut..].trim_start();
    }
    let words: Vec<&str> = h
        .split(|c: char| c.is_whitespace())
        .filter(|w| !w.is_empty())
        .collect();
    let mut k = 0;
    // Visibility: `pub`, `pub(crate)`, `pub(in path)` (possibly split by spaces).
    if words
        .get(k)
        .is_some_and(|w| *w == "pub" || w.starts_with("pub("))
    {
        let mut open = words[k].matches('(').count();
        let mut close = words[k].matches(')').count();
        k += 1;
        if open == 0 && words.get(k).is_some_and(|w| w.starts_with('(')) {
            open += words[k].matches('(').count();
            close += words[k].matches(')').count();
            k += 1;
        }
        while open > close && k < words.len() {
            open += words[k].matches('(').count();
            close += words[k].matches(')').count();
            k += 1;
        }
    }
    let rest = &words[k..];
    let strip = |r: &[&str], w: &str| -> usize { usize::from(r.first() == Some(&w)) };
    let u = strip(rest, "unsafe");
    let a = strip(&rest[u..], "auto");
    if rest.get(u + a) == Some(&"trait") && rest.len() > u + a + 1 {
        return Enclosing::Trait;
    }
    if k == 0 && rest.get(u) == Some(&"extern") {
        match &rest[u + 1..] {
            [] => return Enclosing::Extern,
            [abi] if *abi == "\"\"" => return Enclosing::Extern,
            _ => {}
        }
    }
    Enclosing::Unknown
}

#[cfg(test)]
mod tests {
    use super::{Enclosing, enclosing_at};

    fn at(src: &str) -> Enclosing {
        let offset = src.find("@@").expect("marker");
        enclosing_at(src, offset)
    }

    #[test]
    fn traits_and_extern_blocks_are_recognised() {
        assert_eq!(at("trait T { @@ }"), Enclosing::Trait);
        assert_eq!(
            at("pub(crate) unsafe trait T<X: Into<[u8; 4]>>: Sized where X: Copy { @@ }"),
            Enclosing::Trait
        );
        assert_eq!(
            at("/// doc\n#[cfg(any())] pub auto trait T { fn a() {} @@ }"),
            Enclosing::Trait
        );
        assert_eq!(at("unsafe extern \"C\" { fn a(); @@ }"), Enclosing::Extern);
        assert_eq!(at("#[link(name = \"m\")] extern { @@ }"), Enclosing::Extern);
        assert_eq!(
            at("extern \"C-unwind\" {\n // trait T {\n @@ }"),
            Enclosing::Extern
        );
    }

    #[test]
    fn the_position_must_hold_the_function() {
        assert!(super::is_fn_named("fn f() {}", "f"));
        assert!(super::is_fn_named("fn  f<T>();", "f"));
        assert!(!super::is_fn_named("fn fg() {}", "f"));
        assert!(!super::is_fn_named("fnf() {}", "f"));
        assert!(!super::is_fn_named("let x = 1;", "f"));
    }

    #[test]
    fn everything_else_is_unknown() {
        assert_eq!(at("@@"), Enclosing::Unknown);
        assert_eq!(at("mod m { @@ }"), Enclosing::Unknown);
        assert_eq!(at("impl T for S { @@ }"), Enclosing::Unknown);
        assert_eq!(at("trait T { fn d() { @@ } }"), Enclosing::Unknown);
        assert_eq!(at("extern \"C\" fn f() { @@ }"), Enclosing::Unknown);
        assert_eq!(at("trait T {} fn f() { @@ }"), Enclosing::Unknown);
        assert_eq!(
            at("const S: &str = \"trait T {\"; fn f() { let c = '{'; @@ }"),
            Enclosing::Unknown
        );
        assert_eq!(
            at("const S: &str = r#\"trait T { \"#; @@"),
            Enclosing::Unknown
        );
        assert_eq!(
            at("fn f<'a>(x: &'a u8) { /* trait T { */ @@ }"),
            Enclosing::Unknown
        );
        assert_eq!(at("macro_rules! m { () => { @@ } }"), Enclosing::Unknown);
    }
}
