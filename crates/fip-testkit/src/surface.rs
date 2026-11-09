// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Source checks for crates verified with Verus's attribute syntax.
//!
//! Under the attribute syntax a function without `verus_spec` is external to Verus,
//! i.e. silently unverified, and `--no-cheating` does not object. [`scan_dir`] lists
//! every `fn` item with the `verus_spec` attribute that directly precedes it (if any),
//! so a test can require one on every function.
//!
//! It also exposes the function-level specification text, so a test can forbid
//! `decreases` there: Verus rejects any recursive cycle among verified functions that
//! lacks a `decreases` clause, so a crate whose functions have none contains no
//! recursion among its verified functions (see `docs/decisions/` on stack bounds).
//!
//! [`unlisted_verifier_attributes`] lists every `verifier::..` attribute outside
//! [`VERIFIER_ALLOWED`]: `verifier::exec_allows_no_decreases_clause` lets an exec
//! function recurse without `decreases`, which the bounded-stack claim relies on, and
//! the other unlisted ones (`external_body`, `external`, ..) change what is verified.
//!
//! Conventions this line-based scanner relies on (rustfmt output satisfies them):
//! - `verus! {` opens a block on its own line; the block is skipped by brace count;
//! - attributes start a line with `#[` and are balanced by `[`/`]`;
//! - a `fn` item starts a line, after optional `pub`, `pub(..)`, `const`, `async`,
//!   `unsafe`, `safe`, `default`, `extern "abi"`.

use std::fs;
use std::path::{Path, PathBuf};

/// One `fn` item found in the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnItem {
    /// File the item is in.
    pub file: PathBuf,
    /// 1-based line of the `fn` keyword line.
    pub line: usize,
    /// The trimmed line containing `fn`.
    pub signature: String,
    /// Text of the `#[cfg_attr(verus_keep_ghost, verus_spec(..))]` attribute directly
    /// attached to the item, if any.
    pub spec: Option<String>,
}

/// `true` if `t` (trimmed) starts a `fn` item.
#[must_use]
pub fn is_fn_line(t: &str) -> bool {
    let mut s = t;
    loop {
        if let Some(rest) = s.strip_prefix("pub(") {
            let Some(close) = rest.find(')') else {
                return false;
            };
            s = rest[close + 1..].trim_start();
            continue;
        }
        let mut stripped = false;
        for q in ["pub ", "const ", "async ", "unsafe ", "safe ", "default "] {
            if let Some(rest) = s.strip_prefix(q) {
                s = rest.trim_start();
                stripped = true;
                break;
            }
        }
        if stripped {
            continue;
        }
        if let Some(rest) = s.strip_prefix("extern ") {
            let rest = rest.trim_start();
            s = match rest.strip_prefix('"') {
                Some(abi) => abi.find('"').map_or(rest, |e| abi[e + 1..].trim_start()),
                None => rest,
            };
            continue;
        }
        return s.starts_with("fn ");
    }
}

fn count(s: &str, open: char, close: char) -> i64 {
    let mut d = 0_i64;
    for c in s.chars() {
        if c == open {
            d += 1;
        } else if c == close {
            d -= 1;
        }
    }
    d
}

/// Strips a trailing `// ...` comment (not inside a string; good enough for code lines).
fn code_part(line: &str) -> &str {
    let mut in_str = false;
    let b = line.as_bytes();
    for i in 0..b.len() {
        match b[i] {
            b'"' if i == 0 || b[i - 1] != b'\\' => in_str = !in_str,
            b'/' if !in_str && i + 1 < b.len() && b[i + 1] == b'/' => return &line[..i],
            _ => {}
        }
    }
    line
}

/// Scans one file's text.
#[must_use]
pub fn scan_text(file: &Path, text: &str) -> Vec<FnItem> {
    let mut out = Vec::new();
    let mut verus_depth: i64 = 0;
    let mut attr_depth: i64 = 0;
    let mut attr_buf = String::new();
    let mut pending: Option<String> = None;
    for (n, raw) in text.lines().enumerate() {
        let t = raw.trim_start();
        let code = code_part(t);
        if verus_depth > 0 {
            verus_depth += count(code, '{', '}');
            continue;
        }
        if t.starts_with("verus! {") || t.starts_with("verus!{") {
            verus_depth = count(code, '{', '}');
            pending = None;
            continue;
        }
        if attr_depth > 0 {
            attr_buf.push('\n');
            attr_buf.push_str(t);
            attr_depth += count(code, '[', ']');
            if attr_depth <= 0 {
                attr_depth = 0;
                finish_attr(&mut attr_buf, &mut pending);
            }
            continue;
        }
        if t.starts_with("#[") {
            attr_buf.clear();
            attr_buf.push_str(t);
            attr_depth = count(code, '[', ']');
            if attr_depth <= 0 {
                attr_depth = 0;
                finish_attr(&mut attr_buf, &mut pending);
            }
            continue;
        }
        if t.is_empty() || t.starts_with("//") || t.starts_with("#!") {
            continue;
        }
        if is_fn_line(t) {
            out.push(FnItem {
                file: file.to_path_buf(),
                line: n + 1,
                signature: t.to_string(),
                spec: pending.take(),
            });
        } else {
            pending = None;
        }
    }
    out
}

fn finish_attr(buf: &mut String, pending: &mut Option<String>) {
    if buf.starts_with("#[cfg_attr(verus_keep_ghost") && buf.contains("verus_spec(") {
        *pending = Some(std::mem::take(buf));
    }
    // Other attributes (`#[inline]`, `#[must_use]`, …) keep an earlier spec pending.
}

/// Scans every `.rs` file directly in `dir`, recursing into subdirectories.
///
/// # Panics
///
/// Panics if `dir` or a file in it cannot be read.
#[must_use]
pub fn scan_dir(dir: &Path) -> Vec<FnItem> {
    let mut files = Vec::new();
    collect(dir, &mut files);
    files.sort();
    files
        .iter()
        .flat_map(|p| scan_text(p, &fs::read_to_string(p).expect("read source file")))
        .collect()
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in fs::read_dir(dir).expect("read source dir") {
        let p = e.expect("dir entry").path();
        if p.is_dir() {
            collect(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
}

/// `verifier::..` attributes that only steer the solver (nonlinear arithmetic, a
/// separate prover process, a resource limit, loop isolation): they cannot make Verus
/// accept recursion or skip a body.
pub const VERIFIER_ALLOWED: &[&str] = &["nonlinear", "spinoff_prover", "rlimit", "loop_isolation"];

/// One `verifier::<name>` (or `verifier(<name>)`) in code, outside comments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifierAttr {
    /// File the attribute is in.
    pub file: PathBuf,
    /// 1-based line.
    pub line: usize,
    /// The attribute's name (`exec_allows_no_decreases_clause`).
    pub name: String,
}

/// Every `verifier::<name>` / `verifier(<name>` of `text` outside `//` comments,
/// inside `verus! { .. }` blocks as well.
#[must_use]
pub fn verifier_attributes(file: &Path, text: &str) -> Vec<VerifierAttr> {
    let mut out = Vec::new();
    for (n, line) in text.lines().enumerate() {
        let code = line.split("//").next().unwrap_or("");
        let mut rest = code;
        while let Some(i) = rest.find("verifier") {
            let before = &rest[..i];
            let after = &rest[i + "verifier".len()..];
            rest = after;
            if before
                .chars()
                .last()
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
            {
                continue;
            }
            let Some(tail) = after
                .trim_start()
                .strip_prefix("::")
                .or_else(|| after.trim_start().strip_prefix('('))
            else {
                continue;
            };
            let name: String = tail
                .trim_start()
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                out.push(VerifierAttr {
                    file: file.to_path_buf(),
                    line: n + 1,
                    name,
                });
            }
        }
    }
    out
}

/// The `verifier::..` attributes under `dir` not in [`VERIFIER_ALLOWED`].
///
/// # Panics
///
/// Panics if `dir` or a file in it cannot be read.
#[must_use]
pub fn unlisted_verifier_attributes(dir: &Path) -> Vec<VerifierAttr> {
    let mut files = Vec::new();
    collect(dir, &mut files);
    files.sort();
    files
        .iter()
        .flat_map(|p| verifier_attributes(p, &fs::read_to_string(p).expect("read source file")))
        .filter(|a| !VERIFIER_ALLOWED.contains(&a.name.as_str()))
        .collect()
}

/// Every `trusted_call` identifier of `text` in code (outside `//` comments and string
/// literals), in any spelling (`#[verifier::trusted_call]`, `verifier(trusted_call)`,
/// ..): the fork's `#[verifier::trusted_call] { .. }` block trusts the calls in it
/// (the fork audit, 2026-11-09). `--no-cheating` rejects the block; this gate rejects
/// the identifier itself, independently of the Verus build.
#[must_use]
pub fn trusted_calls(file: &Path, text: &str) -> Vec<VerifierAttr> {
    tokens(text)
        .into_iter()
        .filter(|(t, _)| t == "trusted_call")
        .map(|(name, line)| VerifierAttr {
            file: file.to_path_buf(),
            line,
            name,
        })
        .collect()
}

/// The `trusted_call` identifiers under `dir` ([`trusted_calls`]).
///
/// # Panics
///
/// Panics if `dir` or a file in it cannot be read.
#[must_use]
pub fn trusted_calls_in(dir: &Path) -> Vec<VerifierAttr> {
    let mut files = Vec::new();
    collect(dir, &mut files);
    files.sort();
    files
        .iter()
        .flat_map(|p| trusted_calls(p, &fs::read_to_string(p).expect("read source file")))
        .collect()
}

/// Traits whose implementation is a trust point of the fork's `allocates`
/// accounting (the fork audit, 2026-11-09): `allocates` counts calls of the
/// allocator specifications, and an implementation of one of these `unsafe` traits
/// is code whose allocator contract Verus does not check. `Allocator` is stable since
/// rustc 1.100, with the marker traits `GlobalAllocator`, `StaticAllocator` and
/// `AllocatorClone`. Matched by the last segment of the implemented trait's path.
pub const ALLOCATOR_TRAITS: &[&str] = &[
    "Allocator",
    "GlobalAlloc",
    "GlobalAllocator",
    "StaticAllocator",
    "AllocatorClone",
];

/// Every implementation of an [`ALLOCATOR_TRAITS`] trait in `text` (`impl`, `unsafe
/// impl`, generic, any path, also inside `verus! { .. }` and `macro_rules!` bodies),
/// with the trait's name as `name`.
#[must_use]
pub fn allocator_impls(file: &Path, text: &str) -> Vec<VerifierAttr> {
    let toks = tokens(text);
    let is = |k: usize, s: &str| toks.get(k).is_some_and(|(t, _)| t == s);
    // A `>` that does not end `->` or `=>`.
    let closes_angle = |k: usize| is(k, ">") && !(k > 0 && (is(k - 1, "-") || is(k - 1, "=")));
    let mut out = Vec::new();
    for (k, (t, line)) in toks.iter().enumerate() {
        if t != "impl" {
            continue;
        }
        let mut j = k + 1;
        // The impl's own generics.
        if is(j, "<") {
            let mut angle = 0_usize;
            while j < toks.len() {
                if is(j, "<") {
                    angle += 1;
                } else if closes_angle(j) {
                    angle = angle.saturating_sub(1);
                    if angle == 0 {
                        j += 1;
                        break;
                    }
                }
                j += 1;
            }
        }
        // The trait path, up to `for` at angle depth 0 (none: an inherent impl or an
        // `impl Trait` type); its last identifier is the trait's name.
        let mut name: Option<&str> = None;
        let mut angle = 0_usize;
        let mut paren = 0_usize;
        while j < toks.len() {
            let s = toks[j].0.as_str();
            if s == "(" || s == "[" {
                paren += 1;
            } else if s == ")" || s == "]" {
                if paren == 0 {
                    break;
                }
                paren -= 1;
            } else if paren > 0 {
                // Inside `(..)`/`[..]` of the path (`Fn(..)` sugar, array types).
                j += 1;
                continue;
            } else if s == "<" {
                angle += 1;
            } else if closes_angle(j) {
                angle = angle.saturating_sub(1);
            } else if angle == 0 && (s == "{" || s == ";" || s == "," || s == "where") {
                break;
            } else if angle == 0 && s == "for" {
                if let Some(n) = name
                    && ALLOCATOR_TRAITS.contains(&n)
                {
                    out.push(VerifierAttr {
                        file: file.to_path_buf(),
                        line: *line,
                        name: n.to_string(),
                    });
                }
                break;
            } else if angle == 0 && s.starts_with(|c: char| c.is_alphabetic() || c == '_') {
                name = Some(s);
            }
            j += 1;
        }
    }
    out
}

/// The implementations of [`ALLOCATOR_TRAITS`] traits under `dir`
/// ([`allocator_impls`]).
///
/// # Panics
///
/// Panics if `dir` or a file in it cannot be read.
#[must_use]
pub fn allocator_impls_in(dir: &Path) -> Vec<VerifierAttr> {
    let mut files = Vec::new();
    collect(dir, &mut files);
    files.sort();
    files
        .iter()
        .flat_map(|p| allocator_impls(p, &fs::read_to_string(p).expect("read source file")))
        .collect()
}

type Chars<'a> = std::iter::Peekable<std::str::Chars<'a>>;

/// Skips a `/* .. */` comment (nested) after its `/`, counting newlines.
fn skip_block_comment(it: &mut Chars<'_>, line: &mut usize) {
    it.next();
    let mut depth = 1_usize;
    while depth > 0 {
        match it.next() {
            None => break,
            Some('\n') => *line += 1,
            Some('*') if it.peek() == Some(&'/') => {
                it.next();
                depth -= 1;
            }
            Some('/') if it.peek() == Some(&'*') => {
                it.next();
                depth += 1;
            }
            Some(_) => {}
        }
    }
}

/// Skips a string literal after its opening `"`, counting newlines.
fn skip_string(it: &mut Chars<'_>, line: &mut usize) {
    while let Some(d) = it.next() {
        match d {
            '\\' => {
                if it.next() == Some('\n') {
                    *line += 1;
                }
            }
            '\n' => *line += 1,
            '"' => break,
            _ => {}
        }
    }
}

/// After a `'`: skips a character literal (`'x'`, `'\n'`); a lifetime (`'a`) is
/// left to the identifier branch.
fn skip_char(it: &mut Chars<'_>) {
    let mut look = it.clone();
    let closed = match look.next() {
        Some('\\') => true,
        Some(_) => look.next() == Some('\''),
        None => false,
    };
    if closed {
        while let Some(d) = it.next() {
            if d == '\\' {
                it.next();
            } else if d == '\'' {
                break;
            }
        }
    }
}

/// After the prefix `r`/`br`: skips a raw string literal (`r"..."`, `r#"..."#`) and
/// returns `true`, or returns `false` (an identifier) without consuming anything.
fn skip_raw_string(it: &mut Chars<'_>, line: &mut usize) -> bool {
    let mut look = it.clone();
    let mut hashes = 0_usize;
    while look.peek() == Some(&'#') {
        look.next();
        hashes += 1;
    }
    if look.next() != Some('"') {
        return false;
    }
    *it = look;
    'raw: while let Some(d) = it.next() {
        if d == '\n' {
            *line += 1;
        } else if d == '"' {
            let mut look = it.clone();
            for _ in 0..hashes {
                if look.next() != Some('#') {
                    continue 'raw;
                }
            }
            *it = look;
            break;
        }
    }
    true
}

/// Identifiers and single punctuation characters of `text` with their 1-based line,
/// outside `//` and `/* .. */` comments, string literals (also raw ones) and
/// character literals (lifetimes are kept as identifiers after the `'`).
fn tokens(text: &str) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    let mut line = 1;
    let mut it = text.chars().peekable();
    while let Some(c) = it.next() {
        match c {
            '\n' => line += 1,
            '/' if it.peek() == Some(&'/') => {
                for d in it.by_ref() {
                    if d == '\n' {
                        line += 1;
                        break;
                    }
                }
            }
            '/' if it.peek() == Some(&'*') => skip_block_comment(&mut it, &mut line),
            '"' => skip_string(&mut it, &mut line),
            '\'' => skip_char(&mut it),
            c if c.is_alphanumeric() || c == '_' => {
                let mut s = String::from(c);
                while let Some(&d) = it.peek() {
                    if d.is_alphanumeric() || d == '_' {
                        s.push(d);
                        it.next();
                    } else {
                        break;
                    }
                }
                if (s == "r" || s == "br")
                    && matches!(it.peek(), Some('#' | '"'))
                    && skip_raw_string(&mut it, &mut line)
                {
                    continue;
                }
                out.push((s, line));
            }
            c if c.is_whitespace() => {}
            c => out.push((c.to_string(), line)),
        }
    }
    out
}

/// Items with no `verus_spec` attribute.
#[must_use]
pub fn unspecified(items: &[FnItem]) -> Vec<FnItem> {
    items.iter().filter(|i| i.spec.is_none()).cloned().collect()
}

/// Items whose function-level specification has a `decreases` clause, i.e. which
/// Verus would accept as (possibly mutually) recursive.
#[must_use]
pub fn with_fn_decreases(items: &[FnItem]) -> Vec<FnItem> {
    items
        .iter()
        .filter(|i| i.spec.as_deref().is_some_and(|s| s.contains("decreases")))
        .cloned()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scan(s: &str) -> Vec<FnItem> {
        scan_text(Path::new("x.rs"), s)
    }

    #[test]
    fn verifier_attributes_are_found() {
        let names = |s: &str| -> Vec<String> {
            verifier_attributes(Path::new("x.rs"), s)
                .into_iter()
                .map(|a| a.name)
                .collect()
        };
        assert_eq!(
            names(
                "#[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]\nfn spin() {}\n"
            ),
            vec!["exec_allows_no_decreases_clause"]
        );
        assert_eq!(
            names(
                "verus! {\n#[verifier::external_body]\nfn f() {}\n#[verifier(external)]\nfn g() {}\n}\n"
            ),
            vec!["external_body", "external"]
        );
        assert_eq!(
            names(
                "/// hid by `verifier::spinoff_prover`\nfn f() {} // verifier::external\nlet my_verifier = 1;\n"
            ),
            Vec::<String>::new()
        );
        assert_eq!(
            names("#[cfg_attr(verus_keep_ghost, verifier::nonlinear)]\n"),
            vec!["nonlinear"]
        );
    }

    #[test]
    fn qualifiers_and_visibility() {
        for l in [
            "fn f() {}",
            "pub fn f() {}",
            "pub(crate) fn f() {}",
            "pub(super) const unsafe fn f() {}",
            "pub(in crate::a) fn f() {}",
            "unsafe extern \"C\" fn f() {}",
            "pub async fn f() {}",
        ] {
            assert!(is_fn_line(l), "{l}");
        }
        for l in [
            "let fn_ptr = f;",
            "struct Fn;",
            "pub type F = fn();",
            "impl Foo {",
        ] {
            assert!(!is_fn_line(l), "{l}");
        }
    }

    #[test]
    fn multiline_spec_attaches() {
        let items = scan(
            "#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    ensures r == x[0],\n))]\n#[inline]\npub fn f(x: &[u8]) -> u8 { x[0] }\n",
        );
        assert_eq!(items.len(), 1);
        assert!(items[0].spec.as_deref().unwrap().contains("ensures"));
    }

    #[test]
    fn spec_does_not_jump_over_other_items() {
        let items = scan(
            "#[cfg_attr(verus_keep_ghost, verus_spec(ensures true))]\nstruct S;\n\npub fn f() {}\n",
        );
        assert_eq!(unspecified(&items).len(), 1);
    }

    #[test]
    fn loop_spec_does_not_leak_to_next_fn() {
        let items = scan(
            "#[cfg_attr(verus_keep_ghost, verus_spec(ensures true))]\nfn f() {\n    #[cfg_attr(verus_keep_ghost, verus_spec(invariant true,))]\n    while g() {}\n}\nfn g() -> bool { false }\n",
        );
        let un = unspecified(&items);
        assert_eq!(un.len(), 1);
        assert!(un[0].signature.starts_with("fn g"));
    }

    #[test]
    fn verus_blocks_and_impl_methods() {
        let items = scan(
            "verus! {\npub open spec fn s() -> bool { true }\n} // verus!\nimpl A {\n    pub fn m(&self) {}\n}\n",
        );
        assert_eq!(items.len(), 1);
        assert!(items[0].signature.starts_with("pub fn m"));
        assert!(items[0].spec.is_none());
    }

    #[test]
    fn fn_level_decreases_is_reported() {
        let items = scan(
            "#[cfg_attr(verus_keep_ghost, verus_spec(\n    decreases n,\n))]\nfn f(n: u32) {}\n#[cfg_attr(verus_keep_ghost, verus_spec(ensures true))]\nfn g() {}\n",
        );
        let d = with_fn_decreases(&items);
        assert_eq!(d.len(), 1);
        assert!(d[0].signature.starts_with("fn f"));
    }

    #[test]
    fn trusted_calls_are_found() {
        let lines = |s: &str| -> Vec<usize> {
            trusted_calls(Path::new("x.rs"), s)
                .into_iter()
                .map(|a| a.line)
                .collect()
        };
        assert_eq!(
            lines(
                "fn f() {\n    #[verifier::trusted_call]\n    { g() }\n}\nverus! {\n#[verifier(trusted_call)] { h() }\n}\n#[cfg_attr(verus_keep_ghost, verifier::trusted_call)]\nfn k() {}\n"
            ),
            vec![2, 6, 8]
        );
        assert_eq!(
            lines(
                "// verifier::trusted_call\n/* trusted_call */\nconst S: &str = \"trusted_call\";\nconst R: &str = r#\"trusted_call \"# ;\nfn untrusted_call() {}\nlet c = 'x';\n"
            ),
            Vec::<usize>::new()
        );
    }

    #[test]
    fn allocator_impls_are_found() {
        let found = |s: &str| -> Vec<(usize, String)> {
            allocator_impls(Path::new("x.rs"), s)
                .into_iter()
                .map(|a| (a.line, a.name))
                .collect()
        };
        assert_eq!(
            found(
                "unsafe impl core::alloc::GlobalAlloc for Arena {}\nverus! {\nunsafe impl<'a, T: Copy> Allocator for &'a Pool<T> where T: Send {}\n}\nmacro_rules! m { ($t:ty) => { unsafe impl ::core::alloc::Allocator for $t {} } }\nunsafe impl<F: Fn() -> u8> std::alloc::GlobalAlloc\n    for Sys<F>\n{\n}\nunsafe impl core::alloc::StaticAllocator for Arena {}\n"
            ),
            vec![
                (1, "GlobalAlloc".to_string()),
                (3, "Allocator".to_string()),
                (5, "Allocator".to_string()),
                (6, "GlobalAlloc".to_string()),
                (10, "StaticAllocator".to_string()),
            ]
        );
        assert_eq!(
            found(
                "impl<A: Allocator> Vec2<A> { fn f(a: A) {} }\nimpl<A: GlobalAlloc> Wrap for Holder<A> {}\nimpl dyn Allocator {}\n// unsafe impl Allocator for X {}\nconst S: &str = \"unsafe impl GlobalAlloc for Y {}\";\nimpl AllocatorLike for Z {}\nfn g(x: impl Allocator) {}\nunsafe impl crate::AllocFreeDrop for Node {}\n"
            ),
            Vec::<(usize, String)>::new()
        );
    }
}
