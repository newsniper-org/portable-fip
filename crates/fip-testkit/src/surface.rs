// SPDX-License-Identifier: Apache-2.0
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
}
