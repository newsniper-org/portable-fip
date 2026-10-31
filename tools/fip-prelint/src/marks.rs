// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The contract attributes under the tool `fip`.
//!
//! - `#![cfg_attr(fip_prelint, fip::export)]` (crate root): use this crate's MIR for
//!   verdicts in other crates.
//! - `#[cfg_attr(fip_prelint, fip::mark(..))]` (functions): a root, emitted by
//!   `fip-macros`. Arguments, all optional except `kind`:
//!   `kind = "fip" | "fbip"`, `n = N` (allocation bound, default 0),
//!   `strict = true | false` (default false), `panic_macros = true | false`
//!   (default true), `param(name = K, ..)` (declared bounds of callable parameters).
//!
//! Any other name under `fip::` is rejected: rustc accepts unknown names under a
//! registered tool silently.

/// Names allowed under `fip::`.
pub const KNOWN: &[&str] = &["export", "mark"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Fip,
    Fbip,
}

/// A parsed `fip::mark(..)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mark {
    pub kind: Kind,
    pub n: u64,
    pub strict: bool,
    pub panic_macros: bool,
    pub params: Vec<(String, u64)>,
}

impl Mark {
    /// The attribute as the user wrote it (`#[fip]`, `#[fip(2)]`, `#[fbip]`, with
    /// `strict` if set).
    pub fn tag(&self) -> String {
        let mut args = Vec::new();
        if self.kind == Kind::Fip && self.n > 0 {
            args.push(self.n.to_string());
        }
        if self.strict {
            args.push("strict = true".to_string());
        }
        let kind = match self.kind {
            Kind::Fip => "fip",
            Kind::Fbip => "fbip",
        };
        if args.is_empty() {
            format!("#[{kind}]")
        } else {
            format!("#[{kind}({})]", args.join(", "))
        }
    }
}

/// Splits at top-level commas (not inside parentheses or string literals).
fn split_top(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0_i32;
    let mut in_str = false;
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '"' => in_str = !in_str,
            '(' if !in_str => depth += 1,
            ')' if !in_str => depth -= 1,
            ',' if !in_str && depth == 0 => {
                parts.push(std::mem::take(&mut cur));
                continue;
            }
            _ => {}
        }
        cur.push(c);
    }
    if !cur.trim().is_empty() {
        parts.push(cur);
    }
    parts.into_iter().map(|p| p.trim().to_string()).collect()
}

fn parse_bool(key: &str, v: &str) -> Result<bool, String> {
    match v {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err(format!("`{key}` takes `true` or `false`, found `{v}`")),
    }
}

fn parse_u64(key: &str, v: &str) -> Result<u64, String> {
    v.trim_end_matches("u64")
        .parse()
        .map_err(|_| format!("`{key}` takes an integer, found `{v}`"))
}

/// Parses the argument list of `fip::mark(..)` (without the parentheses).
pub fn parse_mark(args: &str) -> Result<Mark, String> {
    let mut kind = None;
    let mut mark = Mark {
        kind: Kind::Fip,
        n: 0,
        strict: false,
        panic_macros: true,
        params: Vec::new(),
    };
    for part in split_top(args) {
        if let Some(rest) = part.strip_prefix("param") {
            let rest = rest.trim();
            let inner = rest
                .strip_prefix('(')
                .and_then(|r| r.strip_suffix(')'))
                .ok_or_else(|| format!("expected `param(name = K, ..)`, found `{part}`"))?;
            for decl in split_top(inner) {
                let (name, k) = decl
                    .split_once('=')
                    .ok_or_else(|| format!("expected `name = K` in `param(..)`, found `{decl}`"))?;
                mark.params
                    .push((name.trim().to_string(), parse_u64("param", k.trim())?));
            }
            continue;
        }
        let (key, value) = part
            .split_once('=')
            .ok_or_else(|| format!("expected `key = value`, found `{part}`"))?;
        let (key, value) = (key.trim(), value.trim());
        match key {
            "kind" => {
                kind = Some(match value.trim_matches('"') {
                    "fip" => Kind::Fip,
                    "fbip" => Kind::Fbip,
                    other => return Err(format!("`kind` is \"fip\" or \"fbip\", found `{other}`")),
                });
            }
            "n" => mark.n = parse_u64(key, value)?,
            "strict" => mark.strict = parse_bool(key, value)?,
            "panic_macros" => mark.panic_macros = parse_bool(key, value)?,
            other => return Err(format!("unknown key `{other}` in `fip::mark(..)`")),
        }
    }
    mark.kind = kind
        .ok_or_else(|| "`fip::mark(..)` needs `kind = \"fip\"` or `kind = \"fbip\"`".to_string())?;
    if mark.kind == Kind::Fbip && mark.n != 0 {
        return Err("`kind = \"fbip\"` takes no bound `n`".to_string());
    }
    Ok(mark)
}

/// Extracts the argument list from a printed attribute `#[fip::mark(..)]`.
pub fn mark_args_of_printed(attr: &str) -> Option<&str> {
    let s = attr.trim();
    let s = s.strip_prefix("#[")?.strip_suffix(']')?.trim();
    let s = s.strip_prefix("fip::mark")?.trim();
    s.strip_prefix('(')?.strip_suffix(')')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_mark() {
        let m = parse_mark(
            r#"kind = "fip", n = 2, strict = true, panic_macros = false, param(g = 0, h = 1)"#,
        )
        .unwrap();
        assert_eq!(m.kind, Kind::Fip);
        assert_eq!(m.n, 2);
        assert!(m.strict && !m.panic_macros);
        assert_eq!(m.params, vec![("g".to_string(), 0), ("h".to_string(), 1)]);
        assert_eq!(m.tag(), "#[fip(2, strict = true)]");
    }

    #[test]
    fn printed_attribute() {
        let a = r#"#[fip::mark(kind = "fbip", n = 0, strict = false, panic_macros = true)]"#;
        let m = parse_mark(mark_args_of_printed(a).unwrap()).unwrap();
        assert_eq!(m.kind, Kind::Fbip);
        assert_eq!(m.tag(), "#[fbip]");
    }

    #[test]
    fn rejects_bad_marks() {
        assert!(parse_mark("n = 1").is_err());
        assert!(parse_mark(r#"kind = "fop""#).is_err());
        assert!(parse_mark(r#"kind = "fip", strict = yes"#).is_err());
        assert!(parse_mark(r#"kind = "fip", bound = 1"#).is_err());
    }
}
