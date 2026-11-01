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
//!   (default true), `param(name = K, ..)` (declared bounds of callable parameters:
//!   of a generic type, a function pointer or `&dyn Fn*`/`&dyn FipFn`). On a trait
//!   method declaration (written by hand): a contract that every implementation is
//!   checked against and that dynamic calls of the method cost.
//! - `#[cfg_attr(fip_prelint, fip::alloc_source)]`, `fip::alloc_source(n = N)`
//!   (`N ≥ 1`, default 1) and `#[cfg_attr(fip_prelint, fip::free_source)]`
//!   (functions, methods, trait method declarations, foreign functions): a declared
//!   allocation or free source. A call counts `N` allocations or a possible free (both
//!   attributes: a reallocation) at the call site; the body is not analysed (allocator
//!   internals are outside FIP). On a trait method declaration the mark applies to
//!   every implementation.
//!
//! - `#[cfg_attr(fip_prelint, fip::requires(i < j, j < xs.len()))]` (functions): a
//!   declared precondition (grammar: `fip_lint_rules::requires`), assumed in the
//!   function when it is a root and checked at every analysed call site; a function
//!   with a precondition used as a function value is reported there.
//!
//! Any other name under `fip::` is rejected: rustc accepts unknown names under a
//! registered tool silently.

/// Names allowed under `fip::`.
pub const KNOWN: &[&str] = &["export", "mark", "alloc_source", "free_source", "requires"];

/// The conjuncts of the printed `fip::requires(..)` attributes of one function
/// (several attributes are one conjunction); `Ok(None)` if it has none.
pub fn requires_of_printed<'a>(
    attrs: impl IntoIterator<Item = &'a str>,
) -> Result<Option<Vec<fip_lint_rules::requires::Conjunct>>, String> {
    let mut found: Option<Vec<fip_lint_rules::requires::Conjunct>> = None;
    for attr in attrs {
        let Some(("requires", args)) = tool_attr_of_printed(attr) else {
            continue;
        };
        let cs = fip_lint_rules::requires::parse(args.unwrap_or(""))?;
        found.get_or_insert_with(Vec::new).extend(cs);
    }
    Ok(found)
}

/// What one call of an allocation or free source does.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Source {
    /// Allocations per call (0: none).
    pub alloc: u64,
    /// A possible free.
    pub free: bool,
}

impl Source {
    /// Both declarations of one function (or of an impl method and its trait
    /// method): the larger allocation count and any free.
    #[must_use]
    pub fn merge(self, o: Source) -> Source {
        Source {
            alloc: self.alloc.max(o.alloc),
            free: self.free || o.free,
        }
    }
}

/// `(name, args)` of a printed tool attribute `#[fip::name]` or `#[fip::name(args)]`.
pub fn tool_attr_of_printed(attr: &str) -> Option<(&str, Option<&str>)> {
    let s = attr.trim();
    let s = s.strip_prefix("#[")?.strip_suffix(']')?.trim();
    let s = s.strip_prefix("fip::")?;
    match s.find('(') {
        Some(i) => {
            let args = s[i..].trim().strip_prefix('(')?.strip_suffix(')')?;
            Some((s[..i].trim(), Some(args)))
        }
        None => Some((s.trim(), None)),
    }
}

/// Allocations per call declared by `fip::alloc_source` (`args`: the list inside the
/// parentheses, if any). `n = 0` is rejected: it would declare an allocation-free
/// function whose body is never analysed.
pub fn parse_alloc_source(args: Option<&str>) -> Result<u64, String> {
    let mut n = 1;
    for part in split_top(args.unwrap_or("")) {
        let (key, value) = part.split_once('=').ok_or_else(|| {
            format!("expected `n = N` in `fip::alloc_source(..)`, found `{part}`")
        })?;
        match key.trim() {
            "n" => n = parse_u64("n", value.trim())?,
            other => return Err(format!("unknown key `{other}` in `fip::alloc_source(..)`")),
        }
    }
    if n == 0 {
        return Err(
            "`fip::alloc_source(n = 0)` would declare an allocation-free function without checking it; the count is at least 1"
                .to_string(),
        );
    }
    Ok(n)
}

/// `fip::free_source` takes no arguments.
pub fn parse_free_source(args: Option<&str>) -> Result<(), String> {
    match args.map(str::trim) {
        None | Some("") => Ok(()),
        Some(a) => Err(format!(
            "`fip::free_source` takes no arguments, found `{a}`"
        )),
    }
}

/// The source declared by the printed tool attributes of one function: `Ok(None)` if
/// it has neither `fip::alloc_source` nor `fip::free_source`.
pub fn source_of_printed<'a>(
    attrs: impl IntoIterator<Item = &'a str>,
) -> Result<Option<Source>, String> {
    let mut found: Option<Source> = None;
    for attr in attrs {
        let Some((name, args)) = tool_attr_of_printed(attr) else {
            continue;
        };
        let s = match name {
            "alloc_source" => Source {
                alloc: parse_alloc_source(args)?,
                free: false,
            },
            "free_source" => {
                parse_free_source(args)?;
                Source {
                    alloc: 0,
                    free: true,
                }
            }
            _ => continue,
        };
        found = Some(found.map_or(s, |f| f.merge(s)));
    }
    Ok(found)
}

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

    #[test]
    fn source_marks() {
        let s = |a: &[&str]| source_of_printed(a.iter().copied());
        assert_eq!(
            s(&["#[fip::alloc_source]"]),
            Ok(Some(Source {
                alloc: 1,
                free: false
            }))
        );
        assert_eq!(
            s(&["#[fip::alloc_source(n = 3)]"]),
            Ok(Some(Source {
                alloc: 3,
                free: false
            }))
        );
        assert_eq!(
            s(&["#[fip::free_source]", "#[fip::alloc_source]"]),
            Ok(Some(Source {
                alloc: 1,
                free: true
            }))
        );
        assert_eq!(s(&[r#"#[fip::mark(kind = "fip")]"#]), Ok(None));
        assert!(s(&["#[fip::alloc_source(n = 0)]"]).is_err());
        assert!(s(&["#[fip::alloc_source(count = 2)]"]).is_err());
        assert!(s(&["#[fip::alloc_source(2)]"]).is_err());
        assert!(s(&["#[fip::free_source(n = 1)]"]).is_err());
        assert_eq!(
            tool_attr_of_printed("#[fip::alloc_source(n = 2)]"),
            Some(("alloc_source", Some("n = 2")))
        );
        assert_eq!(
            tool_attr_of_printed("#[fip::free_source]"),
            Some(("free_source", None))
        );
    }
}
