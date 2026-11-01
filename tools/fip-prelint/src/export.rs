// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Does a crate root declare `fip::export`? (limits plan L10c)
//!
//! Decided before compilation (the role, and so the flags, depend on it), from the
//! crate root's **inner attributes as rustc parses them**: `rustc_parse` lexes the file
//! (comments, doc comments, raw strings and string literals are tokens or skipped, never
//! attribute text) and `Parser::parse_inner_attributes` returns the attributes at the
//! top of the file, before the first item. An attribute declares the export when it is
//!
//! - `#![fip::export]`, or
//! - `#![cfg_attr(<pred>, .., fip::export, ..)]` whose predicate is not known to be
//!   false, also nested (`cfg_attr(a, cfg_attr(b, fip::export))`).
//!
//! The predicate is evaluated three-valued: `fip_prelint` is true (the driver sets it),
//! `feature = ".."` and other options given as `--cfg` on the command line are known,
//! `not`/`all`/`any` combine; anything else (`unix`, `target_os = ..`) is unknown, and
//! unknown counts as declared. Both errors are sound: a crate taken for exported whose
//! attribute is inactive gets the driver's flags but no active `fip::export`, so its
//! functions stay `⊤` downstream; a crate not taken for exported is passed through and
//! is `⊤` (or the `export_unencoded` hard error if its attribute is active anyway).
//!
//! Not detectable before expansion: a crate attribute produced by a macro or
//! `include!`. Such a crate is passed through (`⊤` downstream). If the file does not
//! parse, the previous text test is the fallback (compilation reports the parse error
//! anyway).

use std::path::Path;
use std::sync::Arc;

use rustc_ast::ast::{AttrArgs, AttrKind, MetaItemInner, MetaItemKind, Path as AstPath};
use rustc_ast::token::TokenKind;
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_errors::DiagCtxt;
use rustc_errors::emitter::SilentEmitter;
use rustc_parse::lexer::StripTokens;
use rustc_parse::parser::{ForceCollect, Parser};
use rustc_session::parse::ParseSess;
use rustc_span::edition::Edition;
use rustc_span::source_map::{FilePathMapping, SourceMap};
use rustc_span::{FileName, Symbol};

/// Three-valued result of a `cfg` predicate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tri {
    True,
    False,
    Unknown,
}

impl Tri {
    fn not(self) -> Tri {
        match self {
            Tri::True => Tri::False,
            Tri::False => Tri::True,
            Tri::Unknown => Tri::Unknown,
        }
    }
}

/// The `--cfg` options of the command line: `name` or `name="value"`.
#[derive(Default, Debug)]
pub struct Cfgs {
    names: Vec<String>,
    pairs: Vec<(String, String)>,
}

impl Cfgs {
    /// From the rustc arguments (`--cfg x`, `--cfg=x`, `--cfg feature="y"`).
    pub fn from_args(args: &[String]) -> Cfgs {
        let mut c = Cfgs::default();
        let mut it = args.iter();
        while let Some(a) = it.next() {
            let spec = if a == "--cfg" {
                it.next().map(String::as_str)
            } else {
                a.strip_prefix("--cfg=")
            };
            let Some(spec) = spec else { continue };
            match spec.split_once('=') {
                Some((k, v)) => c
                    .pairs
                    .push((k.trim().to_string(), v.trim().trim_matches('"').to_string())),
                None => c.names.push(spec.trim().to_string()),
            }
        }
        c
    }

    fn name(&self, n: &str) -> Tri {
        if n == "fip_prelint" || self.names.iter().any(|x| x == n) {
            Tri::True
        } else {
            Tri::Unknown
        }
    }

    fn pair(&self, k: &str, v: &str) -> Tri {
        if self.pairs.iter().any(|(a, b)| a == k && b == v) {
            Tri::True
        } else if k == "feature" {
            // cargo passes every enabled feature.
            Tri::False
        } else {
            Tri::Unknown
        }
    }
}

fn path_is(p: &AstPath, segs: &[&str]) -> bool {
    p.segments.len() == segs.len()
        && p.segments
            .iter()
            .zip(segs)
            .all(|(s, w)| s.ident.name.as_str() == *w)
}

fn eval(pred: &MetaItemInner, cfgs: &Cfgs) -> Tri {
    let MetaItemInner::MetaItem(mi) = pred else {
        // `cfg(true)`/`cfg(false)` literals.
        return match pred {
            MetaItemInner::Lit(l) if l.symbol == Symbol::intern("true") => Tri::True,
            MetaItemInner::Lit(l) if l.symbol == Symbol::intern("false") => Tri::False,
            _ => Tri::Unknown,
        };
    };
    let name = if mi.path.segments.len() == 1 {
        mi.path.segments[0].ident.name.as_str().to_string()
    } else {
        return Tri::Unknown;
    };
    match &mi.kind {
        MetaItemKind::Word => cfgs.name(&name),
        MetaItemKind::NameValue(lit) => cfgs.pair(&name, lit.symbol.as_str()),
        MetaItemKind::List(items) => match name.as_str() {
            "not" if items.len() == 1 => eval(&items[0], cfgs).not(),
            "all" => {
                let mut acc = Tri::True;
                for i in items {
                    match eval(i, cfgs) {
                        Tri::False => return Tri::False,
                        Tri::Unknown => acc = Tri::Unknown,
                        Tri::True => {}
                    }
                }
                acc
            }
            "any" => {
                let mut acc = Tri::False;
                for i in items {
                    match eval(i, cfgs) {
                        Tri::True => return Tri::True,
                        Tri::Unknown => acc = Tri::Unknown,
                        Tri::False => {}
                    }
                }
                acc
            }
            _ => Tri::Unknown,
        },
    }
}

/// Splits a token stream at its top-level commas.
fn split_commas(ts: &TokenStream) -> Vec<TokenStream> {
    let mut parts = vec![Vec::new()];
    for tt in ts.iter() {
        if let TokenTree::Token(tok, _) = tt
            && tok.kind == TokenKind::Comma
        {
            parts.push(Vec::new());
        } else if let Some(last) = parts.last_mut() {
            last.push(tt.clone());
        }
    }
    if parts.last().is_some_and(Vec::is_empty) {
        parts.pop();
    }
    parts.into_iter().map(TokenStream::new).collect()
}

/// Whether the attribute item `path args` declares `fip::export` (`cfg_attr` nesting
/// followed). `Err` if a `cfg_attr` does not parse.
fn item_declares(
    psess: &ParseSess,
    path: &AstPath,
    args: &AttrArgs,
    cfgs: &Cfgs,
) -> Result<bool, ()> {
    if path_is(path, &["fip", "export"]) {
        return Ok(true);
    }
    if !path_is(path, &["cfg_attr"]) {
        return Ok(false);
    }
    let AttrArgs::Delimited(d) = args else {
        return Err(());
    };
    let parts = split_commas(&d.tokens);
    let Some((pred, items)) = parts.split_first() else {
        return Err(());
    };
    let mut p = Parser::new(psess, pred.clone(), None);
    let pred = match p.parse_meta_item_inner() {
        Ok(m) => m,
        Err(e) => {
            e.cancel();
            return Err(());
        }
    };
    if p.token.kind != TokenKind::Eof {
        return Err(());
    }
    if eval(&pred, cfgs) == Tri::False {
        return Ok(false);
    }
    for it in items {
        let mut p = Parser::new(psess, it.clone(), None);
        let item = match p.parse_attr_item(ForceCollect::No) {
            Ok(i) => i.node,
            Err(e) => {
                e.cancel();
                return Err(());
            }
        };
        if p.token.kind != TokenKind::Eof {
            return Err(());
        }
        if item_declares(psess, &item.path, &item.args, cfgs)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Parses `src` (a crate root) and decides; `None` if it does not parse.
pub fn declares_in(src: String, edition: Edition, cfgs: &Cfgs) -> Option<bool> {
    rustc_span::create_session_globals_then(edition, &[], None, || {
        let sm = Arc::new(SourceMap::new(FilePathMapping::empty()));
        let psess = ParseSess::with_dcx(DiagCtxt::new(Box::new(SilentEmitter)), sm);
        let mut parser = match rustc_parse::new_parser_from_source_str(
            &psess,
            FileName::Custom("crate root".to_string()),
            src,
            StripTokens::ShebangAndFrontmatter,
        ) {
            Ok(p) => p,
            Err(errs) => {
                for e in errs {
                    e.cancel();
                }
                return None;
            }
        };
        let attrs = match parser.parse_inner_attributes() {
            Ok(a) => a,
            Err(e) => {
                e.cancel();
                return None;
            }
        };
        let mut found = false;
        for a in &attrs {
            if let AttrKind::Normal(n) = &a.kind {
                match item_declares(&psess, &n.item.path, &n.item.args, cfgs) {
                    Ok(true) => found = true,
                    Ok(false) => {}
                    Err(()) => return None,
                }
            }
        }
        Some(found)
    })
}

/// The pre-parser text test, used only when the crate root does not parse.
fn declares_by_text(text: &str) -> bool {
    let compact: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    compact.contains("#![cfg_attr(fip_prelint,fip::export)]") || compact.contains("#![fip::export]")
}

/// `true` if the crate root at `root` declares `fip::export` (see the module
/// documentation). Runs on its own thread: the parser needs rustc's session globals,
/// which must not be set on the thread that later runs the compiler.
pub fn declares_export(root: &Path, args: &[String]) -> bool {
    let Ok(text) = std::fs::read_to_string(root) else {
        return false;
    };
    let edition = args
        .iter()
        .position(|a| a == "--edition")
        .and_then(|i| args.get(i + 1))
        .map(String::as_str)
        .or_else(|| args.iter().find_map(|a| a.strip_prefix("--edition=")))
        .and_then(|e| e.parse::<Edition>().ok())
        .unwrap_or(Edition::Edition2015);
    let cfgs = Cfgs::from_args(args);
    let t = text.clone();
    let parsed = std::thread::spawn(move || declares_in(t, edition, &cfgs))
        .join()
        .ok()
        .flatten();
    parsed.unwrap_or_else(|| declares_by_text(&text))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn d(src: &str) -> Option<bool> {
        let src = src.to_string();
        std::thread::spawn(move || {
            let cfgs = Cfgs::from_args(&[
                "--cfg".to_string(),
                "feature=\"on\"".to_string(),
                "--cfg".to_string(),
                "set".to_string(),
            ]);
            declares_in(src, Edition::Edition2024, &cfgs)
        })
        .join()
        .unwrap()
    }

    #[test]
    fn plain_forms() {
        assert_eq!(
            d("#![cfg_attr(fip_prelint, fip::export)]\npub fn f() {}"),
            Some(true)
        );
        assert_eq!(d("#![fip::export]\n"), Some(true));
        assert_eq!(
            d("//! docs\n#![no_std]\n#![cfg_attr(fip_prelint, fip::export)]\n"),
            Some(true)
        );
        assert_eq!(d("#!/usr/bin/env run\n#![fip::export]\n"), Some(true));
    }

    #[test]
    fn cfg_attr_forms() {
        // Several attributes, a comment inside, nesting, combinators.
        assert_eq!(
            d("#![cfg_attr(fip_prelint, allow(dead_code), fip::export)]"),
            Some(true)
        );
        assert_eq!(
            d("#![cfg_attr(fip_prelint, /* opt in */ fip::export)]"),
            Some(true)
        );
        assert_eq!(
            d("#![cfg_attr(all(fip_prelint, set), cfg_attr(fip_prelint, fip::export))]"),
            Some(true)
        );
        assert_eq!(
            d("#![cfg_attr(any(nowhere, fip_prelint), fip::export)]"),
            Some(true)
        );
        assert_eq!(d("#![cfg_attr(feature = \"on\", fip::export)]"), Some(true));
        // Unknown predicate: counted as declared (sound either way).
        assert_eq!(d("#![cfg_attr(unix, fip::export)]"), Some(true));
        // Known false.
        assert_eq!(
            d("#![cfg_attr(not(fip_prelint), fip::export)]"),
            Some(false)
        );
        assert_eq!(
            d("#![cfg_attr(feature = \"off\", fip::export)]"),
            Some(false)
        );
        assert_eq!(
            d("#![cfg_attr(all(fip_prelint, not(set)), fip::export)]"),
            Some(false)
        );
        assert_eq!(
            d("#![cfg_attr(fip_prelint, cfg_attr(false, fip::export))]"),
            Some(false)
        );
        // Other attributes.
        assert_eq!(d("#![cfg_attr(fip_prelint, fip::exported)]"), Some(false));
        assert_eq!(d("#![cfg_attr(fip_prelint, export)]"), Some(false));
    }

    #[test]
    fn not_attributes() {
        assert_eq!(
            d("// #![cfg_attr(fip_prelint, fip::export)]\npub fn f() {}"),
            Some(false)
        );
        assert_eq!(d("/* #![fip::export] */\npub fn f() {}"), Some(false));
        assert_eq!(
            d("//! `#![cfg_attr(fip_prelint, fip::export)]`\npub fn f() {}"),
            Some(false)
        );
        assert_eq!(
            d("pub const S: &str = r#\"#![cfg_attr(fip_prelint, fip::export)]\"#;"),
            Some(false)
        );
        // Not at the top: an inner attribute after an item is not a crate attribute.
        assert_eq!(d("pub fn f() {}\nmod m { #![fip::export] }"), Some(false));
        assert_eq!(d("#![doc = \"#![fip::export]\"]"), Some(false));
    }

    #[test]
    fn unparsable_falls_back() {
        assert_eq!(d("#![cfg_attr(fip_prelint fip::export)]"), None);
        assert!(declares_by_text("#![cfg_attr(fip_prelint, fip::export)]"));
    }
}
