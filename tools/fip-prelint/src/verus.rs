// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Verus as an oracle for panic freedom (top plan T13.4): the sidecar of verified
//! bodies, shared by its generator (`cargo fip-prelint --verus-sidecar`) and the
//! driver that reads it. No rustc dependency.
//!
//! A `--no-cheating` Verus run of a whole crate writes the sidecar: per exec function
//! Verus verified (taken from the VIR Verus logs, `--log vir`, of a run whose
//! `--output-json` result is a success without errors over the entire crate), its
//! path, file and the SHA-256 of its **item text**: the function from its first outer
//! attribute or doc comment (the `verus_spec` attribute holds the spec) to the closing
//! brace of its body ([`item_region`]). The stamp names the Verus version and commit,
//! the Z3 version and the flags; every source file of the run is hashed too (callee
//! specs, spec functions and imported crates are part of what a proof relied on).
//!
//! The driver drops a body-local `Assert` panic site (overflow, bounds, division
//! checks) of a listed function only if the sidecar's stamp equals the trusted pin
//! (`verus-trusted.txt`), every source hash and the item hash match the files it
//! analyses; otherwise the site stays reported, with the reason.
//!
//! Format (one item per line, `#` comments, blank lines ignored):
//!
//! ```text
//! fip-prelint verus sidecar
//! format 4
//! crate <crate name>
//! verus <version> <commit>
//! z3 <version>
//! toolchain <rust toolchain of the Verus build>
//! flags <verus flags relevant to trust: --no-cheating, and -V alloc-check if given>
//! cfg <target triple of the run> <its cargo features, comma-separated, or ->
//! verified <number Verus reported verified>
//! source <path relative to the sidecar's directory> <sha256>
//! fn <crate>::<path> <file relative to the sidecar's directory>:<line> <sha256 of the item text> <requires | ->
//! skip <crate>::<path> <reason>
//! ```
//!
//! Format 3 (2026-11-04) added the `cfg` line: the driver uses a sidecar only for a
//! build of the same target with the same features. The generator also refuses a crate
//! whose sources test any other cfg ([`crate_cfg_conflict`]) and lists no item whose
//! text holds a `cfg` other than the Verus-only attribute forms ([`cfg_conflict`]).
//!
//! Format 4 (2026-11-04, re-audit N3/N4) changes no line, only what a sidecar of
//! that format guarantees, so the driver refuses format 3 sidecars: every source of
//! the run is scanned (not only `src/`), macros that can build a cfg test or read the
//! environment are refused ([`macro_conflict`]), and a function verified against the
//! specification of a function skipped because its code differs between the builds is
//! skipped too (`relies on the specification of ..`).
//!
//! `<line>` is the 1-based line where the item text starts. In `<path>` every impl
//! block is the segment `{impl}` ([`impl_key`]): Verus names an impl block
//! `impl&%N` and rustc `{impl#N}`, both with the `DefPath` disambiguator of their own
//! build, and the two builds differ wherever `cfg(verus_keep_ghost)` adds or removes an
//! impl block (measured on `fip-strict`: Verus's `impl&%8` is rustc's `{impl#1}`). An
//! impl method is therefore identified by its path without the number, its file and
//! the line of its item text, never by the number.

use std::fmt::Write as _;

/// Version of the format.
pub const FORMAT: u32 = 4;

/// The Verus flag without which no sidecar is written or used.
pub const NO_CHEATING: &str = "--no-cheating";

/// The value of the Verus fork's `-V alloc-check` option (`allocates` bounds checked;
/// decision record 2026-11-06-redesign-verus-allocates). Recorded in `flags` as the two
/// words `-V alloc-check` when the run used it; not yet required by the driver.
pub const ALLOC_CHECK: &str = "alloc-check";

// ---------------------------------------------------------------------------------
// SHA-256 (FIPS 180-4), dependency-free.

const K: [u32; 64] = [
    0x428a_2f98,
    0x7137_4491,
    0xb5c0_fbcf,
    0xe9b5_dba5,
    0x3956_c25b,
    0x59f1_11f1,
    0x923f_82a4,
    0xab1c_5ed5,
    0xd807_aa98,
    0x1283_5b01,
    0x2431_85be,
    0x550c_7dc3,
    0x72be_5d74,
    0x80de_b1fe,
    0x9bdc_06a7,
    0xc19b_f174,
    0xe49b_69c1,
    0xefbe_4786,
    0x0fc1_9dc6,
    0x240c_a1cc,
    0x2de9_2c6f,
    0x4a74_84aa,
    0x5cb0_a9dc,
    0x76f9_88da,
    0x983e_5152,
    0xa831_c66d,
    0xb003_27c8,
    0xbf59_7fc7,
    0xc6e0_0bf3,
    0xd5a7_9147,
    0x06ca_6351,
    0x1429_2967,
    0x27b7_0a85,
    0x2e1b_2138,
    0x4d2c_6dfc,
    0x5338_0d13,
    0x650a_7354,
    0x766a_0abb,
    0x81c2_c92e,
    0x9272_2c85,
    0xa2bf_e8a1,
    0xa81a_664b,
    0xc24b_8b70,
    0xc76c_51a3,
    0xd192_e819,
    0xd699_0624,
    0xf40e_3585,
    0x106a_a070,
    0x19a4_c116,
    0x1e37_6c08,
    0x2748_774c,
    0x34b0_bcb5,
    0x391c_0cb3,
    0x4ed8_aa4a,
    0x5b9c_ca4f,
    0x682e_6ff3,
    0x748f_82ee,
    0x78a5_636f,
    0x84c8_7814,
    0x8cc7_0208,
    0x90be_fffa,
    0xa450_6ceb,
    0xbef9_a3f7,
    0xc671_78f2,
];

/// SHA-256 of `data`, lower-case hex.
pub fn sha256_hex(data: &[u8]) -> String {
    let mut h: [u32; 8] = [
        0x6a09_e667,
        0xbb67_ae85,
        0x3c6e_f372,
        0xa54f_f53a,
        0x510e_527f,
        0x9b05_688c,
        0x1f83_d9ab,
        0x5be0_cd19,
    ];
    let mut msg = data.to_vec();
    let bits = (data.len() as u64).wrapping_mul(8);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bits.to_be_bytes());
    for chunk in msg.chunks(64) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (x, y) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *x = x.wrapping_add(y);
        }
    }
    let mut out = String::with_capacity(64);
    for x in h {
        let _ = write!(out, "{x:08x}");
    }
    out
}

// ---------------------------------------------------------------------------------
// A small Rust lexer: enough to skip comments, strings and character literals.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tok {
    Ws,
    Comment,
    /// `///` or `/** .. */`: an outer doc comment (an attribute).
    OuterDoc,
    Ident,
    Literal,
    Lifetime,
    Punct(u8),
}

fn is_ident_start(b: u8) -> bool {
    b == b'_' || b.is_ascii_alphabetic() || b >= 0x80
}

fn is_ident_continue(b: u8) -> bool {
    b == b'_' || b.is_ascii_alphanumeric() || b >= 0x80
}

/// Length in bytes of the UTF-8 character starting with `b`.
fn utf8_len(b: u8) -> usize {
    match b {
        0xF0..=0xFF => 4,
        0xE0..=0xEF => 3,
        0xC0..=0xDF => 2,
        _ => 1,
    }
}

/// Tokens of `src` as `(kind, start, end)` byte ranges covering the whole text.
fn lex(src: &str) -> Vec<(Tok, usize, usize)> {
    let s = src.as_bytes();
    let n = s.len();
    let mut out = Vec::new();
    let mut i = 0;
    while i < n {
        let start = i;
        let b = s[i];
        let kind = if b.is_ascii_whitespace() {
            while i < n && s[i].is_ascii_whitespace() {
                i += 1;
            }
            Tok::Ws
        } else if b == b'/' && s.get(i + 1) == Some(&b'/') {
            while i < n && s[i] != b'\n' {
                i += 1;
            }
            let text = &s[start..i];
            if text.starts_with(b"///") && !text.starts_with(b"////") {
                Tok::OuterDoc
            } else {
                Tok::Comment
            }
        } else if b == b'/' && s.get(i + 1) == Some(&b'*') {
            let mut depth = 0usize;
            while i < n {
                if s[i] == b'/' && s.get(i + 1) == Some(&b'*') {
                    depth += 1;
                    i += 2;
                } else if s[i] == b'*' && s.get(i + 1) == Some(&b'/') {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            let text = &s[start..i];
            if text.starts_with(b"/**") && !text.starts_with(b"/***") && text != b"/**/" {
                Tok::OuterDoc
            } else {
                Tok::Comment
            }
        } else if b == b'"' {
            i = skip_string(s, i);
            Tok::Literal
        } else if b == b'\'' {
            // A character literal `'x'`, `'\n'`, or a lifetime / label `'a`.
            if s.get(i + 1) == Some(&b'\\') {
                // The quote, the backslash and the escaped character, then up to the
                // closing quote (`'\u{..}'`).
                i += 3;
                while i < n && s[i] != b'\'' {
                    i += 1;
                }
                i = (i + 1).min(n);
                Tok::Literal
            } else if i + 1 < n {
                let l = utf8_len(s[i + 1]);
                if s.get(i + 1 + l) == Some(&b'\'') {
                    i += 2 + l;
                    Tok::Literal
                } else {
                    i += 1;
                    while i < n && is_ident_continue(s[i]) {
                        i += 1;
                    }
                    Tok::Lifetime
                }
            } else {
                i += 1;
                Tok::Punct(b'\'')
            }
        } else if is_ident_start(b) {
            while i < n && is_ident_continue(s[i]) {
                i += 1;
            }
            let word = &s[start..i];
            let raw_prefix = matches!(word, b"r" | b"br" | b"cr");
            let str_prefix = matches!(word, b"b" | b"c");
            if raw_prefix && matches!(s.get(i), Some(b'"' | b'#')) {
                // A raw string `r#".."#`, unless it is a raw identifier `r#name`.
                let mut j = i;
                while j < n && s[j] == b'#' {
                    j += 1;
                }
                if s.get(j) == Some(&b'"') {
                    let hashes = j - i;
                    j += 1;
                    loop {
                        if j >= n {
                            break;
                        }
                        if s[j] == b'"'
                            && s[j + 1..]
                                .iter()
                                .take(hashes)
                                .filter(|&&c| c == b'#')
                                .count()
                                == hashes
                        {
                            j += 1 + hashes;
                            break;
                        }
                        j += 1;
                    }
                    i = j.min(n);
                    Tok::Literal
                } else {
                    Tok::Ident
                }
            } else if str_prefix && s.get(i) == Some(&b'"') {
                i = skip_string(s, i);
                Tok::Literal
            } else if word == b"b" && s.get(i) == Some(&b'\'') {
                i += 1;
                if s.get(i) == Some(&b'\\') {
                    i += 2;
                }
                while i < n && s[i] != b'\'' {
                    i += 1;
                }
                i = (i + 1).min(n);
                Tok::Literal
            } else {
                Tok::Ident
            }
        } else if b.is_ascii_digit() {
            while i < n
                && (is_ident_continue(s[i])
                    || (s[i] == b'.' && s.get(i + 1).is_some_and(u8::is_ascii_digit)))
            {
                i += 1;
            }
            Tok::Literal
        } else {
            i += utf8_len(b).max(1);
            Tok::Punct(b)
        };
        let end = i.min(n);
        out.push((kind, start, end));
        i = end;
    }
    out
}

/// End of the string literal whose opening quote is at `i`.
fn skip_string(s: &[u8], mut i: usize) -> usize {
    let n = s.len();
    i += 1;
    while i < n && s[i] != b'"' {
        i += if s[i] == b'\\' { 2 } else { 1 };
    }
    (i + 1).min(n)
}

/// The item text of a function: from `start` (the first token of the function after
/// its attributes, its visibility or `fn`), extended backwards over the outer
/// attributes (`#[..]`) and outer doc comments directly in front of it (comments and
/// whitespace between them included), to `end` (just after the closing brace of the
/// body). `None` if `start` is not a token boundary or `end` does not follow a `}`.
pub fn item_region(src: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    if end > src.len() || start >= end || !src.is_char_boundary(end) {
        return None;
    }
    if !src[..end].ends_with('}') {
        return None;
    }
    Some((attrs_start(src, start)?, end))
}

/// `start` (a token boundary) extended backwards over the outer attributes and outer
/// doc comments directly in front of it, as in [`item_region`].
pub fn attrs_start(src: &str, start: usize) -> Option<usize> {
    let toks = lex(src);
    let mut k = toks.iter().position(|t| t.1 == start)?;
    if matches!(toks[k].0, Tok::Ws | Tok::Comment) {
        return None;
    }
    let mut lo = start;
    // The previous token that is not whitespace or a plain comment.
    while let Some(j) = (0..k)
        .rev()
        .find(|&j| !matches!(toks[j].0, Tok::Ws | Tok::Comment))
    {
        match toks[j].0 {
            Tok::OuterDoc => {
                lo = toks[j].1;
                k = j;
            }
            Tok::Punct(b']') => {
                let mut depth = 0usize;
                let mut open = None;
                for m in (0..=j).rev() {
                    match toks[m].0 {
                        Tok::Punct(b']') => depth += 1,
                        Tok::Punct(b'[') => {
                            depth -= 1;
                            if depth == 0 {
                                open = Some(m);
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                let Some(open) = open else { break };
                let Some(p) = (0..open)
                    .rev()
                    .find(|&p| !matches!(toks[p].0, Tok::Ws | Tok::Comment))
                else {
                    break;
                };
                if toks[p].0 != Tok::Punct(b'#') {
                    break;
                }
                lo = toks[p].1;
                k = p;
            }
            _ => break,
        }
    }
    Some(lo)
}

/// SHA-256 of the item text ([`item_region`]).
pub fn item_hash(src: &str, start: usize, end: usize) -> Option<String> {
    let (lo, hi) = item_region(src, start, end)?;
    Some(sha256_hex(&src.as_bytes()[lo..hi]))
}

/// Byte offset of 1-based `line` and 1-based character column `col` (rustc's span
/// notation) in `src`.
pub fn offset_of(src: &str, line: usize, col: usize) -> Option<usize> {
    let mut off = 0usize;
    for (i, l) in src.split_inclusive('\n').enumerate() {
        if i + 1 == line {
            let mut chars = l.char_indices();
            let mut at = 0usize;
            for _ in 1..col {
                let (_, c) = chars.next()?;
                at += c.len_utf8();
            }
            return Some(off + at);
        }
        off += l.len();
    }
    // Just past the last line (an empty last line).
    (line == src.split_inclusive('\n').count() + 1 && col == 1).then_some(off)
}

/// One `cfg(..)`, `cfg!(..)` or `cfg_attr(..)` in a text: its kind and its top-level
/// arguments, each as its tokens without whitespace, comments or doc comments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CfgUse {
    /// `cfg`, `cfg!` or `cfg_attr`.
    pub kind: &'static str,
    pub args: Vec<String>,
}

impl CfgUse {
    fn shown(&self) -> String {
        let open = if self.kind == "cfg!" {
            "cfg!("
        } else if self.kind == "cfg" {
            "cfg("
        } else {
            "cfg_attr("
        };
        let text = format!("{open}{})", self.args.join(", "));
        let mut end = text.len().min(64);
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        if end < text.len() {
            format!("`{}..`", &text[..end])
        } else {
            format!("`{text}`")
        }
    }
}

/// Every `cfg(..)`, `cfg!(..)` and `cfg_attr(..)` of `text`, nested ones included
/// (outside comments and string literals).
pub fn cfg_uses(text: &str) -> Vec<CfgUse> {
    let toks: Vec<(Tok, usize, usize)> = lex(text)
        .into_iter()
        .filter(|t| !matches!(t.0, Tok::Ws | Tok::Comment | Tok::OuterDoc))
        .collect();
    let tx = |k: usize| &text[toks[k].1..toks[k].2];
    let mut out = Vec::new();
    for k in 0..toks.len() {
        if toks[k].0 != Tok::Ident {
            continue;
        }
        let (kind, open) = match tx(k) {
            "cfg" if toks.get(k + 1).is_some_and(|t| t.0 == Tok::Punct(b'(')) => ("cfg", k + 1),
            "cfg"
                if toks.get(k + 1).is_some_and(|t| t.0 == Tok::Punct(b'!'))
                    && toks.get(k + 2).is_some_and(|t| t.0 == Tok::Punct(b'(')) =>
            {
                ("cfg!", k + 2)
            }
            "cfg_attr" if toks.get(k + 1).is_some_and(|t| t.0 == Tok::Punct(b'(')) => {
                ("cfg_attr", k + 1)
            }
            _ => continue,
        };
        let mut args = vec![String::new()];
        let mut depth = 0usize;
        let mut m = open;
        while m < toks.len() {
            match toks[m].0 {
                Tok::Punct(b'(' | b'[' | b'{') => {
                    depth += 1;
                    if depth == 1 {
                        m += 1;
                        continue;
                    }
                }
                Tok::Punct(b')' | b']' | b'}') => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                Tok::Punct(b',') if depth == 1 => {
                    args.push(String::new());
                    m += 1;
                    continue;
                }
                _ => {}
            }
            if let Some(a) = args.last_mut() {
                a.push_str(tx(m));
            }
            m += 1;
        }
        if args.last().is_some_and(String::is_empty) {
            args.pop();
        }
        out.push(CfgUse { kind, args });
    }
    out
}

/// `true` if every attribute of a `cfg_attr` payload starts with one of `prefixes` (an
/// entry ending in `(` or `::` is a prefix, any other is the whole attribute or its
/// name before `(`).
fn payload_only(payload: &[String], prefixes: &[&str]) -> bool {
    !payload.is_empty()
        && payload.iter().all(|a| {
            prefixes.iter().any(|p| {
                if p.ends_with('(') || p.ends_with("::") {
                    a.starts_with(p)
                } else {
                    a == p || a.starts_with(&format!("{p}("))
                }
            })
        })
}

/// Why an item text may compile to other code for the driver than for Verus, if it
/// may (top plan T13.4, tightened 2026-11-04). Verus compiles the crate without
/// `--cfg fip_prelint`, without the cargo features and without `cfg(test)`; the driver
/// compiles it with them. Every `cfg(..)`, `cfg!(..)` and `cfg_attr(..)` is refused
/// except the attribute-only forms that cannot change the code either side compiles:
///
/// - `cfg_attr(verus_keep_ghost, A..)` with each `A` a `verus_spec(..)`,
///   `verus_verify` or `verifier::..` attribute (Verus-only specifications; any other
///   payload, such as `cfg(any())`, could delete code for Verus only);
/// - `cfg_attr(not(verus_keep_ghost), fip_macros::..)` (the plain-build `#[fip]`, whose
///   added code has macro-expansion spans, which the driver never drops);
/// - `cfg_attr(fip_prelint, fip::..)` (the driver's inert tool attributes).
///
/// A `verus_keep_ghost` anywhere else is refused as well, and so is every
/// [`macro_conflict`] of the text (without the crate-wide rule on macros defined
/// elsewhere, which [`crate_cfg_conflict`] applies). `None` if there is nothing.
pub fn cfg_conflict(text: &str) -> Option<String> {
    let uses = cfg_uses(text);
    let mut allowed_ghosts = 0usize;
    for u in &uses {
        let ok = u.kind == "cfg_attr"
            && match u.args.first().map(String::as_str) {
                Some("verus_keep_ghost") => {
                    payload_only(&u.args[1..], &["verus_spec(", "verus_verify", "verifier::"])
                }
                Some("not(verus_keep_ghost)") => {
                    payload_only(&u.args[1..], &["fip_macros::", "::fip_macros::"])
                }
                Some("fip_prelint") => payload_only(&u.args[1..], &["fip::"]),
                _ => false,
            };
        if !ok {
            return Some(u.shown());
        }
        if u.args
            .first()
            .is_some_and(|a| a.contains("verus_keep_ghost"))
        {
            allowed_ghosts += 1;
        }
    }
    let ghosts = lex(text)
        .into_iter()
        .filter(|t| t.0 == Tok::Ident && &text[t.1..t.2] == "verus_keep_ghost")
        .count();
    if ghosts != allowed_ghosts {
        return Some("`verus_keep_ghost` outside an allowed `cfg_attr`".to_string());
    }
    macro_conflict(text, None)
}

/// Cfg names a crate with a Verus sidecar may test anywhere in its sources:
/// `verus_keep_ghost` (the two builds' split, checked per item by [`cfg_conflict`]) and
/// `feature` (the run's features are in the stamp and compared by the driver).
const CRATE_CFG_NAMES: &[&str] = &["verus_keep_ghost", "feature"];

/// Why a source file of a crate with a Verus sidecar may make the driver's build
/// differ from Verus's outside the listed item texts, if it may: a `cfg(..)`,
/// `cfg!(..)` or `cfg_attr(..)` predicate that names anything but
/// [`CRATE_CFG_NAMES`] (e.g. `test`, `fip_prelint`, `debug_assertions`,
/// `target_arch`: a `#[cfg(test)] const` or an inherent method in a
/// `#[cfg(test)] mod` would change what a listed item compiles to), except the inert
/// `cfg_attr(fip_prelint, fip::..)`. `None` if there is none.
///
/// Also every [`macro_conflict`] of `src`, with `local` the names the crate's sources
/// define by `macro_rules!` ([`macro_rules_names`] of all of them).
pub fn crate_cfg_conflict(src: &str, local: &[String]) -> Option<String> {
    for u in cfg_uses(src) {
        let pred = match u.kind {
            "cfg_attr" => u.args.first().cloned().unwrap_or_default(),
            _ => u.args.join(","),
        };
        if u.kind == "cfg_attr" && pred == "fip_prelint" && payload_only(&u.args[1..], &["fip::"]) {
            continue;
        }
        let names = cfg_names(&pred);
        if let Some(bad) = names
            .iter()
            .find(|n| !CRATE_CFG_NAMES.contains(&n.as_str()))
        {
            return Some(format!("{} tests `{bad}`", u.shown()));
        }
    }
    macro_conflict(src, Some(local))
}

/// The names `text` defines by `macro_rules! name`.
pub fn macro_rules_names(text: &str) -> Vec<String> {
    let toks: Vec<(Tok, usize, usize)> = lex(text)
        .into_iter()
        .filter(|t| !matches!(t.0, Tok::Ws | Tok::Comment | Tok::OuterDoc))
        .collect();
    let mut out = Vec::new();
    for k in 0..toks.len() {
        if toks[k].0 == Tok::Ident
            && &text[toks[k].1..toks[k].2] == "macro_rules"
            && toks.get(k + 1).is_some_and(|t| t.0 == Tok::Punct(b'!'))
            && let Some(n) = toks.get(k + 2).filter(|t| t.0 == Tok::Ident)
        {
            out.push(text[n.1..n.2].to_string());
        }
    }
    out
}

/// Macros that read the build's environment or other files: `env!` / `option_env!`
/// (cargo sets variables for the driver's rustc that the direct Verus run does not
/// have) and `include!` / `include_str!` / `include_bytes!` (the included file is
/// not among the hashed sources).
const ENV_MACROS: &[&str] = &[
    "env",
    "option_env",
    "include",
    "include_str",
    "include_bytes",
];

/// Identifiers that, passed to a macro as a bare token, let its expansion build a
/// cfg test or an environment read the text scan does not see (`gate!(cfg, x)` with
/// `macro_rules! gate { ($c:ident, $p:ident) => { $c!($p) } }`).
const BUILD_IDENTS: &[&str] = &[
    "cfg",
    "cfg_attr",
    "env",
    "option_env",
    "include",
    "include_str",
    "include_bytes",
];

/// Macros defined outside a crate's sources that a crate with a Verus sidecar may
/// invoke: `core` / `std` macros whose expansion tests no cfg and reads no
/// environment (not `debug_assert!`, which tests `debug_assertions`), Verus's
/// (`vstd`, pinned by the trusted stamp) and `fip_macros::fip_fn!`. Any other macro
/// of a dependency could expand to `cfg!(fip_prelint)` or `option_env!(..)`, which
/// is then evaluated with this crate's cfgs and environment.
const KNOWN_MACROS: &[&str] = &[
    "assert",
    "assert_eq",
    "assert_ne",
    "calc",
    "column",
    "compile_error",
    "concat",
    "file",
    "fip_fn",
    "format",
    "format_args",
    "line",
    "map",
    "matches",
    "module_path",
    "panic",
    "proof",
    "proof_decl",
    "seq",
    "set",
    "stringify",
    "todo",
    "unimplemented",
    "unreachable",
    "vec",
    "verus",
    "write",
    "writeln",
];

/// First path segments under which a [`KNOWN_MACROS`] name may be invoked.
const KNOWN_MACRO_ROOTS: &[&str] = &["core", "std", "alloc", "vstd", "builtin", "fip_macros"];

/// Why a macro invocation of `text` may expand differently for the driver than for
/// Verus (re-audit N3, 2026-11-04: `gate!(cfg, fip_prelint)` and
/// `option_env!("CARGO_PKG_NAME")` were listed and their division sites
/// discharged), if it may:
///
/// - an [`ENV_MACROS`] invocation (`env!`, `option_env!`, `include*!`);
/// - a macro named by a metavariable (`$c!(..)`): it can be `cfg!`;
/// - a macro whose arguments hold a [`BUILD_IDENTS`] identifier as a bare token
///   (not a `cfg(..)` / `cfg!(..)` / `cfg_attr(..)` use, which [`cfg_uses`] reads);
/// - with `local` (the `macro_rules!` names of every source of the crate, whose
///   bodies the crate scan reads): a macro that is not one of them and is not a
///   [`KNOWN_MACROS`] name invoked bare or under a [`KNOWN_MACRO_ROOTS`] path.
///
/// Not seen: attribute and derive macros of dependencies, and a glob import from a
/// dependency that shadows a known macro's name (trust boundary in
/// `docs/decisions/2026-11-01-fip-prelint.md`, amendment "Verus sidecars after the
/// re-audit").
pub fn macro_conflict(text: &str, local: Option<&[String]>) -> Option<String> {
    let toks: Vec<(Tok, usize, usize)> = lex(text)
        .into_iter()
        .filter(|t| !matches!(t.0, Tok::Ws | Tok::Comment | Tok::OuterDoc))
        .collect();
    let tx = |k: usize| &text[toks[k].1..toks[k].2];
    let is = |k: usize, c: u8| toks.get(k).is_some_and(|t| t.0 == Tok::Punct(c));
    let ident = |k: usize| toks.get(k).filter(|t| t.0 == Tok::Ident).map(|_| tx(k));
    for k in 0..toks.len() {
        let Some(name) = ident(k) else { continue };
        let open = is(k + 1, b'!') && (is(k + 2, b'(') || is(k + 2, b'[') || is(k + 2, b'{'));
        if !open || name == "macro_rules" || name == "cfg" {
            continue;
        }
        if k > 0 && is(k - 1, b'$') {
            return Some(format!(
                "`${name}!(..)` (a macro named by a metavariable, which can be `cfg!`)"
            ));
        }
        if ENV_MACROS.contains(&name) {
            return Some(format!(
                "`{name}!(..)` (it reads the build's environment or a file outside the hashed sources)"
            ));
        }
        // The argument tokens, to the matching close.
        let mut depth = 0usize;
        let mut m = k + 2;
        while m < toks.len() {
            match toks[m].0 {
                Tok::Punct(b'(' | b'[' | b'{') => depth += 1,
                Tok::Punct(b')' | b']' | b'}') => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                Tok::Ident => {
                    let w = tx(m);
                    let used = is(m + 1, b'(') || (is(m + 1, b'!') && is(m + 2, b'('));
                    if BUILD_IDENTS.contains(&w) && !used {
                        return Some(format!(
                            "`{name}!(..)` with the bare token `{w}` (its expansion can test a cfg or read the environment)"
                        ));
                    }
                }
                _ => {}
            }
            m += 1;
        }
        if let Some(local) = local {
            // The path before the name: `a::b::name!`.
            let mut first = None;
            let mut j = k;
            while j >= 3 && is(j - 1, b':') && is(j - 2, b':') && ident(j - 3).is_some() {
                first = ident(j - 3);
                j -= 3;
            }
            let own = first.is_none_or(|r| matches!(r, "crate" | "self" | "super"))
                && local.iter().any(|l| l == name);
            let rooted = first.is_none_or(|r| KNOWN_MACRO_ROOTS.contains(&r));
            if !own && !(KNOWN_MACROS.contains(&name) && rooted) {
                let shown = match first {
                    Some(r) => format!("{r}::..::{name}"),
                    None => name.to_string(),
                };
                return Some(format!(
                    "`{shown}!(..)` (a macro defined outside the crate's sources, whose expansion may test a cfg or read the environment)"
                ));
            }
        }
    }
    None
}

/// The cfg names a compact predicate tests (`not(any(a,feature="x"))` → `a`,
/// `feature`).
fn cfg_names(pred: &str) -> Vec<String> {
    let mut out = Vec::new();
    for t in lex(pred) {
        if t.0 != Tok::Ident {
            continue;
        }
        let w = &pred[t.1..t.2];
        let call = pred[t.2..].starts_with('(');
        if call && matches!(w, "not" | "any" | "all") {
            continue;
        }
        out.push(w.to_string());
    }
    out
}

/// A function path with every impl-block segment written `{impl}`: Verus's
/// `impl&%N` and rustc's `{impl#N}` (see the module documentation: the numbers of the
/// two builds differ, so they are never compared).
pub fn impl_key(path: &str) -> String {
    path.split("::")
        .map(|seg| {
            let verus = seg
                .strip_prefix("impl&%")
                .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()));
            let rustc = seg
                .strip_prefix("{impl#")
                .and_then(|r| r.strip_suffix('}'))
                .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()));
            if verus || rustc { "{impl}" } else { seg }
        })
        .collect::<Vec<_>>()
        .join("::")
}

/// 1-based line of byte offset `at` in `src`.
pub fn line_of(src: &str, at: usize) -> usize {
    src.as_bytes()[..at.min(src.len())]
        .iter()
        .filter(|&&b| b == b'\n')
        .count()
        + 1
}

/// Byte ranges of the items that carry exactly `#[cfg(verus_keep_ghost)]` (from the
/// attribute through the item's closing `}` or `;`): code only the Verus build
/// compiles, such as a `verus! { .. }` block with Verus-only twins of plain items.
pub fn ghost_only_regions(src: &str) -> Vec<(usize, usize)> {
    let toks: Vec<(Tok, usize, usize)> = lex(src)
        .into_iter()
        .filter(|t| !matches!(t.0, Tok::Ws | Tok::Comment | Tok::OuterDoc))
        .collect();
    let text = |k: usize| &src[toks[k].1..toks[k].2];
    let attr = ["#", "[", "cfg", "(", "verus_keep_ghost", ")", "]"];
    let mut out = Vec::new();
    let mut k = 0;
    while k + attr.len() <= toks.len() {
        if !(0..attr.len()).all(|m| text(k + m) == attr[m]) {
            k += 1;
            continue;
        }
        let start = toks[k].1;
        let mut depth = 0usize;
        let mut end = None;
        let mut m = k + attr.len();
        while m < toks.len() {
            match toks[m].0 {
                Tok::Punct(b'(' | b'[') => depth += 1,
                Tok::Punct(b')' | b']') => depth = depth.saturating_sub(1),
                Tok::Punct(b';') if depth == 0 => {
                    end = Some(toks[m].2);
                    break;
                }
                Tok::Punct(b'{') if depth == 0 => {
                    let mut braces = 0usize;
                    while m < toks.len() {
                        match toks[m].0 {
                            Tok::Punct(b'{') => braces += 1,
                            Tok::Punct(b'}') => {
                                braces -= 1;
                                if braces == 0 {
                                    end = Some(toks[m].2);
                                    break;
                                }
                            }
                            _ => {}
                        }
                        m += 1;
                    }
                    break;
                }
                _ => {}
            }
            m += 1;
        }
        let end = end.unwrap_or(src.len());
        out.push((start, end));
        k = m.max(k + 1);
    }
    out
}

// ---------------------------------------------------------------------------------
// The sidecar.

/// One verified function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    /// `<crate>::<module path>::<name>`, impl blocks written `{impl}` ([`impl_key`]).
    pub path: String,
    /// File relative to the sidecar's directory.
    pub file: String,
    /// 1-based line where the item text starts.
    pub line: usize,
    /// SHA-256 of the item text.
    pub hash: String,
    /// The function has a Verus `requires`: callers must establish it.
    pub requires: bool,
}

/// A parsed sidecar.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Sidecar {
    pub format: u32,
    pub krate: String,
    pub verus_version: String,
    pub verus_commit: String,
    pub z3: String,
    pub toolchain: String,
    pub flags: Vec<String>,
    /// Target triple the Verus run compiled the crate for.
    pub target: String,
    /// Cargo features of the run (`--cfg feature="x"`), sorted.
    pub features: Vec<String>,
    pub verified: u64,
    pub sources: Vec<(String, String)>,
    pub fns: Vec<Entry>,
    /// Exec functions of the crate Verus saw but that are not listed, with why.
    pub skipped: Vec<(String, String)>,
}

impl Sidecar {
    /// The stamp as shown in reports.
    pub fn stamp(&self) -> String {
        format!(
            "Verus {} ({}), Z3 {}, {}",
            self.verus_version,
            &self.verus_commit[..self.verus_commit.len().min(12)],
            self.z3,
            self.flags.join(" ")
        )
    }

    pub fn parse(text: &str) -> Result<Sidecar, String> {
        let mut s = Sidecar::default();
        let mut lines = text
            .lines()
            .map(str::trim_end)
            .filter(|l| !l.is_empty() && !l.starts_with('#'));
        if lines.next() != Some("fip-prelint verus sidecar") {
            return Err("not a fip-prelint Verus sidecar (missing header line)".to_string());
        }
        let mut have_format = false;
        let mut have_cfg = false;
        for l in lines {
            let (key, rest) = l.split_once(' ').unwrap_or((l, ""));
            let words: Vec<&str> = rest.split_whitespace().collect();
            let bad = || format!("malformed line `{l}`");
            match key {
                "format" => {
                    s.format = rest.trim().parse().map_err(|_| bad())?;
                    have_format = true;
                }
                "crate" => s.krate = rest.trim().to_string(),
                "verus" => {
                    let [v, c] = words[..] else { return Err(bad()) };
                    s.verus_version = v.to_string();
                    s.verus_commit = c.to_string();
                }
                "z3" => s.z3 = rest.trim().to_string(),
                "toolchain" => s.toolchain = rest.trim().to_string(),
                "flags" => s.flags = words.iter().map(|w| (*w).to_string()).collect(),
                "cfg" => {
                    let [t, f] = words[..] else { return Err(bad()) };
                    s.target = t.to_string();
                    s.features = if f == "-" {
                        Vec::new()
                    } else {
                        f.split(',').map(str::to_string).collect()
                    };
                    have_cfg = true;
                }
                "verified" => s.verified = rest.trim().parse().map_err(|_| bad())?,
                "source" => {
                    let [p, h] = words[..] else { return Err(bad()) };
                    s.sources.push((p.to_string(), h.to_string()));
                }
                "fn" => {
                    let [p, at, h, r] = words[..] else {
                        return Err(bad());
                    };
                    let (f, line) = at.rsplit_once(':').ok_or_else(bad)?;
                    let line: usize = line.parse().map_err(|_| bad())?;
                    if line == 0 || f.is_empty() {
                        return Err(bad());
                    }
                    let requires = match r {
                        "requires" => true,
                        "-" => false,
                        _ => return Err(bad()),
                    };
                    s.fns.push(Entry {
                        path: p.to_string(),
                        file: f.to_string(),
                        line,
                        hash: h.to_string(),
                        requires,
                    });
                }
                "skip" => {
                    let (p, why) = rest.split_once(' ').unwrap_or((rest, ""));
                    s.skipped.push((p.to_string(), why.to_string()));
                }
                _ => return Err(format!("unknown line `{l}`")),
            }
        }
        if !have_format {
            return Err("no `format` line".to_string());
        }
        if s.format != FORMAT {
            return Err(format!(
                "format {} (this driver reads format {FORMAT})",
                s.format
            ));
        }
        if s.krate.is_empty() || s.verus_version.is_empty() || s.z3.is_empty() || !have_cfg {
            return Err("incomplete stamp (crate, verus, z3 or cfg line missing)".to_string());
        }
        Ok(s)
    }

    pub fn render(&self) -> String {
        let mut o = String::new();
        o.push_str("fip-prelint verus sidecar\n");
        o.push_str(
            "# Generated by `cargo fip-prelint --verus-sidecar` (just verify); do not edit.\n\
             # Exec functions Verus verified with --no-cheating, with the SHA-256 of their item\n\
             # text (outer attributes and doc comments through the body). Top plan T13.4.\n",
        );
        let _ = writeln!(o, "format {}", self.format);
        let _ = writeln!(o, "crate {}", self.krate);
        let _ = writeln!(o, "verus {} {}", self.verus_version, self.verus_commit);
        let _ = writeln!(o, "z3 {}", self.z3);
        let _ = writeln!(o, "toolchain {}", self.toolchain);
        let _ = writeln!(o, "flags {}", self.flags.join(" "));
        let features = if self.features.is_empty() {
            "-".to_string()
        } else {
            self.features.join(",")
        };
        let _ = writeln!(o, "cfg {} {features}", self.target);
        let _ = writeln!(o, "verified {}", self.verified);
        for (p, h) in &self.sources {
            let _ = writeln!(o, "source {p} {h}");
        }
        for e in &self.fns {
            let r = if e.requires { "requires" } else { "-" };
            let _ = writeln!(o, "fn {} {}:{} {} {r}", e.path, e.file, e.line, e.hash);
        }
        for (p, why) in &self.skipped {
            let _ = writeln!(o, "skip {p} {why}");
        }
        o
    }

    /// `Ok` if this sidecar was produced by the trusted Verus build with
    /// `--no-cheating`; else why not.
    pub fn check_stamp(&self, trusted: &Trusted) -> Result<(), String> {
        if !self.flags.iter().any(|f| f == NO_CHEATING) {
            return Err(format!("generated without `{NO_CHEATING}`"));
        }
        if self.verus_version != trusted.verus_version || self.verus_commit != trusted.verus_commit
        {
            return Err(format!(
                "stamped Verus {} ({}), the trusted build is Verus {} ({})",
                self.verus_version,
                &self.verus_commit[..self.verus_commit.len().min(12)],
                trusted.verus_version,
                &trusted.verus_commit[..trusted.verus_commit.len().min(12)]
            ));
        }
        if self.z3 != trusted.z3 {
            return Err(format!(
                "stamped Z3 {}, the trusted Z3 is {}",
                self.z3, trusted.z3
            ));
        }
        Ok(())
    }
}

/// The Verus build whose results are trusted (`verus-trusted.txt`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Trusted {
    pub verus_version: String,
    pub verus_commit: String,
    pub z3: String,
}

impl Trusted {
    pub fn parse(text: &str) -> Result<Trusted, String> {
        let mut t = Trusted::default();
        for l in text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
        {
            let words: Vec<&str> = l.split_whitespace().collect();
            match words[..] {
                ["verus", v, c] => {
                    t.verus_version = v.to_string();
                    t.verus_commit = c.to_string();
                }
                ["z3", z] => t.z3 = z.to_string(),
                _ => return Err(format!("malformed line `{l}` in the trusted Verus pin")),
            }
        }
        if t.verus_version.is_empty() || t.z3.is_empty() {
            return Err("the trusted Verus pin names no Verus or no Z3".to_string());
        }
        Ok(t)
    }
}

/// The `verus-sidecar = ".."` value of `[package.metadata.fip-prelint]` in a
/// `Cargo.toml` text, if declared.
pub fn declared_sidecar(manifest: &str) -> Option<String> {
    let mut inside = false;
    for l in manifest.lines() {
        let t = l.trim();
        if t.starts_with('[') {
            inside = t == "[package.metadata.fip-prelint]";
            continue;
        }
        if inside
            && let Some((k, v)) = t.split_once('=')
            && k.trim() == "verus-sidecar"
        {
            let v = v.trim();
            return v
                .strip_prefix('"')
                .and_then(|v| v.strip_suffix('"'))
                .map(str::to_string);
        }
    }
    None
}

/// The library crate name of a `Cargo.toml` text: `[lib] name`, else the package
/// name with `-` replaced by `_`.
pub fn lib_crate_name(manifest: &str) -> Option<String> {
    let mut section = String::new();
    let mut package = None;
    let mut lib = None;
    for l in manifest.lines() {
        let t = l.trim();
        if t.starts_with('[') {
            section = t.to_string();
            continue;
        }
        if let Some((k, v)) = t.split_once('=')
            && k.trim() == "name"
        {
            let v = v.trim().trim_matches('"').to_string();
            match section.as_str() {
                "[package]" => package = Some(v),
                "[lib]" => lib = Some(v),
                _ => {}
            }
        }
    }
    lib.or_else(|| package.map(|p| p.replace('-', "_")))
}

/// The `path = ".."` values of the dependency tables of a `Cargo.toml` text
/// (`[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`, their `target.*`
/// and `workspace` forms, `[dependencies.<name>]` tables, `[patch.*]` and
/// `[replace]`), inline tables included. `path` keys of `[lib]`, `[[bin]]` and other
/// target tables are source files and are not returned.
pub fn path_dependencies(manifest: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut inside = false;
    for l in manifest.lines() {
        let t = l.trim();
        if t.starts_with('[') {
            let name = t
                .trim_start_matches('[')
                .split(']')
                .next()
                .unwrap_or("")
                .trim();
            inside = name
                .split('.')
                .any(|seg| seg.trim().ends_with("dependencies"))
                || name.starts_with("patch")
                || name == "replace"
                || name.starts_with("replace.");
            continue;
        }
        if !inside {
            continue;
        }
        let code = t.split('#').next().unwrap_or("");
        let b = code.as_bytes();
        let mut i = 0;
        while let Some(rel) = code[i..].find("path") {
            let at = i + rel;
            i = at + 4;
            let before_ok = at == 0 || matches!(b[at - 1], b'{' | b',' | b' ' | b'\t');
            let rest = code[at + 4..].trim_start();
            if !before_ok || !rest.starts_with('=') {
                continue;
            }
            let Some(v) = rest[1..].trim_start().strip_prefix('"') else {
                continue;
            };
            if let Some(end) = v.find('"') {
                out.push(v[..end].to_string());
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    const SRC: &str = "use x;\n\n/// Doc with ] and [ and \"quote.\n#[cfg_attr(verus_keep_ghost, verus_spec(r =>\n    requires a < 10, // ]\n    ensures r == a,\n))]\n// plain comment\n#[inline]\npub fn f(a: u8) -> u8 {\n    let s = \"}]\";\n    let c = '}';\n    a\n}\n\nfn g<'a>(x: &'a u8) -> u8 { *x }\n";

    #[test]
    fn region_covers_attributes_and_docs() {
        let start = SRC.find("pub fn f").unwrap();
        let end = SRC.find("    a\n}").unwrap() + "    a\n}".len();
        let (lo, hi) = item_region(SRC, start, end).unwrap();
        assert_eq!(lo, SRC.find("/// Doc").unwrap());
        assert_eq!(hi, end);
        // Any edit of the spec or the body changes the hash.
        let h = item_hash(SRC, start, end).unwrap();
        let spec = SRC.replace("requires a < 10", "requires a < 11");
        let s2 = spec.find("pub fn f").unwrap();
        let e2 = spec.find("    a\n}").unwrap() + 7;
        assert_ne!(item_hash(&spec, s2, e2).unwrap(), h);
        let body = SRC.replace("    a\n}", "    a + 0\n}");
        let s3 = body.find("pub fn f").unwrap();
        let e3 = body.find("    a + 0\n}").unwrap() + "    a + 0\n}".len();
        assert_ne!(item_hash(&body, s3, e3).unwrap(), h);
        // An edit outside the item does not.
        let other = SRC.replace("use x;", "use y;");
        let s4 = other.find("pub fn f").unwrap();
        let e4 = other.find("    a\n}").unwrap() + 7;
        assert_eq!(item_hash(&other, s4, e4).unwrap(), h);
    }

    #[test]
    fn region_stops_at_previous_item_and_rejects_bad_bounds() {
        let start = SRC.find("fn g").unwrap();
        let end = SRC.len() - 1;
        assert_eq!(item_region(SRC, start, end), Some((start, end)));
        assert_eq!(item_region(SRC, start + 1, end), None);
        assert_eq!(item_region(SRC, start, end - 1), None);
    }

    #[test]
    fn lexer_lifetimes_chars_raw_strings() {
        let src = "r#\"a\"]\"# 'a 'b' '\\'' b'x' b'\\'' br\"]\" x";
        let kinds: Vec<Tok> = lex(src)
            .into_iter()
            .map(|t| t.0)
            .filter(|k| *k != Tok::Ws)
            .collect();
        assert_eq!(
            kinds,
            vec![
                Tok::Literal,
                Tok::Lifetime,
                Tok::Literal,
                Tok::Literal,
                Tok::Literal,
                Tok::Literal,
                Tok::Literal,
                Tok::Ident
            ]
        );
    }

    #[test]
    fn offsets() {
        let src = "ab\nc한d\n";
        assert_eq!(offset_of(src, 1, 1), Some(0));
        assert_eq!(offset_of(src, 2, 3), Some(3 + 1 + 3));
        assert_eq!(offset_of(src, 3, 1), Some(src.len()));
    }

    #[test]
    fn ghost_cfg() {
        assert_eq!(
            cfg_conflict("#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r))]"),
            None
        );
        assert_eq!(
            cfg_conflict("#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict = true))]"),
            None
        );
        assert_eq!(
            cfg_conflict(
                "/// cfg(test) in a doc comment\n#[cfg_attr(fip_prelint, fip::mark(kind = \"fip\"))]\n#[cfg_attr(verus_keep_ghost, verifier::nonlinear)]\nfn f() { g(\"cfg!(x)\") }"
            ),
            None
        );
        assert!(cfg_conflict("{ #[cfg(not(verus_keep_ghost))] let x = a + 1; }").is_some());
        assert!(cfg_conflict("{ if cfg!(verus_keep_ghost) { 1 } else { 2 } }").is_some());
        // The audit's probes (2026-11-04): a cfg the driver sets and Verus does not,
        // `cfg!` folded to a literal, and a Verus-only `cfg_attr` deleting code.
        assert!(cfg_conflict("{ #[cfg(fip_prelint)] let _x = xs[i]; }").is_some());
        assert!(cfg_conflict("{ if cfg!(fip_prelint) { a / b } else { 0 } }").is_some());
        assert!(
            cfg_conflict("{ #[cfg_attr(verus_keep_ghost, cfg(any()))] let _x = xs[i]; }").is_some()
        );
        assert!(cfg_conflict("{ #[cfg(feature = \"fast\")] let _x = xs[7]; }").is_some());
        assert!(cfg_conflict("#[cfg_attr(test, inline)] fn f() {}").is_some());
        assert!(cfg_conflict("#[cfg_attr(fip_prelint, inline)] fn f() {}").is_some());
        assert!(
            cfg_conflict("#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r), cfg(any()))]")
                .is_some()
        );
        assert!(cfg_conflict("fn f() { m!(verus_keep_ghost) }").is_some());
    }

    #[test]
    fn crate_cfg() {
        assert_eq!(
            crate_cfg_conflict(
                "#[cfg(verus_keep_ghost)]\nuse vstd::prelude::*;\n#[cfg(not(verus_keep_ghost))]\nfn f() {}\n#[cfg(feature = \"x\")]\nfn g() {}\n#[cfg_attr(fip_prelint, fip::export)]\nmod m {}\n",
                &[]
            ),
            None
        );
        for bad in [
            "#[cfg(test)]\nmod tests {}\n",
            "#[cfg(fip_prelint)]\nconst N: usize = 0;\n",
            "#[cfg(not(fip_prelint))]\nconst N: usize = 4;\n",
            "const D: bool = cfg!(debug_assertions);\n",
            "#[cfg(target_arch = \"x86_64\")]\nconst N: usize = 1;\n",
            "#[cfg_attr(fip_prelint, derive(Clone))]\nstruct S;\n",
        ] {
            assert!(crate_cfg_conflict(bad, &[]).is_some(), "{bad}");
        }
    }

    /// Re-audit N3 (2026-11-04): a `cfg!` built by a macro from a bare `cfg` token and
    /// an `option_env!` were listed (8 verified, 0 skipped) and their division sites
    /// discharged; the driver's `--no-verus` run reported both.
    #[test]
    fn macros_that_can_test_cfgs_or_read_the_environment() {
        let gate = "macro_rules! gate { ($c:ident, $p:ident) => { $c!($p) } }\n";
        let probe_mac = "pub fn probe_mac(a: u32, b: u32) -> u32 { if gate!(cfg, fip_prelint) { a / b } else { 0 } }\n";
        let probe_env = "pub fn probe_env(a: u32, b: u32) -> u32 { match option_env!(\"CARGO_PKG_NAME\") { Some(_) => a / b, None => 0 } }\n";
        // Item texts (the per-function check, without the crate's macro names).
        let e = cfg_conflict(probe_mac).unwrap_or_default();
        assert!(e.contains("bare token `cfg`"), "{e}");
        let e = cfg_conflict(probe_env).unwrap_or_default();
        assert!(e.contains("option_env!"), "{e}");
        // The crate scan: the metavariable macro, `env!`, `include*!`, dependency
        // macros, and the bare tokens.
        let local = macro_rules_names(gate);
        assert_eq!(local, vec!["gate".to_string()]);
        let e = crate_cfg_conflict(gate, &local).unwrap_or_default();
        assert!(e.contains("`$c!(..)`"), "{e}");
        for (bad, want) in [
            (probe_mac, "bare token `cfg`"),
            (probe_env, "option_env!"),
            ("const N: &str = env!(\"CARGO_PKG_NAME\");\n", "env!"),
            ("const N: &str = ::core::env!(\"X\");\n", "env!"),
            ("include!(\"other.rs\");\n", "include!"),
            (
                "const B: &[u8] = include_bytes!(\"n.bin\");\n",
                "include_bytes!",
            ),
            ("fn f() -> bool { dep::gate!() }\n", "dep::..::gate!"),
            (
                "fn f() -> bool { other!() }\n",
                "`other!(..)` (a macro defined outside",
            ),
            ("fn f() { debug_assert!(true) }\n", "debug_assert!"),
            ("fn f() { dep::assert!(true) }\n", "dep::..::assert!"),
            (
                "fn f() -> bool { m!(option_env, \"X\") }\n",
                "bare token `option_env`",
            ),
            ("fn f() -> bool { m![cfg_attr] }\n", "bare token `cfg_attr`"),
        ] {
            let e = crate_cfg_conflict(bad, &local).unwrap_or_default();
            assert!(e.contains(want), "{bad}: {e}");
        }
        // Known macros, local ones, and `cfg(..)` uses the cfg scan reads.
        let ok = "macro_rules! proof { ($($t:tt)*) => {} }\nfn f(x: u8) { assert!(x < 9); ::core::assert_eq!(x, x); proof!{ let y = x; } fip_macros::fip_fn!(|a: u8| a); }\n#[cfg(verus_keep_ghost)]\nverus! { spec fn s() -> Seq<u8> { seq![1u8] } }\nfn g() { m2!(#[cfg(feature = \"x\")] 1) }\nmacro_rules! m2 { ($($t:tt)*) => {} }\n";
        let local = macro_rules_names(ok);
        assert_eq!(crate_cfg_conflict(ok, &local), None);
    }

    #[test]
    fn impl_keys_lines_and_ghost_regions() {
        assert_eq!(impl_key("c::impl&%8::assume"), "c::{impl}::assume");
        assert_eq!(impl_key("c::{impl#1}::assume"), "c::{impl}::assume");
        assert_eq!(impl_key("c::m::impl&%12::f"), "c::m::{impl}::f");
        assert_eq!(impl_key("c::impl&%::f"), "c::impl&%::f");
        assert_eq!(impl_key("c::{impl#x}::f"), "c::{impl#x}::f");
        assert_eq!(impl_key("c::f"), "c::f");
        assert_eq!(line_of("a\nb\nc", 0), 1);
        assert_eq!(line_of("a\nb\nc", 4), 3);
        let src = "fn a() {}\n#[cfg(verus_keep_ghost)]\nverus! {\nimpl X { fn f() { g(\"}\") } }\n}\n#[cfg(verus_keep_ghost)]\nuse vstd::prelude::*;\n#[cfg(not(verus_keep_ghost))]\nimpl X { fn f() {} }\n";
        let r = ghost_only_regions(src);
        assert_eq!(r.len(), 2, "{r:?}");
        assert_eq!(
            &src[r[0].0..r[0].1],
            "#[cfg(verus_keep_ghost)]\nverus! {\nimpl X { fn f() { g(\"}\") } }\n}"
        );
        assert_eq!(
            &src[r[1].0..r[1].1],
            "#[cfg(verus_keep_ghost)]\nuse vstd::prelude::*;"
        );
    }

    #[test]
    fn sidecar_round_trip_and_stamp() {
        let s = Sidecar {
            format: FORMAT,
            krate: "c".to_string(),
            verus_version: "0.1".to_string(),
            verus_commit: "abcdef".to_string(),
            z3: "4.16.0".to_string(),
            toolchain: "1.99.1".to_string(),
            flags: vec![NO_CHEATING.to_string()],
            target: "x86_64-unknown-linux-gnu".to_string(),
            features: vec!["a".to_string(), "b".to_string()],
            verified: 3,
            sources: vec![("src/lib.rs".to_string(), "00".to_string())],
            fns: vec![Entry {
                path: "c::{impl}::f".to_string(),
                file: "src/lib.rs".to_string(),
                line: 12,
                hash: "11".to_string(),
                requires: true,
            }],
            skipped: vec![("c::g".to_string(), "external body".to_string())],
        };
        assert_eq!(Sidecar::parse(&s.render()), Ok(s.clone()));
        let t = Trusted {
            verus_version: "0.1".to_string(),
            verus_commit: "abcdef".to_string(),
            z3: "4.16.0".to_string(),
        };
        assert_eq!(s.check_stamp(&t), Ok(()));
        let other = Trusted {
            verus_version: "0.2".to_string(),
            ..t.clone()
        };
        assert!(s.check_stamp(&other).is_err());
        let z3 = Trusted {
            z3: "4.12.5".to_string(),
            ..t.clone()
        };
        assert!(s.check_stamp(&z3).is_err());
        let cheat = Sidecar {
            flags: Vec::new(),
            ..s.clone()
        };
        assert!(cheat.check_stamp(&t).is_err());
        assert!(Sidecar::parse(&s.render().replace("format 4", "format 3")).is_err());
        assert!(Sidecar::parse(&s.render().replace("format 4", "format 2")).is_err());
        // Format 3 and later require the `cfg` line.
        assert!(
            Sidecar::parse(&s.render().replace("cfg x86_64-unknown-linux-gnu a,b\n", "")).is_err()
        );
        let none = Sidecar {
            features: Vec::new(),
            ..s.clone()
        };
        assert!(none.render().contains("cfg x86_64-unknown-linux-gnu -\n"));
        assert_eq!(Sidecar::parse(&none.render()), Ok(none));
        assert!(Sidecar::parse(&s.render().replace("src/lib.rs:12", "src/lib.rs")).is_err());
    }

    #[test]
    fn manifest_path_dependencies() {
        let m = "[package]\nname = \"x\"\n[lib]\npath = \"src/x.rs\"\n[[bin]]\nname = \"b\"\npath = \"src/b.rs\"\n[dependencies]\na = { path = \"../a\" }\nb = { version = \"1\", path= \"../b\" } # c = { path = \"../c\" }\nfilepath = \"1\"\n[dev-dependencies.d]\npath = \"../d\"\n[target.'cfg(unix)'.build-dependencies]\ne = {path=\"/abs/e\"}\n[workspace.dependencies]\nf = { path = \"crates/f\" }\n[patch.crates-io]\ng = { path = \"../g\" }\n[features]\npath = []\n";
        assert_eq!(
            path_dependencies(m),
            vec!["../a", "../b", "../d", "/abs/e", "crates/f", "../g"]
        );
    }

    #[test]
    fn manifest_declaration() {
        let m = "[package]\nname = \"x\"\n\n[package.metadata.fip-prelint]\nverus-sidecar = \"verus-verified.txt\"\n";
        assert_eq!(declared_sidecar(m), Some("verus-verified.txt".to_string()));
        assert_eq!(declared_sidecar("[package]\nverus-sidecar = \"a\"\n"), None);
        assert_eq!(lib_crate_name(m), Some("x".to_string()));
        assert_eq!(
            lib_crate_name("[package]\nname = \"a-b\"\n[lib]\nname = \"c\"\n"),
            Some("c".to_string())
        );
        assert_eq!(
            lib_crate_name("[package]\nname = \"a-b\"\n"),
            Some("a_b".to_string())
        );
    }
}
