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
//! format 7
//! crate <crate name>
//! verus <version> <commit>
//! z3 <version>
//! toolchain <rust toolchain of the Verus build>
//! flags <verus flags relevant to trust: --no-cheating -V alloc-check>
//! cfg <target triple of the run> <its cargo features, comma-separated, or -> <its edition>
//! verified <number Verus reported verified>
//! source <path relative to the sidecar's directory> <sha256>
//! import <imported crate> <sha256 of its sidecar> <the edition it was verified for>
//! fn <crate>::<path> <file relative to the sidecar's directory>:<line> <sha256 of the item text> <requires | -> <allocates> <deallocates> <encapsulates | ->
//! skip <crate>::<path> <reason>
//! divergent <trait name> <file relative to the sidecar's directory>:<line>
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
//! Format 5 (2026-11-06, decision 2026-11-06-redesign-verus-allocates, phase 4) adds
//! the `divergent` lines: every trait with an implementation or a declaration under a
//! cfg naming `verus_keep_ghost` ([`divergent_traits`]). Verus assumes a trait
//! method's specification for every implementation, also the plain-only ones it never
//! compiled, so every function naming a method of such a trait is skipped
//! (`relies on the specification of ..`), in this crate's run and in every run
//! importing it. The driver refuses format 4 sidecars, which were written without
//! this rule.
//!
//! Format 5 also records, per listed function, the `allocates` bound Verus proved
//! ([`AllocBound`]): `-` (no clause), a literal `c` or a parameter-linear form
//! `c+k*p+..` (unsigned integer parameters), or `opaque:<sha256>` for any other
//! expression; and it requires `-V alloc-check` in `flags` (the generator refuses a run
//! without it, the driver a sidecar without it). The driver takes a literal bound in
//! place of its own allocation count of the function's body only for a non-generic
//! function without `requires` whose instance calls no trait method implemented by
//! unverified code, and only where its own count is not a finite number at most the
//! bound; a finite count above the bound is an error (`crate::verustrust`).
//!
//! Format 6 (2026-11-20, fork `83fd42f3b`) adds, per listed function, its `deallocates`
//! bound (the fork counts deallocations; same spellings as `allocates`) and whether it
//! has `encapsulates alloc(a, d)` (then `<allocates>` is `a` and `<deallocates>` is `d`,
//! and Verus proved neither: the function's body is the runtime's to Verus). The driver
//! takes no allocation bound from an `encapsulates` function, uses its counts only for a
//! declared source they equal, and refuses format 5 sidecars, which cannot tell such a
//! function from one with a proved bound.
//!
//! Format 7 (2026-11-22) adds the run's edition to the `cfg` line. Verus's default
//! edition is not cargo's: without `--edition` the crate is verified as written for an
//! older edition than the one it is compiled for (measured: a 2024 keyword is an
//! identifier), and editions differ in what a method call resolves to and in where
//! temporaries are dropped. The generator refuses a run without `--edition`; the driver
//! uses a sidecar only for a crate compiled for the recorded edition, and refuses
//! format 6 sidecars, which do not say. A run with `--import` rests on the imported
//! crate's specifications: an `import` line names each imported crate with the SHA-256
//! of the sidecar it was imported with (`--import-sidecar`) and that sidecar's edition.
//! The driver uses the importing sidecar only if the crate of that name in the build
//! declares a sidecar with that hash which is itself usable (unchanged sources, the
//! trusted stamp) and is compiled for that edition. The identity is the imported
//! sidecar, not a path: an imported crate from a registry or a git dependency lives in
//! cargo's checkout, whose path differs from machine to machine.
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
pub const FORMAT: u32 = 7;

/// The editions a sidecar's `cfg` line may record (rustc's spellings).
pub const EDITIONS: &[&str] = &["2015", "2018", "2021", "2024"];

/// The Verus flag without which no sidecar is written or used.
pub const NO_CHEATING: &str = "--no-cheating";

/// The value of the Verus fork's `-V alloc-check` option (`allocates` bounds checked;
/// decision record 2026-11-06-redesign-verus-allocates). Recorded in `flags` as the two
/// words `-V alloc-check`; required since format 5 (the generator refuses a run
/// without it, the driver a sidecar whose `flags` lack it).
pub const ALLOC_CHECK: &str = "alloc-check";

/// `true` if a sidecar's recorded `flags` hold `-V alloc-check`.
pub fn has_alloc_check(flags: &[String]) -> bool {
    flags
        .windows(2)
        .any(|w| w[0] == "-V" && w[1] == ALLOC_CHECK)
}

/// Verus flags that verify the crate as a standard-library crate (vstd, core, std),
/// whose trusted items and `assume_specification`s are not user code (the fork
/// audit, 2026-11-09). The fork rejects them with `--no-cheating`; independently of
/// that, the generator refuses a run with one ([`crate::verusgen::REFUSED_FLAGS`]) and
/// records it in `flags` if present, and the driver refuses a sidecar whose `flags`
/// hold one.
pub const STD_CRATE_FLAGS: &[&str] = &["--is-vstd", "--is-core", "--is-stdlib-outside-of-core"];

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

/// The line of the first identifier `internal` in the code of `src` (comments and
/// string literals apart), if any. `verus::internal(..)` are the attributes Verus's own
/// macros write for the verifier; written by hand they state to it what no clause was
/// checked for (on the fork `e93729c25`, `#[verus::internal(encapsulates_alloc)]` made
/// any function a leaf of the allocation check; `b358424cd` removed that one). The
/// path need not be spelled in one place: `verus::r#internal` and a macro's
/// `#[$t::$i(..)]` called with `m!(verus, internal)` reach Verus as the same attribute
/// (measured on `83fd42f3b`), so the identifier itself is refused, as
/// `fip_testkit::surface` refuses `trusted_call`. A crate with a sidecar has none.
pub fn verus_internal_use(src: &str) -> Option<usize> {
    lex(src)
        .into_iter()
        .find(|t| t.0 == Tok::Ident && &src[t.1..t.2] == "internal")
        .map(|t| line_of(src, t.1))
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

// ---------------------------------------------------------------------------------
// Names defined for one build only (decision 2026-11-01-fip-prelint, amendment
// 2026-11-24 (4)).

/// Crates whose items exist only in Verus's build by design: a gated `use` of one of
/// them brings ghost names, which exec code compiled in both builds cannot name. (It
/// also brings traits with exec methods into scope, `vstd::prelude`'s
/// `ArrayAdditionalExecFns` among them, and a method call does not name its trait: the
/// generator skips a function that calls an exec function of these crates,
/// `verusgen::SKIP_VERUS_EXEC`.)
pub const VERUS_ROOTS: &[&str] = &[
    "vstd",
    "verus_builtin",
    "verus_builtin_macros",
    "builtin",
    "builtin_macros",
];

/// The macros whose arguments are ghost code, when the crate does not define them
/// otherwise than as empty shims for plain builds (see [`Gated::ghost_macros`]).
const GHOST_MACROS: &[&str] = &["proof", "proof_decl"];

/// What [`gated_names`] finds in the sources of a crate.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Gated {
    /// Names that mean something else, or exist only, in one of the two builds: a
    /// `const`, `static`, `type`, `macro_rules!`, `struct`, `enum` or `union` defined
    /// under a `#[cfg(..)]` (on the item, on an item around it, or in a module file
    /// declared under one), a name a gated `use` brings from another crate than
    /// Verus's, and every definition of those kinds that names one.
    pub names: std::collections::BTreeSet<String>,
    /// Of `proof` and `proof_decl`: those the crate does not define itself, or only as
    /// shims that expand to nothing in plain builds. Their arguments are ghost code.
    pub ghost_macros: std::collections::BTreeSet<String>,
    /// The files (as given) of modules declared under a `#[cfg(..)]`, or with a
    /// `cfg_attr(.., path = ..)`: one build may read another file for the module.
    pub files: std::collections::BTreeSet<String>,
}

/// Whether `src[lo..hi]` lies inside an item with a `#[cfg(..)]` attribute, any
/// predicate, or `src` has an inner `#![cfg(..)]`.
pub fn in_gated_item(src: &str, lo: usize, hi: usize) -> bool {
    let toks = code_toks(src);
    gated_items(src, &toks).iter().any(|&(a, b)| {
        let start = toks.get(a).map_or(0, |t| t.1);
        let end = if b == 0 {
            0
        } else {
            toks.get(b - 1).map_or(src.len(), |t| t.2)
        };
        start <= lo && hi <= end
    })
}

/// What a crate may put under `verus_keep_ghost` and still have its functions listed
/// (decision 2026-11-01-fip-prelint, amendments 2026-11-25 and 2026-11-25 (2)): the
/// first use of the gate in `files` (path relative to the crate directory, text) that
/// is none of it, with its place.
///
/// The driver analyses the plain build, which has no `verus_keep_ghost`; Verus proves
/// the build that has it. Every way found, on 2026-11-24, in which one function text
/// was two programs went through code under that gate, and the list of ways was never
/// shown complete. So the rule is turned around: the gate may be used in the shapes
/// below, which cannot change exec code, and in no other, whatever the other is.
///
/// 1. `cfg_attr(verus_keep_ghost, ..)` with Verus's attributes (`verus_spec(..)`,
///    `verus_verify`, `verifier::..`), `feature(..)`, lint levels, `doc`;
///    `cfg_attr(not(verus_keep_ghost), ..)` with `fip_macros::..`, lint levels, `doc`.
/// 2. `#[cfg(verus_keep_ghost)] use ..;` from one of Verus's crates ([`VERUS_ROOTS`]),
///    or from a ghost module of the crate (3).
/// 3. `#[cfg(verus_keep_ghost)]` on a `verus! { .. }` block, a `mod name { .. }` or a
///    `mod name;` (then the module's files), holding specifications and proofs only:
///    `spec`, `proof` and `axiom` functions, `spec` constants, `use`, `broadcast`
///    items, modules, and impls and traits of those (with their associated types). No
///    exec function, no other definition (`struct`, `enum`, `union`, `const`, `static`,
///    a type alias, `macro_rules!`), no `extern`, no invocation of a macro of the crate.
/// 4. `#[cfg(not(verus_keep_ghost))] macro_rules!` for `proof` and `proof_decl`,
///    expanding to nothing.
/// 5. The marker pattern: `#[cfg(not(verus_keep_ghost))] trait Name {}` with
///    `#[cfg(not(verus_keep_ghost))] impl<T: ?Sized> Name for T {}` (for plain builds,
///    where every type has the marker), and `#[cfg(verus_keep_ghost)] [unsafe] impl ..
///    for Type {}` of a trait of Verus's crates (`vstd::alloc_check::NoDeallocDrop`,
///    ..), with an empty body.
///
/// Anything else is a violation: another predicate, `cfg!(verus_keep_ghost)`,
/// `#![cfg(..)]`, the gate on a function, an impl with items, a definition, a field, a
/// statement, an item of plain builds only.
pub fn gate_violation(files: &[(String, String)]) -> Option<String> {
    use std::collections::{BTreeMap, BTreeSet};
    use std::path::Path;
    type Toks = [(Tok, usize, usize)];
    const LINTS: &[&str] = &["allow(", "warn(", "deny(", "forbid(", "expect(", "doc"];

    type File<'a> = (&'a str, &'a str, Vec<(Tok, usize, usize)>);
    let parsed: Vec<File> = files
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str(), code_toks(s)))
        .collect();

    // The index after the attributes and the visibility that start at `k`.
    fn after_attrs(src: &str, toks: &Toks, mut k: usize, end: usize) -> usize {
        let text = |k: usize| &src[toks[k].1..toks[k].2];
        loop {
            if k + 1 < end && text(k) == "#" && text(k + 1) == "[" {
                let mut depth = 0usize;
                k += 1;
                while k < end {
                    match toks[k].0 {
                        Tok::Punct(b'[' | b'(') => depth += 1,
                        Tok::Punct(b']' | b')') => {
                            depth -= 1;
                            if depth == 0 {
                                k += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    k += 1;
                }
                continue;
            }
            if k < end && text(k) == "pub" {
                k += 1;
                if k < end && text(k) == "(" {
                    while k < end && text(k) != ")" {
                        k += 1;
                    }
                    k += 1;
                }
                continue;
            }
            return k;
        }
    }
    // The tokens of a cfg predicate: of the group that opens at `open` (a `(`).
    fn pred_at<'s>(src: &'s str, toks: &Toks, open: usize, end: usize) -> Vec<&'s str> {
        let mut out = Vec::new();
        let mut depth = 0usize;
        for t in &toks[open..end] {
            let w = &src[t.1..t.2];
            match t.0 {
                Tok::Punct(b'(') => {
                    depth += 1;
                    if depth > 1 {
                        out.push(w);
                    }
                }
                Tok::Punct(b')') => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                    out.push(w);
                }
                _ => out.push(w),
            }
        }
        out
    }
    // Whether the header in front of token `m` (back to the end of what is before it)
    // has one of `words`.
    fn header_has(src: &str, toks: &Toks, a: usize, m: usize, words: &[&str]) -> bool {
        let mut j = m;
        while j > a {
            j -= 1;
            match toks[j].0 {
                Tok::Punct(b';' | b'{' | b'}' | b']') => return false,
                Tok::Ident if words.contains(&&src[toks[j].1..toks[j].2]) => return true,
                _ => {}
            }
        }
        false
    }
    // Whether the nearest block around token `m` is the body of an impl or a trait.
    fn in_impl_or_trait(src: &str, toks: &Toks, a: usize, m: usize) -> bool {
        let mut depth = 0usize;
        let mut j = m;
        while j > a {
            j -= 1;
            match toks[j].0 {
                Tok::Punct(b'}') => depth += 1,
                Tok::Punct(b'{') if depth > 0 => depth -= 1,
                Tok::Punct(b'{') => {
                    // Its header, back to the end of what is before it.
                    let mut h = j;
                    while h > a {
                        h -= 1;
                        match toks[h].0 {
                            Tok::Punct(b';' | b'{' | b'}') => return false,
                            Tok::Ident
                                if matches!(&src[toks[h].1..toks[h].2], "impl" | "trait") =>
                            {
                                return true;
                            }
                            _ => {}
                        }
                    }
                    return false;
                }
                _ => {}
            }
        }
        false
    }
    // Whether the `use` tree in `toks[from..to]` imports from one of Verus's crates or
    // through a ghost module of the crate.
    fn ghost_use(
        src: &str,
        toks: &Toks,
        from: usize,
        to: usize,
        ghost_mods: &BTreeSet<String>,
    ) -> bool {
        let text = |k: usize| &src[toks[k].1..toks[k].2];
        let Some(root) = (from..to).find(|&k| toks[k].0 == Tok::Ident).map(text) else {
            return false;
        };
        if VERUS_ROOTS.contains(&root) {
            return true;
        }
        if !matches!(root, "crate" | "self" | "super") {
            return false;
        }
        // (the path before any `{`, `*` or `as`)
        (from..to)
            .take_while(|&k| !matches!(toks[k].0, Tok::Punct(b'{' | b'*')) && text(k) != "as")
            .any(|k| toks[k].0 == Tok::Ident && ghost_mods.contains(text(k)))
    }
    // The first thing in `toks[a..b]`, a block under `#[cfg(verus_keep_ghost)]`, that is
    // not a specification or a proof. In a module (`module`), `use` is the module's own.
    #[allow(clippy::too_many_arguments)]
    fn not_ghost(
        src: &str,
        toks: &Toks,
        a: usize,
        b: usize,
        module: bool,
        ghost_mods: &BTreeSet<String>,
        local_macros: &BTreeSet<String>,
        plain_markers: &BTreeSet<String>,
    ) -> Option<(usize, String)> {
        let text = |k: usize| &src[toks[k].1..toks[k].2];
        let ident = |k: usize| k < b && toks[k].0 == Tok::Ident;
        let is = |k: usize, w: &str| k < b && text(k) == w;
        let mut m = a;
        while m < b {
            // Attributes are not code.
            if is(m, "#") && (is(m + 1, "[") || (is(m + 1, "!") && is(m + 2, "["))) {
                let mut depth = 0usize;
                while m < b {
                    match toks[m].0 {
                        Tok::Punct(b'[') => depth += 1,
                        Tok::Punct(b']') => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                    m += 1;
                }
                m += 1;
                continue;
            }
            if toks[m].0 != Tok::Ident {
                m += 1;
                continue;
            }
            let w = text(m);
            let prev = if m > a { text(m - 1) } else { "" };
            let found = match w {
                "macro_rules" if is(m + 1, "!") => Some("a `macro_rules!`".to_string()),
                "fn" if ident(m + 1)
                    && !header_has(src, toks, a, m, &["spec", "proof", "axiom"]) =>
                {
                    Some(format!("the exec function `{}`", text(m + 1)))
                }
                "struct" | "enum" if ident(m + 1) => {
                    Some(format!("the definition of `{}`", text(m + 1)))
                }
                "union" if ident(m + 1) && (is(m + 2, "{") || is(m + 2, "<")) => {
                    Some(format!("the definition of `{}`", text(m + 1)))
                }
                "static" if ident(m + 1) => Some("a `static`".to_string()),
                "const"
                    if ident(m + 1)
                        && is(m + 2, ":")
                        && !matches!(prev, "<" | "," | "*" | "~")
                        && !header_has(src, toks, a, m, &["spec"]) =>
                {
                    Some(format!("the constant `{}`", text(m + 1)))
                }
                "type"
                    if ident(m + 1)
                        && (is(m + 2, "=")
                            || is(m + 2, "<")
                            || is(m + 2, ":")
                            || is(m + 2, ";"))
                        && !in_impl_or_trait(src, toks, a, m) =>
                {
                    Some(format!("the type alias `{}`", text(m + 1)))
                }
                "extern" => Some("`extern`".to_string()),
                // An impl (the item: `impl` in a type comes after `:`, `->`, `(`, ..).
                "impl" if matches!(prev, "" | "}" | ";" | "]" | "{" | "unsafe" | "default") => {
                    ghost_impl_violation(src, toks, m, b)
                }
                "trait" if ident(m + 1) => ghost_trait_violation(src, toks, m, b, plain_markers),
                "use" if !module && prev != "broadcast" => {
                    let end = (m..b).find(|&k| is(k, ";")).unwrap_or(b);
                    (!ghost_use(src, toks, m + 1, end, ghost_mods)).then(|| {
                        "a `use` of something else than Verus's crates or a ghost module of the crate"
                            .to_string()
                    })
                }
                _ if is(m + 1, "!")
                    && matches!(
                        toks.get(m + 2).map(|t| t.0),
                        Some(Tok::Punct(b'(' | b'[' | b'{'))
                    )
                    && local_macros.contains(w)
                    && !GHOST_MACROS.contains(&w) =>
                {
                    Some(format!("an invocation of the crate's macro `{w}!`"))
                }
                _ => None,
            };
            if let Some(what) = found {
                return Some((m, what));
            }
            m += 1;
        }
        None
    }
    // The items with an outer `#[cfg(..)]`: token ranges from the `#`.
    fn outer_gated(src: &str, toks: &Toks) -> Vec<(usize, usize)> {
        let text = |k: usize| &src[toks[k].1..toks[k].2];
        let is = |k: usize, s: &str| k < toks.len() && text(k) == s;
        (0..toks.len())
            .filter(|&k| is(k, "#") && is(k + 1, "[") && is(k + 2, "cfg") && is(k + 3, "("))
            .map(|k| {
                let first = after_attrs(src, toks, k, toks.len());
                let item = first < toks.len()
                    && matches!(
                        text(first),
                        "fn" | "impl"
                            | "struct"
                            | "enum"
                            | "union"
                            | "trait"
                            | "mod"
                            | "use"
                            | "const"
                            | "static"
                            | "type"
                            | "macro_rules"
                            | "extern"
                            | "unsafe"
                            | "async"
                            | "default"
                            | "verus"
                    );
                (k, item_end_in(toks, k + 1, !item))
            })
            .collect()
    }

    let at = |path: &str, src: &str, toks: &Toks, k: usize| {
        format!("{path}:{}", line_of(src, toks[k].1))
    };
    // First pass: the ghost modules (declared under `#[cfg(verus_keep_ghost)]`), the
    // files of those declared with `#[path]`, the marker traits of plain builds, and
    // the macros of the crate.
    let mut ghost_mods: BTreeSet<String> = BTreeSet::new();
    let mut ghost_files: BTreeSet<String> = BTreeSet::new();
    let mut markers: BTreeMap<String, usize> = BTreeMap::new();
    let mut local_macros: BTreeSet<String> = BTreeSet::new();
    // The traits of the crate that have no method and no supertrait, in every
    // declaration of the name: as a supertrait of a trait of specifications they bring
    // no method into scope.
    let mut methodless: BTreeSet<String> = BTreeSet::new();
    let mut with_methods: BTreeSet<String> = BTreeSet::new();
    for (_, src, toks) in &parsed {
        let text = |k: usize| &src[toks[k].1..toks[k].2];
        for k in 0..toks.len() {
            if text(k) == "trait" && toks.get(k + 1).is_some_and(|t| t.0 == Tok::Ident) {
                let name = text(k + 1).to_string();
                match trait_shape(src, toks, k, toks.len()) {
                    Some((supers, body, end))
                        if supers.is_empty() && !(body..end).any(|j| text(j) == "fn") =>
                    {
                        methodless.insert(name);
                    }
                    _ => {
                        with_methods.insert(name);
                    }
                }
            }
        }
    }
    methodless.retain(|n| !with_methods.contains(n));
    for (_, src, toks) in &parsed {
        let text = |k: usize| &src[toks[k].1..toks[k].2];
        local_macros.extend(macro_rules_names(src));
        for (a, b) in outer_gated(src, toks) {
            let pred = pred_at(src, toks, a + 3, b);
            let k = after_attrs(src, toks, a, b);
            if k + 2 >= toks.len() || toks[k + 1].0 != Tok::Ident {
                continue;
            }
            if pred == ["verus_keep_ghost"] && text(k) == "mod" {
                ghost_mods.insert(text(k + 1).to_string());
                for m in a..k {
                    if text(m) == "path"
                        && m + 2 < k
                        && text(m + 1) == "="
                        && toks[m + 2].0 == Tok::Literal
                        && let Some(n) = Path::new(text(m + 2).trim_matches('"'))
                            .file_name()
                            .and_then(|n| n.to_str())
                    {
                        ghost_files.insert(n.to_string());
                    }
                }
            }
            if pred == ["not", "(", "verus_keep_ghost", ")"]
                && let Some((name, arity)) = marker_trait(src, toks, k, b)
            {
                markers.insert(name, arity);
            }
        }
    }
    for (path, src, toks) in &parsed {
        let text = |k: usize| &src[toks[k].1..toks[k].2];
        let is = |k: usize, s: &str| k < toks.len() && text(k) == s;
        // 1. `cfg_attr(P, payload)` with `verus_keep_ghost` in `P`.
        for u in cfg_uses(src) {
            if u.kind != "cfg_attr" {
                continue;
            }
            let pred = u.args.first().map(String::as_str).unwrap_or("");
            if !pred.contains("verus_keep_ghost") {
                continue;
            }
            let ok = match pred {
                "verus_keep_ghost" => payload_only(
                    &u.args[1..],
                    &[
                        &["verus_spec(", "verus_verify", "verifier::", "feature("],
                        LINTS,
                    ]
                    .concat(),
                ),
                "not(verus_keep_ghost)" => payload_only(
                    &u.args[1..],
                    &[&["fip_macros::", "::fip_macros::"], LINTS].concat(),
                ),
                _ => false,
            };
            if !ok {
                return Some(format!(
                    "{path}: {}: only Verus's attributes, `feature(..)`, lint levels and `doc` may depend on `verus_keep_ghost` (and `fip_macros::..` on its negation)",
                    u.shown()
                ));
            }
        }
        // `cfg!(..)` and `#![cfg(..)]`.
        for k in 0..toks.len() {
            if is(k, "cfg")
                && is(k + 1, "!")
                && is(k + 2, "(")
                && pred_at(src, toks, k + 2, toks.len()).contains(&"verus_keep_ghost")
            {
                return Some(format!(
                    "{}: `cfg!(..)` on `verus_keep_ghost`: code that runs in one build only",
                    at(path, src, toks, k)
                ));
            }
            if is(k, "#")
                && is(k + 1, "!")
                && is(k + 2, "[")
                && is(k + 3, "cfg")
                && is(k + 4, "(")
                && pred_at(src, toks, k + 4, toks.len()).contains(&"verus_keep_ghost")
            {
                return Some(format!(
                    "{}: `#![cfg(..)]` on `verus_keep_ghost`: declare the module under the gate instead",
                    at(path, src, toks, k)
                ));
            }
        }
        // 3. A file of a ghost module.
        let p = Path::new(path);
        let stem = p.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        let ghost_file = ghost_mods.contains(stem)
            || p.file_name()
                .and_then(|s| s.to_str())
                .is_some_and(|n| ghost_files.contains(n))
            || p.parent().is_some_and(|d| {
                d.components().any(|c| {
                    c.as_os_str()
                        .to_str()
                        .is_some_and(|c| ghost_mods.contains(c))
                })
            });
        if ghost_file
            && let Some((m, what)) = not_ghost(
                src,
                toks,
                0,
                toks.len(),
                true,
                &ghost_mods,
                &local_macros,
                &methodless,
            )
        {
            return Some(format!(
                "{}: {what} in a module declared under `#[cfg(verus_keep_ghost)]`: only specifications and proofs may be there",
                at(path, src, toks, m)
            ));
        }
        for (a, b) in outer_gated(src, toks) {
            let pred = pred_at(src, toks, a + 3, b);
            if !pred.contains(&"verus_keep_ghost") {
                continue;
            }
            let ghost = pred == ["verus_keep_ghost"];
            let plain = pred == ["not", "(", "verus_keep_ghost", ")"];
            let shown = format!("#[cfg({})]", pred.concat());
            if !ghost && !plain {
                return Some(format!(
                    "{}: `{shown}`: only `verus_keep_ghost` and `not(verus_keep_ghost)` are read",
                    at(path, src, toks, a)
                ));
            }
            let k = after_attrs(src, toks, a, b);
            let head = if k < b { text(k) } else { "" };
            // (`unsafe impl`)
            let k_impl = if head == "unsafe" && is(k + 1, "impl") {
                k + 1
            } else {
                k
            };
            let empty_body = b >= 2 && text(b - 2) == "{" && text(b - 1) == "}";
            let refuse = |what: &str| {
                Some(format!(
                    "{}: {what} under `{shown}`: the gate is for specifications and proofs, the empty `proof!` shims and marker traits",
                    at(path, src, toks, a)
                ))
            };
            if ghost {
                match head {
                    "use" => {
                        let to = if text(b - 1) == ";" { b - 1 } else { b };
                        if !ghost_use(src, toks, k + 1, to, &ghost_mods) {
                            return refuse(
                                "a `use` of something else than Verus's crates or a ghost module of the crate",
                            );
                        }
                    }
                    "verus" | "mod" => {
                        let block = head == "mod" || is(k + 1, "!");
                        if !block {
                            return refuse("`verus`");
                        }
                        // (`mod name;`: its files are read above)
                        if let Some((m, what)) = not_ghost(
                            src,
                            toks,
                            k + 1,
                            b,
                            head == "mod",
                            &ghost_mods,
                            &local_macros,
                            &methodless,
                        ) {
                            return Some(format!(
                                "{}: {what} under `{shown}`: only specifications and proofs may be there (exec code of Verus's build only is another program than the plain build's)",
                                at(path, src, toks, m)
                            ));
                        }
                    }
                    _ if is(k_impl, "impl") => {
                        // A marker impl: `impl<..> Path for Type {}` of a trait of
                        // Verus's crates.
                        let for_at = (k_impl..b).find(|&m| text(m) == "for");
                        let mut from = k_impl + 1;
                        if is(from, "<") {
                            let mut depth = 0usize;
                            while from < b {
                                match text(from) {
                                    "<" => depth += 1,
                                    ">" => {
                                        depth -= 1;
                                        if depth == 0 {
                                            break;
                                        }
                                    }
                                    _ => {}
                                }
                                from += 1;
                            }
                            from += 1;
                        }
                        let marker = for_at.is_some_and(|f| {
                            let path_ids: Vec<&str> = (from..f)
                                .take_while(|&m| text(m) != "<")
                                .filter(|&m| toks[m].0 == Tok::Ident)
                                .map(text)
                                .collect();
                            path_ids.first().is_some_and(|r| VERUS_ROOTS.contains(r))
                                || path_ids.last().is_some_and(|l| VERUS_MARKERS.contains(l))
                        });
                        if !(marker && empty_body) {
                            return refuse(
                                "an impl that is not an empty impl of a marker trait of Verus's crates",
                            );
                        }
                    }
                    "" => {}
                    other => return refuse(&format!("`{other}`")),
                }
            } else {
                match head {
                    "macro_rules" => {
                        let name = if k + 2 < b { text(k + 2) } else { "" };
                        if !(GHOST_MACROS.contains(&name)
                            && empty_macro(toks, k, item_end(toks, k)))
                        {
                            return refuse(&format!("`macro_rules! {name}`"));
                        }
                    }
                    "trait" => {
                        if marker_trait(src, toks, k, b).is_none() {
                            return refuse("a trait that is not an empty marker trait");
                        }
                    }
                    "impl" => {
                        if !marker_blanket(src, toks, k, b, &markers) {
                            return refuse(
                                "an impl that is not the blanket impl of an empty marker trait",
                            );
                        }
                    }
                    "" => {}
                    other => return refuse(&format!("`{other}`: an item of plain builds only,")),
                }
            }
        }
    }
    None
}

/// The marker traits of `vstd::alloc_check`, also under a re-exported name.
const VERUS_MARKERS: &[&str] = &["AllocFreeDrop", "NoDeallocDrop"];

/// The header of the trait declared at token `k` (`trait`) of `toks[..b]`: the last
/// names of its supertraits (`None` in the list for a `where` clause, which is not
/// read), and the token range of its body. `None` if the header is not read.
fn trait_shape(
    src: &str,
    toks: &[(Tok, usize, usize)],
    k: usize,
    b: usize,
) -> Option<(Vec<Option<String>>, usize, usize)> {
    let text = |m: usize| {
        if m < b {
            &src[toks[m].1..toks[m].2]
        } else {
            ""
        }
    };
    let mut m = k + 2;
    let mut angle = 0i32;
    let mut supers: Vec<Option<String>> = Vec::new();
    let mut in_supers = false;
    let mut last: Option<String> = None;
    loop {
        if m >= b {
            return None;
        }
        match text(m) {
            "<" => angle += 1,
            // (`->`)
            ">" if m > 0 && text(m - 1) == "-" && toks[m - 1].2 == toks[m].1 => {}
            ">" => angle -= 1,
            ":" if angle == 0 && !in_supers && text(m + 1) != ":" && text(m - 1) != ":" => {
                in_supers = true;
            }
            "+" if angle == 0 && in_supers => supers.push(last.take()),
            "where" if angle == 0 => supers.push(None),
            "{" if angle <= 0 => break,
            ";" => return None,
            w if angle == 0 && in_supers && toks[m].0 == Tok::Ident => last = Some(w.to_string()),
            _ => {}
        }
        m += 1;
    }
    if in_supers {
        supers.push(last.take());
    }
    let mut depth = 0usize;
    let mut end = m;
    while end < b {
        match toks[end].0 {
            Tok::Punct(b'{') => depth += 1,
            Tok::Punct(b'}') => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
        end += 1;
    }
    (end < b).then_some((supers, m + 1, end))
}

/// Why the trait declared at token `k`, under `#[cfg(verus_keep_ghost)]`, is more than a
/// trait of specifications: a bound on it would bring methods into scope in Verus's
/// build only. Its supertraits are traits of the crate without methods (`plain`), the
/// drop markers of Verus's crates, or `Sized`.
fn ghost_trait_violation(
    src: &str,
    toks: &[(Tok, usize, usize)],
    k: usize,
    b: usize,
    plain: &std::collections::BTreeSet<String>,
) -> Option<String> {
    let name = &src[toks[k + 1].1..toks[k + 1].2];
    let Some((supers, _, _)) = trait_shape(src, toks, k, b) else {
        return Some(format!("the trait `{name}`, whose header is not read,"));
    };
    for sup in supers {
        match sup {
            Some(t)
                if plain.contains(&t) || VERUS_MARKERS.contains(&t.as_str()) || t == "Sized" => {}
            Some(t) => {
                return Some(format!(
                    "the trait `{name}` with the supertrait `{t}` (a bound on `{name}` would bring `{t}`'s methods into scope in Verus's build only; a supertrait may be a trait of the crate without methods or supertraits)"
                ));
            }
            None => {
                return Some(format!("the trait `{name}` with a `where` clause"));
            }
        }
    }
    None
}

/// Why the impl at token `k` (`impl`), under `#[cfg(verus_keep_ghost)]`, is more than
/// specifications. An inherent impl is read item by item. An impl of a trait exists in
/// Verus's build only, with everything the trait provides: it has to give a `spec` or
/// `proof` function (then the trait is one of specifications: declared under the gate,
/// where no exec function may be), or be an empty impl of a marker of Verus's crates.
fn ghost_impl_violation(
    src: &str,
    toks: &[(Tok, usize, usize)],
    k: usize,
    b: usize,
) -> Option<String> {
    let text = |m: usize| {
        if m < b {
            &src[toks[m].1..toks[m].2]
        } else {
            ""
        }
    };
    let mut m = k + 1;
    let mut angle = 0i32;
    let mut for_at: Option<usize> = None;
    let mut path_from = k + 1;
    loop {
        if m >= b {
            return Some("an impl whose header is not read".to_string());
        }
        match text(m) {
            "<" => angle += 1,
            ">" if text(m - 1) == "-" && toks[m - 1].2 == toks[m].1 => {}
            ">" => {
                angle -= 1;
                if angle == 0 && for_at.is_none() && path_from == k + 1 && text(k + 1) == "<" {
                    path_from = m + 1;
                }
            }
            "for" if angle == 0 && for_at.is_none() => for_at = Some(m),
            "{" if angle <= 0 => break,
            ";" => return Some("an impl whose header is not read".to_string()),
            _ => {}
        }
        m += 1;
    }
    // (an inherent impl: nothing of this rule's)
    let for_at = for_at?;
    let path: Vec<&str> = (path_from..for_at)
        .take_while(|&j| text(j) != "<")
        .filter(|&j| toks[j].0 == Tok::Ident)
        .map(text)
        .collect();
    let (Some(root), Some(last)) = (path.first(), path.last()) else {
        return Some("an impl whose header is not read".to_string());
    };
    let body = m;
    let mut depth = 0usize;
    let mut end = body;
    while end < b {
        match toks[end].0 {
            Tok::Punct(b'{') => depth += 1,
            Tok::Punct(b'}') => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
        end += 1;
    }
    let empty = end == body + 1;
    if empty && (VERUS_ROOTS.contains(root) || VERUS_MARKERS.contains(last)) {
        return None;
    }
    let ghost_fn = (body + 1..end).any(|j| {
        text(j) == "fn" && {
            // (its header, back to the end of what is before it)
            let mut h = j;
            let mut found = false;
            while h > body {
                h -= 1;
                match toks[h].0 {
                    Tok::Punct(b';' | b'{' | b'}' | b']') => break,
                    Tok::Ident if matches!(text(h), "spec" | "proof" | "axiom") => {
                        found = true;
                        break;
                    }
                    _ => {}
                }
            }
            found
        }
    });
    (!ghost_fn).then(|| {
        format!(
            "an impl of the trait `{last}` that gives no `spec` or `proof` function (it exists in Verus's build only, with every method the trait provides)"
        )
    })
}

/// `trait Name {}` or `trait Name<P, ..> {}` in `toks[k..b]`: an empty trait whose
/// parameters, if any, are type parameters without bounds or defaults. Its name and the
/// number of its parameters.
fn marker_trait(
    src: &str,
    toks: &[(Tok, usize, usize)],
    k: usize,
    b: usize,
) -> Option<(String, usize)> {
    let text = |m: usize| {
        if m < b {
            &src[toks[m].1..toks[m].2]
        } else {
            ""
        }
    };
    let ident = |m: usize| m < b && toks[m].0 == Tok::Ident;
    if text(k) != "trait" || !ident(k + 1) {
        return None;
    }
    let mut m = k + 2;
    let mut arity = 0usize;
    if text(m) == "<" {
        loop {
            if !ident(m + 1) {
                return None;
            }
            arity += 1;
            match text(m + 2) {
                "," => m += 2,
                ">" => {
                    m += 3;
                    break;
                }
                _ => return None,
            }
        }
    }
    (text(m) == "{" && text(m + 1) == "}" && m + 2 == b).then(|| (text(k + 1).to_string(), arity))
}

/// `impl<T: ?Sized> Name for T {}` or `impl<T: ?Sized, P, ..> Name<P, ..> for T {}` in
/// `toks[k..b]`, for a marker trait of `markers`: implemented for every type, with every
/// parameter of the trait free.
fn marker_blanket(
    src: &str,
    toks: &[(Tok, usize, usize)],
    k: usize,
    b: usize,
    markers: &std::collections::BTreeMap<String, usize>,
) -> bool {
    let text = |m: usize| {
        if m < b {
            &src[toks[m].1..toks[m].2]
        } else {
            ""
        }
    };
    let ident = |m: usize| m < b && toks[m].0 == Tok::Ident;
    // `impl < T : ? Sized`
    if !(text(k) == "impl"
        && text(k + 1) == "<"
        && ident(k + 2)
        && text(k + 3) == ":"
        && text(k + 4) == "?"
        && text(k + 5) == "Sized")
    {
        return false;
    }
    let this = text(k + 2);
    let mut m = k + 6;
    let mut params: Vec<&str> = Vec::new();
    while text(m) == "," && ident(m + 1) {
        params.push(text(m + 1));
        m += 2;
    }
    if text(m) != ">" || !ident(m + 1) {
        return false;
    }
    let Some(&arity) = markers.get(text(m + 1)) else {
        return false;
    };
    m += 2;
    // The trait's arguments: the impl's other parameters, each once, in order.
    if arity != params.len() || params.contains(&this) {
        return false;
    }
    let distinct: std::collections::BTreeSet<&str> = params.iter().copied().collect();
    if distinct.len() != params.len() {
        return false;
    }
    if arity > 0 {
        if text(m) != "<" {
            return false;
        }
        for (i, p) in params.iter().enumerate() {
            if text(m + 1) != *p {
                return false;
            }
            match (text(m + 2), i + 1 == arity) {
                (",", false) => m += 2,
                (">", true) => m += 3,
                _ => return false,
            }
        }
    }
    text(m) == "for"
        && text(m + 1) == this
        && text(m + 2) == "{"
        && text(m + 3) == "}"
        && m + 4 == b
}

/// The identifiers of `src` (code tokens: not in comments, doc comments or literals;
/// also those of `macro_rules!` bodies and macro arguments).
pub fn ident_tokens(src: &str) -> impl Iterator<Item = &str> {
    code_toks(src)
        .into_iter()
        .filter(|t| t.0 == Tok::Ident)
        .map(move |t| &src[t.1..t.2])
}

fn code_toks(src: &str) -> Vec<(Tok, usize, usize)> {
    lex(src)
        .into_iter()
        .filter(|t| !matches!(t.0, Tok::Ws | Tok::Comment | Tok::OuterDoc))
        .collect()
}

/// The index after the item that starts at token `k` (through its `;`, or its closing
/// `}`), with attributes before it counted in.
fn item_end(toks: &[(Tok, usize, usize)], k: usize) -> usize {
    item_end_in(toks, k, false)
}

/// [`item_end`]; with `in_list`, the item may be an element of a list (a field, a
/// variant, a statement of a block): it also ends before a `,` and before the closer
/// of what encloses it.
fn item_end_in(toks: &[(Tok, usize, usize)], k: usize, in_list: bool) -> usize {
    let mut depth = 0usize;
    let mut m = k;
    while m < toks.len() {
        match toks[m].0 {
            Tok::Punct(b'(' | b'[') => depth += 1,
            Tok::Punct(b')' | b']') if depth == 0 => return m,
            Tok::Punct(b')' | b']') => depth -= 1,
            Tok::Punct(b'}') if depth == 0 => return m,
            Tok::Punct(b',') if depth == 0 && in_list => return m,
            Tok::Punct(b';') if depth == 0 => return m + 1,
            Tok::Punct(b'{') if depth == 0 => {
                let mut braces = 0usize;
                while m < toks.len() {
                    match toks[m].0 {
                        Tok::Punct(b'{') => braces += 1,
                        Tok::Punct(b'}') => {
                            braces -= 1;
                            if braces == 0 {
                                return m + 1;
                            }
                        }
                        _ => {}
                    }
                    m += 1;
                }
                return toks.len();
            }
            _ => {}
        }
        m += 1;
    }
    toks.len()
}

/// Token ranges `k..end` of the items of `toks` with a `#[cfg(..)]` attribute, any
/// predicate (`k` at the `#`); the whole file for an inner `#![cfg(..)]`.
fn gated_items(src: &str, toks: &[(Tok, usize, usize)]) -> Vec<(usize, usize)> {
    let text = |k: usize| &src[toks[k].1..toks[k].2];
    let is = |k: usize, s: &str| k < toks.len() && text(k) == s;
    let mut out = Vec::new();
    for k in 0..toks.len() {
        if !is(k, "#") {
            continue;
        }
        if is(k + 1, "!") && is(k + 2, "[") && is(k + 3, "cfg") && is(k + 4, "(") {
            return vec![(0, toks.len())];
        }
        if is(k + 1, "[") && is(k + 2, "cfg") && is(k + 3, "(") {
            // After the attributes: an item (its header may have commas, in generics),
            // or an element of a list (a field, a variant, an argument).
            let mut first = k;
            while is(first, "#") && is(first + 1, "[") {
                let mut depth = 0usize;
                first += 1;
                while first < toks.len() {
                    match toks[first].0 {
                        Tok::Punct(b'[' | b'(') => depth += 1,
                        Tok::Punct(b']' | b')') => {
                            depth -= 1;
                            if depth == 0 {
                                first += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    first += 1;
                }
            }
            let item = first < toks.len()
                && matches!(
                    text(first),
                    "pub"
                        | "fn"
                        | "impl"
                        | "struct"
                        | "enum"
                        | "union"
                        | "trait"
                        | "mod"
                        | "use"
                        | "const"
                        | "static"
                        | "type"
                        | "macro_rules"
                        | "extern"
                        | "unsafe"
                        | "async"
                        | "default"
                        | "verus"
                );
            out.push((k, item_end_in(toks, k + 1, !item)));
        }
    }
    out
}

/// The leaves of the `use` tree in `toks[from..to]` (after `use`, before `;`): for
/// each, the name it brings and the name of what it imports (they differ with `as`);
/// whether the tree has a glob; and its root. `None` if the root is one of
/// [`VERUS_ROOTS`].
#[allow(clippy::type_complexity)]
fn use_leaves(
    src: &str,
    toks: &[(Tok, usize, usize)],
    from: usize,
    to: usize,
) -> Option<(Vec<(String, String)>, bool, String)> {
    let text = |k: usize| &src[toks[k].1..toks[k].2];
    let root = (from..to).find(|&k| toks[k].0 == Tok::Ident).map(text)?;
    if VERUS_ROOTS.contains(&root) {
        return None;
    }
    let mut leaves = Vec::new();
    let mut glob = false;
    let mut open: Vec<usize> = Vec::new();
    for k in from..=to {
        let boundary = k == to || matches!(toks[k].0, Tok::Punct(b',' | b'}' | b';'));
        if k < to {
            match toks[k].0 {
                Tok::Punct(b'{') => open.push(k),
                Tok::Punct(b'*') => glob = true,
                _ => {}
            }
        }
        if boundary && k > from && toks[k - 1].0 == Tok::Ident {
            let leaf = text(k - 1);
            if leaf == "self" {
                // `a::b::{self}`: the name is `b`.
                if let Some(&b) = open.last()
                    && b >= from + 3
                    && toks[b - 3].0 == Tok::Ident
                {
                    let n = text(b - 3).to_string();
                    leaves.push((n.clone(), n));
                }
            } else {
                // `x as y`: brings `y`, imports `x`.
                let orig = if k >= from + 3 && text(k - 2) == "as" && toks[k - 3].0 == Tok::Ident {
                    text(k - 3)
                } else {
                    leaf
                };
                leaves.push((leaf.to_string(), orig.to_string()));
            }
        }
        if k < to && toks[k].0 == Tok::Punct(b'}') {
            open.pop();
        }
    }
    Some((leaves, glob, root.to_string()))
}

struct Def {
    kind: &'static str,
    name: String,
    /// Token range of the definition, from its keyword.
    at: usize,
    end: usize,
}

/// The `const`, `static`, `type`, `macro_rules!`, `struct`, `enum` and `union`
/// definitions of `toks`, by their names (a `const` generic parameter, `*const T` and
/// `const fn` are none).
fn definitions(src: &str, toks: &[(Tok, usize, usize)]) -> Vec<Def> {
    let text = |k: usize| &src[toks[k].1..toks[k].2];
    let ident = |k: usize| k < toks.len() && toks[k].0 == Tok::Ident;
    let is = |k: usize, s: &str| k < toks.len() && text(k) == s;
    let mut out = Vec::new();
    for k in 0..toks.len() {
        if !ident(k) {
            continue;
        }
        let prev = if k > 0 { text(k - 1) } else { "" };
        let (kind, n) = match text(k) {
            "const" if !matches!(prev, "<" | "," | "*" | "~") && ident(k + 1) && is(k + 2, ":") => {
                ("const", k + 1)
            }
            "static" if ident(k + 1) && is(k + 1, "mut") && ident(k + 2) && is(k + 3, ":") => {
                ("static", k + 2)
            }
            "static" if ident(k + 1) && is(k + 2, ":") => ("static", k + 1),
            "type"
                if ident(k + 1)
                    && (is(k + 2, "=") || is(k + 2, "<") || is(k + 2, ":") || is(k + 2, ";")) =>
            {
                ("type", k + 1)
            }
            "macro_rules" if is(k + 1, "!") && ident(k + 2) => ("macro_rules", k + 2),
            "struct" | "enum" if ident(k + 1) => ("type-def", k + 1),
            "union" if ident(k + 1) && (is(k + 2, "{") || is(k + 2, "<")) => ("type-def", k + 1),
            _ => continue,
        };
        let name = text(n).to_string();
        if name == "_" {
            continue;
        }
        out.push(Def {
            kind,
            name,
            at: k,
            end: item_end(toks, k),
        });
    }
    out
}

/// Whether the `macro_rules!` in `toks[at..end]` expands to nothing in every arm.
fn empty_macro(toks: &[(Tok, usize, usize)], at: usize, end: usize) -> bool {
    let p = |k: usize, c: u8| k < end && toks[k].0 == Tok::Punct(c);
    let mut arms = 0;
    for k in at..end {
        if p(k, b'=') && p(k + 1, b'>') {
            arms += 1;
            if !(p(k + 2, b'{') && p(k + 3, b'}')) {
                return false;
            }
        }
    }
    arms > 0
}

/// The names of `files` (path relative to the crate directory, text) that the two
/// builds may give different meanings ([`Gated`]). The driver's build has no
/// `verus_keep_ghost`: a `macro_rules!`, a `const` or a type alias defined once for each
/// build, or defined for one and found elsewhere by the other (a glob import, an
/// earlier `macro_rules!`), makes one function text two programs (measured
/// 2026-11-24: a `#[fip]` caller of a loop that allocates in the plain build only
/// passed with the bound Verus proved for its own build).
pub fn gated_names(files: &[(String, String)]) -> Gated {
    use std::collections::BTreeSet;
    struct File<'a> {
        path: &'a str,
        src: &'a str,
        toks: Vec<(Tok, usize, usize)>,
        regions: Vec<(usize, usize)>,
        defs: Vec<Def>,
    }
    let mut parsed: Vec<File> = files
        .iter()
        .map(|(path, src)| {
            let toks = code_toks(src);
            let regions = gated_items(src, &toks);
            let defs = definitions(src, &toks);
            File {
                path,
                src,
                toks,
                regions,
                defs,
            }
        })
        .collect();
    let mut names: BTreeSet<String> = BTreeSet::new();
    let mut gated_mods: BTreeSet<String> = BTreeSet::new();
    // (file names given by `#[path = ".."]` on a gated module)
    let mut gated_paths: BTreeSet<String> = BTreeSet::new();
    // A module with `cfg_attr(.., path = ..)`: one build reads another file for it.
    for f in &parsed {
        let text = |k: usize| &f.src[f.toks[k].1..f.toks[k].2];
        for k in 0..f.toks.len() {
            if f.toks[k].0 == Tok::Ident
                && text(k) == "cfg_attr"
                && k >= 2
                && text(k - 1) == "["
                && text(k - 2) == "#"
            {
                let end = item_end(&f.toks, k - 1);
                let has_path = (k..end).any(|m| {
                    f.toks[m].0 == Tok::Ident
                        && text(m) == "path"
                        && m + 1 < end
                        && text(m + 1) == "="
                });
                let module = (k..end).find(|&m| {
                    f.toks[m].0 == Tok::Ident
                        && text(m) == "mod"
                        && m + 2 < f.toks.len()
                        && f.toks[m + 1].0 == Tok::Ident
                        && text(m + 2) == ";"
                });
                if let (true, Some(m)) = (has_path, module) {
                    gated_mods.insert(text(m + 1).to_string());
                }
            }
        }
    }
    // The traits the crate declares: an impl of another one (`Drop`, `Clone`, `Ord`,
    // ..) under a gate can run where no call names it, inside the standard library
    // (`mem::drop(t)`, `Vec::<T>::clear`, `sort`), so the type it is for is a gated
    // name itself (measured: `v.clear()` on a `Vec<Tok>` with a plain-only
    // `impl Drop for Tok` passed).
    let local_traits: BTreeSet<String> = parsed
        .iter()
        .flat_map(|f| {
            (0..f.toks.len()).filter_map(|k| {
                let text = |k: usize| &f.src[f.toks[k].1..f.toks[k].2];
                (f.toks[k].0 == Tok::Ident
                    && text(k) == "trait"
                    && f.toks.get(k + 1).is_some_and(|t| t.0 == Tok::Ident))
                .then(|| text(k + 1).to_string())
            })
        })
        .collect();
    for f in &parsed {
        let text = |k: usize| &f.src[f.toks[k].1..f.toks[k].2];
        for &(a, b) in &f.regions {
            for k in a..b {
                if !(f.toks[k].0 == Tok::Ident && text(k) == "impl") {
                    continue;
                }
                // `impl<..> Path<..> for Type<..> {`: the header, to its `{`.
                let end = (k..b)
                    .find(|&m| f.toks[m].0 == Tok::Punct(b'{'))
                    .unwrap_or(b);
                let Some(at_for) =
                    (k..end).find(|&m| f.toks[m].0 == Tok::Ident && text(m) == "for")
                else {
                    continue;
                };
                // The generic parameters of the impl (a blanket impl is for none of
                // the crate's types).
                let mut params: BTreeSet<&str> = BTreeSet::new();
                if k + 1 < end && text(k + 1) == "<" {
                    let mut depth = 0usize;
                    let mut m = k + 1;
                    while m < at_for {
                        match text(m) {
                            "<" => depth += 1,
                            ">" => {
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                            }
                            _ => {
                                if depth == 1
                                    && f.toks[m].0 == Tok::Ident
                                    && matches!(text(m - 1), "<" | "," | "const")
                                {
                                    params.insert(text(m));
                                }
                            }
                        }
                        m += 1;
                    }
                }
                // The trait and the type: the last identifier of each path, before any `<`.
                let tail = |toks: &[(Tok, usize, usize)]| -> Option<&str> {
                    let mut last = None;
                    let mut depth = 0usize;
                    for t in toks {
                        match &f.src[t.1..t.2] {
                            "<" => depth += 1,
                            ">" => depth = depth.saturating_sub(1),
                            "where" if depth == 0 => break,
                            w => {
                                if depth == 0 && t.0 == Tok::Ident {
                                    last = Some(w);
                                }
                            }
                        }
                    }
                    last
                };
                // (after the impl's own `<..>`)
                let mut from = k + 1;
                if from < at_for && text(from) == "<" {
                    let mut depth = 0usize;
                    while from < at_for {
                        match text(from) {
                            "<" => depth += 1,
                            ">" => {
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                            }
                            _ => {}
                        }
                        from += 1;
                    }
                    from += 1;
                }
                let tr = tail(&f.toks[from.min(at_for)..at_for]);
                if tr.is_none_or(|t| local_traits.contains(t)) {
                    continue;
                }
                let ty = tail(&f.toks[at_for + 1..end]);
                if let Some(t) = ty
                    && !params.contains(t)
                {
                    names.insert(t.to_string());
                }
            }
        }
    }
    // Gated `use` and `mod name;` items.
    for f in &parsed {
        let text = |k: usize| &f.src[f.toks[k].1..f.toks[k].2];
        for &(a, b) in &f.regions {
            // `#[path = "file.rs"]` among the attributes of a gated module.
            for m in a..b {
                if f.toks[m].0 == Tok::Ident
                    && text(m) == "path"
                    && m + 2 < b
                    && text(m + 1) == "="
                    && f.toks[m + 2].0 == Tok::Literal
                {
                    let lit = text(m + 2).trim_matches('"');
                    if let Some(name) = std::path::Path::new(lit)
                        .file_name()
                        .and_then(|n| n.to_str())
                    {
                        gated_paths.insert(name.to_string());
                    }
                }
            }
            // After the attributes and the visibility.
            let mut k = a;
            while k < b && text(k) == "#" {
                let mut depth = 0usize;
                k += 1;
                while k < b {
                    match f.toks[k].0 {
                        Tok::Punct(b'[' | b'(') => depth += 1,
                        Tok::Punct(b']' | b')') => {
                            depth -= 1;
                            if depth == 0 {
                                k += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    k += 1;
                }
            }
            if k < b && text(k) == "pub" {
                k += 1;
                if k < b && text(k) == "(" {
                    while k < b && text(k) != ")" {
                        k += 1;
                    }
                    k += 1;
                }
            }
            if k >= b {
                continue;
            }
            match text(k) {
                "use" => {
                    let to = if text(b - 1) == ";" { b - 1 } else { b };
                    // (a glob brings names that cannot be listed: the crate is one that
                    // `gate_violation` reports, unless the glob is of a ghost module)
                    if let Some((leaves, _glob, _root)) = use_leaves(f.src, &f.toks, k + 1, to) {
                        names.extend(leaves.into_iter().map(|(n, _)| n));
                    }
                }
                "mod" if k + 2 < b && f.toks[k + 1].0 == Tok::Ident && text(k + 2) == ";" => {
                    gated_mods.insert(text(k + 1).to_string());
                }
                _ => {}
            }
        }
    }
    // A module file declared under a gate is gated as a whole.
    let mut files_gated: BTreeSet<String> = BTreeSet::new();
    for f in &mut parsed {
        let p = std::path::Path::new(f.path);
        let stem = p.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        let name = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
        let in_gated_mod = gated_mods.contains(stem)
            || gated_paths.contains(name)
            || p.parent().is_some_and(|d| {
                d.components().any(|c| {
                    c.as_os_str()
                        .to_str()
                        .is_some_and(|c| gated_mods.contains(c))
                })
            });
        if in_gated_mod {
            f.regions = vec![(0, f.toks.len())];
            files_gated.insert(f.path.to_string());
        }
    }
    let mut ghost_macros: BTreeSet<String> = GHOST_MACROS.iter().map(|m| m.to_string()).collect();
    for f in &parsed {
        for d in &f.defs {
            // Under a gate, or with one inside or among its own attributes (a field or
            // a variant of one build only, `cfg_attr(.., derive(..))`, `repr`).
            // (back over the visibility: `pub`, `pub(crate)`, ..)
            let mut first = d.at;
            while first > 0 {
                match f.toks[first - 1].0 {
                    Tok::Ident => first -= 1,
                    Tok::Punct(b')') => {
                        let mut m = first - 1;
                        while m > 0 && f.toks[m].0 != Tok::Punct(b'(') {
                            m -= 1;
                        }
                        if m > 0 && f.toks[m - 1].0 == Tok::Ident {
                            first = m - 1;
                        } else {
                            break;
                        }
                    }
                    _ => break,
                }
            }
            let from = attrs_start(f.src, f.toks[first].1).unwrap_or(f.toks[first].1);
            // (the shapes `cfg_conflict` admits change nothing: `cfg_attr(verus_keep_ghost,
            // verus_verify)`, `verifier::..`, the driver's inert attributes)
            let to = if d.end == 0 {
                from
            } else {
                f.toks[d.end - 1].2
            };
            let own = cfg_conflict(&f.src[from..to]).is_some();
            let gated = own || f.regions.iter().any(|&(a, b)| a <= d.at && d.at < b);
            let shim = d.kind == "macro_rules"
                && GHOST_MACROS.contains(&d.name.as_str())
                && gated
                && empty_macro(&f.toks, d.at, d.end);
            if d.kind == "macro_rules" && GHOST_MACROS.contains(&d.name.as_str()) && !shim {
                ghost_macros.remove(&d.name);
            }
            if gated && !shim {
                names.insert(d.name.clone());
            }
        }
    }
    // Definitions naming one, to a fixpoint.
    loop {
        let mut changed = false;
        for f in &parsed {
            for d in &f.defs {
                if names.contains(&d.name) {
                    continue;
                }
                let hit = (d.at + 1..d.end).any(|k| {
                    f.toks[k].0 == Tok::Ident && names.contains(&f.src[f.toks[k].1..f.toks[k].2])
                });
                if hit {
                    names.insert(d.name.clone());
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    Gated {
        names,
        ghost_macros,
        files: files_gated,
    }
}

/// The first identifier of `item`'s exec code that is one of `gated.names`:
/// attributes (specifications are written in them) and the arguments of
/// `gated.ghost_macros` apart.
///
/// A name in `traits` (the traits declared or implemented in one build only,
/// [`divergent_traits`]) counts only where it is called or is the start of a path
/// (`X(..)`, `X!(..)`, `X::..`). As a bound (`F: Fn(T) -> T + crate::X`) it is the
/// marker pattern, which has its own rules: the generator taints a function naming a
/// method of such a trait, and the driver takes no Verus bound for a generic function.
pub fn gated_name_use(
    item: &str,
    gated: &Gated,
    traits: &std::collections::BTreeSet<String>,
) -> Option<String> {
    let toks = code_toks(item);
    let text = |k: usize| &item[toks[k].1..toks[k].2];
    let close = |open: u8| match open {
        b'(' => b')',
        b'[' => b']',
        _ => b'}',
    };
    // The index after the group opening at `k`.
    let skip_group = |k: usize| -> usize {
        let Tok::Punct(o) = toks[k].0 else {
            return k + 1;
        };
        let c = close(o);
        let mut depth = 0usize;
        let mut m = k;
        while m < toks.len() {
            if toks[m].0 == Tok::Punct(o) {
                depth += 1;
            } else if toks[m].0 == Tok::Punct(c) {
                depth -= 1;
                if depth == 0 {
                    return m + 1;
                }
            }
            m += 1;
        }
        toks.len()
    };
    let mut k = 0;
    while k < toks.len() {
        if text(k) == "#" {
            let b = if k + 1 < toks.len() && text(k + 1) == "!" {
                k + 2
            } else {
                k + 1
            };
            if b < toks.len() && text(b) == "[" {
                k = skip_group(b);
                continue;
            }
        }
        if toks[k].0 == Tok::Ident {
            let w = text(k);
            if gated.ghost_macros.contains(w)
                && k + 2 < toks.len()
                && text(k + 1) == "!"
                && matches!(toks[k + 2].0, Tok::Punct(b'(' | b'[' | b'{'))
            {
                k = skip_group(k + 2);
                continue;
            }
            if gated.names.contains(w) {
                let used = k + 1 < toks.len()
                    && (matches!(toks[k + 1].0, Tok::Punct(b'(' | b'!'))
                        || (toks[k + 1].0 == Tok::Punct(b':')
                            && toks.get(k + 2).is_some_and(|t| t.0 == Tok::Punct(b':'))));
                if used || !traits.contains(w) {
                    return Some(w.to_string());
                }
            }
        }
        k += 1;
    }
    None
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

/// Traits whose implementations or declaration may differ between the Verus build and
/// the driver's (decision 2026-11-06-redesign-verus-allocates, phase 4): the name and
/// the byte offset of every trait implementation (`impl .. Trait<..> for ..`, also
/// `unsafe impl` and inside a `macro_rules!` body) and every trait declaration
/// (`trait Trait`) that lies inside an item gated by a cfg naming `verus_keep_ghost`:
/// `#[cfg(P)]` with `verus_keep_ghost` anywhere in `P` (`verus_keep_ghost`,
/// `not(verus_keep_ghost)`, `all(..)`, ..), or `#[cfg_attr(P, .. cfg(..) ..)]` with
/// `verus_keep_ghost` in `P`.
///
/// Verus checks a call of a trait method against the trait's specification and
/// assumes it holds for every implementation; it never sees a plain-only
/// implementation, and a Verus-only one is not the code the driver analyses (measured
/// with the phase-4 probe: a plain-only `impl Step for S` returning 0 under the Verus
/// declaration's `ensures r > 0` had the divisions by `t.step()` of a generic and of a
/// concrete caller discharged). The generator taints every function naming a method
/// of such a trait ([`crate::verusgen::build`]). A trait is found by its name only, so
/// two traits of one name are both treated as divergent (fail closed).
pub fn divergent_traits(src: &str) -> Vec<(String, usize)> {
    let toks: Vec<(Tok, usize, usize)> = lex(src)
        .into_iter()
        .filter(|t| !matches!(t.0, Tok::Ws | Tok::Comment | Tok::OuterDoc))
        .collect();
    let text = |k: usize| &src[toks[k].1..toks[k].2];
    let is = |k: usize, s: &str| k < toks.len() && text(k) == s;
    // The matching closing delimiter of the opening one at `k`.
    let close = |k: usize| -> usize {
        let mut depth = 0usize;
        let mut m = k;
        while m < toks.len() {
            match toks[m].0 {
                Tok::Punct(b'(' | b'[' | b'{') => depth += 1,
                Tok::Punct(b')' | b']' | b'}') => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return m;
                    }
                }
                _ => {}
            }
            m += 1;
        }
        toks.len()
    };
    // Gated regions: token ranges from the attribute through the item's `;` or `}`.
    let mut regions: Vec<(usize, usize)> = Vec::new();
    let mut k = 0;
    while k + 3 < toks.len() {
        if !(is(k, "#")
            && is(k + 1, "[")
            && (is(k + 2, "cfg") || is(k + 2, "cfg_attr"))
            && is(k + 3, "("))
        {
            k += 1;
            continue;
        }
        let attr_kind = text(k + 2);
        let pclose = close(k + 3);
        // The predicate: up to the first top-level comma of a `cfg_attr`.
        let mut pred_end = pclose;
        if attr_kind == "cfg_attr" {
            let mut depth = 0usize;
            for (m, t) in toks
                .iter()
                .enumerate()
                .take(pclose.min(toks.len()))
                .skip(k + 4)
            {
                match t.0 {
                    Tok::Punct(b'(' | b'[' | b'{') => depth += 1,
                    Tok::Punct(b')' | b']' | b'}') => depth = depth.saturating_sub(1),
                    Tok::Punct(b',') if depth == 0 => {
                        pred_end = m;
                        break;
                    }
                    _ => {}
                }
            }
        }
        let ghost =
            (k + 4..pred_end).any(|m| toks[m].0 == Tok::Ident && text(m) == "verus_keep_ghost");
        let gates = attr_kind == "cfg"
            || (pred_end..pclose).any(|m| toks[m].0 == Tok::Ident && text(m) == "cfg");
        if !(ghost && gates) {
            k += 1;
            continue;
        }
        // The item: through its first `;` or balanced `{ .. }` outside `(..)`/`[..]`.
        let mut m = pclose + 1;
        if is(m, "]") {
            m += 1;
        }
        let mut depth = 0usize;
        let mut end = toks.len();
        while m < toks.len() {
            match toks[m].0 {
                Tok::Punct(b'(' | b'[') => depth += 1,
                Tok::Punct(b')' | b']') => depth = depth.saturating_sub(1),
                Tok::Punct(b';') if depth == 0 => {
                    end = m;
                    break;
                }
                Tok::Punct(b'{') if depth == 0 => {
                    end = close(m);
                    break;
                }
                _ => {}
            }
            m += 1;
        }
        regions.push((k, end.min(toks.len())));
        k += 4;
    }
    let mut out: Vec<(String, usize)> = Vec::new();
    let inside = |m: usize| regions.iter().any(|&(a, b)| a <= m && m < b);
    // A `>` that is not the end of `->`/`=>`.
    let closes_angle = |m: usize| {
        toks[m].0 == Tok::Punct(b'>')
            && !(m > 0
                && matches!(toks[m - 1].0, Tok::Punct(b'-' | b'='))
                && toks[m - 1].2 == toks[m].1)
    };
    for m in 0..toks.len() {
        if toks[m].0 != Tok::Ident || !inside(m) {
            continue;
        }
        match text(m) {
            "trait" if m + 1 < toks.len() && toks[m + 1].0 == Tok::Ident => {
                out.push((text(m + 1).to_string(), toks[m].1));
            }
            "impl" => {
                let mut j = m + 1;
                let mut angle = 0usize;
                // The impl's own generics.
                if is(j, "<") {
                    while j < toks.len() {
                        if is(j, "<") {
                            angle += 1;
                        } else if closes_angle(j) {
                            angle -= 1;
                            if angle == 0 {
                                j += 1;
                                break;
                            }
                        }
                        j += 1;
                    }
                }
                // The trait path, up to `for` at angle depth 0.
                let mut name: Option<&str> = None;
                let mut angle = 0usize;
                while j < toks.len() {
                    match toks[j].0 {
                        Tok::Punct(b'<') => angle += 1,
                        _ if closes_angle(j) => angle = angle.saturating_sub(1),
                        Tok::Punct(b'(' | b'[') => j = close(j),
                        Tok::Punct(b'{' | b';' | b')' | b']' | b',') if angle == 0 => break,
                        Tok::Ident if angle == 0 && text(j) == "for" => {
                            if let Some(n) = name {
                                out.push((n.to_string(), toks[m].1));
                            }
                            break;
                        }
                        Tok::Ident if angle == 0 && text(j) == "where" => break,
                        Tok::Ident if angle == 0 => name = Some(text(j)),
                        _ => {}
                    }
                    j += 1;
                }
            }
            _ => {}
        }
    }
    out
}

/// The trait of a VIR or rustc path of a trait method (`krate::m::Trait::method`):
/// its second-to-last segment, if the path has one.
pub fn trait_segment(path: &str) -> Option<&str> {
    let mut segs = path.rsplit("::");
    segs.next()?;
    segs.next()
}

/// Traits whose implementation is a trust point of the fork's allocation accounting:
/// `allocates` counts calls of the allocator specifications, and an `unsafe impl` of
/// one of these traits is code whose allocator contract Verus does not check (the
/// fork audit, 2026-11-09). `Allocator` is stable since rustc 1.100, with the unsafe
/// marker traits `GlobalAllocator`, `StaticAllocator` and `AllocatorClone` (claims
/// about the allocator's blocks, `core::alloc`).
pub const ALLOCATOR_TRAITS: &[&str] = &[
    "Allocator",
    "GlobalAlloc",
    "GlobalAllocator",
    "StaticAllocator",
    "AllocatorClone",
];

/// Every implementation of a trait named in [`ALLOCATOR_TRAITS`] in `src`, gated or
/// not, also inside `verus! { .. }` and `macro_rules!` bodies, as `(trait, byte offset
/// of `impl`)`. A trait is found by the last segment of its path, so any trait of one
/// of these names counts (fail closed).
pub fn allocator_impls(src: &str) -> Vec<(String, usize)> {
    let toks: Vec<(Tok, usize, usize)> = lex(src)
        .into_iter()
        .filter(|t| !matches!(t.0, Tok::Ws | Tok::Comment | Tok::OuterDoc))
        .collect();
    let text = |k: usize| &src[toks[k].1..toks[k].2];
    let is = |k: usize, s: &str| k < toks.len() && text(k) == s;
    // The matching closing delimiter of the opening one at `k`.
    let close = |k: usize| -> usize {
        let mut depth = 0usize;
        let mut m = k;
        while m < toks.len() {
            match toks[m].0 {
                Tok::Punct(b'(' | b'[' | b'{') => depth += 1,
                Tok::Punct(b')' | b']' | b'}') => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return m;
                    }
                }
                _ => {}
            }
            m += 1;
        }
        toks.len()
    };
    // A `>` that is not the end of `->`/`=>`.
    let closes_angle = |m: usize| {
        toks[m].0 == Tok::Punct(b'>')
            && !(m > 0
                && matches!(toks[m - 1].0, Tok::Punct(b'-' | b'='))
                && toks[m - 1].2 == toks[m].1)
    };
    let mut out = Vec::new();
    for m in 0..toks.len() {
        if toks[m].0 != Tok::Ident || text(m) != "impl" {
            continue;
        }
        let mut j = m + 1;
        // The impl's own generics.
        if is(j, "<") {
            let mut angle = 0usize;
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
        // The trait path, up to `for` at angle depth 0; its last segment is the
        // trait's name.
        let mut name: Option<&str> = None;
        let mut angle = 0usize;
        while j < toks.len() {
            match toks[j].0 {
                Tok::Punct(b'<') => angle += 1,
                _ if closes_angle(j) => angle = angle.saturating_sub(1),
                Tok::Punct(b'(' | b'[') => j = close(j),
                Tok::Punct(b'{' | b';' | b')' | b']' | b',') if angle == 0 => break,
                Tok::Ident if angle == 0 && text(j) == "for" => {
                    if let Some(n) = name
                        && ALLOCATOR_TRAITS.contains(&n)
                    {
                        out.push((n.to_string(), toks[m].1));
                    }
                    break;
                }
                Tok::Ident if angle == 0 && text(j) == "where" => break,
                Tok::Ident if angle == 0 => name = Some(text(j)),
                _ => {}
            }
            j += 1;
        }
    }
    out
}

// ---------------------------------------------------------------------------------
// The sidecar.

/// The `allocates` bound Verus proved for a function (`-V alloc-check`), as the
/// generator records it (decision 2026-11-06-redesign-verus-allocates, phase 4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AllocBound {
    /// No `allocates` clause: nothing proved about allocations.
    None,
    /// `c + Σ kᵢ·pᵢ` over unsigned integer parameters `pᵢ` (sorted by name, every
    /// `kᵢ > 0`); no parameters: the literal `c`.
    Linear(u64, Vec<(String, u64)>),
    /// Any other expression: the SHA-256 of its VIR text without spans and ids.
    Opaque(String),
}

impl AllocBound {
    /// The literal bound, if the bound is one.
    pub fn literal(&self) -> Option<u64> {
        match self {
            AllocBound::Linear(c, terms) if terms.is_empty() => Some(*c),
            _ => None,
        }
    }

    /// The sidecar spelling: `-`, `<c>`, `<c>+<k>*<p>..`, `opaque:<sha256>`.
    pub fn render(&self) -> String {
        match self {
            AllocBound::None => "-".to_string(),
            AllocBound::Linear(c, terms) => {
                let mut s = c.to_string();
                for (p, k) in terms {
                    let _ = write!(s, "+{k}*{p}");
                }
                s
            }
            AllocBound::Opaque(h) => format!("opaque:{h}"),
        }
    }

    /// Reads [`AllocBound::render`]'s spelling; `None` if malformed.
    pub fn parse(s: &str) -> Option<AllocBound> {
        if s == "-" {
            return Some(AllocBound::None);
        }
        if let Some(h) = s.strip_prefix("opaque:") {
            return (h.len() == 64 && h.bytes().all(|b| b.is_ascii_hexdigit()))
                .then(|| AllocBound::Opaque(h.to_string()));
        }
        let mut parts = s.split('+');
        let c: u64 = parts.next()?.parse().ok()?;
        let mut terms: Vec<(String, u64)> = Vec::new();
        for t in parts {
            let (k, p) = t.split_once('*')?;
            let k: u64 = k.parse().ok()?;
            let ident =
                p.bytes().next().is_some_and(is_ident_start) && p.bytes().all(is_ident_continue);
            if k == 0 || !ident || terms.last().is_some_and(|(q, _)| q.as_str() >= p) {
                return None;
            }
            terms.push((p.to_string(), k));
        }
        Some(AllocBound::Linear(c, terms))
    }
}

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
    /// Its proved `allocates` bound (for [`Entry::encapsulates`]: the stated `a`).
    pub allocates: AllocBound,
    /// Its `deallocates` bound (for [`Entry::encapsulates`]: the stated `d`).
    pub deallocates: AllocBound,
    /// The function has `encapsulates alloc(a, d)`: its counts are stated, not proved
    /// (Verus does not check its body against them).
    pub encapsulates: bool,
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
    /// Edition of the run (`--edition`): `2015`, `2018`, `2021`, `2024`.
    pub edition: String,
    pub verified: u64,
    pub sources: Vec<(String, String)>,
    /// The crates the run imported (`--import` with `--import-sidecar`): crate name,
    /// SHA-256 of the sidecar it was imported with, that sidecar's edition.
    pub imports: Vec<(String, String, String)>,
    pub fns: Vec<Entry>,
    /// Exec functions of the crate Verus saw but that are not listed, with why.
    pub skipped: Vec<(String, String)>,
    /// Traits with an implementation or declaration under a cfg naming
    /// `verus_keep_ghost` in a source of the run ([`divergent_traits`]): trait name,
    /// file, line. Every function naming one of their methods is skipped, also in an
    /// importing crate's run.
    pub divergent: Vec<(String, String, usize)>,
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
                    let [t, f, e] = words[..] else {
                        return Err(bad());
                    };
                    if !EDITIONS.contains(&e) {
                        return Err(bad());
                    }
                    s.edition = e.to_string();
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
                "import" => {
                    let [c, h, e] = words[..] else {
                        return Err(bad());
                    };
                    let hex = h.len() == 64 && h.bytes().all(|b| b.is_ascii_hexdigit());
                    if !hex || !EDITIONS.contains(&e) {
                        return Err(bad());
                    }
                    s.imports
                        .push((c.to_string(), h.to_string(), e.to_string()));
                }
                "fn" => {
                    let [p, at, h, r, a, dl, enc] = words[..] else {
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
                    let allocates = AllocBound::parse(a).ok_or_else(bad)?;
                    let deallocates = AllocBound::parse(dl).ok_or_else(bad)?;
                    let encapsulates = match enc {
                        "encapsulates" => true,
                        "-" => false,
                        _ => return Err(bad()),
                    };
                    s.fns.push(Entry {
                        path: p.to_string(),
                        file: f.to_string(),
                        line,
                        hash: h.to_string(),
                        requires,
                        allocates,
                        deallocates,
                        encapsulates,
                    });
                }
                "skip" => {
                    let (p, why) = rest.split_once(' ').unwrap_or((rest, ""));
                    s.skipped.push((p.to_string(), why.to_string()));
                }
                "divergent" => {
                    let [t, at] = words[..] else {
                        return Err(bad());
                    };
                    let (f, line) = at.rsplit_once(':').ok_or_else(bad)?;
                    let line: usize = line.parse().map_err(|_| bad())?;
                    if line == 0 || f.is_empty() {
                        return Err(bad());
                    }
                    s.divergent.push((t.to_string(), f.to_string(), line));
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
             # Exec functions Verus verified with --no-cheating -V alloc-check, with the SHA-256\n\
             # of their item text (outer attributes and doc comments through the body) and\n\
             # their `allocates` and `deallocates` bounds (stated, not proved, for a\n\
             # function with `encapsulates`). Top plan T13.4, redesign phase 4.\n",
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
        let _ = writeln!(o, "cfg {} {features} {}", self.target, self.edition);
        let _ = writeln!(o, "verified {}", self.verified);
        for (p, h) in &self.sources {
            let _ = writeln!(o, "source {p} {h}");
        }
        for (c, h, e) in &self.imports {
            let _ = writeln!(o, "import {c} {h} {e}");
        }
        for e in &self.fns {
            let r = if e.requires { "requires" } else { "-" };
            let enc = if e.encapsulates { "encapsulates" } else { "-" };
            let _ = writeln!(
                o,
                "fn {} {}:{} {} {r} {} {} {enc}",
                e.path,
                e.file,
                e.line,
                e.hash,
                e.allocates.render(),
                e.deallocates.render()
            );
        }
        for (p, why) in &self.skipped {
            let _ = writeln!(o, "skip {p} {why}");
        }
        for (t, f, line) in &self.divergent {
            let _ = writeln!(o, "divergent {t} {f}:{line}");
        }
        o
    }

    /// `Ok` if this sidecar was produced by the trusted Verus build with
    /// `--no-cheating` and `-V alloc-check`, and with no other recorded flag (in
    /// particular none of [`STD_CRATE_FLAGS`]); else why not.
    pub fn check_stamp(&self, trusted: &Trusted) -> Result<(), String> {
        if !self.flags.iter().any(|f| f == NO_CHEATING) {
            return Err(format!("generated without `{NO_CHEATING}`"));
        }
        if !has_alloc_check(&self.flags) {
            return Err(format!(
                "generated without `-V {ALLOC_CHECK}` (its `allocates` bounds were not checked)"
            ));
        }
        if let Some(f) = self
            .flags
            .iter()
            .find(|f| STD_CRATE_FLAGS.contains(&f.as_str()))
        {
            return Err(format!(
                "generated with `{f}` (the crate was verified as a standard-library crate, not as user code)"
            ));
        }
        if let Some(f) = self
            .flags
            .iter()
            .find(|f| ![NO_CHEATING, "-V", ALLOC_CHECK].contains(&f.as_str()))
        {
            return Err(format!(
                "its `flags` record `{f}`, which the driver does not know"
            ));
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

/// What a `Cargo.toml` text says about the edition of the package's library.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ManifestEdition {
    /// `edition = "2024"` of `[lib]`, else of `[package]`; `2015` if neither has the key
    /// (cargo's default).
    Literal(String),
    /// `edition.workspace = true` (or `edition = { workspace = true }`): the edition of
    /// `[workspace.package]` in the workspace's manifest.
    Workspace,
    /// A value this reader does not understand.
    Unknown,
}

/// The edition cargo compiles the library of a `Cargo.toml` text for
/// ([`ManifestEdition`]).
pub fn manifest_edition(manifest: &str) -> ManifestEdition {
    let mut section = String::new();
    let mut package: Option<ManifestEdition> = None;
    let mut lib: Option<ManifestEdition> = None;
    for l in manifest.lines() {
        let t = l.split('#').next().unwrap_or("").trim();
        if t.starts_with('[') {
            section = t.to_string();
            continue;
        }
        let Some((k, v)) = t.split_once('=') else {
            continue;
        };
        let (k, v) = (k.trim(), v.trim());
        let value = match k {
            "edition" => match v.strip_prefix('"').and_then(|v| v.strip_suffix('"')) {
                Some(e) if EDITIONS.contains(&e) => ManifestEdition::Literal(e.to_string()),
                Some(_) => ManifestEdition::Unknown,
                None if v.replace(' ', "") == "{workspace=true}" => ManifestEdition::Workspace,
                None => ManifestEdition::Unknown,
            },
            "edition.workspace" if v == "true" => ManifestEdition::Workspace,
            "edition.workspace" => ManifestEdition::Unknown,
            _ => continue,
        };
        match section.as_str() {
            "[package]" => package = Some(value),
            "[lib]" => lib = Some(value),
            _ => {}
        }
    }
    lib.or(package)
        .unwrap_or_else(|| ManifestEdition::Literal("2015".to_string()))
}

/// The `edition = ".."` of `[workspace.package]` in a workspace manifest's text.
pub fn workspace_edition(manifest: &str) -> Option<String> {
    let mut inside = false;
    for l in manifest.lines() {
        let t = l.split('#').next().unwrap_or("").trim();
        if t.starts_with('[') {
            inside = t == "[workspace.package]";
            continue;
        }
        if inside
            && let Some((k, v)) = t.split_once('=')
            && k.trim() == "edition"
        {
            let e = v.trim().strip_prefix('"')?.strip_suffix('"')?;
            return EDITIONS.contains(&e).then(|| e.to_string());
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

    /// Phase 4 (cfg twins): trait implementations and declarations under a cfg naming
    /// `verus_keep_ghost` make the trait divergent; ungated ones, inherent impls,
    /// `impl Trait` types, `feature` gates and Verus-only specification attributes do
    /// not.
    #[test]
    fn divergent_traits_found_under_ghost_cfgs() {
        let names = |src: &str| -> Vec<String> {
            divergent_traits(src).into_iter().map(|(t, _)| t).collect()
        };
        // The probe's shape: twin declarations and a plain-only implementation.
        let probe = "#[cfg(verus_keep_ghost)]\nverus! {\npub trait Step { fn step(&self) -> u32; }\nimpl Step for S { fn step(&self) -> u32 { 1 } }\n}\n#[cfg(not(verus_keep_ghost))]\npub trait Step { fn step(&self) -> u32; }\n#[cfg(not(verus_keep_ghost))]\nimpl Step for S { fn step(&self) -> u32 { 0 } }\n";
        assert_eq!(names(probe), vec!["Step", "Step", "Step", "Step"]);
        let at: Vec<usize> = divergent_traits(probe)
            .into_iter()
            .map(|(_, o)| line_of(probe, o))
            .collect();
        assert_eq!(at, vec![3, 4, 7, 9]);
        // `fip-strict`'s shapes: generics with `->` and `$(..)*`, paths, `unsafe impl`,
        // a gated impl inside a `macro_rules!` body, any predicate naming the cfg, a
        // `cfg_attr` whose payload is a `cfg`.
        let strict = "macro_rules! m { ($($A:ident),*) => {\n    #[cfg(not(verus_keep_ghost))]\n    impl<C: Fn($($A),*) -> R, $($A,)* R> FipFn<($($A,)*)> for Certified<C> where C: Copy { fn call(&self) {} }\n} }\n#[cfg(not(verus_keep_ghost))]\nunsafe impl<F: crate::FipBound> crate::FipBound for Stateless<F> {}\n#[cfg(all(feature = \"x\", not(verus_keep_ghost)))]\nimpl<T> core::ops::Deref for W<T> { type Target = T; fn deref(&self) -> &T { &self.0 } }\n#[cfg_attr(verus_keep_ghost, cfg(any()))]\nimpl Hidden for X {}\n";
        assert_eq!(names(strict), vec!["FipFn", "FipBound", "Deref", "Hidden"]);
        // Not divergent.
        let same = "pub trait Step { fn step(&self) -> u32; }\nimpl Step for S { fn step(&self) -> u32 { 1 } }\n#[cfg(not(verus_keep_ghost))]\nimpl S { fn plain(&self) -> impl Iterator<Item = u8> { None.into_iter() } }\n#[cfg(feature = \"x\")]\nimpl Other for S {}\n#[cfg_attr(verus_keep_ghost, verus_spec(ensures true))]\nimpl Spec for S {}\n#[cfg(verus_keep_ghost)]\nfn ghost(x: impl Step) -> u8 { 0 }\n";
        assert_eq!(names(same), Vec::<String>::new());
        assert_eq!(trait_segment("fip_strict::FipFn::call"), Some("FipFn"));
        assert_eq!(trait_segment("hole::m::Step::step"), Some("Step"));
        assert_eq!(trait_segment("f"), None);
    }

    /// The fork audit (2026-11-09): implementations of `Allocator` / `GlobalAlloc`,
    /// by any path, generic, gated, inside `verus!` or a `macro_rules!` body, are
    /// found; a bound or a parameter of that name, an inherent impl, a comment and a
    /// string are not.
    #[test]
    fn allocator_impls_found() {
        let names = |src: &str| -> Vec<String> {
            allocator_impls(src).into_iter().map(|(t, _)| t).collect()
        };
        let found = "unsafe impl core::alloc::GlobalAlloc for Arena {}\nverus! {\nunsafe impl<'a, T: Copy> Allocator for &'a Pool<T> where T: Send {}\n}\nmacro_rules! m { ($t:ty) => { unsafe impl ::core::alloc::Allocator for $t {} } }\n#[cfg(not(verus_keep_ghost))]\nunsafe impl<F: Fn() -> u8> std::alloc::GlobalAlloc for Sys<F> {}\nunsafe impl core::alloc::StaticAllocator for Arena {}\n";
        assert_eq!(
            names(found),
            vec![
                "GlobalAlloc",
                "Allocator",
                "Allocator",
                "GlobalAlloc",
                "StaticAllocator"
            ]
        );
        let at: Vec<usize> = allocator_impls(found)
            .into_iter()
            .map(|(_, o)| line_of(found, o))
            .collect();
        assert_eq!(at, vec![1, 3, 5, 7, 8]);
        let none = "impl<A: Allocator> Vec2<A> { fn f(a: A) {} }\nimpl<A: GlobalAlloc> Wrap for Holder<A> {}\nimpl dyn Allocator {}\n// unsafe impl Allocator for X {}\nconst S: &str = \"unsafe impl GlobalAlloc for Y {}\";\nimpl AllocatorLike for Z {}\nfn g(x: impl Allocator) {}\n";
        assert_eq!(names(none), Vec::<String>::new());
    }

    /// Phase 4: the spellings of proved bounds.
    #[test]
    fn alloc_bound_spellings() {
        let h = "ab".repeat(32);
        for (b, text) in [
            (AllocBound::None, "-".to_string()),
            (AllocBound::Linear(0, Vec::new()), "0".to_string()),
            (AllocBound::Linear(7, Vec::new()), "7".to_string()),
            (
                AllocBound::Linear(1, vec![("m".to_string(), 1), ("n".to_string(), 2)]),
                "1+1*m+2*n".to_string(),
            ),
            (AllocBound::Opaque(h.clone()), format!("opaque:{h}")),
        ] {
            assert_eq!(b.render(), text);
            assert_eq!(AllocBound::parse(&text), Some(b));
        }
        assert_eq!(AllocBound::parse("7").and_then(|b| b.literal()), Some(7));
        assert_eq!(AllocBound::parse("0+1*n").and_then(|b| b.literal()), None);
        for bad in [
            "",
            "x",
            "-1",
            "1+n",
            "1+0*n",
            "1+2*n+1*m",
            "1+1*n+1*n",
            "opaque:zz",
            "1+2*9n",
        ] {
            assert_eq!(AllocBound::parse(bad), None, "{bad}");
        }
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
            flags: vec![
                NO_CHEATING.to_string(),
                "-V".to_string(),
                ALLOC_CHECK.to_string(),
            ],
            target: "x86_64-unknown-linux-gnu".to_string(),
            features: vec!["a".to_string(), "b".to_string()],
            edition: "2024".to_string(),
            verified: 3,
            sources: vec![("src/lib.rs".to_string(), "00".to_string())],
            imports: vec![("dep".to_string(), "ab".repeat(32), "2021".to_string())],
            fns: vec![Entry {
                path: "c::{impl}::f".to_string(),
                file: "src/lib.rs".to_string(),
                line: 12,
                hash: "11".to_string(),
                requires: true,
                allocates: AllocBound::Linear(2, vec![("n".to_string(), 3)]),
                deallocates: AllocBound::Linear(1, Vec::new()),
                encapsulates: true,
            }],
            skipped: vec![("c::g".to_string(), "external body".to_string())],
            divergent: vec![("Step".to_string(), "src/lib.rs".to_string(), 3)],
        };
        assert_eq!(Sidecar::parse(&s.render()), Ok(s.clone()));
        assert!(s.render().contains("\ndivergent Step src/lib.rs:3\n"));
        assert!(
            Sidecar::parse(
                &s.render()
                    .replace("divergent Step src/lib.rs:3", "divergent Step")
            )
            .is_err()
        );
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
        // Without `--no-cheating` (also with `-V alloc-check`): refused.
        for flags in [Vec::new(), vec!["-V".to_string(), ALLOC_CHECK.to_string()]] {
            let cheat = Sidecar { flags, ..s.clone() };
            assert!(
                cheat
                    .check_stamp(&t)
                    .is_err_and(|e| e.contains("without `--no-cheating`")),
                "{:?}",
                cheat.check_stamp(&t)
            );
        }
        // A standard-library crate run (the fork audit): refused, whatever else the
        // flags hold; so is any flag the driver does not know.
        for f in STD_CRATE_FLAGS {
            let std_crate = Sidecar {
                flags: vec![
                    NO_CHEATING.to_string(),
                    (*f).to_string(),
                    "-V".to_string(),
                    ALLOC_CHECK.to_string(),
                ],
                ..s.clone()
            };
            assert!(
                std_crate
                    .check_stamp(&t)
                    .is_err_and(|e| e.contains(&format!("generated with `{f}`"))),
                "{:?}",
                std_crate.check_stamp(&t)
            );
            assert!(Sidecar::parse(&std_crate.render()).is_ok_and(|p| p == std_crate));
        }
        let unknown = Sidecar {
            flags: vec![
                NO_CHEATING.to_string(),
                "-V".to_string(),
                ALLOC_CHECK.to_string(),
                "--no-lifetime".to_string(),
            ],
            ..s.clone()
        };
        assert!(
            unknown
                .check_stamp(&t)
                .is_err_and(|e| e.contains("`--no-lifetime`")),
            "{:?}",
            unknown.check_stamp(&t)
        );
        // Format 5: `-V alloc-check` is part of the stamp.
        let unchecked = Sidecar {
            flags: vec![NO_CHEATING.to_string()],
            ..s.clone()
        };
        assert!(
            unchecked
                .check_stamp(&t)
                .is_err_and(|e| e.contains("-V alloc-check")),
            "{:?}",
            unchecked.check_stamp(&t)
        );
        // Every `fn` line has its bound.
        assert!(
            s.render().contains(" requires 2+3*n 1 encapsulates\n"),
            "{}",
            s.render()
        );
        for short in [
            " requires\n",
            " requires 2+3*n\n",
            " requires 2+3*n 1\n",
            " requires 2+3*n 1 yes\n",
        ] {
            let cut = s
                .render()
                .replace(" requires 2+3*n 1 encapsulates\n", short);
            assert!(Sidecar::parse(&cut).is_err(), "{short}");
        }
        assert_eq!(
            verus_internal_use("fn f() {}\n#[verus::internal(encapsulates_alloc)]\nfn g() {}"),
            Some(2)
        );
        assert_eq!(
            verus_internal_use("#[cfg_attr(verus_keep_ghost, verus :: internal(x))] fn g() {}"),
            Some(1)
        );
        assert_eq!(
            verus_internal_use("macro_rules! m { () => { #[verus::internal(x)] fn g() {} } }"),
            Some(1)
        );
        assert_eq!(
            verus_internal_use(
                "// verus::internal\n/// verus::internal\nfn f() { let _ = \"verus::internal\"; }"
            ),
            None
        );
        assert_eq!(
            verus_internal_use("#[verus::r#internal(x)]\nfn g() {}"),
            Some(1)
        );
        assert_eq!(
            verus_internal_use(
                "macro_rules! m { ($t:ident, $i:ident) => { #[$t::$i(x)] fn g() {} } }\nm!(verus, internal);"
            ),
            Some(2)
        );
        assert_eq!(
            verus_internal_use("use verus::internals; fn internal_use() {}"),
            None
        );
        let current = format!("format {FORMAT}");
        for old in ["format 6", "format 5", "format 4", "format 3", "format 2"] {
            assert!(
                Sidecar::parse(&s.render().replace(&current, old)).is_err(),
                "{old}"
            );
        }
        // Format 3 and later require the `cfg` line.
        assert!(
            Sidecar::parse(
                &s.render()
                    .replace("cfg x86_64-unknown-linux-gnu a,b 2024\n", "")
            )
            .is_err()
        );
        let none = Sidecar {
            features: Vec::new(),
            edition: "2024".to_string(),
            ..s.clone()
        };
        assert!(
            none.render()
                .contains("cfg x86_64-unknown-linux-gnu - 2024\n")
        );
        let line = format!("import dep {} 2021\n", "ab".repeat(32));
        assert!(s.render().contains(&line), "{}", s.render());
        for bad in [
            format!("import dep {} 2023\n", "ab".repeat(32)),
            "import dep abab 2021\n".to_string(),
            format!("import dep {}\n", "ab".repeat(32)),
        ] {
            assert!(
                Sidecar::parse(&s.render().replace(&line, &bad)).is_err(),
                "{bad}"
            );
        }
        assert_eq!(
            manifest_edition("[package]\nname = \"a\"\nedition = \"2024\"\n"),
            ManifestEdition::Literal("2024".to_string())
        );
        assert_eq!(
            manifest_edition("[package]\nname = \"a\"\n"),
            ManifestEdition::Literal("2015".to_string())
        );
        assert_eq!(
            manifest_edition("[package]\nedition = \"2024\"\n[lib]\nedition = \"2021\" # old\n"),
            ManifestEdition::Literal("2021".to_string())
        );
        assert_eq!(
            manifest_edition("[package]\nedition.workspace = true\n"),
            ManifestEdition::Workspace
        );
        assert_eq!(
            manifest_edition("[package]\nedition = { workspace = true }\n"),
            ManifestEdition::Workspace
        );
        assert_eq!(
            manifest_edition("[package]\nedition = \"2027\"\n"),
            ManifestEdition::Unknown
        );
        assert_eq!(
            manifest_edition("[package]\nname = \"a\"\n[dependencies]\nedition = \"2021\"\n"),
            ManifestEdition::Literal("2015".to_string())
        );
        assert_eq!(
            workspace_edition(
                "[workspace]\nmembers = []\n[workspace.package]\nedition = \"2024\"\n"
            ),
            Some("2024".to_string())
        );
        assert_eq!(workspace_edition("[workspace]\nmembers = []\n"), None);
        // The edition is part of the line: none, or one rustc does not have, is malformed.
        for bad in [
            "cfg x86_64-unknown-linux-gnu a,b\n",
            "cfg x86_64-unknown-linux-gnu a,b 2023\n",
        ] {
            let cut = s
                .render()
                .replace("cfg x86_64-unknown-linux-gnu a,b 2024\n", bad);
            assert!(Sidecar::parse(&cut).is_err(), "{bad}");
        }
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

    fn gated_of(files: &[(&str, &str)]) -> Gated {
        let files: Vec<(String, String)> = files
            .iter()
            .map(|(p, s)| (p.to_string(), s.to_string()))
            .collect();
        gated_names(&files)
    }

    /// Amendment 2026-11-24 (4): what the two builds may define differently.
    #[test]
    fn gated_definitions_are_found() {
        // A macro, a const, a static, a type alias and a struct, each defined once per build.
        let twins = "#[cfg(verus_keep_ghost)]\nmacro_rules! tick { ($x:expr) => {}; }\n#[cfg(not(verus_keep_ghost))]\nmacro_rules! tick { ($x:expr) => { core::mem::forget(Box::new($x)); }; }\n#[cfg(verus_keep_ghost)]\npub const N: usize = 0;\n#[cfg(not(verus_keep_ghost))]\npub const N: usize = 64;\n#[cfg(not(verus_keep_ghost))]\nstatic mut S: u8 = 0;\n#[cfg(verus_keep_ghost)]\npub type Cell = u64;\n#[cfg(not(verus_keep_ghost))]\npub struct Buf(Box<u8>);\npub const FREE: usize = 1;\npub fn f<const K: usize>(p: *const u8) {}\n";
        let g = gated_of(&[("src/lib.rs", twins)]);
        for n in ["tick", "N", "S", "Cell", "Buf"] {
            assert!(g.names.contains(n), "{n}: {:?}", g.names);
        }
        // Not gated; a const generic parameter and `*const T` define nothing.
        for n in ["FREE", "K", "u8", "f"] {
            assert!(!g.names.contains(n), "{n}: {:?}", g.names);
        }
        // Definitions that name a gated one, to a fixpoint; inside a gated item too.
        let chain = "#[cfg(verus_keep_ghost)]\nverus! {\n    pub const N: usize = 0;\n}\npub const M: usize = N + 1;\npub struct W { c: [u8; M] }\nmacro_rules! use_w { () => { W { c: [0; M] } }; }\npub const OTHER: usize = 3;\n";
        let g = gated_of(&[("src/lib.rs", chain)]);
        for n in ["N", "M", "W", "use_w"] {
            assert!(g.names.contains(n), "{n}: {:?}", g.names);
        }
        assert!(!g.names.contains("OTHER"));
        // A module file declared under a gate is gated as a whole; `#![cfg(..)]` too.
        let g = gated_of(&[
            (
                "src/lib.rs",
                "#[cfg(verus_keep_ghost)]\npub mod spec;\nmod plain;\n",
            ),
            ("src/spec.rs", "pub const K: usize = 1;\n"),
            ("src/spec/state.rs", "pub type T = u8;\n"),
            ("src/plain.rs", "pub const P: usize = 1;\n"),
            (
                "src/inner.rs",
                "#![cfg(not(verus_keep_ghost))]\npub const Q: usize = 1;\n",
            ),
        ]);
        assert!(g.names.contains("K") && g.names.contains("T") && g.names.contains("Q"));
        assert!(!g.names.contains("P"));
    }

    #[test]
    fn gated_uses_are_found() {
        // Verus's crates bring ghost names; other paths bring names by their leaves.
        let src = "#[cfg(verus_keep_ghost)]\nuse vstd::prelude::*;\n#[cfg(verus_keep_ghost)]\npub use vstd::alloc_check::NoDeallocDrop;\n#[cfg(verus_keep_ghost)]\nuse crate::spec::{a, b as c, m::{self, d}};\n#[cfg(verus_keep_ghost)]\npub(crate) use core::marker::Copy as DropFreeFn;\nuse core::mem::swap;\n";
        let g = gated_of(&[("src/lib.rs", src)]);
        for n in ["a", "c", "m", "d", "DropFreeFn"] {
            assert!(g.names.contains(n), "{n}: {:?}", g.names);
        }
        for n in [
            "b",
            "spec",
            "core",
            "marker",
            "Copy",
            "swap",
            "NoDeallocDrop",
            "prelude",
        ] {
            assert!(!g.names.contains(n), "{n}: {:?}", g.names);
        }
        // A gated glob brings names that cannot be listed: none here, and the crate is
        // one `gate_violation` reports.
        let g = gated_of(&[("src/lib.rs", "#[cfg(verus_keep_ghost)]\nuse a::*;\n")]);
        assert!(g.names.is_empty(), "{:?}", g.names);
        assert!(violation(&[("src/lib.rs", "#[cfg(verus_keep_ghost)]\nuse a::*;\n")]).is_some());
    }

    #[test]
    fn ghost_macro_shims() {
        // fip-core's shims: nothing in plain builds, vstd's macros under Verus.
        let shim = "#[cfg(not(verus_keep_ghost))]\nmacro_rules! proof { ($($t:tt)*) => {}; }\n#[cfg(not(verus_keep_ghost))]\nmacro_rules! proof_decl { ($($t:tt)*) => {}; }\n";
        let g = gated_of(&[("src/lib.rs", shim)]);
        assert!(g.names.is_empty(), "{:?}", g.names);
        assert!(g.ghost_macros.contains("proof") && g.ghost_macros.contains("proof_decl"));
        // A shim that expands to code is a gated macro like another, and its arguments
        // are not ghost code; so is an ungated macro of that name.
        let full =
            "#[cfg(not(verus_keep_ghost))]\nmacro_rules! proof { ($($t:tt)*) => { $($t)* }; }\n";
        let g = gated_of(&[("src/lib.rs", full)]);
        assert!(g.names.contains("proof") && !g.ghost_macros.contains("proof"));
        let own = "macro_rules! proof { ($($t:tt)*) => { $($t)* }; }\n";
        let g = gated_of(&[("src/lib.rs", own)]);
        assert!(!g.names.contains("proof") && !g.ghost_macros.contains("proof"));
        assert!(g.ghost_macros.contains("proof_decl"));
    }

    #[test]
    fn gated_names_in_exec_code() {
        let none = std::collections::BTreeSet::new();
        let g = Gated {
            names: ["N", "tick", "post", "Marker"]
                .iter()
                .map(|s| s.to_string())
                .collect(),
            ghost_macros: ["proof"].iter().map(|s| s.to_string()).collect(),
            files: Default::default(),
        };
        let hit = |item: &str| gated_name_use(item, &g, &none);
        assert_eq!(hit("pub fn f() -> usize { N }").as_deref(), Some("N"));
        assert_eq!(
            hit("pub fn f(i: u8) { tick!(i); }").as_deref(),
            Some("tick")
        );
        // Specifications (attributes) and ghost blocks are not exec code.
        assert_eq!(
            hit(
                "#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures post(r), N > 0))]\npub fn f() -> u8 {\n    #[cfg_attr(verus_keep_ghost, verus_spec(invariant post(0)))]\n    loop {}\n    proof! { assert(post(N)); }\n}"
            ),
            None
        );
        assert_eq!(
            hit("// N\n/// tick\npub fn f() -> &'static str { \"N\" }"),
            None
        );
        // Without the shim the arguments of `proof!` are code.
        let g2 = Gated {
            names: g.names.clone(),
            ghost_macros: Default::default(),
            files: Default::default(),
        };
        assert_eq!(
            gated_name_use("pub fn f() { proof! { let _x = N; } }", &g2, &none).as_deref(),
            Some("N")
        );
        // A divergent trait as a bound is the marker pattern; called, or as a path, it is not.
        let traits: std::collections::BTreeSet<String> = ["Marker".to_string()].into();
        let with = |item: &str| gated_name_use(item, &g, &traits);
        assert_eq!(
            with("pub fn f<T: crate::Marker + Copy>(t: T) where T: Marker {}"),
            None
        );
        assert_eq!(with("pub fn f() { Marker(); }").as_deref(), Some("Marker"));
        assert_eq!(
            with("pub fn f() { Marker::go(); }").as_deref(),
            Some("Marker")
        );
        assert_eq!(
            hit("pub fn f<T: Marker>(t: T) {}").as_deref(),
            Some("Marker")
        );
    }

    /// Audit 2026-11-24: other ways one text is two programs.
    #[test]
    fn gated_from_inside_and_by_attributes() {
        // A field of one build only, a derive or a `repr` of one build only.
        let src = "#[cfg_attr(verus_keep_ghost, verus_verify)]\npub struct Ok1(u8);\n#[cfg_attr(verus_keep_ghost, verifier::external_body)]\n#[cfg_attr(fip_prelint, fip::mark(kind = \"x\"))]\npub struct Ok2(u8);\npub struct Buf {\n    pub a: u8,\n    #[cfg(not(verus_keep_ghost))]\n    pub extra: Box<u8>,\n}\n#[cfg_attr(not(verus_keep_ghost), derive(Clone))]\npub struct D(u8);\n#[cfg_attr(not(verus_keep_ghost), repr(C))]\npub(crate) struct R(u8);\npub enum E {\n    A,\n    #[cfg(verus_keep_ghost)]\n    B,\n}\n#[derive(Clone)]\npub struct Plain(u8);\n";
        let g = gated_of(&[("src/lib.rs", src)]);
        for n in ["Buf", "D", "R", "E"] {
            assert!(g.names.contains(n), "{n}: {:?}", g.names);
        }
        for n in ["Plain", "Ok1", "Ok2"] {
            assert!(!g.names.contains(n), "{n}: {:?}", g.names);
        }
    }

    #[test]
    fn gated_trait_imports_are_names() {
        // A trait with methods in scope in one build only changes what `x.m()` calls,
        // and the call does not name it: such a crate is one `gate_violation` reports
        // (amendment 2026-11-25 (2)); here the import gives its name like another.
        let twins = "pub mod a { pub trait Tr { fn m(self); } }\npub mod b { pub trait Tr { fn m(self); } }\n#[cfg(verus_keep_ghost)]\nuse crate::a::Tr;\n#[cfg(not(verus_keep_ghost))]\nuse crate::b::Tr;\n";
        assert!(gated_of(&[("src/lib.rs", twins)]).names.contains("Tr"));
        let e = violation(&[("src/lib.rs", twins)]).unwrap();
        assert!(
            e.starts_with("src/lib.rs:3: a `use` of something else"),
            "{e}"
        );
        let marker = "#[cfg(verus_keep_ghost)]\npub use core::marker::Copy as DropFreeFn;\n";
        assert!(
            gated_of(&[("src/lib.rs", marker)])
                .names
                .contains("DropFreeFn")
        );
    }

    #[test]
    fn gated_module_files() {
        // `#[path]` under a gate, and `cfg_attr(.., path = ..)`: the module's file is
        // another one in the other build.
        let g = gated_of(&[
            (
                "src/lib.rs",
                "#[cfg(verus_keep_ghost)]\n#[path = \"v_verus.rs\"]\npub mod v;\n#[cfg_attr(not(verus_keep_ghost), path = \"w_plain.rs\")]\npub mod w;\npub mod x;\n",
            ),
            ("src/v_verus.rs", "pub fn helper() {}\n"),
            ("src/w.rs", "pub fn helper() {}\n"),
            ("src/x.rs", "pub fn helper() {}\n"),
        ]);
        assert!(
            g.files.contains("src/v_verus.rs") && g.files.contains("src/w.rs"),
            "{:?}",
            g.files
        );
        assert!(!g.files.contains("src/x.rs") && !g.files.contains("src/lib.rs"));
        // An item under any gate, also one that `ghost_only_regions` does not read.
        let src = "#[cfg(all(verus_keep_ghost))]\npub mod v {\n    pub fn helper() {}\n}\npub fn free() {}\n";
        let at = src.find("pub fn helper").unwrap();
        assert!(in_gated_item(src, at, at + 18));
        let at = src.find("pub fn free").unwrap();
        assert!(!in_gated_item(src, at, at + 16));
        assert!(ghost_only_regions(src).is_empty());
        // An item's header may have commas: the whole item is under the gate.
        let src = "#[cfg(not(verus_keep_ghost))]\nimpl<A, B> Tr<A, B> for S<A, B>\nwhere\n    A: Copy,\n{\n    fn m(self) {}\n}\npub fn free() {}\n";
        let at = src.find("fn m").unwrap();
        assert!(in_gated_item(src, at, at + 13));
        let at = src.find("pub fn free").unwrap();
        assert!(!in_gated_item(src, at, at + 16));
    }

    /// Audit 2026-11-24: an impl of a std trait under a gate runs inside std.
    #[test]
    fn gated_impls_of_foreign_traits() {
        let src = "pub struct Tok(u8);\npub struct Num(u8);\npub struct Free(u8);\npub trait Own { fn m(&self); }\n#[cfg(not(verus_keep_ghost))]\nimpl Drop for Tok {\n    fn drop(&mut self) {}\n}\n#[cfg(not(verus_keep_ghost))]\nimpl<'a> core::cmp::PartialEq<Num> for crate::Num {\n    fn eq(&self, o: &Num) -> bool { true }\n}\n#[cfg(not(verus_keep_ghost))]\nimpl Own for Free {\n    fn m(&self) {}\n}\n#[cfg(not(verus_keep_ghost))]\nimpl<T: ?Sized> Clone for Wrap<T> where T: Copy {\n    fn clone(&self) -> Self { loop {} }\n}\n#[cfg(not(verus_keep_ghost))]\nimpl<T> Default for T {\n    fn default() -> T { loop {} }\n}\nimpl Clone for Free {\n    fn clone(&self) -> Self { Free(0) }\n}\n";
        let g = gated_of(&[("src/lib.rs", src)]);
        for n in ["Tok", "Num", "Wrap"] {
            assert!(g.names.contains(n), "{n}: {:?}", g.names);
        }
        // A trait of the crate (its methods are named where they are called), a
        // blanket impl, an impl that is not gated.
        for n in ["Free", "T", "Own"] {
            assert!(!g.names.contains(n), "{n}: {:?}", g.names);
        }
    }

    fn violation(files: &[(&str, &str)]) -> Option<String> {
        let files: Vec<(String, String)> = files
            .iter()
            .map(|(p, s)| (p.to_string(), s.to_string()))
            .collect();
        gate_violation(&files)
    }

    /// Amendments 2026-11-25: what may be under `verus_keep_ghost`. The allowed shapes,
    /// together (fip-core's and a crate with a marker).
    #[test]
    fn gate_whitelist_allows() {
        let lib = "#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]\n#![cfg_attr(fip_prelint, fip::export)]\n#[cfg(verus_keep_ghost)]\nuse vstd::prelude::*;\n#[cfg(verus_keep_ghost)]\npub mod spec;\n#[cfg(verus_keep_ghost)]\nuse crate::spec::{post, inv};\n#[cfg(verus_keep_ghost)]\nuse crate::spec::state::{\n    step_ok,\n};\n#[cfg(not(verus_keep_ghost))]\nmacro_rules! proof { ($($t:tt)*) => {}; }\n#[cfg(not(verus_keep_ghost))]\nmacro_rules! proof_decl {\n    ($($t:tt)*) => {};\n}\n#[cfg(verus_keep_ghost)]\npub use vstd::alloc_check::NoDeallocDrop;\n/// Every type, in plain builds.\n#[cfg(not(verus_keep_ghost))]\npub trait NoDeallocDrop {}\n#[cfg(not(verus_keep_ghost))]\nimpl<T: ?Sized> NoDeallocDrop for T {}\n#[cfg_attr(verus_keep_ghost, verus_verify)]\npub struct S(pub u8);\n#[cfg(verus_keep_ghost)]\n#[allow(unsafe_code)]\nunsafe impl vstd::alloc_check::NoDeallocDrop for S {}\n#[cfg(verus_keep_ghost)]\nunsafe impl<T: Copy> crate::NoDeallocDrop for W<T> {}\n#[cfg(verus_keep_ghost)]\nverus! {\nuse vstd::seq::*;\npub open spec fn twice(x: int) -> int { 2 * x }\npub spec const LIMIT: int = 8;\nproof fn lemma() ensures true { let t = seq![1int]; }\npub broadcast proof fn b(x: int) ensures #[trigger] twice(x) == 2 * x {}\npub broadcast group g { b }\nbroadcast use g;\nimpl View for S { type V = int; open spec(checked) fn view(&self) -> int { 0 } }\npub trait Model { type M; spec fn model(&self) -> Self::M; }\n#[allow(unsafe_code)] unsafe impl<const N: usize> vstd::alloc_check::AllocFreeDrop for S {}\n}\n#[cfg(verus_keep_ghost)]\nmod more {\n    use super::*;\n    verus! { pub closed spec fn k() -> bool { true } }\n}\n#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == x))]\n#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict))]\npub fn id(x: u8) -> u8 {\n    proof! { assert(twice(1) == 2); }\n    x\n}\n/// Verus ignores it (no attribute): no gate needed.\npub fn plain_root() {}\n";
        let spec = "use vstd::prelude::*;\nuse super::S;\nverus! {\npub open spec fn post(x: int) -> bool { true }\npub closed spec fn inv(x: int) -> bool { true }\npub mod state {\n    use super::*;\n    pub open spec fn step_ok(x: int) -> bool { post(x) }\n}\n}\n";
        assert_eq!(
            violation(&[("src/lib.rs", lib), ("src/spec.rs", spec)]),
            None
        );
        // Other cfgs are not this rule's (the crate scan refuses or records them).
        assert_eq!(
            violation(&[("src/lib.rs", "#[cfg(feature = \"x\")]\npub fn f() {}\n")]),
            None
        );
    }

    /// Everything else under the gate, whatever it is.
    #[test]
    fn gate_marker_traits_with_parameters() {
        // A marker of plain builds may have type parameters, each free in the blanket
        // impl: the supertrait `FipSpec<Args>` of `fip_strict::FipFn`, a trait of
        // specifications under Verus (amendment 2026-11-25 (3)).
        let ok = "#[cfg(not(verus_keep_ghost))]\npub trait Spec<Args> {}\n#[cfg(not(verus_keep_ghost))]\nimpl<T: ?Sized, Args> Spec<Args> for T {}\n#[cfg(not(verus_keep_ghost))]\npub trait Two<A, B> {}\n#[cfg(not(verus_keep_ghost))]\nimpl<X: ?Sized, A, B> Two<A, B> for X {}\n#[cfg(verus_keep_ghost)]\nverus! {\npub trait Spec<Args>: Out<Args> {\n    spec fn pre(&self, args: Args) -> bool;\n    spec fn post(&self, args: Args, out: Self::Output) -> bool;\n}\n}\npub trait Out<Args> { type Output; }\n";
        assert_eq!(violation(&[("src/lib.rs", ok)]), None);
        for (decl, what) in [
            // not empty, bounded, defaulted, a lifetime, a const
            (
                "pub trait M<A> { fn m(&self); }",
                "a trait that is not an empty marker trait",
            ),
            (
                "pub trait M<A: Copy> {}",
                "a trait that is not an empty marker trait",
            ),
            (
                "pub trait M<A = u8> {}",
                "a trait that is not an empty marker trait",
            ),
            (
                "pub trait M<'a> {}",
                "a trait that is not an empty marker trait",
            ),
            (
                "pub trait M<const N: usize> {}",
                "a trait that is not an empty marker trait",
            ),
            (
                "pub trait M<A>: Copy {}",
                "a trait that is not an empty marker trait",
            ),
            (
                "pub trait M<A> where A: Copy {}",
                "a trait that is not an empty marker trait",
            ),
        ] {
            let src = format!("#[cfg(not(verus_keep_ghost))]\n{decl}\n");
            let e = violation(&[("src/lib.rs", &src)]).unwrap();
            assert!(e.contains(what), "{decl}: {e}");
        }
        for imp in [
            // not every type, not every argument, an argument twice, the wrong number
            "impl<T, A> M<A> for T {}",
            "impl<T: ?Sized, A: Copy> M<A> for T {}",
            "impl<T: ?Sized> M<u8> for T {}",
            "impl<T: ?Sized, A> M<u8> for T {}",
            "impl<T: ?Sized, A> M<T> for T {}",
            "impl<T: ?Sized, A> M<A> for A {}",
            "impl<T: ?Sized, A> M<A> for &T {}",
            "impl<T: ?Sized, A, B> M<A> for T {}",
            "impl<T: ?Sized, A> M<A, A> for T {}",
            "impl<T: ?Sized, A> M<A> for T where A: Copy {}",
            "impl<T: ?Sized, A> M<A> for T { }\nimpl<T: ?Sized, A> Other<A> for T {}",
        ] {
            let src = format!(
                "#[cfg(not(verus_keep_ghost))]\npub trait M<A> {{}}\n#[cfg(not(verus_keep_ghost))]\n{imp}\n"
            );
            let got = violation(&[("src/lib.rs", &src)]);
            if imp.contains("Other") {
                // (the second impl has no gate: nothing of the rule's)
                assert_eq!(got, None, "{imp}");
                continue;
            }
            let e = got.unwrap_or_else(|| panic!("accepted: {imp}"));
            assert!(
                e.contains("an impl that is not the blanket impl of an empty marker trait"),
                "{imp}: {e}"
            );
        }
        // The arity is the trait's.
        let two = "#[cfg(not(verus_keep_ghost))]\npub trait M<A, B> {}\n#[cfg(not(verus_keep_ghost))]\nimpl<T: ?Sized, A> M<A> for T {}\n";
        assert!(violation(&[("src/lib.rs", two)]).is_some());
        let swapped = "#[cfg(not(verus_keep_ghost))]\npub trait M<A, B> {}\n#[cfg(not(verus_keep_ghost))]\nimpl<T: ?Sized, A, B> M<B, A> for T {}\n";
        assert!(violation(&[("src/lib.rs", swapped)]).is_some());
    }

    /// Amendment 2026-11-25 (3): an impl of a trait under the gate exists in Verus's
    /// build only, with every method the trait provides, and a bound on a trait declared
    /// there brings its supertraits' methods into scope. Found on 2026-11-25 while
    /// moving the drop markers' impls of `fip-strict` into a block: the list admitted
    /// `impl Copy for X {}` and an empty impl of a trait with provided methods.
    #[test]
    fn gate_ghost_impls_and_traits() {
        let pre = "pub struct X;\npub trait Tr { fn m(&self) {} }\npub trait Out<A> { type Output; }\npub trait Sub: Out<u8> { }\n";
        let wrap = |body: &str| format!("{pre}#[cfg(verus_keep_ghost)]\nverus! {{\n{body}\n}}\n");
        for body in [
            "impl X { spec fn s(&self) -> bool { true } }",
            "impl X {}",
            "pub trait Gh { spec fn s(&self) -> bool; }\nimpl Gh for X { open spec fn s(&self) -> bool { true } }",
            "pub trait Gh<A>: Out<A> { spec fn post(&self, a: A, o: Self::Output) -> bool; }",
            "pub trait Gh: Sized { proof fn p(&self); }",
            "pub trait Gh: NoDeallocDrop { spec fn s(&self) -> bool; }",
            "impl vstd::view::View for X { type V = int; open spec fn view(&self) -> int { 0 } }",
            "impl View for X { type V = int; open spec fn view(&self) -> int { 0 } }",
            "impl<A, F: for<'a> Tr2<(&'a A,)>> Gh2<A> for F where F: Fn(A) -> A, { open spec fn s(&self) -> bool { true } }",
            "unsafe impl vstd::alloc_check::AllocFreeDrop for X {}",
            "unsafe impl<T: Copy> NoDeallocDrop for Y<T> {}",
            "pub proof fn p(f: impl Fn(u8) -> u8) {}",
            "pub open spec fn q() -> spec_fn(u8) -> bool { |x: u8| true }",
        ] {
            assert_eq!(violation(&[("src/lib.rs", &wrap(body))]), None, "{body}");
        }
        for (body, what) in [
            (
                "impl Copy for X {}",
                "an impl of the trait `Copy` that gives no `spec` or `proof` function",
            ),
            (
                "unsafe impl Send for X {}",
                "an impl of the trait `Send` that gives no",
            ),
            (
                "impl Tr for X {}",
                "an impl of the trait `Tr` that gives no",
            ),
            (
                "impl crate::Tr for X {}",
                "an impl of the trait `Tr` that gives no",
            ),
            (
                "impl<T> Tr for T {}",
                "an impl of the trait `Tr` that gives no",
            ),
            (
                "impl<T: for<'a> Fn(&'a u8) -> u8> Tr for T {}",
                "an impl of the trait `Tr` that gives no",
            ),
            (
                "impl Tr2 for X { type A = u8; }",
                "an impl of the trait `Tr2` that gives no",
            ),
            (
                "impl core::ops::Deref for X { type Target = u8; }",
                "an impl of the trait `Deref` that gives no",
            ),
            (
                "impl other::Marker for X {}",
                "an impl of the trait `Marker` that gives no",
            ),
            (
                "pub trait Gh: Copy { spec fn s(&self) -> bool; }",
                "the trait `Gh` with the supertrait `Copy`",
            ),
            (
                "pub trait Gh: Tr { spec fn s(&self) -> bool; }",
                "the trait `Gh` with the supertrait `Tr`",
            ),
            (
                "pub trait Gh: Sub { spec fn s(&self) -> bool; }",
                "the trait `Gh` with the supertrait `Sub`",
            ),
            (
                "pub trait Gh: Out<u8> + Clone { spec fn s(&self) -> bool; }",
                "the trait `Gh` with the supertrait `Clone`",
            ),
            (
                "pub trait Gh where Self: Copy { spec fn s(&self) -> bool; }",
                "the trait `Gh` with a `where` clause",
            ),
            ("pub trait Gh { fn m(&self) {} }", "the exec function `m`"),
        ] {
            let e = violation(&[("src/lib.rs", &wrap(body))])
                .unwrap_or_else(|| panic!("accepted: {body}"));
            assert!(e.contains(what), "{body}: {e}");
        }
        // The same in a module of specifications.
        let lib = "pub struct X;\npub trait Tr { fn m(&self) {} }\n#[cfg(verus_keep_ghost)]\npub mod spec;\n";
        let e = violation(&[
            ("src/lib.rs", lib),
            (
                "src/spec.rs",
                "use vstd::prelude::*;\nverus! {\nimpl crate::Tr for crate::X {}\n}\n",
            ),
        ])
        .unwrap();
        assert!(
            e.starts_with("src/spec.rs:3: an impl of the trait `Tr` that gives no"),
            "{e}"
        );
        // A trait of the crate that has a method in one of its declarations is not one
        // without methods.
        let two = "pub mod a { pub trait Out { type O; } }\npub mod b { pub trait Out { fn m(&self); } }\n#[cfg(verus_keep_ghost)]\nverus! {\npub trait Gh: Out { spec fn s(&self) -> bool; }\n}\n";
        assert!(
            violation(&[("src/lib.rs", two)])
                .unwrap()
                .contains("with the supertrait `Out`")
        );
    }

    #[test]
    fn gate_whitelist_refuses() {
        let one = |src: &str| {
            violation(&[("src/lib.rs", src)]).unwrap_or_else(|| panic!("allowed: {src}"))
        };
        // Exec code of Verus's build only.
        let e = one("#[cfg(verus_keep_ghost)]\nverus! {\npub fn helper() -> (r: u8) { 0 }\n}\n");
        assert!(
            e.starts_with(
                "src/lib.rs:3: the exec function `helper` under `#[cfg(verus_keep_ghost)]`"
            ),
            "{e}"
        );
        let e = violation(&[
            ("src/lib.rs", "#[cfg(verus_keep_ghost)]\npub mod spec;\n"),
            ("src/spec.rs", "pub fn exec() {}\n"),
        ])
        .unwrap();
        assert!(
            e.starts_with("src/spec.rs:1: the exec function `exec` in a module declared under"),
            "{e}"
        );
        let e = violation(&[
            (
                "src/lib.rs",
                "#[cfg(verus_keep_ghost)]\n#[path = \"v.rs\"]\nmod w;\n",
            ),
            ("src/v.rs", "pub const fn exec() {}\n"),
        ])
        .unwrap();
        assert!(e.starts_with("src/v.rs:1: the exec function `exec`"), "{e}");
        for (src, what) in [
            ("#[cfg(verus_keep_ghost)]\npub fn f() {}\n", "`fn`"),
            (
                "#[cfg(verus_keep_ghost)]\nimpl S {\n    pub fn m(&self) {}\n}\n",
                "an impl that is not an empty impl of a marker trait",
            ),
            (
                "#[cfg(verus_keep_ghost)]\nimpl Copy for S {}\n",
                "an impl that is not an empty impl of a marker trait",
            ),
            (
                "#[cfg(verus_keep_ghost)]\npub const N: usize = 0;\n",
                "`const`",
            ),
            ("#[cfg(verus_keep_ghost)]\npub type Cell = u64;\n", "`type`"),
            ("#[cfg(verus_keep_ghost)]\npub struct G(u8);\n", "`struct`"),
            ("#[cfg(verus_keep_ghost)]\npub trait T {}\n", "`trait`"),
            (
                "#[cfg(verus_keep_ghost)]\nmacro_rules! tick { ($x:expr) => {}; }\n",
                "`macro_rules`",
            ),
            (
                "#[cfg(verus_keep_ghost)]\nmake_impls!(A, B);\n",
                "`make_impls`",
            ),
            (
                "#[cfg(verus_keep_ghost)]\nextern crate alloc;\n",
                "`extern`",
            ),
            (
                "#[cfg(verus_keep_ghost)]\nuse crate::a::Tr;\n",
                "a `use` of something else",
            ),
            (
                "#[cfg(verus_keep_ghost)]\npub use core::marker::Copy as DropFreeFn;\n",
                "a `use` of something else",
            ),
            (
                "#[cfg(verus_keep_ghost)]\nuse dep::*;\n",
                "a `use` of something else",
            ),
        ] {
            let e = one(src);
            assert!(
                e.contains(what) && e.contains("under `#[cfg(verus_keep_ghost)]`"),
                "{src}: {e}"
            );
        }
        // Inside a ghost block: definitions, macros of the crate, other imports.
        for (body, what) in [
            ("pub struct G { pub n: int }", "the definition of `G`"),
            ("pub enum E { A }", "the definition of `E`"),
            ("pub const N: usize = 0;", "the constant `N`"),
            ("pub type Cell = u64;", "the type alias `Cell`"),
            ("pub static S: u8 = 0;", "a `static`"),
            ("macro_rules! m { () => {}; }", "a `macro_rules!`"),
            (
                "impl Tr for S { fn m(&self) {} }",
                "an impl of the trait `Tr` that gives no `spec` or `proof` function",
            ),
            ("pub trait Tr { fn m(&self); }", "the exec function `m`"),
            ("use crate::a::Tr;", "a `use` of something else"),
            ("tick!(1);", "an invocation of the crate's macro `tick!`"),
        ] {
            let src = format!(
                "macro_rules! tick {{ ($x:expr) => {{}}; }}\n#[cfg(verus_keep_ghost)]\nverus! {{\npub open spec fn ok() -> bool {{ true }}\n{body}\n}}\n"
            );
            let e = one(&src);
            assert!(
                e.starts_with("src/lib.rs:5: ") && e.contains(what),
                "{body}: {e}"
            );
        }
        // Items of plain builds only.
        for (src, what) in [
            (
                "#[cfg(not(verus_keep_ghost))]\npub mod plain {\n    pub fn root() {}\n}\n",
                "`mod`",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\npub fn helper() -> u8 { 1 }\n",
                "`fn`",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\nimpl Drop for Tok {\n    fn drop(&mut self) {}\n}\n",
                "an impl that is not the blanket impl",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\nimpl<T: ?Sized> Other for T {}\n",
                "an impl that is not the blanket impl",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\npub trait M {}\n#[cfg(not(verus_keep_ghost))]\nimpl M for Tok {}\n",
                "an impl that is not the blanket impl",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\npub trait Tr { fn m(&self) {} }\n",
                "a trait that is not an empty marker trait",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\npub const N: usize = 64;\n",
                "`const`",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\npub type Cell = i32;\n",
                "`type`",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\npub struct Then<F, G>(pub F, pub G);\n",
                "`struct`",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\nuse crate::b::Tr;\n",
                "`use`",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\nmacro_rules! tick { ($x:expr) => { let _ = $x; }; }\n",
                "`macro_rules! tick`",
            ),
            (
                "#[cfg(not(verus_keep_ghost))]\nmacro_rules! proof { ($($t:tt)*) => { $($t)* }; }\n",
                "`macro_rules! proof`",
            ),
        ] {
            let e = one(src);
            assert!(
                e.contains(what) && e.contains("under `#[cfg(not(verus_keep_ghost))]`"),
                "{src}: {e}"
            );
        }
        // The gate inside a function or a definition, and as an expression.
        let e = one(
            "pub fn on() -> bool {\n    #[cfg(not(verus_keep_ghost))]\n    return true;\n    false\n}\n",
        );
        assert!(e.starts_with("src/lib.rs:2: `return`"), "{e}");
        let e = one(
            "pub fn f(x: u8) -> u8 {\n    #[cfg(verus_keep_ghost)]\n    proof! { }\n    x\n}\n",
        );
        assert!(e.starts_with("src/lib.rs:2: `proof`"), "{e}");
        let e = one(
            "pub struct Buf {\n    pub a: u8,\n    #[cfg(not(verus_keep_ghost))]\n    pub extra: Box<u8>,\n}\n",
        );
        assert!(e.starts_with("src/lib.rs:3: `extra`"), "{e}");
        let e = one("pub fn f() -> u8 { if cfg!(verus_keep_ghost) { 0 } else { 1 } }\n");
        assert!(
            e.starts_with("src/lib.rs:1: `cfg!(..)` on `verus_keep_ghost`"),
            "{e}"
        );
        let e = one("#![cfg(verus_keep_ghost)]\npub fn f() {}\n");
        assert!(
            e.starts_with("src/lib.rs:1: `#![cfg(..)]` on `verus_keep_ghost`"),
            "{e}"
        );
        // Other predicates and payloads.
        let e = one("#[cfg(all(verus_keep_ghost))]\npub mod v {}\n");
        assert!(
            e.contains("`#[cfg(all(verus_keep_ghost))]`: only `verus_keep_ghost` and"),
            "{e}"
        );
        for bad in [
            "#[cfg_attr(not(verus_keep_ghost), path = \"p.rs\")]\nmod v;\n",
            "#[cfg_attr(not(verus_keep_ghost), derive(Clone))]\npub struct S;\n",
            "#![cfg_attr(not(verus_keep_ghost), no_std)]\n",
            "#[cfg_attr(verus_keep_ghost, repr(C))]\npub struct S;\n",
            "#[cfg_attr(all(verus_keep_ghost), verus_verify)]\npub struct S;\n",
            "pub fn f() {\n    #[cfg_attr(verus_keep_ghost, cfg(any()))]\n    return;\n}\n",
        ] {
            let e = one(bad);
            assert!(e.contains("may depend on `verus_keep_ghost`"), "{bad}: {e}");
        }
    }
}
