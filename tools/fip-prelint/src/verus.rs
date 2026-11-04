// SPDX-License-Identifier: Apache-2.0
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
//! format 1
//! crate <crate name>
//! verus <version> <commit>
//! z3 <version>
//! toolchain <rust toolchain of the Verus build>
//! flags <verus flags relevant to trust, e.g. --no-cheating>
//! verified <number Verus reported verified>
//! source <path relative to the sidecar's directory> <sha256>
//! fn <crate>::<path> <file relative to the sidecar's directory> <sha256 of the item text> <requires | ->
//! skip <crate>::<path> <reason>
//! ```

use std::fmt::Write as _;

/// Version of the format.
pub const FORMAT: u32 = 1;

/// The Verus flag without which no sidecar is written or used.
pub const NO_CHEATING: &str = "--no-cheating";

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
    Some((lo, end))
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

/// Occurrences of `verus_keep_ghost` in an item text that may make the code Verus
/// verified differ from the code the plain build compiles: anything but a Verus-only
/// attribute (`cfg_attr(verus_keep_ghost, ..)`) or the plain-build `#[fip]` attribute
/// (`cfg_attr(not(verus_keep_ghost), fip_macros::..)`, whose added code has
/// macro-expansion spans, which the driver never drops). `None` if there is none.
pub fn ghost_cfg_conflict(text: &str) -> Option<String> {
    let compact: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    let mut rest = compact.as_str();
    while let Some(i) = rest.find("verus_keep_ghost") {
        let before = &rest[..i];
        let after = &rest[i + "verus_keep_ghost".len()..];
        let ok = (before.ends_with("cfg_attr(") && after.starts_with(','))
            || (before.ends_with("cfg_attr(not(")
                && (after.starts_with("),fip_macros::") || after.starts_with("),::fip_macros::")));
        if !ok {
            let from = before.len().saturating_sub(24);
            return Some(format!(
                "`{}verus_keep_ghost{}`",
                &before[before.floor_char_boundary(from)..],
                &after[..after.floor_char_boundary(16.min(after.len()))]
            ));
        }
        rest = after;
    }
    None
}

// ---------------------------------------------------------------------------------
// The sidecar.

/// One verified function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    /// `<crate>::<module path>::<name>` (as Verus names it).
    pub path: String,
    /// File relative to the sidecar's directory.
    pub file: String,
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
                "verified" => s.verified = rest.trim().parse().map_err(|_| bad())?,
                "source" => {
                    let [p, h] = words[..] else { return Err(bad()) };
                    s.sources.push((p.to_string(), h.to_string()));
                }
                "fn" => {
                    let [p, f, h, r] = words[..] else {
                        return Err(bad());
                    };
                    let requires = match r {
                        "requires" => true,
                        "-" => false,
                        _ => return Err(bad()),
                    };
                    s.fns.push(Entry {
                        path: p.to_string(),
                        file: f.to_string(),
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
        if s.krate.is_empty() || s.verus_version.is_empty() || s.z3.is_empty() {
            return Err("incomplete stamp (crate, verus or z3 line missing)".to_string());
        }
        Ok(s)
    }

    pub fn render(&self) -> String {
        let mut o = String::new();
        o.push_str("fip-prelint verus sidecar\n");
        o.push_str(
            "# Generated by `cargo fip-prelint --verus-sidecar` (just verify-core); do not edit.\n\
             # Exec functions Verus verified with --no-cheating, with the SHA-256 of their item\n\
             # text (outer attributes and doc comments through the body). Top plan T13.4.\n",
        );
        let _ = writeln!(o, "format {}", self.format);
        let _ = writeln!(o, "crate {}", self.krate);
        let _ = writeln!(o, "verus {} {}", self.verus_version, self.verus_commit);
        let _ = writeln!(o, "z3 {}", self.z3);
        let _ = writeln!(o, "toolchain {}", self.toolchain);
        let _ = writeln!(o, "flags {}", self.flags.join(" "));
        let _ = writeln!(o, "verified {}", self.verified);
        for (p, h) in &self.sources {
            let _ = writeln!(o, "source {p} {h}");
        }
        for e in &self.fns {
            let r = if e.requires { "requires" } else { "-" };
            let _ = writeln!(o, "fn {} {} {} {r}", e.path, e.file, e.hash);
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
            ghost_cfg_conflict("#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r))]"),
            None
        );
        assert_eq!(
            ghost_cfg_conflict(
                "#[cfg_attr(not(verus_keep_ghost), fip_macros::fip(strict = true))]"
            ),
            None
        );
        assert!(ghost_cfg_conflict("{ #[cfg(not(verus_keep_ghost))] let x = a + 1; }").is_some());
        assert!(ghost_cfg_conflict("{ if cfg!(verus_keep_ghost) { 1 } else { 2 } }").is_some());
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
            verified: 3,
            sources: vec![("src/lib.rs".to_string(), "00".to_string())],
            fns: vec![Entry {
                path: "c::f".to_string(),
                file: "src/lib.rs".to_string(),
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
        assert!(Sidecar::parse(&s.render().replace("format 1", "format 2")).is_err());
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
