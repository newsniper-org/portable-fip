// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Generator of the Verus sidecar (top plan T13.4), `cargo fip-prelint
//! --verus-sidecar`: runs Verus with `--output-json --log vir`, refuses anything but
//! a successful `--no-cheating` run over the entire crate, and lists the exec
//! functions of the crate that Verus verified (from the VIR log: mode `Exec`, a body,
//! not `external_body`; `#[verifier::external]` items are not in the VIR at all),
//! with their item hashes ([`crate::verus::item_hash`]).

use std::collections::BTreeSet;
use std::path::{Component, Path, PathBuf};

use crate::verus::{self, Entry, NO_CHEATING, Sidecar};

/// Flags that restrict or weaken what Verus checks: a run with one of them is never
/// recorded.
pub const REFUSED_FLAGS: &[&str] = &[
    "--no-verify",
    "--no-lifetime",
    "--verify-root",
    "--verify-module",
    "--verify-only-module",
    "--verify-function",
    "--no-builtin",
    "--no-vstd",
];

// ---------------------------------------------------------------------------------
// A minimal JSON reader (the `--output-json` result).

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(kv) => kv.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn path(&self, keys: &[&str]) -> Option<&Json> {
        keys.iter().try_fold(self, |j, k| j.get(k))
    }
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Json::Bool(b) => Some(*b),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            Json::Num(n) if *n >= 0.0 && n.fract() == 0.0 => Some(*n as u64),
            _ => None,
        }
    }
}

pub fn parse_json(text: &str) -> Result<Json, String> {
    let b = text.as_bytes();
    let mut i = 0;
    let v = json_value(b, &mut i)?;
    json_ws(b, &mut i);
    if i != b.len() {
        return Err(format!("trailing data at byte {i}"));
    }
    Ok(v)
}

fn json_ws(b: &[u8], i: &mut usize) {
    while *i < b.len() && b[*i].is_ascii_whitespace() {
        *i += 1;
    }
}

fn json_value(b: &[u8], i: &mut usize) -> Result<Json, String> {
    json_ws(b, i);
    let err = |i: usize| format!("unexpected input at byte {i}");
    match b.get(*i) {
        Some(b'{') => {
            *i += 1;
            let mut kv = Vec::new();
            json_ws(b, i);
            if b.get(*i) == Some(&b'}') {
                *i += 1;
                return Ok(Json::Obj(kv));
            }
            loop {
                json_ws(b, i);
                let Json::Str(k) = json_value(b, i)? else {
                    return Err(err(*i));
                };
                json_ws(b, i);
                if b.get(*i) != Some(&b':') {
                    return Err(err(*i));
                }
                *i += 1;
                let v = json_value(b, i)?;
                kv.push((k, v));
                json_ws(b, i);
                match b.get(*i) {
                    Some(b',') => *i += 1,
                    Some(b'}') => {
                        *i += 1;
                        return Ok(Json::Obj(kv));
                    }
                    _ => return Err(err(*i)),
                }
            }
        }
        Some(b'[') => {
            *i += 1;
            let mut v = Vec::new();
            json_ws(b, i);
            if b.get(*i) == Some(&b']') {
                *i += 1;
                return Ok(Json::Arr(v));
            }
            loop {
                v.push(json_value(b, i)?);
                json_ws(b, i);
                match b.get(*i) {
                    Some(b',') => *i += 1,
                    Some(b']') => {
                        *i += 1;
                        return Ok(Json::Arr(v));
                    }
                    _ => return Err(err(*i)),
                }
            }
        }
        Some(b'"') => {
            *i += 1;
            let mut s = Vec::new();
            while let Some(&c) = b.get(*i) {
                *i += 1;
                match c {
                    b'"' => {
                        return String::from_utf8(s)
                            .map(Json::Str)
                            .map_err(|e| e.to_string());
                    }
                    b'\\' => {
                        let e = *b.get(*i).ok_or_else(|| err(*i))?;
                        *i += 1;
                        match e {
                            b'n' => s.push(b'\n'),
                            b't' => s.push(b'\t'),
                            b'r' => s.push(b'\r'),
                            b'b' => s.push(8),
                            b'f' => s.push(12),
                            b'u' => {
                                let hex = b.get(*i..*i + 4).ok_or_else(|| err(*i))?;
                                let code = u32::from_str_radix(
                                    std::str::from_utf8(hex).map_err(|e| e.to_string())?,
                                    16,
                                )
                                .map_err(|e| e.to_string())?;
                                *i += 4;
                                let ch = char::from_u32(code).unwrap_or('\u{fffd}');
                                let mut buf = [0u8; 4];
                                s.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                            }
                            other => s.push(other),
                        }
                    }
                    c => s.push(c),
                }
            }
            Err("unterminated string".to_string())
        }
        Some(b't') if b[*i..].starts_with(b"true") => {
            *i += 4;
            Ok(Json::Bool(true))
        }
        Some(b'f') if b[*i..].starts_with(b"false") => {
            *i += 5;
            Ok(Json::Bool(false))
        }
        Some(b'n') if b[*i..].starts_with(b"null") => {
            *i += 4;
            Ok(Json::Null)
        }
        Some(c) if *c == b'-' || c.is_ascii_digit() => {
            let start = *i;
            while *i < b.len() && (b[*i].is_ascii_digit() || b"+-.eE".contains(&b[*i])) {
                *i += 1;
            }
            std::str::from_utf8(&b[start..*i])
                .ok()
                .and_then(|s| s.parse().ok())
                .map(Json::Num)
                .ok_or_else(|| err(start))
        }
        _ => Err(err(*i)),
    }
}

// ---------------------------------------------------------------------------------
// The VIR log (`--log vir`): top-level `(@ "<span>" (Function ..))` records.

/// A span as Verus prints it: `<file>:<line>:<col>: <line>:<col> (#n)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSpan {
    pub file: String,
    pub lo: (usize, usize),
    pub hi: (usize, usize),
}

pub fn parse_span(s: &str) -> Option<VirSpan> {
    let s = s.split(" (#").next()?;
    let (left, right) = s.rsplit_once(": ")?;
    let mut l = left.rsplitn(3, ':');
    let lcol = l.next()?.parse().ok()?;
    let lline = l.next()?.parse().ok()?;
    let file = l.next()?.to_string();
    let (rline, rcol) = right.split_once(':')?;
    Some(VirSpan {
        file,
        lo: (lline, lcol),
        hi: (rline.parse().ok()?, rcol.parse().ok()?),
    })
}

/// One function of the VIR log.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirFn {
    pub path: String,
    /// The function's span (its signature).
    pub span: VirSpan,
    pub mode: String,
    pub external_body: bool,
    /// The span of the body, if it has one.
    pub body: Option<VirSpan>,
    pub requires: bool,
    /// The function's span comes from a macro expansion (its syntax context is not
    /// `#0`): one text for every expansion.
    pub expanded: bool,
}

/// End of the balanced s-expression starting at `open` (a `(`), strings skipped.
fn sexp_end(t: &[u8], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut j = open;
    let mut in_str = false;
    while j < t.len() {
        let c = t[j];
        if in_str {
            if c == b'\\' {
                j += 1;
            } else if c == b'"' {
                in_str = false;
            }
        } else if c == b'"' {
            in_str = true;
        } else if c == b'(' {
            depth += 1;
        } else if c == b')' {
            depth -= 1;
            if depth == 0 {
                return Some(j + 1);
            }
        }
        j += 1;
    }
    None
}

/// The direct children of the field `key` (e.g. `:body`) of a record: its text up to
/// the next field of the same record, as a substring of `rec`.
fn field<'r>(rec: &'r str, key: &str) -> Option<&'r str> {
    // Fields are found at nesting depth 1 of the `(Function ..)` record.
    let t = rec.as_bytes();
    let mut depth = 0usize;
    let mut in_str = false;
    let mut j = 0;
    let mut start = None;
    while j < t.len() {
        let c = t[j];
        if in_str {
            if c == b'\\' {
                j += 1;
            } else if c == b'"' {
                in_str = false;
            }
        } else if c == b'"' {
            in_str = true;
        } else if c == b'(' {
            depth += 1;
        } else if c == b')' {
            depth = depth.saturating_sub(1);
            if depth == 0 && start.is_some() {
                return start.map(|s| &rec[s..j]);
            }
        } else if depth == 1 && c == b':' {
            if let Some(s) = start {
                return Some(&rec[s..j]);
            }
            // The key, then whitespace (Verus wraps long records at any space).
            if rec[j..].starts_with(key)
                && rec[j + key.len()..].starts_with(|c: char| c.is_ascii_whitespace())
            {
                start = Some(j + key.len());
                j += key.len();
                continue;
            }
        }
        j += 1;
    }
    start.map(|s| &rec[s..])
}

pub fn vir_functions(text: &str) -> Result<Vec<VirFn>, String> {
    let t = text.as_bytes();
    let mut out = Vec::new();
    let marker = "(@ \"";
    let mut from = 0;
    while let Some(rel) = text[from..].find(marker) {
        let at = from + rel;
        // Only top-level records: at the start of a line.
        if at != 0 && t[at - 1] != b'\n' {
            from = at + marker.len();
            continue;
        }
        let end = sexp_end(t, at).ok_or("unbalanced VIR log")?;
        from = end;
        let rec = &text[at..end];
        let Some(q) = rec[marker.len()..].find('"') else {
            continue;
        };
        let span_text = &rec[marker.len()..marker.len() + q];
        let after = rec[marker.len() + q + 1..].trim_start();
        if !after.starts_with("(Function") {
            continue;
        }
        let Some(fstart) = rec.find("(Function") else {
            continue;
        };
        let Some(fend) = sexp_end(t, at + fstart) else {
            continue;
        };
        let func = &text[at + fstart..fend];
        let span = parse_span(span_text).ok_or_else(|| format!("bad span `{span_text}`"))?;
        let name = field(func, ":name").ok_or("function without :name")?;
        let path = name
            .split(":path")
            .nth(1)
            .and_then(|p| p.split_whitespace().next())
            .map(|p| p.trim_end_matches(')'))
            .ok_or_else(|| format!("bad :name `{name}`"))?
            .to_string();
        let mode = field(func, ":mode")
            .map(|m| m.split_whitespace().next().unwrap_or("").to_string())
            .ok_or_else(|| format!("`{path}`: no :mode"))?;
        let attrs = field(func, ":attrs").ok_or_else(|| format!("`{path}`: no :attrs"))?;
        let external_body = attrs
            .split(":is_external_body")
            .nth(1)
            .map(|r| r.trim_start().starts_with("true"))
            .ok_or_else(|| format!("`{path}`: no :is_external_body"))?;
        let body_text = field(func, ":body").ok_or_else(|| format!("`{path}`: no :body"))?;
        let body_text = body_text.trim();
        let body = if body_text.starts_with("None") {
            None
        } else {
            let q = body_text
                .strip_prefix("(@@")
                .map(str::trim_start)
                .and_then(|r| r.strip_prefix('"'))
                .and_then(|r| r.split('"').next())
                .ok_or_else(|| format!("`{path}`: unrecognised :body"))?;
            Some(parse_span(q).ok_or_else(|| format!("`{path}`: bad body span `{q}`"))?)
        };
        let req = field(func, ":require").ok_or_else(|| format!("`{path}`: no :require"))?;
        let requires = req.trim() != "()";
        out.push(VirFn {
            path,
            span,
            mode,
            external_body,
            body,
            requires,
            expanded: !span_text.ends_with(" (#0)"),
        });
    }
    Ok(out)
}

// ---------------------------------------------------------------------------------
// Generation.

/// `path` relative to `base` (both made absolute against the current directory and
/// normalised lexically; symlinks are resolved where the paths exist).
pub fn relative(path: &Path, base: &Path) -> String {
    let abs = |p: &Path| -> Vec<String> {
        let p = std::fs::canonicalize(p).unwrap_or_else(|_| {
            std::env::current_dir()
                .map(|d| d.join(p))
                .unwrap_or_else(|_| p.to_path_buf())
        });
        let mut v: Vec<String> = Vec::new();
        for c in p.components() {
            match c {
                Component::ParentDir => {
                    v.pop();
                }
                Component::Normal(s) => v.push(s.to_string_lossy().into_owned()),
                _ => {}
            }
        }
        v
    };
    let (p, b) = (abs(path), abs(base));
    let common = p.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let mut parts: Vec<String> = vec!["..".to_string(); b.len() - common];
    parts.extend(p[common..].iter().cloned());
    parts.join("/")
}

/// The run's provenance, read from Verus's `--output-json` result.
pub struct RunInfo {
    pub version: String,
    pub commit: String,
    pub toolchain: String,
    pub verified: u64,
}

/// Checks the `--output-json` result: success, no errors, the entire crate.
pub fn run_info(json: &Json) -> Result<RunInfo, String> {
    let r = |k: &str| json.path(&["verification-results", k]);
    let flag = |k: &str| r(k).and_then(Json::as_bool);
    if flag("success") != Some(true) {
        return Err("Verus reported no success".to_string());
    }
    if flag("encountered-error") != Some(false) || flag("encountered-vir-error") != Some(false) {
        return Err("Verus encountered an error".to_string());
    }
    if r("errors").and_then(Json::as_u64) != Some(0) {
        return Err("Verus reported errors".to_string());
    }
    if flag("is-verifying-entire-crate") != Some(true) {
        return Err("Verus did not verify the entire crate".to_string());
    }
    let s = |k: &str| {
        json.path(&["verus", k])
            .and_then(Json::as_str)
            .map(str::to_string)
            .ok_or_else(|| format!("no `verus.{k}` in the JSON result"))
    };
    Ok(RunInfo {
        version: s("version")?,
        commit: s("commit")?,
        toolchain: s("toolchain")?,
        verified: r("verified").and_then(Json::as_u64).unwrap_or(0),
    })
}

/// Builds the sidecar of crate `krate` (its directory `crate_dir`, where the sidecar
/// is committed; paths are relative to it) from the functions of the VIR log.
/// Paths in VIR spans are relative to `root`, the directory Verus ran in.
pub fn build(
    root: &Path,
    krate: &str,
    crate_dir: &Path,
    info: &RunInfo,
    z3: &str,
    flags: &[String],
    fns: &[VirFn],
) -> Result<Sidecar, String> {
    let mut sources: BTreeSet<String> = BTreeSet::new();
    let mut add_source = |file: &Path| {
        if file.is_file() {
            sources.insert(relative(file, crate_dir));
        }
    };
    // Every workspace file the run read (spans of this crate and of imported crates),
    // and every source file of the crate.
    for f in fns {
        let p = Path::new(&f.span.file);
        if p.is_relative() && !f.span.file.starts_with("vstd/") {
            add_source(&root.join(p));
        }
    }
    let mut stack = vec![crate_dir.join("src")];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "rs") {
                add_source(&p);
            }
        }
    }
    let mut source_hashes = Vec::new();
    for s in &sources {
        let bytes =
            std::fs::read(crate_dir.join(s)).map_err(|e| format!("{s}: cannot read: {e}"))?;
        source_hashes.push((s.clone(), verus::sha256_hex(&bytes)));
    }
    let prefix = format!("{krate}::");
    let mut entries = Vec::new();
    let mut skipped = Vec::new();
    for f in fns {
        if !f.path.starts_with(&prefix) || f.mode != "Exec" {
            continue;
        }
        let why = if f.external_body {
            Some("external_body (not verified)".to_string())
        } else if f.expanded {
            Some("generated by a macro expansion (one item text for every expansion)".to_string())
        } else {
            None
        };
        if let Some(why) = why {
            skipped.push((f.path.clone(), why));
            continue;
        }
        let Some(body) = &f.body else {
            skipped.push((f.path.clone(), "no body".to_string()));
            continue;
        };
        if body.file != f.span.file {
            skipped.push((
                f.path.clone(),
                "body in another file than the signature".to_string(),
            ));
            continue;
        }
        let file = root.join(&f.span.file);
        let src = std::fs::read_to_string(&file)
            .map_err(|e| format!("{}: cannot read: {e}", f.span.file))?;
        let (Some(start), Some(end)) = (
            verus::offset_of(&src, f.span.lo.0, f.span.lo.1),
            verus::offset_of(&src, body.hi.0, body.hi.1),
        ) else {
            skipped.push((f.path.clone(), "span outside its file".to_string()));
            continue;
        };
        let Some((lo, hi)) = verus::item_region(&src, start, end) else {
            skipped.push((f.path.clone(), "item text not found".to_string()));
            continue;
        };
        if verus::ghost_only_regions(&src)
            .iter()
            .any(|&(a, b)| a <= lo && hi <= b)
        {
            skipped.push((
                f.path.clone(),
                "only in the Verus build (inside `#[cfg(verus_keep_ghost)]`)".to_string(),
            ));
            continue;
        }
        if let Some(c) = verus::ghost_cfg_conflict(&src[lo..hi]) {
            skipped.push((
                f.path.clone(),
                format!("the item text mentions {c}: plain and Verus code may differ"),
            ));
            continue;
        }
        entries.push(Entry {
            path: verus::impl_key(&f.path),
            file: relative(&file, crate_dir),
            line: verus::line_of(&src, lo),
            hash: verus::sha256_hex(&src.as_bytes()[lo..hi]),
            requires: f.requires,
        });
    }
    entries.sort_by(|a, b| (&a.path, &a.file, a.line).cmp(&(&b.path, &b.file, b.line)));
    // Two entries with one path, file and line would be ambiguous: neither is listed.
    let key = |e: &Entry| (e.path.clone(), e.file.clone(), e.line);
    let dups: BTreeSet<(String, String, usize)> = entries
        .windows(2)
        .filter(|w| key(&w[0]) == key(&w[1]))
        .map(|w| key(&w[0]))
        .collect();
    entries.retain(|e| !dups.contains(&key(e)));
    skipped.extend(
        dups.into_iter()
            .map(|(p, f, l)| (p, format!("several functions with this path at {f}:{l}"))),
    );
    skipped.sort();
    skipped.dedup();
    let mut flags_kept: Vec<String> = flags
        .iter()
        .filter(|f| *f == NO_CHEATING)
        .cloned()
        .collect();
    flags_kept.dedup();
    Ok(Sidecar {
        format: verus::FORMAT,
        krate: krate.to_string(),
        verus_version: info.version.clone(),
        verus_commit: info.commit.clone(),
        z3: z3.to_string(),
        toolchain: info.toolchain.clone(),
        flags: flags_kept,
        verified: info.verified,
        sources: source_hashes,
        fns: entries,
        skipped,
    })
}

/// The Z3 that `verus` uses: `VERUS_Z3_PATH`, else `z3` next to the (resolved) Verus
/// binary.
pub fn z3_path(verus: &str) -> PathBuf {
    if let Some(p) = std::env::var_os("VERUS_Z3_PATH") {
        return PathBuf::from(p);
    }
    let exe = if verus.contains('/') {
        PathBuf::from(verus)
    } else {
        std::env::var_os("PATH")
            .and_then(|paths| {
                std::env::split_paths(&paths)
                    .map(|d| d.join(verus))
                    .find(|p| p.is_file())
            })
            .unwrap_or_else(|| PathBuf::from(verus))
    };
    let exe = std::fs::canonicalize(&exe).unwrap_or(exe);
    exe.with_file_name("z3")
}

/// `X.Y.Z` from `Z3 version X.Y.Z - 64 bit`.
pub fn z3_version(output: &str) -> Option<String> {
    let rest = output.split("Z3 version ").nth(1)?;
    let v = rest.split_whitespace().next()?;
    v.chars()
        .all(|c| c.is_ascii_digit() || c == '.')
        .then(|| v.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Trimmed from a real `--log vir` of Verus 0.2026.10.18 (crate `t`, run without
    /// `--no-cheating`): an exec function with a body and `requires`, one with
    /// `#[verifier::external_body]`, and a spec function.
    const VIR: &str = r#"(@ "src/lib.rs:3:1: 3:30 (#0)" (Function
  :name (Fun :path t::f) :proxy None :kind (FunctionKind Static) :owning_module t :mode
  Exec :typ_params () :params () :ret (@ "x" (Param :name "r" :mode Exec)) :require (
   (@ "src/lib.rs:4:14: 4:20 (#0)" (> Const (Bool true)))
  ) :ensure (() ()) :decrease () :attrs (FunctionAttrs :uses_ghost_blocks true :is_external_body false :is_unsafe false
  ) :body (@@ "src/lib.rs:5:1: 7:2 (#0)" (> Block ()))
  :extra_dependencies ()))

(@ "src/lib.rs:10:1: 10:20 (#0)" (Function
  :name (Fun :path t::ext) :proxy None :mode Exec :require () :attrs (FunctionAttrs :is_external_body true
  ) :body None :extra_dependencies ()))

(@ "src/lib.rs:12:1: 12:20 (#0)" (Function
  :name (Fun :path t::s) :proxy None :mode Spec :require () :attrs (FunctionAttrs :is_external_body false
  ) :body (@@ "src/lib.rs:12:21: 12:30 (#0)" (> Block ())) :extra_dependencies ()))
"#;

    #[test]
    fn vir_records() {
        let fns = vir_functions(VIR).unwrap();
        assert_eq!(fns.len(), 3);
        assert_eq!(fns[0].path, "t::f");
        assert_eq!(fns[0].mode, "Exec");
        assert!(!fns[0].external_body);
        assert!(fns[0].requires);
        assert_eq!(
            fns[0].body,
            Some(VirSpan {
                file: "src/lib.rs".to_string(),
                lo: (5, 1),
                hi: (7, 2)
            })
        );
        assert_eq!(fns[1].path, "t::ext");
        assert!(fns[1].external_body);
        assert!(!fns[1].requires);
        assert_eq!(fns[1].body, None);
        assert_eq!(fns[2].mode, "Spec");
    }

    #[test]
    fn external_body_is_never_listed() {
        let dir = std::env::temp_dir().join(format!("fip-verusgen-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        let src = "// line 1\n\npub fn f(a: u8) -> u8\n    requires true\n{\n    a\n}\n\n#[verifier::external_body]\npub fn ext() -> u8 { 1 }\n\nspec fn s() -> u8 { 1 }\n";
        std::fs::write(dir.join("src/lib.rs"), src).unwrap();
        let info = RunInfo {
            version: "v".to_string(),
            commit: "c".to_string(),
            toolchain: "t".to_string(),
            verified: 2,
        };
        let fns = vir_functions(VIR).unwrap();
        let s = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap();
        assert_eq!(s.fns.len(), 1, "{s:?}");
        assert_eq!(s.fns[0].path, "t::f");
        assert!(s.fns[0].requires);
        assert_eq!(s.fns[0].file, "src/lib.rs");
        assert!(
            s.skipped
                .iter()
                .any(|(p, why)| p == "t::ext" && why.contains("external_body"))
        );
        assert!(s.flags.is_empty());
        assert_eq!(s.sources.len(), 1);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Impl methods (top plan item 8): listed as `{impl}` with their line; a method
    /// inside `#[cfg(verus_keep_ghost)]` (no plain twin at that place) and one whose
    /// span comes from a macro expansion are skipped.
    #[test]
    fn impl_methods() {
        let vir = r#"(@ "src/lib.rs:3:5: 3:26 (#0)" (Function
  :name (Fun :path t::impl&%3::m) :proxy None :mode Exec :require () :attrs (FunctionAttrs :is_external_body false
  ) :body (@@ "src/lib.rs:3:27: 5:6 (#0)" (> Block ())) :extra_dependencies ()))

(@ "src/lib.rs:10:5: 10:26 (#0)" (Function
  :name (Fun :path t::impl&%1::g) :proxy None :mode Exec :require () :attrs (FunctionAttrs :is_external_body false
  ) :body (@@ "src/lib.rs:10:27: 12:6 (#0)" (> Block ())) :extra_dependencies ()))

(@ "src/lib.rs:15:40: 15:60 (#4)" (Function
  :name (Fun :path t::impl&%7::e) :proxy None :mode Exec :require () :attrs (FunctionAttrs :is_external_body false
  ) :body (@@ "src/lib.rs:15:60: 15:65 (#4)" (> Block ())) :extra_dependencies ()))
"#;
        let dir = std::env::temp_dir().join(format!("fip-verusgen-impl-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        let src = "pub struct S;\nimpl S {\n    pub fn m(&self) -> u8 {\n        1\n    }\n}\n#[cfg(verus_keep_ghost)]\nverus! {\nimpl S {\n    pub fn g(&self) -> u8 {\n        2\n    }\n}\n}\nmacro_rules! mk { () => { impl S { pub fn e(&self) -> u8 { 3 } } } }\n";
        std::fs::write(dir.join("src/lib.rs"), src).unwrap();
        let info = RunInfo {
            version: "v".to_string(),
            commit: "c".to_string(),
            toolchain: "t".to_string(),
            verified: 3,
        };
        let fns = vir_functions(vir).unwrap();
        assert!(!fns[0].expanded && fns[2].expanded);
        let s = build(&dir, "t", &dir, &info, "4.16.0", &[], &fns).unwrap();
        assert_eq!(s.fns.len(), 1, "{s:?}");
        assert_eq!(s.fns[0].path, "t::{impl}::m");
        assert_eq!((s.fns[0].file.as_str(), s.fns[0].line), ("src/lib.rs", 3));
        assert!(
            s.skipped
                .iter()
                .any(|(p, why)| p == "t::impl&%1::g" && why.contains("only in the Verus build"))
        );
        assert!(
            s.skipped
                .iter()
                .any(|(p, why)| p == "t::impl&%7::e" && why.contains("macro expansion"))
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn json_and_run_info() {
        let ok = r#"{"verification-results": {"encountered-error": false, "encountered-vir-error": false, "success": true, "verified": 7, "errors": 0, "is-verifying-entire-crate": true}, "verus": {"version": "0.1", "commit": "abc", "toolchain": "1.99.1"}}"#;
        let j = parse_json(ok).unwrap();
        let i = run_info(&j).unwrap();
        assert_eq!((i.version.as_str(), i.verified), ("0.1", 7));
        let partial = ok.replace(
            "\"is-verifying-entire-crate\": true",
            "\"is-verifying-entire-crate\": false",
        );
        assert!(run_info(&parse_json(&partial).unwrap()).is_err());
        let failed = ok.replace("\"errors\": 0", "\"errors\": 1");
        assert!(run_info(&parse_json(&failed).unwrap()).is_err());
    }

    #[test]
    fn spans_and_versions() {
        assert_eq!(
            parse_span("crates/a/src/x.rs:280:1: 283:11 (#0)"),
            Some(VirSpan {
                file: "crates/a/src/x.rs".to_string(),
                lo: (280, 1),
                hi: (283, 11)
            })
        );
        assert_eq!(
            z3_version("Z3 version 4.16.0 - 64 bit\n").as_deref(),
            Some("4.16.0")
        );
        assert_eq!(
            relative(Path::new("/a/b/c.rs"), Path::new("/a/d")),
            "../b/c.rs"
        );
    }
}
