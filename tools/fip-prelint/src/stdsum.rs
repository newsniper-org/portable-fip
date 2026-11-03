// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Generated summaries of standard-library functions without MIR (limits plan L6),
//! stored as a plain-text sidecar (L10e).
//!
//! The shipped `core`/`alloc`/`std` carry MIR only for generic and inlinable
//! functions. `cargo fip-prelint --std-summaries` analyses a `-Zbuild-std` build with
//! the release settings of the shipped `std` (`-Copt-level=3`, no debug assertions,
//! no overflow checks) and writes, per non-generic function reached from the seed
//! crate, what the driver's own analysis finds in it. The driver uses an entry only
//! where the shipped `std` has no MIR, and only if the stamp matches its compiler and
//! the target exactly; otherwise such a function stays `⊤`.
//!
//! Format (one item per line, `#` comments, blank lines ignored):
//!
//! ```text
//! fip-prelint std summaries
//! format 1
//! rustc 1.99.1 (<commit> <date>)
//! target x86_64-unknown-linux-gnu
//! settings opt-level=3 debug-assertions=off overflow-checks=off
//! std-src <fnv-1a 64 of the library sources, hex>
//!
//! fn <def path>
//! alloc <n | inf>
//! term <mult | inf> <key>
//! free <witness>
//! panic <witness>
//! top <witness>
//! recursion <witness>
//! end
//! ```
//!
//! Term keys are calls the summarised function makes through its parameters, left
//! open and resolved at each call site: `§out <i> <trait method>` (a dynamic call on
//! the output reached through parameter `i`: a `&mut dyn fmt::Write`, a
//! `&mut fmt::Formatter`, or one held below it, such as a `core::fmt` builder's
//! formatter or a `PadAdapter`'s buffer), `§fmt <i> out <out>` (the formatting
//! functions carried by the `fmt::Arguments` in parameter `i`, called with a
//! `Formatter` writing to `<out>`) and `§dyn <i> <trait method> fmt <out>` (top plan
//! T7a: the method of the `&dyn fmt::Debug`/`&dyn fmt::Display` in parameter `i`,
//! called with a `Formatter` writing to `<out>`). An output `<out>` is `param <j>`
//! (parameter `j`'s output), `pad <out>` (a `core::fmt::builders::PadAdapter` over
//! `<out>`, the `{:#?}` path) or `ty <type>`. The `§dyn` and `pad` forms were added
//! without a format change: they only add keys, and a driver that does not know a
//! key reports it as `⊤`.
//!
//! Format 2 (top plan item 8b): a call of a foreign function inside a summarised
//! function is the term `§ffi <symbol> <abi>` (its link symbol and ABI as rustc
//! prints it, `"C"`), resolved at the use site with the FFI marks of the analysed
//! crate (certified: its events; excluded: none; else the FFI error), where format 1
//! recorded it as `top`. The format number changed so that a format-1 driver refuses
//! the file instead of reading a summary that leaves out what format 1 put in `top`.

use std::collections::BTreeMap;

/// Version of the format and of the meaning of its entries; bumped whenever the
/// analysis that produces them changes what an entry means.
pub const FORMAT: u32 = 2;

/// The stamp of a sidecar: what it was generated for.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stamp {
    pub format: u32,
    pub rustc: String,
    pub target: String,
    pub settings: String,
    pub std_src: String,
}

/// An allocation bound: `n` or `∞`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Count {
    Fin(u64),
    Inf,
}

impl Count {
    fn parse(s: &str) -> Result<Count, String> {
        if s == "inf" {
            return Ok(Count::Inf);
        }
        s.parse::<u64>()
            .map(Count::Fin)
            .map_err(|_| format!("expected a count or `inf`, found `{s}`"))
    }
    fn show(self) -> String {
        match self {
            Count::Fin(n) => n.to_string(),
            Count::Inf => "inf".to_string(),
        }
    }
}

/// The summary of one function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSummary {
    pub alloc: Count,
    /// Open calls through parameters, with their multiplicity.
    pub terms: Vec<(Count, String)>,
    pub free: Vec<String>,
    pub panic: Vec<String>,
    pub top: Vec<String>,
    pub recursion: Option<String>,
}

impl Default for FnSummary {
    fn default() -> Self {
        FnSummary {
            alloc: Count::Fin(0),
            terms: Vec::new(),
            free: Vec::new(),
            panic: Vec::new(),
            top: Vec::new(),
            recursion: None,
        }
    }
}

/// A parsed sidecar.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Sidecar {
    pub stamp: Stamp,
    pub fns: BTreeMap<String, FnSummary>,
}

/// One-line text: newlines would break the format.
fn one_line(s: &str) -> String {
    s.replace(['\n', '\r'], " ")
}

impl Sidecar {
    /// Parses a sidecar; any malformed line is an error (never a partial file).
    pub fn parse(text: &str) -> Result<Sidecar, String> {
        let mut lines = text
            .lines()
            .enumerate()
            .map(|(i, l)| (i + 1, l.trim_end()))
            .filter(|(_, l)| !l.trim().is_empty() && !l.starts_with('#'));
        match lines.next() {
            Some((_, "fip-prelint std summaries")) => {}
            _ => return Err("not a fip-prelint std summaries file (header)".to_string()),
        }
        let mut sc = Sidecar::default();
        let mut format = None;
        let mut current: Option<(String, FnSummary)> = None;
        for (n, line) in lines {
            let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
            let err = |m: &str| format!("line {n}: {m}");
            if let Some((_, s)) = current.as_mut() {
                match key {
                    "alloc" => s.alloc = Count::parse(rest).map_err(|e| err(&e))?,
                    "term" => {
                        let (m, k) = rest
                            .split_once(' ')
                            .ok_or_else(|| err("expected `term <mult> <key>`"))?;
                        s.terms
                            .push((Count::parse(m).map_err(|e| err(&e))?, k.to_string()));
                    }
                    "free" => s.free.push(rest.to_string()),
                    "panic" => s.panic.push(rest.to_string()),
                    "top" => s.top.push(rest.to_string()),
                    "recursion" => s.recursion = Some(rest.to_string()),
                    "end" => {
                        let (name, s) = current.take().expect("inside an entry");
                        if sc.fns.insert(name.clone(), s).is_some() {
                            return Err(err(&format!("`{name}` summarised twice")));
                        }
                    }
                    other => return Err(err(&format!("unknown key `{other}` in an entry"))),
                }
                continue;
            }
            match key {
                "format" => {
                    format = Some(
                        rest.parse::<u32>()
                            .map_err(|_| err("expected `format <n>`"))?,
                    );
                }
                "rustc" => sc.stamp.rustc = rest.to_string(),
                "target" => sc.stamp.target = rest.to_string(),
                "settings" => sc.stamp.settings = rest.to_string(),
                "std-src" => sc.stamp.std_src = rest.to_string(),
                "fn" if !rest.is_empty() => {
                    current = Some((rest.to_string(), FnSummary::default()));
                }
                other => return Err(err(&format!("unknown key `{other}`"))),
            }
        }
        if current.is_some() {
            return Err("unterminated entry (missing `end`)".to_string());
        }
        sc.stamp.format = format.ok_or("missing `format`")?;
        Ok(sc)
    }

    /// The text of the sidecar (entries in path order, so regenerating is a stable
    /// diff).
    pub fn render(&self) -> String {
        let mut out = String::from(
            "fip-prelint std summaries\n# Generated by `cargo fip-prelint --std-summaries`; do not edit.\n",
        );
        out.push_str(&format!("format {}\n", self.stamp.format));
        out.push_str(&format!("rustc {}\n", one_line(&self.stamp.rustc)));
        out.push_str(&format!("target {}\n", one_line(&self.stamp.target)));
        out.push_str(&format!("settings {}\n", one_line(&self.stamp.settings)));
        out.push_str(&format!("std-src {}\n", one_line(&self.stamp.std_src)));
        for (name, s) in &self.fns {
            out.push_str(&format!("\nfn {}\n", one_line(name)));
            out.push_str(&format!("alloc {}\n", s.alloc.show()));
            for (m, k) in &s.terms {
                out.push_str(&format!("term {} {}\n", m.show(), one_line(k)));
            }
            for w in &s.free {
                out.push_str(&format!("free {}\n", one_line(w)));
            }
            for w in &s.panic {
                out.push_str(&format!("panic {}\n", one_line(w)));
            }
            for w in &s.top {
                out.push_str(&format!("top {}\n", one_line(w)));
            }
            if let Some(w) = &s.recursion {
                out.push_str(&format!("recursion {}\n", one_line(w)));
            }
            out.push_str("end\n");
        }
        out
    }

    /// `Err(reason)` unless the sidecar was generated for exactly this format,
    /// compiler and target.
    pub fn check_stamp(&self, rustc: &str, target: &str) -> Result<(), String> {
        let s = &self.stamp;
        if s.format != FORMAT {
            return Err(format!(
                "format {} (this driver reads format {FORMAT})",
                s.format
            ));
        }
        if s.rustc != rustc {
            return Err(format!(
                "generated for rustc `{}`, this driver is rustc `{rustc}`",
                s.rustc
            ));
        }
        if s.target != target {
            return Err(format!(
                "generated for target `{}`, this crate is compiled for `{target}`",
                s.target
            ));
        }
        Ok(())
    }
}

/// FNV-1a, 64 bit: a dependency-free, stable content hash (provenance of the std
/// sources a sidecar was generated from).
pub fn fnv1a(hash: u64, bytes: &[u8]) -> u64 {
    let mut h = hash;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// The FNV-1a offset basis.
pub const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;

/// Hash of every file under `dirs` (relative paths and contents, in path order).
pub fn hash_tree(dirs: &[std::path::PathBuf]) -> Result<String, String> {
    let mut files = Vec::new();
    let mut stack: Vec<std::path::PathBuf> = dirs.to_vec();
    while let Some(d) = stack.pop() {
        let rd = std::fs::read_dir(&d).map_err(|e| format!("{}: {e}", d.display()))?;
        for e in rd {
            let p = e.map_err(|e| e.to_string())?.path();
            if p.is_dir() {
                stack.push(p);
            } else {
                files.push(p);
            }
        }
    }
    files.sort();
    let mut h = FNV_OFFSET;
    for f in files {
        h = fnv1a(h, f.to_string_lossy().as_bytes());
        let bytes = std::fs::read(&f).map_err(|e| format!("{}: {e}", f.display()))?;
        h = fnv1a(h, &bytes);
    }
    Ok(format!("{h:016x}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Sidecar {
        let mut fns = BTreeMap::new();
        fns.insert(
            "core::fmt::write".to_string(),
            FnSummary {
                alloc: Count::Fin(0),
                terms: vec![
                    (Count::Inf, "§out 0 core::fmt::Write::write_str".to_string()),
                    (Count::Inf, "§fmt 1 out param 0".to_string()),
                    (Count::Fin(1), "§ffi syscall \"C\"".to_string()),
                ],
                free: Vec::new(),
                panic: vec!["`core::panicking::panic_fmt`".to_string()],
                top: Vec::new(),
                recursion: None,
            },
        );
        fns.insert(
            "alloc::fmt::format::format_inner".to_string(),
            FnSummary {
                alloc: Count::Inf,
                terms: vec![(
                    Count::Inf,
                    "§fmt 0 out ty alloc::string::String".to_string(),
                )],
                free: vec!["a -> b: deallocation".to_string()],
                panic: Vec::new(),
                top: vec!["`x` (no MIR)".to_string()],
                recursion: Some("recursion".to_string()),
            },
        );
        Sidecar {
            stamp: Stamp {
                format: FORMAT,
                rustc: "1.99.1 (abc 2026-01-01)".to_string(),
                target: "x86_64-unknown-linux-gnu".to_string(),
                settings: "opt-level=3".to_string(),
                std_src: "0123".to_string(),
            },
            fns,
        }
    }

    #[test]
    fn round_trip() {
        let s = sample();
        let text = s.render();
        assert_eq!(Sidecar::parse(&text), Ok(s));
    }

    #[test]
    fn stamp_must_match() {
        let s = sample();
        assert!(
            s.check_stamp("1.99.1 (abc 2026-01-01)", "x86_64-unknown-linux-gnu")
                .is_ok()
        );
        assert!(
            s.check_stamp("1.99.2 (def 2026-02-01)", "x86_64-unknown-linux-gnu")
                .is_err()
        );
        assert!(
            s.check_stamp("1.99.1 (abc 2026-01-01)", "wasm32-unknown-unknown")
                .is_err()
        );
        let mut old = sample();
        old.stamp.format = FORMAT + 1;
        assert!(
            old.check_stamp("1.99.1 (abc 2026-01-01)", "x86_64-unknown-linux-gnu")
                .is_err()
        );
        // A format-1 file (foreign calls as `top`) is not read as format 2.
        old.stamp.format = 1;
        assert!(
            old.check_stamp("1.99.1 (abc 2026-01-01)", "x86_64-unknown-linux-gnu")
                .is_err()
        );
    }

    #[test]
    fn malformed_files_are_rejected() {
        assert!(Sidecar::parse("").is_err());
        assert!(Sidecar::parse("something else\n").is_err());
        let text = sample().render();
        assert!(Sidecar::parse(&text.replace("end\n", "")).is_err());
        assert!(Sidecar::parse(&text.replace("alloc inf", "alloc lots")).is_err());
        assert!(Sidecar::parse(&text.replace("panic ", "panik ")).is_err());
        assert!(Sidecar::parse(&text.replace(&format!("format {FORMAT}\n"), "")).is_err());
        let twice = format!("{text}\nfn core::fmt::write\nend\n");
        assert!(Sidecar::parse(&twice).is_err());
    }

    /// The committed sidecars parse, and one is stamped for this driver's compiler: a
    /// repinned toolchain without regenerated summaries fails here (at run time such a
    /// file is not used, and functions without MIR are `⊤`).
    #[test]
    fn committed_summaries_match_this_driver() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("std-summaries");
        let rustc = crate::analysis::rustc_version();
        let release = rustc.split(' ').next().unwrap_or("unknown");
        let mut matching = 0;
        for e in std::fs::read_dir(&dir).expect("std-summaries/") {
            let p = e.expect("entry").path();
            if p.extension().is_none_or(|x| x != "txt") {
                continue;
            }
            let sc = Sidecar::parse(&std::fs::read_to_string(&p).expect("read"))
                .unwrap_or_else(|e| panic!("{}: {e}", p.display()));
            let name = p.file_name().expect("name").to_string_lossy().to_string();
            if name.starts_with(&format!("{release}-")) {
                assert_eq!(
                    sc.stamp.rustc, rustc,
                    "{name}: regenerate (`just prelint-std-summaries`)"
                );
                assert_eq!(name, format!("{release}-{}.txt", sc.stamp.target));
                matching += 1;
            }
        }
        assert!(
            matching > 0,
            "no std summaries for rustc {rustc} in {}",
            dir.display()
        );
    }

    #[test]
    fn hash_is_fnv1a() {
        // Reference values of FNV-1a 64.
        assert_eq!(fnv1a(FNV_OFFSET, b""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(fnv1a(FNV_OFFSET, b"a"), 0xaf63_dc4c_8601_ec8c);
    }
}
