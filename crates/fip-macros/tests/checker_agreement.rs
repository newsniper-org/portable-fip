// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `#[fip]` (token lint) and `fip_testkit::summaries` (crate-wide checker) agree:
//! every behaviour-related, non-strict `compile_fail` example of `src/lib.rs` is a
//! violation for the checker, the accepted examples in `tests/accept.rs` are not,
//! and the checker reports no violation over this crate's tests together with the
//! crates they call.

use std::path::{Path, PathBuf};

use fip_testkit::summaries::{Report, fip_violations, fip_violations_in};

/// Copies of the `compile_fail` examples in `src/lib.rs` whose rejection is about
/// behaviour (allocation sites, recursion), without the hidden `# fn main() {}` line.
const REJECTED: &[&str] = &[
    "#[fip_macros::fip]\nfn f(x: i32) -> Box<i32> { Box::new(x) }",
    "#[fip_macros::fip]\nfn f(x: &[u8]) -> usize { let v = vec![0u8; 4]; v.len() + x.len() }",
    "#[fip_macros::fip]\nfn f(x: &[u8]) -> usize { let y = x.to_vec(); y.len() }",
    "#[fip_macros::fip]\nfn f(n: u32) -> u32 { if n == 0 { 0 } else { f(n - 1) } }",
    "#[fip_macros::fip(1)]\nfn f(n: u32) -> u32 { let mut s = 0; for i in 0..n { let b = Box::new(i); s += *b; } s }",
    "#[fip_macros::fip(1)]\nfn f(a: u8, b: u8) -> (Box<u8>, Box<u8>) { (Box::new(a), Box::new(b)) }",
    "#[fip_macros::fbip]\nfn f(x: u8) -> String { format!(\"{x}\") }",
];

fn manifest() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn check(name: &str, src: &str) -> Report {
    fip_violations_in(&[(PathBuf::from(name), src.to_string())])
}

#[test]
fn snippets_are_the_ones_in_the_crate_docs() {
    let lib = std::fs::read_to_string(manifest().join("src/lib.rs")).expect("read src/lib.rs");
    for s in REJECTED {
        let mut block = String::from("//! ```compile_fail\n");
        for line in s.lines() {
            block.push_str("//! ");
            block.push_str(line);
            block.push('\n');
        }
        block.push_str("//! # fn main() {}\n//! ```\n");
        assert!(
            lib.contains(&block),
            "snippet no longer in src/lib.rs (update REJECTED):\n{block}"
        );
    }
}

#[test]
fn rejected_examples_are_violations() {
    for s in REJECTED {
        let r = check("snippet.rs", s);
        assert!(!r.violations.is_empty(), "checker accepts:\n{s}\n{r:?}");
    }
}

#[test]
fn accepted_examples_are_not_violations() {
    let path = manifest().join("tests/accept.rs");
    let src = std::fs::read_to_string(&path).expect("read tests/accept.rs");
    let r = check("accept.rs", &src);
    assert!(r.violations.is_empty(), "{r}");
    assert!(r.conditional.is_empty(), "{r}");
    assert!(r.roots.len() >= 8, "{r:?}");
}

#[test]
fn tests_and_called_crates_have_no_violation() {
    let crates = manifest().join("..");
    let tests = manifest().join("tests");
    let core = crates.join("fip-core/src");
    let alloc = crates.join("fip-alloc/src");
    let strict = crates.join("fip-strict/src");
    let r = fip_violations(&[
        ("fip_macros_tests", tests.as_path()),
        ("fip_core", core.as_path()),
        ("fip_alloc", alloc.as_path()),
        ("fip_strict", strict.as_path()),
    ]);
    assert!(r.violations.is_empty(), "{r}");
    // every root is either a pass or reported as conditional, never silently dropped
    assert!(r.roots.iter().all(|s| s.summary != "⊤"), "{:?}", r.roots);
    for c in &r.conditional {
        eprintln!(
            "conditional: {} {} (fip relative to its parameters: {})",
            c.attribute, c.root, c.summary
        );
    }
    for s in &r.roots {
        eprintln!(
            "root: {} {} bound {} at {}",
            s.attribute, s.root, s.summary, s.at
        );
    }
    assert!(Path::new(&core).is_dir());
}
