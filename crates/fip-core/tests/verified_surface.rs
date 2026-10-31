// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gate: every exec function in `src/` carries a Verus specification.
//!
//! With the attribute syntax, a function without `verus_spec` is silently treated
//! as external by Verus, i.e. not verified, and `--no-cheating` does not object.
//! This test closes that gap by checking the source text.

use std::fs;
use std::path::Path;

/// Returns `(file, line, signature)` for every `fn` item not preceded by a
/// `verus_spec` attribute. Functions inside `verus! { .. }` blocks are spec/proof
/// items and are skipped.
fn unspecified_fns(dir: &Path) -> Vec<(String, usize, String)> {
    let mut out = Vec::new();
    let mut files: Vec<_> = fs::read_dir(dir)
        .expect("read src dir")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        .collect();
    files.sort();
    for path in files {
        let text = fs::read_to_string(&path).expect("read source");
        let mut in_verus_block = false;
        let mut pending_spec = false;
        for (n, line) in text.lines().enumerate() {
            let t = line.trim_start();
            if t.starts_with("verus! {") {
                in_verus_block = true;
                continue;
            }
            if in_verus_block {
                if t.starts_with("} // verus!") {
                    in_verus_block = false;
                }
                continue;
            }
            if t.contains("verus_spec(") && t.starts_with("#[cfg_attr(verus_keep_ghost") {
                pending_spec = true;
                continue;
            }
            let is_fn = ["pub fn ", "fn ", "pub(crate) fn "]
                .iter()
                .any(|p| t.starts_with(p));
            if is_fn {
                if !pending_spec {
                    out.push((path.display().to_string(), n + 1, t.to_string()));
                }
                pending_spec = false;
            } else if !(t.is_empty()
                || t.starts_with("#[")
                || t.starts_with("///")
                || t.starts_with("//")
                || pending_spec)
            {
                pending_spec = false;
            }
        }
    }
    out
}

#[test]
fn every_function_is_specified() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let missing = unspecified_fns(&dir);
    assert!(
        missing.is_empty(),
        "functions without a verus_spec attribute:\n{missing:#?}"
    );
}

#[test]
fn checker_detects_a_missing_spec() {
    let dir = std::env::temp_dir().join(format!(
        "{}-surface-{}",
        env!("CARGO_PKG_NAME"),
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("mkdir");
    fs::write(
        dir.join("x.rs"),
        "#[cfg_attr(verus_keep_ghost, verus_spec(ensures true))]\npub fn ok() {}\n\n/// doc\npub fn bad() {}\n",
    )
    .expect("write");
    let missing = unspecified_fns(&dir);
    fs::remove_dir_all(&dir).expect("cleanup");
    assert_eq!(missing.len(), 1, "{missing:?}");
    assert!(missing[0].2.starts_with("pub fn bad"));
}
