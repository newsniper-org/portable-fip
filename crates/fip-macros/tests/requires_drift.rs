// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Drift guard for `requires(..)` in `fip-core`. There `#[fip]` is compiled out under
//! Verus (`cfg_attr(not(verus_keep_ghost), fip_macros::fip(..))`), so the macro never
//! sees the `verus_spec` next to it and cannot compare the two (it does where it sees
//! both, e.g. `verify/compose.rs`). This test reads the sources instead: every
//! conjunct of a `requires(..)` inside `fip_macros::fip(..)` must be among the
//! conjuncts of the `requires` of the `verus_spec` that follows it.

use std::path::Path;

use fip_lint_rules::requires::{display, from_verus, not_in, parse};

/// The text inside the parentheses that open at `open` (a `(`).
fn group(s: &str, open: usize) -> &str {
    let mut depth = 0_i32;
    for (k, c) in s[open..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return &s[open + 1..open + k];
                }
            }
            _ => {}
        }
    }
    &s[open + 1..]
}

/// `(function head, fip requires, verus spec)` of every `fip_macros::fip(..)` with a
/// `requires(..)` in `src`; the spec is empty if no `verus_spec` follows before the
/// function's `fn`.
fn pairs(src: &str) -> Vec<(String, String, String)> {
    let mut out = Vec::new();
    let mut at = 0;
    while let Some(k) = src[at..].find("fip_macros::fip(") {
        let open = at + k + "fip_macros::fip".len();
        let args = group(src, open);
        at = open + 1;
        let Some(r) = args.find("requires(") else {
            continue;
        };
        let fip = group(args, r + "requires".len()).to_string();
        let rest = &src[open + args.len()..];
        let fn_at = rest
            .find("\nfn ")
            .or_else(|| rest.find(" fn "))
            .unwrap_or(rest.len());
        let spec = rest[..fn_at]
            .find("verus_spec(")
            .map(|v| group(rest, v + "verus_spec".len()).to_string())
            .unwrap_or_default();
        let head = rest[fn_at..]
            .lines()
            .nth(1)
            .unwrap_or("")
            .trim()
            .to_string();
        out.push((head, fip, spec));
    }
    out
}

/// The conjuncts of `fip` missing from the `requires` of `spec`.
fn drift(fip: &str, spec: &str) -> Vec<String> {
    let fip = parse(fip).expect("requires(..) parses");
    let verus = from_verus(spec);
    not_in(&fip, &verus).into_iter().map(display).collect()
}

#[test]
fn fip_core_requires_match_verus() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../fip-core/src");
    let mut checked = 0;
    for entry in std::fs::read_dir(&dir).expect("fip-core/src") {
        let path = entry.expect("entry").path();
        if path.extension().is_none_or(|e| e != "rs") {
            continue;
        }
        let src = std::fs::read_to_string(&path).expect("read source");
        for (head, fip, spec) in pairs(&src) {
            assert!(
                !spec.is_empty(),
                "{}: `{head}` has `requires(..)` but no `verus_spec` after it",
                path.display()
            );
            let missing = drift(&fip, &spec);
            assert!(
                missing.is_empty(),
                "{}: `{head}`: `requires(..)` conjuncts not in the verus_spec requires: {missing:?}",
                path.display()
            );
            checked += 1;
        }
    }
    // `slice::swap_lt` at least.
    assert!(checked >= 1, "no `requires(..)` found in fip-core");
}

/// The guard fails on a drifted copy (negative control).
#[test]
fn drift_is_detected() {
    let src = "#[cfg_attr(\n    not(verus_keep_ghost),\n    fip_macros::fip(strict = true, requires(i <= j, j < xs.len()))\n)]\n\
               #[cfg_attr(verus_keep_ghost, verus_spec(\n    requires\n        i < j < old(xs)@.len(),\n))]\n\
               pub(crate) fn swap_lt<T>(xs: &mut [T], i: usize, j: usize) {}\n";
    let found = pairs(src);
    assert_eq!(found.len(), 1);
    let (_, fip, spec) = &found[0];
    assert_eq!(drift(fip, spec), vec!["i <= j".to_string()]);
    let ok = src.replace("i <= j", "i < j");
    let (_, fip, spec) = &pairs(&ok)[0];
    assert_eq!(drift(fip, spec), Vec::<String>::new());
}
