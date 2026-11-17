// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Guard for `requires(..)` in `fip-core`. Since phase 5 of decision
//! 2026-11-06-redesign-verus-allocates the attribute `#[fip_macros::fip(..)]` runs in
//! the Verus build too and, for `strict`/`total`, generates the Verus `requires` from
//! `requires(..)`: one declaration, so the two cannot drift. This test reads the
//! sources and checks that this holds for every `requires(..)` there: the attribute is
//! `strict` or `total` (only then is the Verus `requires` generated), it is not
//! compiled out under Verus (`cfg_attr(not(verus_keep_ghost), ..)`, which the crate
//! used before phase 5), and the hand-written `verus_spec` after it has no `requires`
//! of its own (the macro rejects that under Verus; this test also catches it in a
//! plain `cargo test`).

use std::path::Path;

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

/// One `fip_macros::fip(..)` attribute with `requires(..)`.
struct Site {
    /// The item's `fn` line.
    head: String,
    /// The attribute's arguments.
    args: String,
    /// The arguments of the `verus_spec(..)` between the attribute and the `fn`, if
    /// any.
    spec: String,
    /// The attribute sits in `cfg_attr(not(verus_keep_ghost), ..)`.
    compiled_out: bool,
}

/// Every `fip_macros::fip(..)` attribute with a `requires(..)` that starts a line of
/// code (doc comments and strings are skipped).
fn sites(src: &str) -> Vec<Site> {
    let mut out = Vec::new();
    let mut offset = 0;
    let lines: Vec<&str> = src.split_inclusive('\n').collect();
    for (n, line) in lines.iter().enumerate() {
        let start = offset;
        offset += line.len();
        let t = line.trim_start();
        let rel = if t.starts_with("#[fip_macros::fip(") {
            "#[fip_macros::fip".len()
        } else if t.starts_with("fip_macros::fip(") {
            "fip_macros::fip".len()
        } else {
            continue;
        };
        let open = start + (line.len() - t.len()) + rel;
        let args = group(src, open);
        if !args.contains("requires(") {
            continue;
        }
        let rest = &src[open + args.len()..];
        let fn_at = [rest.find("\nfn "), rest.find(" fn ")]
            .into_iter()
            .flatten()
            .min()
            .unwrap_or(rest.len());
        let spec = rest[..fn_at]
            .find("verus_spec(")
            .map_or_default(|v| group(rest, v + "verus_spec".len()).to_string());
        let head = rest[fn_at..]
            .lines()
            .find(|l| l.contains("fn "))
            .unwrap_or("")
            .trim()
            .to_string();
        let compiled_out = (n > 0 && lines[n - 1].contains("not(verus_keep_ghost)"))
            || t.contains("not(verus_keep_ghost)");
        out.push(Site {
            head,
            args: args.to_string(),
            spec,
            compiled_out,
        });
    }
    out
}

/// What is wrong with one site (empty: nothing).
fn problems(s: &Site) -> Vec<String> {
    let mut out = Vec::new();
    let words: Vec<&str> = s
        .args
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .collect();
    if !words.iter().any(|w| *w == "strict" || *w == "total") {
        out.push(
            "`requires(..)` without `strict`/`total`: no Verus `requires` is generated".to_string(),
        );
    }
    if s.compiled_out {
        out.push("the attribute is compiled out under Verus".to_string());
    }
    let spec_words: Vec<&str> = s
        .spec
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .collect();
    if spec_words.contains(&"requires") {
        out.push("the hand-written `verus_spec` states a `requires` of its own".to_string());
    }
    out
}

#[test]
fn fip_core_requires_are_generated() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../fip-core/src");
    let mut checked = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("fip-core/src") {
        let path = entry.expect("entry").path();
        if path.extension().is_none_or(|e| e != "rs") {
            continue;
        }
        let src = std::fs::read_to_string(&path).expect("read source");
        for s in sites(&src) {
            let p = problems(&s);
            assert!(p.is_empty(), "{}: `{}`: {p:?}", path.display(), s.head);
            checked.push(s.head);
        }
    }
    for f in ["fn swap_lt", "fn swap<"] {
        assert!(
            checked.iter().any(|h| h.contains(f)),
            "`{f}`'s `requires(..)` was not checked; checked: {checked:?}"
        );
    }
}

/// The guard fails on the forms it exists to reject (negative controls).
#[test]
fn hand_written_or_compiled_out_requires_is_detected() {
    let generated = "#[fip_macros::fip(strict, requires(i < j, j < xs.len()))]\n\
                     #[cfg_attr(verus_keep_ghost, verus_spec(\n    ensures\n        true,\n))]\n\
                     pub(crate) fn swap_lt<T>(xs: &mut [T], i: usize, j: usize) {}\n";
    let found = sites(generated);
    assert_eq!(found.len(), 1);
    assert_eq!(problems(&found[0]), Vec::<String>::new());
    let twice = generated.replace(
        "    ensures\n",
        "    requires\n        i < j,\n    ensures\n",
    );
    assert_eq!(problems(&sites(&twice)[0]).len(), 1);
    let not_strict = generated.replace("fip(strict, ", "fip(");
    assert_eq!(problems(&sites(&not_strict)[0]).len(), 1);
    let compiled_out = generated.replace(
        "#[fip_macros::fip(strict, requires(i < j, j < xs.len()))]\n",
        "#[cfg_attr(\n    not(verus_keep_ghost),\n    fip_macros::fip(strict, requires(i < j, j < xs.len()))\n)]\n",
    );
    assert_eq!(problems(&sites(&compiled_out)[0]).len(), 1);
}
