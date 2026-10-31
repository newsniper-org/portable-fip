// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Pins the hand-written strict certificates of this crate. Adding one requires
//! updating this list; certificates are made and justified in `fip_strict::certs`.

#[test]
fn hand_written_certificates_are_exactly_the_documented_ones() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let found: Vec<(String, String)> = fip_testkit::certs::hand_written(&dir)
        .into_iter()
        .map(|(f, _, line)| {
            let file = f
                .file_name()
                .map(|n| n.to_string_lossy().into_owned())
                .unwrap_or_default();
            let ident = line
                .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .find(|w| w.starts_with("__fip_strict_"))
                .unwrap_or("")
                .to_string();
            (file, ident)
        })
        .collect();
    let mut expected: Vec<(String, String)> =
        "slice.rs:__fip_strict_swap,slot.rs:__fip_strict_replace,lib.rs:__fip_strict_replace"
            .split(',')
            .map(|e| {
                let (f, i) = e.split_once(':').unwrap_or((e, ""));
                (f.to_string(), i.to_string())
            })
            .collect();
    let mut found_sorted = found;
    found_sorted.sort();
    expected.sort();
    assert_eq!(found_sorted, expected);
}
