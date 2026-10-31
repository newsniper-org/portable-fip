// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `fip_strict::certs` is the one place where certificates are made without
//! `Cert::assume`. Pins its exact contents: adding a certificate means updating this
//! list and justifying the entry in `src/lib.rs`. Each certificate names the function
//! its identifier is for.

#[test]
fn certificates_made_here_are_exactly_the_documented_ones() {
    let src = include_str!("../src/lib.rs");
    let lines: Vec<&str> = src.lines().collect();
    let mut made: Vec<(String, String)> = Vec::new();
    for (i, l) in lines.iter().enumerate() {
        if !l.contains(": Cert = Cert {") {
            continue;
        }
        let ident = l
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .find(|w| w.starts_with("__fip_strict_"))
            .unwrap_or("")
            .to_string();
        let name = lines
            .get(i + 1)
            .and_then(|n| n.trim().strip_prefix("name: \""))
            .and_then(|n| n.strip_suffix("\","))
            .unwrap_or("")
            .to_string();
        made.push((ident, name));
    }
    made.sort();
    let expected: Vec<(String, String)> = ["refill", "replace", "swap"]
        .iter()
        .map(|f| (format!("__fip_strict_{f}"), (*f).to_string()))
        .collect();
    assert_eq!(made, expected);
    // `Self { name, allocs }` in `Cert::assume` is the only other construction site.
    assert_eq!(src.matches("Cert {\n        name:").count(), 3);
    assert_eq!(src.matches("Self { name, allocs }").count(), 1);
}

#[test]
fn certificates_carry_their_names() {
    use fip_strict::certs::{__fip_strict_refill, __fip_strict_replace, __fip_strict_swap};
    assert_eq!(__fip_strict_swap.allocs_for("swap"), 0);
    assert_eq!(__fip_strict_replace.name(), "replace");
    assert_eq!(__fip_strict_refill.name(), "refill");
    let r = std::panic::catch_unwind(|| __fip_strict_swap.allocs_for("replace"));
    assert!(
        r.is_err(),
        "a certificate must not be accepted for another name"
    );
}
