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
    // `Self { name, allocs, .. }` in `Cert::assume` and `Cert::assume_no_panic_macros`
    // are the only other construction sites.
    assert_eq!(src.matches("Cert {\n        name:").count(), 3);
    assert_eq!(
        src.matches("Self {\n            name,\n            allocs,")
            .count(),
        2
    );
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

/// Every `unsafe impl .. FipBound` in this crate, plain and Verus declarations: the
/// claims a callable value's bound rests on. `Certified` (claimed by the `unsafe`
/// constructors, `NO_PANIC_MACROS` its const parameter), `Stateless` (one call of
/// the wrapped `F`), `Compose` and `Then` (one call of each part, an overflowing sum
/// fails constant evaluation); the adapters are panic-macro free only if every part
/// is.
#[test]
fn fip_bound_impls_are_exactly_the_documented_ones() {
    let src = include_str!("../src/lib.rs");
    let mut impls: Vec<&str> = src
        .lines()
        .filter(|l| l.starts_with("unsafe impl") && l.contains("FipBound for"))
        .collect();
    impls.sort_unstable();
    assert_eq!(
        impls,
        [
            "unsafe impl<F: FipBound, G: FipBound> FipBound for Compose<F, G> {",
            "unsafe impl<F: FipBound, G: FipBound> FipBound for Compose<F, G> {",
            "unsafe impl<F: FipBound, G: FipBound> FipBound for Then<F, G> {",
            "unsafe impl<F: FipBound, G: FipBound> FipBound for Then<F, G> {",
            "unsafe impl<F: FipBound> FipBound for Stateless<F> {",
            "unsafe impl<F: FipBound> FipBound for Stateless<F> {",
            "unsafe impl<const ALLOCS: u64, C, const P: bool> FipBound for Certified<ALLOCS, C, P> {",
            "unsafe impl<const ALLOCS: u64, C, const P: bool> FipBound for Certified<ALLOCS, C, P> {",
        ]
    );
    assert_eq!(src.matches("    const ALLOCS: u64 = F::ALLOCS;").count(), 2);
    assert_eq!(
        src.matches("    const ALLOCS: u64 = F::ALLOCS + G::ALLOCS;")
            .count(),
        4
    );
    assert_eq!(
        src.matches("    const NO_PANIC_MACROS: bool = P;").count(),
        2
    );
    assert_eq!(
        src.matches("    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS;")
            .count(),
        2
    );
    assert_eq!(
        src.matches("    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS && G::NO_PANIC_MACROS;")
            .count(),
        4
    );
}
