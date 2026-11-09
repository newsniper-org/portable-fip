// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! No certificate is made in this crate without `Cert::assume` (phase 5 of decision
//! 2026-11-06-redesign-verus-allocates removed the module `certs`: the functions it
//! certified are `#[fip(strict ..)]`/`#[fip(total)]` now, with generated
//! certificates). Adding one means updating this test and justifying it.

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
    assert_eq!(made, Vec::<(String, String)>::new());
    // `Self { name, allocs, .. }` in `Cert::assume` and `Cert::assume_no_panic_macros`
    // are the only construction sites.
    assert_eq!(src.matches("Cert {\n        name:").count(), 0);
    assert_eq!(
        src.matches("Self {\n            name,\n            allocs,")
            .count(),
        2
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

/// Every `unsafe impl .. AllocFreeDrop` in this crate (decision
/// 2026-11-06-redesign-verus-allocates, phase 3): Verus-only, inside the `verus!`
/// block (in plain builds `AllocFreeDrop` is a marker implemented for every type, and
/// these impls would conflict with it). They state that dropping the value cannot
/// allocate: `Certified` when the wrapped closure is `Copy` (no drop glue), each
/// adapter when its parts' drops cannot. The fork's `-V alloc-check` checks each impl
/// (it rejects one for a type whose `Drop::drop` is not `allocates 0`); they are no
/// allocation certificate (`FipBound`, above).
#[test]
fn alloc_free_drop_impls_are_exactly_the_documented_ones() {
    let src = include_str!("../src/lib.rs");
    let verus_start = src
        .find("// ---- Verus declarations")
        .expect("Verus region");
    let verus_end = src.find("} // verus!").expect("end of the verus! block");
    // Items start at column 0 (the doc comments that mention such an impl do not).
    let mut impls: Vec<(usize, &str)> = Vec::new();
    let mut at = 0;
    for l in src.lines() {
        if l.starts_with("unsafe impl") && l.contains("AllocFreeDrop for") {
            impls.push((at, l));
        }
        at += l.len() + 1;
    }
    assert!(
        impls.iter().all(|&(p, _)| verus_start < p && p < verus_end),
        "an `unsafe impl AllocFreeDrop` outside the verus! block: {impls:#?}"
    );
    let mut lines: Vec<&str> = impls.iter().map(|&(_, l)| l).collect();
    lines.sort_unstable();
    assert_eq!(
        lines,
        [
            "unsafe impl<F: vstd::alloc_check::AllocFreeDrop, G: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Compose<F, G> {}",
            "unsafe impl<F: vstd::alloc_check::AllocFreeDrop, G: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Then<F, G> {}",
            "unsafe impl<F: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Stateless<F> {}",
            "unsafe impl<const ALLOCS: u64, C: Copy, const P: bool> vstd::alloc_check::AllocFreeDrop for Certified<ALLOCS, C, P> {}",
        ]
    );
}
