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

/// Every `unsafe impl .. FipBound` in this crate (one declaration for both builds): the
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
            "unsafe impl<F: FipBound, G: FipBound> FipBound for Then<F, G> {",
            "unsafe impl<F: FipBound> FipBound for Stateless<F> {",
            "unsafe impl<const ALLOCS: u64, C, const P: bool> FipBound for Certified<ALLOCS, C, P> {",
        ]
    );
    assert_eq!(src.matches("    const ALLOCS: u64 = F::ALLOCS;").count(), 1);
    assert_eq!(
        src.matches("    const ALLOCS: u64 = F::ALLOCS + G::ALLOCS;")
            .count(),
        2
    );
    assert_eq!(
        src.matches("    const NO_PANIC_MACROS: bool = P;").count(),
        1
    );
    assert_eq!(
        src.matches("    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS;")
            .count(),
        1
    );
    assert_eq!(
        src.matches("    const NO_PANIC_MACROS: bool = F::NO_PANIC_MACROS && G::NO_PANIC_MACROS;")
            .count(),
        2
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
    // Each is in the block of specifications, which is for Verus's build only
    // (`#[cfg(verus_keep_ghost)] verus! { .. }`): an empty impl of a marker of Verus's
    // crates, one of the uses of the gate the sidecar generator admits.
    let block = "// ---- Specifications (only under the `verus` driver): no exec code.\n\n#[cfg(verus_keep_ghost)]\nverus! {\n";
    let from = src.find(block).expect("the block of specifications");
    let to = from + src[from..].find("\n} // verus!\n").expect("its end");
    let mut impls: Vec<&str> = Vec::new();
    let mut at = 0;
    for l in src.lines() {
        if l.starts_with("unsafe impl")
            && (l.contains("AllocFreeDrop for") || l.contains("NoDeallocDrop for"))
        {
            assert!(
                from < at && at < to,
                "a drop marker impl outside the block of specifications: {l}"
            );
            assert!(l.ends_with(" {}"), "not an empty impl: {l}");
            impls.push(l);
        }
        at += l.len() + 1;
    }
    impls.sort_unstable();
    assert_eq!(
        impls,
        [
            "unsafe impl<F: vstd::alloc_check::AllocFreeDrop, G: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Compose<F, G> {}",
            "unsafe impl<F: vstd::alloc_check::AllocFreeDrop, G: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Then<F, G> {}",
            "unsafe impl<F: vstd::alloc_check::AllocFreeDrop> vstd::alloc_check::AllocFreeDrop for Stateless<F> {}",
            "unsafe impl<F: vstd::alloc_check::NoDeallocDrop, G: vstd::alloc_check::NoDeallocDrop> vstd::alloc_check::NoDeallocDrop for Compose<F, G> {}",
            "unsafe impl<F: vstd::alloc_check::NoDeallocDrop, G: vstd::alloc_check::NoDeallocDrop> vstd::alloc_check::NoDeallocDrop for Then<F, G> {}",
            "unsafe impl<F: vstd::alloc_check::NoDeallocDrop> vstd::alloc_check::NoDeallocDrop for Stateless<F> {}",
            "unsafe impl<const ALLOCS: u64, C: Copy, const P: bool> vstd::alloc_check::AllocFreeDrop for Certified<ALLOCS, C, P> {}",
            "unsafe impl<const ALLOCS: u64, C: Copy, const P: bool> vstd::alloc_check::NoDeallocDrop for Certified<ALLOCS, C, P> {}",
        ]
    );
}
