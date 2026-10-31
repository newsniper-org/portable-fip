// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-lint-rules — the one rule set shared by `fip-macros` and `fip-testkit`
//!
//! What counts as an allocation site, which Verus macros are ghost code, and which
//! `core` functions are accepted without a certificate. `#[fip]` (token lint) and
//! `fip_testkit::callgraph` (crate-wide checker) both read these tables, so the two
//! tools cannot disagree about the rules.
//!
//! `#![no_std]`, no dependencies, data only.

#![no_std]
#![forbid(unsafe_code)]

/// Standard heap-owning types; `Type::ctor(..)` with a ctor below is an allocation site.
pub const HEAP_TYPES: &[&str] = &[
    "Box",
    "Vec",
    "String",
    "Rc",
    "Arc",
    "BTreeMap",
    "BTreeSet",
    "HashMap",
    "HashSet",
    "VecDeque",
    "BinaryHeap",
    "LinkedList",
];
/// Constructors of [`HEAP_TYPES`] that allocate.
pub const HEAP_CONSTRUCTORS: &[&str] = &[
    "new",
    "pin",
    "with_capacity",
    "from",
    "from_iter",
    "new_uninit",
    "new_zeroed",
    "new_cyclic",
    "default",
];
/// Macros that allocate.
pub const ALLOC_MACROS: &[&str] = &["vec", "format"];
/// Method names that may allocate (by name; the receiver type is not known).
pub const ALLOC_METHODS: &[&str] = &[
    "clone",
    "to_vec",
    "to_owned",
    "to_string",
    "collect",
    "push",
    "push_back",
    "push_front",
    "insert",
    "extend",
    "extend_from_slice",
    "reserve",
    "resize",
    "append",
    "repeat",
    "concat",
    "join",
    "into_boxed_slice",
];
/// Verus ghost-code macros, erased in plain builds; their contents are skipped.
pub const GHOST_MACROS: &[&str] = &["proof", "proof_decl", "proof_with"];

/// `core` functions accepted as `fip` without a certificate: no allocation, no
/// deallocation, no recursion, no call into user code. **Audited, not machine-proved**:
/// "no allocation" follows from `core` having no allocator (crate boundary); the rest
/// was read in the `core` sources of the toolchains in [`CORE_TABLE_AUDITED_AT`].
/// Paths below the crate root, accepted under the roots `core` and `std` (the `std`
/// items are re-exports). `slice::m` means the inherent slice method `<[T]>::m`.
/// Per-entry reasons: `docs/decisions/2026-11-01-strict-core-table.md`.
pub const CORE_TABLE: &[&str] = &[
    "slice::len",
    "slice::is_empty",
    "slice::swap",
    "slice::split_at",
    "slice::split_at_mut",
    "mem::swap",
    "mem::replace",
    "mem::size_of",
    "mem::align_of",
    "hint::black_box",
    "convert::identity",
];

/// rustc versions whose `core` sources were read for [`CORE_TABLE`]. A build with
/// any other version is not covered by the audit (`fip-macros` tests fail on it).
pub const CORE_TABLE_AUDITED_AT: &[&str] = &["1.97.1", "1.99.1"];

/// Method names the crate-wide checker treats as allocation-free **by name** when no
/// method of that name is defined in the scanned sources: the slice/integer methods
/// of [`CORE_TABLE`]. This is an assumption about the receiver (a user type from
/// another crate with an allocating method of the same name is not seen).
pub const ALLOC_FREE_METHODS: &[&str] = &["len", "is_empty", "swap", "split_at", "split_at_mut"];

/// `true` if `root::rest::name` names an entry of [`CORE_TABLE`].
#[must_use]
pub fn in_core_table(root: &str, rest: &[&str], name: &str) -> bool {
    if root != "core" && root != "std" {
        return false;
    }
    CORE_TABLE.iter().any(|entry| {
        let mut parts = entry.split("::");
        let mut ok = true;
        for seg in rest {
            ok &= parts.next() == Some(seg);
        }
        ok && parts.next() == Some(name) && parts.next().is_none()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_table_lookup() {
        assert!(in_core_table("core", &["mem"], "swap"));
        assert!(in_core_table("std", &["mem"], "replace"));
        assert!(!in_core_table("alloc", &["mem"], "swap"));
        assert!(!in_core_table("core", &["mem"], "take"));
        assert!(!in_core_table("core", &[], "swap"));
        assert!(!in_core_table("core", &["mem", "x"], "swap"));
    }
}
