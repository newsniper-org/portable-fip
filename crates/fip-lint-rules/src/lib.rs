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

/// Standard heap-owning types; `Type::ctor(..)` with a ctor below is an allocation site
/// unless the pair is in [`NON_ALLOCATING_CONSTRUCTORS`] (see [`is_heap_constructor`]).
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
/// Constructors of [`HEAP_TYPES`] that may allocate.
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

/// `(type, constructor)` pairs of [`HEAP_TYPES`] × [`HEAP_CONSTRUCTORS`] that never
/// allocate, whatever their arguments (they take none): each builds an empty value
/// (a dangling, capacity-0 buffer or `None` links) in a `const fn`, frees nothing
/// (it drops no value) and calls no user code (no trait method of the element type).
/// **Audited, not machine-proved**, in the `alloc` sources of the toolchains in
/// [`NON_ALLOCATING_CONSTRUCTORS_AUDITED_AT`]; measured with a counting allocator
/// (`fip-macros/tests/non_allocating_ctors.rs`) and agreed by `fip-prelint` (MIR).
/// Recognised, like [`HEAP_TYPES`], by the type's last path segment.
/// Per-entry reasons: `docs/decisions/2026-11-01-strict-core-table.md`.
///
/// Not listed on purpose: `HashMap`/`HashSet` `new`/`default` (`RandomState::new`
/// reads a lazily initialised thread-local, which targets without native TLS store in
/// a heap allocation, and `default` calls the hasher's `Default`, user code);
/// `with_capacity` and `from`/`from_iter` (argument-dependent); every constructor of
/// `Box`, `Rc`, `Arc`.
pub const NON_ALLOCATING_CONSTRUCTORS: &[(&str, &str)] = &[
    ("Vec", "new"),
    ("Vec", "default"),
    ("String", "new"),
    ("String", "default"),
    ("VecDeque", "new"),
    ("VecDeque", "default"),
    ("BTreeMap", "new"),
    ("BTreeMap", "default"),
    ("BTreeSet", "new"),
    ("BTreeSet", "default"),
    ("LinkedList", "new"),
    ("LinkedList", "default"),
    ("BinaryHeap", "new"),
    ("BinaryHeap", "default"),
];

/// rustc versions whose `alloc` sources were read for [`NON_ALLOCATING_CONSTRUCTORS`].
/// A build with any other version is not covered by the audit (`fip-macros` tests
/// fail on it).
pub const NON_ALLOCATING_CONSTRUCTORS_AUDITED_AT: &[&str] = &["1.97.1", "1.99.1"];

/// `true` if `ty::ctor(..)` (by the last segment of the type path) is an allocation
/// site: a [`HEAP_TYPES`] type, a [`HEAP_CONSTRUCTORS`] constructor, and not a
/// [`NON_ALLOCATING_CONSTRUCTORS`] pair.
#[must_use]
pub fn is_heap_constructor(ty: &str, ctor: &str) -> bool {
    HEAP_TYPES.contains(&ty)
        && HEAP_CONSTRUCTORS.contains(&ctor)
        && !is_non_allocating_constructor(ty, ctor)
}

/// `true` if `ty::ctor(..)` is a [`NON_ALLOCATING_CONSTRUCTORS`] pair.
#[must_use]
pub fn is_non_allocating_constructor(ty: &str, ctor: &str) -> bool {
    NON_ALLOCATING_CONSTRUCTORS
        .iter()
        .any(|&(t, c)| t == ty && c == ctor)
}

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

/// Macros that expand to compile-time values or plain control flow and call nothing
/// at run time beyond their arguments (which the checker scans as code).
/// `fip_testkit::summaries` treats them as allocation-free; every other macro not
/// defined by `macro_rules!` in the scanned sources is unknown (`⊤`).
pub const ALLOC_FREE_MACROS: &[&str] = &[
    "cfg",
    "column",
    "compile_error",
    "concat",
    "env",
    "file",
    "include_bytes",
    "include_str",
    "line",
    "matches",
    "module_path",
    "option_env",
    "stringify",
];

/// Macros that allocate only on the panic path. Panic paths are outside what
/// `#[fip]`, the strict mode and the crate-wide checker count (implicit panics such as
/// indexing or overflow are not seen either), so their arguments are scanned and the
/// panic machinery is not. Same list as the strict mode's macro allowlist.
pub const PANIC_MACROS: &[&str] = &[
    "assert",
    "assert_eq",
    "assert_ne",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_ne",
    "unreachable",
    "panic",
];

/// Traits whose bound makes a parameter a callable value for the checker (`F: Fn(..)`,
/// `impl FnMut(..)`, `&dyn FnOnce(..)`, `F: FipFn<..>`); calls to such a parameter
/// are symbolic terms of the caller's summary.
pub const FN_TRAITS: &[&str] = &["Fn", "FnMut", "FnOnce", "FipFn"];

/// Explicit drops: `core::mem::drop` (also reachable as the prelude `drop`). They
/// free and never allocate; the checker records them as frees with allocation count
/// 0. The `Drop` impl that runs is not inspected, exactly like an implicit drop.
pub const DROP_FUNCTIONS: &[&str] = &["mem::drop"];

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

/// `true` if `root::rest::name` names an entry of [`DROP_FUNCTIONS`] under the roots
/// `core` or `std`, or is the prelude `drop` (`root` and `rest` empty).
#[must_use]
pub fn is_drop_function(root: &str, rest: &[&str], name: &str) -> bool {
    if root.is_empty() {
        return rest.is_empty() && name == "drop";
    }
    if root != "core" && root != "std" {
        return false;
    }
    DROP_FUNCTIONS.iter().any(|entry| {
        let mut parts = entry.split("::");
        let mut ok = true;
        for seg in rest {
            ok &= parts.next() == Some(seg);
        }
        ok && parts.next() == Some(name) && parts.next().is_none()
    })
}

/// Tables of the MIR-level checker `fip-prelint` (`tools/fip-prelint`): entry points
/// it does not look into, and intrinsics, which have no MIR body. Paths are
/// defining paths as rustc prints them (`alloc::alloc::exchange_malloc`, not the
/// `std::` re-export); foreign symbols are matched by name.
pub mod mir {
    /// Allocation entry points: a call counts as one allocation. The `alloc::alloc`
    /// functions are what `Box::new` (`exchange_malloc`), `Vec`/`String`/`RawVec`
    /// (`Global::alloc_impl` → `alloc`/`alloc_zeroed`) reach on rustc 1.99.1; the
    /// `__rust_*` symbols are the global allocator shims behind them.
    pub const ALLOC_ENTRY_POINTS: &[&str] = &[
        "alloc::alloc::alloc",
        "alloc::alloc::alloc_zeroed",
        "alloc::alloc::exchange_malloc",
        "__rust_alloc",
        "__rust_alloc_zeroed",
    ];

    /// Reallocation: one allocation and one possible free.
    pub const REALLOC_ENTRY_POINTS: &[&str] = &["alloc::alloc::realloc", "__rust_realloc"];

    /// Deallocation entry points: a possible free.
    pub const DEALLOC_ENTRY_POINTS: &[&str] = &["alloc::alloc::dealloc", "__rust_dealloc"];

    /// Foreign symbols without allocation or free: `__rust_no_alloc_shim_is_unstable_v2`
    /// is an empty marker function that `Global::alloc_impl_runtime` calls before
    /// `__rust_alloc` on rustc 1.99.1, so that linking without a global allocator
    /// fails; the allocation itself is the `__rust_alloc*` call next to it.
    pub const ALLOC_FREE_SYMBOLS: &[&str] = &["__rust_no_alloc_shim_is_unstable_v2"];

    /// Path prefixes of the panic machinery: a call is a panic path and is not
    /// looked into (its allocations happen only while panicking).
    pub const PANIC_PREFIXES: &[&str] = &[
        "core::panicking::",
        "std::panicking::",
        "std::rt::begin_panic",
    ];

    /// Functions that run only when a safety precondition is already violated (the
    /// `assert_unsafe_precondition!` checks of `core`, compiled in under
    /// `debug_assertions`) or are unreachable by contract. They are skipped: the
    /// caller's `unsafe` contract excludes them.
    pub const UB_CHECK_MARKERS: &[&str] =
        &["::precondition_check", "core::hint::unreachable_unchecked"];

    /// Intrinsics without allocation, free, panic or call into user code, with the
    /// reason. An intrinsic not listed here (and not in [`PANIC_INTRINSICS`]) is
    /// unknown (`⊤`).
    pub const ALLOC_FREE_INTRINSICS: &[(&str, &str)] = &[
        ("size_of", "compile-time layout query"),
        ("align_of", "compile-time layout query"),
        ("min_align_of", "compile-time layout query"),
        ("pref_align_of", "compile-time layout query"),
        ("size_of_val", "layout from pointer metadata"),
        ("align_of_val", "layout from pointer metadata"),
        ("min_align_of_val", "layout from pointer metadata"),
        ("needs_drop", "compile-time type query"),
        ("type_id", "compile-time type query"),
        ("type_name", "compile-time type query (static string)"),
        ("variant_count", "compile-time type query"),
        ("ptr_metadata", "reads pointer metadata"),
        ("aggregate_raw_ptr", "builds a raw pointer from parts"),
        ("transmute", "reinterprets bits"),
        ("transmute_unchecked", "reinterprets bits"),
        ("copy_nonoverlapping", "memcpy of caller-provided memory"),
        ("copy", "memmove of caller-provided memory"),
        ("write_bytes", "memset of caller-provided memory"),
        ("volatile_load", "single memory access"),
        ("volatile_store", "single memory access"),
        ("unaligned_volatile_load", "single memory access"),
        ("unaligned_volatile_store", "single memory access"),
        ("volatile_copy_memory", "memmove of caller-provided memory"),
        (
            "volatile_copy_nonoverlapping_memory",
            "memcpy of caller-provided memory",
        ),
        ("volatile_set_memory", "memset of caller-provided memory"),
        ("read_via_copy", "single memory access"),
        ("write_via_move", "single memory access"),
        ("compare_bytes", "memcmp of caller-provided memory"),
        (
            "typed_swap_nonoverlapping",
            "swaps two caller-provided values in place (`mem::swap`)",
        ),
        ("raw_eq", "byte comparison"),
        ("offset", "pointer arithmetic"),
        ("arith_offset", "pointer arithmetic"),
        ("ptr_offset_from", "pointer arithmetic"),
        ("ptr_offset_from_unsigned", "pointer arithmetic"),
        ("ptr_mask", "pointer arithmetic"),
        ("ptr_guaranteed_cmp", "pointer comparison"),
        ("slice_get_unchecked", "unchecked element access"),
        ("add_with_overflow", "integer arithmetic"),
        ("sub_with_overflow", "integer arithmetic"),
        ("mul_with_overflow", "integer arithmetic"),
        ("wrapping_add", "integer arithmetic"),
        ("wrapping_sub", "integer arithmetic"),
        ("wrapping_mul", "integer arithmetic"),
        ("saturating_add", "integer arithmetic"),
        ("saturating_sub", "integer arithmetic"),
        (
            "unchecked_add",
            "integer arithmetic (UB on overflow, no panic)",
        ),
        (
            "unchecked_sub",
            "integer arithmetic (UB on overflow, no panic)",
        ),
        (
            "unchecked_mul",
            "integer arithmetic (UB on overflow, no panic)",
        ),
        ("unchecked_div", "integer arithmetic (UB on zero, no panic)"),
        ("unchecked_rem", "integer arithmetic (UB on zero, no panic)"),
        ("unchecked_shl", "integer arithmetic"),
        ("unchecked_shr", "integer arithmetic"),
        ("unchecked_funnel_shl", "integer arithmetic"),
        ("unchecked_funnel_shr", "integer arithmetic"),
        ("exact_div", "integer arithmetic (UB if inexact, no panic)"),
        ("disjoint_bitor", "integer arithmetic"),
        ("carrying_mul_add", "integer arithmetic"),
        ("rotate_left", "integer arithmetic"),
        ("rotate_right", "integer arithmetic"),
        ("ctpop", "bit count"),
        ("ctlz", "bit count"),
        ("ctlz_nonzero", "bit count"),
        ("cttz", "bit count"),
        ("cttz_nonzero", "bit count"),
        ("bswap", "byte swap"),
        ("bitreverse", "bit reversal"),
        ("three_way_compare", "integer comparison"),
        ("discriminant_value", "reads an enum tag"),
        ("assume", "optimizer hint"),
        ("likely", "optimizer hint"),
        ("unlikely", "optimizer hint"),
        ("cold_path", "optimizer hint"),
        ("select_unpredictable", "branch-free select of two values"),
        ("black_box", "identity with an optimizer barrier"),
        ("is_val_statically_known", "compile-time query"),
        ("ub_checks", "reads the `debug_assertions` setting"),
        ("overflow_checks", "reads the `overflow-checks` setting"),
        ("contract_checks", "reads the contract-checks setting"),
        ("forget", "no-op ownership transfer"),
        ("unreachable", "unreachable by contract (UB if reached)"),
        ("float_to_int_unchecked", "numeric conversion"),
        ("fadd_fast", "float arithmetic"),
        ("fsub_fast", "float arithmetic"),
        ("fmul_fast", "float arithmetic"),
        ("fdiv_fast", "float arithmetic"),
        ("frem_fast", "float arithmetic"),
        ("fadd_algebraic", "float arithmetic"),
        ("fsub_algebraic", "float arithmetic"),
        ("fmul_algebraic", "float arithmetic"),
        ("fdiv_algebraic", "float arithmetic"),
        ("frem_algebraic", "float arithmetic"),
        ("atomic_load", "single atomic memory access"),
        ("atomic_store", "single atomic memory access"),
        ("atomic_xchg", "single atomic memory access"),
        ("atomic_cxchg", "single atomic memory access"),
        ("atomic_cxchgweak", "single atomic memory access"),
        ("atomic_xadd", "single atomic memory access"),
        ("atomic_xsub", "single atomic memory access"),
        ("atomic_and", "single atomic memory access"),
        ("atomic_or", "single atomic memory access"),
        ("atomic_xor", "single atomic memory access"),
        ("atomic_nand", "single atomic memory access"),
        ("atomic_max", "single atomic memory access"),
        ("atomic_min", "single atomic memory access"),
        ("atomic_umax", "single atomic memory access"),
        ("atomic_umin", "single atomic memory access"),
        ("atomic_fence", "memory fence"),
        ("atomic_singlethreadfence", "compiler fence"),
        ("prefetch_read_data", "cache hint"),
        ("prefetch_write_data", "cache hint"),
        ("prefetch_read_instruction", "cache hint"),
        ("prefetch_write_instruction", "cache hint"),
    ];

    /// Intrinsics that abort or panic: a panic path.
    pub const PANIC_INTRINSICS: &[&str] = &[
        "abort",
        "assert_inhabited",
        "assert_zero_valid",
        "assert_mem_uninitialized_valid",
    ];

    fn path_in(path: &str, table: &[&str]) -> bool {
        table.contains(&path)
    }

    /// `true` for an [`ALLOC_ENTRY_POINTS`] path or symbol.
    #[must_use]
    pub fn is_alloc_entry(path: &str) -> bool {
        path_in(path, ALLOC_ENTRY_POINTS)
    }

    /// `true` for a [`REALLOC_ENTRY_POINTS`] path or symbol.
    #[must_use]
    pub fn is_realloc_entry(path: &str) -> bool {
        path_in(path, REALLOC_ENTRY_POINTS)
    }

    /// `true` for a [`DEALLOC_ENTRY_POINTS`] path or symbol.
    #[must_use]
    pub fn is_dealloc_entry(path: &str) -> bool {
        path_in(path, DEALLOC_ENTRY_POINTS)
    }

    /// `true` for an [`ALLOC_FREE_SYMBOLS`] foreign symbol.
    #[must_use]
    pub fn is_alloc_free_symbol(name: &str) -> bool {
        path_in(name, ALLOC_FREE_SYMBOLS)
    }

    /// `true` if `path` starts with a [`PANIC_PREFIXES`] entry.
    #[must_use]
    pub fn is_panic_entry(path: &str) -> bool {
        PANIC_PREFIXES.iter().any(|p| path.starts_with(p))
    }

    /// `true` if `path` contains a [`UB_CHECK_MARKERS`] entry.
    #[must_use]
    pub fn is_ub_check(path: &str) -> bool {
        UB_CHECK_MARKERS.iter().any(|m| path.contains(m))
    }

    /// `true` for an intrinsic in [`ALLOC_FREE_INTRINSICS`].
    #[must_use]
    pub fn is_alloc_free_intrinsic(name: &str) -> bool {
        ALLOC_FREE_INTRINSICS.iter().any(|(n, _)| *n == name)
    }

    /// `true` for an intrinsic in [`PANIC_INTRINSICS`].
    #[must_use]
    pub fn is_panic_intrinsic(name: &str) -> bool {
        PANIC_INTRINSICS.contains(&name)
    }
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

    #[test]
    fn mir_tables() {
        assert!(mir::is_alloc_entry("__rust_alloc"));
        assert!(mir::is_alloc_entry("alloc::alloc::exchange_malloc"));
        assert!(!mir::is_alloc_entry("alloc::alloc::dealloc"));
        assert!(mir::is_realloc_entry("__rust_realloc"));
        assert!(mir::is_dealloc_entry("__rust_dealloc"));
        assert!(mir::is_alloc_free_symbol(
            "__rust_no_alloc_shim_is_unstable_v2"
        ));
        assert!(mir::is_panic_entry("core::panicking::panic_fmt"));
        assert!(!mir::is_panic_entry("core::panic::Location::caller"));
        assert!(mir::is_ub_check(
            "core::slice::index::get_unchecked::precondition_check"
        ));
        assert!(mir::is_alloc_free_intrinsic("typed_swap_nonoverlapping"));
        assert!(!mir::is_alloc_free_intrinsic("catch_unwind"));
        assert!(mir::is_panic_intrinsic("abort"));
        assert!(
            mir::ALLOC_FREE_INTRINSICS
                .iter()
                .all(|(n, why)| !n.is_empty() && !why.is_empty())
        );
    }

    #[test]
    fn non_allocating_constructors() {
        for &(t, c) in NON_ALLOCATING_CONSTRUCTORS {
            assert!(HEAP_TYPES.contains(&t) && HEAP_CONSTRUCTORS.contains(&c));
            assert!(!is_heap_constructor(t, c));
            assert!(c == "new" || c == "default", "{t}::{c} takes arguments");
            assert!(!matches!(t, "Box" | "Rc" | "Arc" | "HashMap" | "HashSet"));
        }
        assert!(is_non_allocating_constructor("Vec", "new"));
        assert!(is_heap_constructor("Vec", "with_capacity"));
        assert!(is_heap_constructor("Box", "new"));
        assert!(is_heap_constructor("Box", "default"));
        assert!(is_heap_constructor("HashMap", "new"));
        assert!(!is_heap_constructor("Foo", "new"));
    }

    #[test]
    fn drop_lookup() {
        assert!(is_drop_function("core", &["mem"], "drop"));
        assert!(is_drop_function("std", &["mem"], "drop"));
        assert!(is_drop_function("", &[], "drop"));
        assert!(!is_drop_function("", &["m"], "drop"));
        assert!(!is_drop_function("core", &["mem"], "forget"));
        assert!(!is_drop_function("alloc", &["mem"], "drop"));
    }
}
