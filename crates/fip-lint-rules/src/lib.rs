// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-lint-rules — the one rule set shared by `fip-macros` and `fip-testkit`
//!
//! What counts as an allocation site, which Verus macros are ghost code, and which
//! `core` functions are accepted without a certificate. `#[fip]` (token lint) and
//! `fip_testkit::callgraph` (crate-wide checker) both read these tables, so the two
//! tools cannot disagree about the rules.
//!
//! `#![no_std]`, no dependencies, data only, except the `requires` grammar
//! ([`requires`], which uses `alloc`).

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

pub mod callee;
pub mod requires;

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

    /// Foreign C allocation functions: `(symbol, allocates, frees)`. Matched only on
    /// foreign items (functions declared in an `extern` block), never on a Rust
    /// function of the same name. A call is an opaque allocation or free source: one
    /// allocation, a possible free, or both (reallocation).
    pub const FOREIGN_ALLOC_SYMBOLS: &[(&str, bool, bool)] = &[
        ("malloc", true, false),
        ("calloc", true, false),
        ("aligned_alloc", true, false),
        ("posix_memalign", true, false),
        ("memalign", true, false),
        ("free", false, true),
        ("realloc", true, true),
        ("reallocarray", true, true),
    ];

    /// Allocator traits, by defining path of the trait in `core`, and their methods:
    /// `(trait, method, allocates, frees)`. Every implementation of such a method (and
    /// the trait's default body) is an opaque allocation or free source: a call counts
    /// at the call site and its body is not analysed (allocator internals are outside
    /// FIP). Methods not listed (`Allocator::by_ref`) are analysed as usual.
    pub const ALLOCATOR_TRAIT_METHODS: &[(&str, &str, bool, bool)] = &[
        ("core::alloc::global::GlobalAlloc", "alloc", true, false),
        (
            "core::alloc::global::GlobalAlloc",
            "alloc_zeroed",
            true,
            false,
        ),
        ("core::alloc::global::GlobalAlloc", "dealloc", false, true),
        ("core::alloc::global::GlobalAlloc", "realloc", true, true),
        ("core::alloc::Allocator", "allocate", true, false),
        ("core::alloc::Allocator", "allocate_zeroed", true, false),
        ("core::alloc::Allocator", "deallocate", false, true),
        ("core::alloc::Allocator", "grow", true, true),
        ("core::alloc::Allocator", "grow_zeroed", true, true),
        ("core::alloc::Allocator", "shrink", true, true),
    ];

    /// `(allocates, frees)` of a [`FOREIGN_ALLOC_SYMBOLS`] entry.
    #[must_use]
    pub fn foreign_alloc_symbol(name: &str) -> Option<(bool, bool)> {
        FOREIGN_ALLOC_SYMBOLS
            .iter()
            .find(|(n, _, _)| *n == name)
            .map(|&(_, a, f)| (a, f))
    }

    /// `(allocates, frees)` of an [`ALLOCATOR_TRAIT_METHODS`] entry.
    #[must_use]
    pub fn allocator_trait_method(trait_path: &str, method: &str) -> Option<(bool, bool)> {
        ALLOCATOR_TRAIT_METHODS
            .iter()
            .find(|(t, m, _, _)| *t == trait_path && *m == method)
            .map(|&(_, _, a, f)| (a, f))
    }

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

    /// Reason of the `f32`/`f64` math intrinsics in [`ALLOC_FREE_INTRINSICS`] (top
    /// plan T7d). LLVM lowers them to instructions or, depending on the target and
    /// its features (`sin`, `pow`, `exp`, `log` always on `x86_64`; `floor`, `fma`
    /// without SSE4.1/FMA), to a call of the C math library's function of the same
    /// name. That call is not analysed: its allocation freedom is the C library's
    /// specification (C standard 7.12; no math function allocates), a trusted claim.
    pub const FLOAT_MATH: &str = "float math: instructions or a call of the C math library's function of the same name (allocation-free by the C standard 7.12; a claim about the linked C library, not analysed)";

    /// Reason of the `powi` intrinsics in [`ALLOC_FREE_INTRINSICS`]: lowered inline or
    /// to `compiler_builtins`' `__powisf2`/`__powidf2` (a loop of multiplications).
    pub const FLOAT_POWI: &str = "float power by an integer: inline multiplications or `compiler_builtins`' `__powisf2`/`__powidf2`";

    /// Reason of the integer/bitwise SIMD intrinsics in [`ALLOC_FREE_INTRINSICS`]
    /// (reached by `hashbrown`'s SSE2 group scan, top plan T7h): lane-wise operations
    /// on values in registers; no memory access, no call.
    pub const SIMD_LANES: &str =
        "SIMD lane-wise operation on values (registers; no memory access, no call)";

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
        ("fabs", "float sign-bit operation"),
        ("copysignf32", "float sign-bit operation"),
        ("copysignf64", "float sign-bit operation"),
        ("sqrtf32", FLOAT_MATH),
        ("sqrtf64", FLOAT_MATH),
        ("powif32", FLOAT_POWI),
        ("powif64", FLOAT_POWI),
        ("sinf32", FLOAT_MATH),
        ("sinf64", FLOAT_MATH),
        ("cosf32", FLOAT_MATH),
        ("cosf64", FLOAT_MATH),
        ("powf32", FLOAT_MATH),
        ("powf64", FLOAT_MATH),
        ("expf32", FLOAT_MATH),
        ("expf64", FLOAT_MATH),
        ("exp2f32", FLOAT_MATH),
        ("exp2f64", FLOAT_MATH),
        ("logf32", FLOAT_MATH),
        ("logf64", FLOAT_MATH),
        ("log10f32", FLOAT_MATH),
        ("log10f64", FLOAT_MATH),
        ("log2f32", FLOAT_MATH),
        ("log2f64", FLOAT_MATH),
        ("fmaf32", FLOAT_MATH),
        ("fmaf64", FLOAT_MATH),
        ("fmuladdf32", FLOAT_MATH),
        ("fmuladdf64", FLOAT_MATH),
        ("floorf32", FLOAT_MATH),
        ("floorf64", FLOAT_MATH),
        ("ceilf32", FLOAT_MATH),
        ("ceilf64", FLOAT_MATH),
        ("truncf32", FLOAT_MATH),
        ("truncf64", FLOAT_MATH),
        ("roundf32", FLOAT_MATH),
        ("roundf64", FLOAT_MATH),
        ("round_ties_even_f32", FLOAT_MATH),
        ("round_ties_even_f64", FLOAT_MATH),
        ("minimumf32", FLOAT_MATH),
        ("minimumf64", FLOAT_MATH),
        ("maximumf32", FLOAT_MATH),
        ("maximumf64", FLOAT_MATH),
        ("minimum_number_nsz_f32", FLOAT_MATH),
        ("minimum_number_nsz_f64", FLOAT_MATH),
        ("maximum_number_nsz_f32", FLOAT_MATH),
        ("maximum_number_nsz_f64", FLOAT_MATH),
        ("simd_add", SIMD_LANES),
        ("simd_sub", SIMD_LANES),
        ("simd_mul", SIMD_LANES),
        ("simd_neg", SIMD_LANES),
        ("simd_and", SIMD_LANES),
        ("simd_or", SIMD_LANES),
        ("simd_xor", SIMD_LANES),
        ("simd_shl", SIMD_LANES),
        ("simd_shr", SIMD_LANES),
        ("simd_saturating_add", SIMD_LANES),
        ("simd_saturating_sub", SIMD_LANES),
        ("simd_eq", SIMD_LANES),
        ("simd_ne", SIMD_LANES),
        ("simd_lt", SIMD_LANES),
        ("simd_le", SIMD_LANES),
        ("simd_gt", SIMD_LANES),
        ("simd_ge", SIMD_LANES),
        ("simd_ctpop", SIMD_LANES),
        ("simd_ctlz", SIMD_LANES),
        ("simd_cttz", SIMD_LANES),
        ("simd_bswap", SIMD_LANES),
        ("simd_bitreverse", SIMD_LANES),
        ("simd_bitmask", SIMD_LANES),
        ("simd_select", SIMD_LANES),
        ("simd_select_bitmask", SIMD_LANES),
        ("simd_shuffle", SIMD_LANES),
        ("simd_splat", SIMD_LANES),
        ("simd_extract", SIMD_LANES),
        ("simd_insert", SIMD_LANES),
        ("simd_cast", SIMD_LANES),
        ("simd_as", SIMD_LANES),
        ("simd_reduce_and", SIMD_LANES),
        ("simd_reduce_or", SIMD_LANES),
        ("simd_reduce_xor", SIMD_LANES),
        ("simd_reduce_all", SIMD_LANES),
        ("simd_reduce_any", SIMD_LANES),
        ("simd_reduce_max", SIMD_LANES),
        ("simd_reduce_min", SIMD_LANES),
        ("simd_reduce_add_unordered", SIMD_LANES),
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

    /// Results of intrinsics, which have no MIR, as return summaries for the value
    /// analysis of `fip-prelint` (limits plan L2; functions with MIR are summarised
    /// from their MIR instead). `(name, k)`: for an integer type argument `T` of bit
    /// width `w`, the result lies in `0..=w - k`. Sources (`core` documentation of
    /// the stable wrappers, which call these intrinsics on rustc 1.99.1):
    /// `count_ones` ("the number of ones in the binary representation"),
    /// `leading_zeros`/`trailing_zeros` (the number of leading/trailing zeros, `w` for
    /// zero), and `NonZero::leading_zeros`/`trailing_zeros` (`ctlz_nonzero`/
    /// `cttz_nonzero`: undefined behaviour for zero, so at most `w - 1`). Each entry has
    /// a differential test against the real function on boundary inputs.
    pub const INTRINSIC_RESULT_BOUNDS: &[(&str, u32)] = &[
        ("ctpop", 0),
        ("ctlz", 0),
        ("cttz", 0),
        ("ctlz_nonzero", 1),
        ("cttz_nonzero", 1),
    ];

    /// The largest result of the intrinsic `name` for an integer type of bit width
    /// `width` ([`INTRINSIC_RESULT_BOUNDS`]); its smallest result is 0.
    #[must_use]
    pub fn intrinsic_result_bound(name: &str, width: u32) -> Option<u32> {
        INTRINSIC_RESULT_BOUNDS
            .iter()
            .find(|(n, _)| *n == name)
            .and_then(|(_, k)| width.checked_sub(*k))
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
    fn requires_grammar() {
        use requires::{Rel, Side, Term, display_all, from_verus, not_in, parse};
        let cs = parse("i < j < xs.len(), 0 <= i, n >= k + 1, 3usize == m - 2").unwrap();
        assert_eq!(
            display_all(&cs),
            "i < j, j < xs.len(), 0 <= i, k + 1 <= n, 3 == m - 2"
        );
        assert_eq!(cs[0].rel, Rel::Lt);
        assert_eq!(
            cs[3].a,
            Side {
                term: Term::Param("k".into()),
                offset: 1
            }
        );
        // Outside the grammar: errors, never dropped.
        for bad in [
            "",
            "i",
            "i != j",
            "i < j * 2",
            "f(i) < j",
            "i < j + k",
            "xs[i] < 1",
            "w.f() < 1",
            "w. < 1",
            "i < j,, k < l",
            "i < 3q",
        ] {
            assert!(parse(bad).is_err(), "{bad}");
        }
        // Access paths (top plan T13.2).
        let cs = parse("xs[0] < ys.len(), i < w.n <= w.b.len(), w.0 + 1 <= w.b[2].k").unwrap();
        assert_eq!(
            display_all(&cs),
            "xs[0] < ys.len(), i < w.n, w.n <= w.b.len(), w.0 + 1 <= w.b[2].k"
        );
        assert_eq!(
            cs[0].a.term,
            Term::Path("xs".into(), alloc::vec![requires::Step::Index(0)])
        );
        assert_eq!(
            cs[2].b.term,
            Term::PathLen("w".into(), alloc::vec![requires::Step::Field("b".into())])
        );
        // The Verus subset: `old(xs)@.len()`, chains; the rest is left out.
        let spec = "r => requires i < j < old(xs)@.len(), forall|k: int| 0 <= k < 3 ==> #[trigger] f(k), n != 0, ensures r == 1";
        let v = from_verus(spec);
        assert_eq!(display_all(&v), "i < j, j < xs.len()");
        let fip = parse("i < j, j < xs.len()").unwrap();
        assert_eq!(not_in(&fip, &v).len(), 0);
        let drift = parse("i <= j").unwrap();
        assert_eq!(not_in(&drift, &v).len(), 1);
        assert_eq!(from_verus("ensures r == 1").len(), 0);
    }

    /// Differential test of `mir::INTRINSIC_RESULT_BOUNDS`: the real stable wrappers of
    /// each intrinsic, on boundary inputs of every unsigned and signed width, stay
    /// within the table's bound (and the bound is reached, so it is not loose).
    #[test]
    fn intrinsic_result_bounds() {
        use core::num::NonZero;
        let bound = |name: &str, w: u32| mir::intrinsic_result_bound(name, w).unwrap();
        macro_rules! check {
            ($($t:ty),*) => {$({
                let w = <$t>::BITS;
                let inputs: [$t; 7] = [0, 1, !0, <$t>::MAX, <$t>::MIN, <$t>::MAX >> 1, 1 << (w - 1)];
                let mut seen = [0u32; 5];
                for x in inputs {
                    let r = [x.count_ones(), x.leading_zeros(), x.trailing_zeros()];
                    for (k, name) in ["ctpop", "ctlz", "cttz"].into_iter().enumerate() {
                        assert!(r[k] <= bound(name, w), "{name}({x}) for {}", stringify!($t));
                        seen[k] = seen[k].max(r[k]);
                    }
                    if let Some(n) = NonZero::new(x) {
                        let r = [n.leading_zeros(), n.trailing_zeros()];
                        for (k, name) in ["ctlz_nonzero", "cttz_nonzero"].into_iter().enumerate() {
                            assert!(r[k] <= bound(name, w), "{name}({x}) for {}", stringify!($t));
                            seen[3 + k] = seen[3 + k].max(r[k]);
                        }
                    }
                }
                for (k, name) in ["ctpop", "ctlz", "cttz", "ctlz_nonzero", "cttz_nonzero"]
                    .into_iter()
                    .enumerate()
                {
                    assert_eq!(seen[k], bound(name, w), "{name} bound reached for {}", stringify!($t));
                }
            })*};
        }
        check!(
            u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
        );
        assert_eq!(mir::intrinsic_result_bound("ctpop", 32), Some(32));
        assert_eq!(mir::intrinsic_result_bound("add_with_overflow", 32), None);
    }

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
        assert_eq!(mir::foreign_alloc_symbol("malloc"), Some((true, false)));
        assert_eq!(mir::foreign_alloc_symbol("free"), Some((false, true)));
        assert_eq!(mir::foreign_alloc_symbol("realloc"), Some((true, true)));
        assert_eq!(mir::foreign_alloc_symbol("memcpy"), None);
        assert_eq!(
            mir::allocator_trait_method("core::alloc::global::GlobalAlloc", "dealloc"),
            Some((false, true))
        );
        assert_eq!(
            mir::allocator_trait_method("core::alloc::Allocator", "grow"),
            Some((true, true))
        );
        assert_eq!(
            mir::allocator_trait_method("core::alloc::Allocator", "by_ref"),
            None
        );
        assert!(mir::FOREIGN_ALLOC_SYMBOLS.iter().all(|(_, a, f)| *a || *f));
        assert!(
            mir::ALLOCATOR_TRAIT_METHODS
                .iter()
                .all(|(_, _, a, f)| *a || *f)
        );
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
