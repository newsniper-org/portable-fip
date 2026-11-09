// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gates on the verified surface of this crate (see `fip_testkit::surface`):
//!
//! 1. every `fn` carries a `verus_spec` attribute, so none is silently unverified;
//! 2. no function-level spec has `decreases`, so Verus has accepted no recursion
//!    among this crate's functions and the call graph is acyclic;
//! 3. no `verifier::..` attribute outside `fip_testkit::surface::VERIFIER_ALLOWED`
//!    (`exec_allows_no_decreases_clause` admits recursion without `decreases`);
//! 4. no `trusted_call` in any spelling (the fork's trusted-call block; the fork
//!    audit, 2026-11-09);
//! 5. no implementation of an allocator trait (`fip_testkit::surface::ALLOCATOR_TRAITS`),
//!    a trust point of Verus's `allocates` accounting (the fork audit, 2026-11-09).
//!
//! `FIP_SURFACE_SRC` overrides the scanned directory; the `verify-negative` recipe
//! uses it to show the gates fail on mutated copies.

use fip_testkit::surface::{
    allocator_impls_in, scan_dir, trusted_calls_in, unlisted_verifier_attributes, unspecified,
    with_fn_decreases,
};
use std::path::PathBuf;

fn src() -> PathBuf {
    std::env::var_os("FIP_SURFACE_SRC").map_or_else(
        || PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src"),
        PathBuf::from,
    )
}

#[test]
fn every_function_is_specified() {
    let items = scan_dir(&src());
    assert!(
        !items.is_empty(),
        "no functions found in {}",
        src().display()
    );
    let missing = unspecified(&items);
    assert!(
        missing.is_empty(),
        "functions without verus_spec:\n{missing:#?}"
    );
}

#[test]
fn no_function_may_recurse() {
    let rec = with_fn_decreases(&scan_dir(&src()));
    assert!(
        rec.is_empty(),
        "function-level `decreases` (recursion allowed):\n{rec:#?}"
    );
}

#[test]
fn no_unlisted_verifier_attribute() {
    let attrs = unlisted_verifier_attributes(&src());
    assert!(
        attrs.is_empty(),
        "`verifier::..` attributes outside the allowlist:\n{attrs:#?}"
    );
}

#[test]
fn no_trusted_call() {
    let found = trusted_calls_in(&src());
    assert!(
        found.is_empty(),
        "`trusted_call` (calls trusted, not verified):\n{found:#?}"
    );
}

#[test]
fn no_allocator_impl() {
    let found = allocator_impls_in(&src());
    assert!(
        found.is_empty(),
        "allocator trait implementations (a trust point of `allocates`):\n{found:#?}"
    );
}
