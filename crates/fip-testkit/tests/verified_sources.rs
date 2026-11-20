// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gates on the verified callers in `verify/` (the `.rs` files `just verify` runs
//! through Verus; see `fip_testkit::surface`; the fork audit, 2026-11-09): no
//! `trusted_call` in any spelling, no implementation of an allocator trait, no
//! `verifier::..` attribute outside the allowlist. The crates' own sources have the
//! same gates in their `verified_surface` tests. `FIP_SURFACE_SRC` overrides the
//! scanned directory (`verify-negative` runs it on mutated copies).

use fip_testkit::surface::{
    allocator_impls_in, internal_idents_in, trusted_calls_in, unlisted_verifier_attributes,
};
use std::path::PathBuf;

fn src() -> PathBuf {
    std::env::var_os("FIP_SURFACE_SRC").map_or_else(
        || PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../verify"),
        PathBuf::from,
    )
}

#[test]
fn verify_sources_are_found() {
    let dir = src();
    let n = std::fs::read_dir(&dir)
        .expect("read verify/")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|x| x == "rs"))
        .count();
    assert!(n > 0, "no `.rs` file in {}", dir.display());
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

#[test]
fn no_internal_identifier() {
    let found = internal_idents_in(&src());
    assert!(
        found.is_empty(),
        "`internal` (`verus::internal(..)` attributes are the verifier's input, not checked):\n{found:#?}"
    );
}
