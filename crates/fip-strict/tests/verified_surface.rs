// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gates on the verified sources of this crate (see `fip_testkit::surface`; the fork
//! audit, 2026-11-09):
//!
//! 1. no `verifier::..` attribute outside `fip_testkit::surface::VERIFIER_ALLOWED`;
//! 2. no `trusted_call` in any spelling (the fork's trusted-call block);
//! 3. no implementation of an allocator trait (`fip_testkit::surface::ALLOCATOR_TRAITS`),
//!    a trust point of Verus's `allocates` accounting.
//!
//! The function-level gates of `fip-core` (a `verus_spec` on every `fn`, no
//! `decreases`) do not apply: the `call` of a `FipFn` impl has its specification in the
//! trait, and the specifications of this crate live in `verus! { .. }`.
//! `FIP_SURFACE_SRC` overrides the scanned directory; the `verify-negative` recipe
//! uses it to show the gates fail on mutated copies.

use fip_testkit::surface::{
    allocator_impls_in, internal_idents_in, trusted_calls_in, unlisted_verifier_attributes,
};
use std::path::PathBuf;

fn src() -> PathBuf {
    std::env::var_os("FIP_SURFACE_SRC").map_or_else(
        || PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src"),
        PathBuf::from,
    )
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
