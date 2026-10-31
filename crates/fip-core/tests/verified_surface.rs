// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Gates on the verified surface of this crate (see `fip_testkit::surface`):
//!
//! 1. every `fn` carries a `verus_spec` attribute, so none is silently unverified;
//! 2. no function-level spec has `decreases`, so Verus has accepted no recursion
//!    among this crate's functions and the call graph is acyclic.
//!
//! `FIP_SURFACE_SRC` overrides the scanned directory; the `verify-negative` recipe
//! uses it to show both gates fail on mutated copies.

use fip_testkit::surface::{scan_dir, unspecified, with_fn_decreases};
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
