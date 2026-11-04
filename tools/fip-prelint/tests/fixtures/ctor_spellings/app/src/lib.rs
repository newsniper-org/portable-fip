// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Constructor spellings the token rule cannot resolve (`fip_lint_rules::callee`):
//! the type is inferred or named through an alias. `#[fip]` accepts each (non-strict
//! mode leaves them to the driver); the driver sees the resolved callee on MIR.

use fip_macros::fip;

type Bytes = Vec<u8>;

/// `Default::default()` building a `Box`: allocates.
#[fip]
pub fn inferred_box() -> Box<u8> {
    Default::default()
}

/// `<_ as Default>::default()` building a `Box`: allocates.
#[fip]
pub fn inferred_qualified_box() -> Box<u8> {
    <_ as Default>::default()
}

/// `From::from` building a `Box`: allocates.
#[fip]
pub fn inferred_from_box(x: u8) -> Box<u8> {
    From::from(x)
}

/// `FromIterator::from_iter` building a `Vec`: allocates.
#[fip]
pub fn inferred_from_iter(x: u8) -> Vec<u8> {
    FromIterator::from_iter([x])
}

/// A type alias of `Vec`: allocates.
#[fip]
pub fn alias_with_capacity() -> Bytes {
    Bytes::with_capacity(4)
}

/// `Default::default()` building a `Vec`: does not allocate (an empty `Vec`).
#[fip]
pub fn inferred_vec() -> Vec<u8> {
    Default::default()
}

/// The audited spellings of a non-allocating constructor: pass.
#[fip]
pub fn spelled_vec() -> (Vec<u8>, Vec<u8>, Vec<u8>, String) {
    (
        Vec::<u8>::new(),
        <Vec<u8>>::new(),
        <Vec<u8> as Default>::default(),
        <String as Default>::default(),
    )
}

/// The same under strict mode: certificates are not needed for them.
#[fip(strict = true)]
pub fn spelled_vec_strict() -> (Vec<u8>, Vec<u8>) {
    (alloc_free_vec(), <Vec<u8>>::default())
}

#[fip(strict = true)]
fn alloc_free_vec() -> Vec<u8> {
    alloc::vec::Vec::<u8>::new()
}

extern crate alloc;
