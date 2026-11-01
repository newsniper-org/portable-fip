// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Malformed preconditions are errors, never dropped.

/// `!=` is outside the grammar.
#[cfg_attr(fip_prelint, fip::requires(i != j))]
pub fn not_equal(i: usize, j: usize) -> usize {
    i ^ j
}

/// A product is outside the grammar.
#[cfg_attr(fip_prelint, fip::requires(i < j * 2))]
pub fn product(i: usize, j: usize) -> usize {
    i ^ j
}

/// `k` is not a parameter.
#[cfg_attr(fip_prelint, fip::requires(i < k))]
pub fn unknown_name(i: usize) -> usize {
    i
}

/// `xs.len()` of an integer.
#[cfg_attr(fip_prelint, fip::requires(i < xs.len()))]
pub fn not_a_slice(i: usize, xs: usize) -> usize {
    i ^ xs
}

/// Never satisfiable.
#[cfg_attr(fip_prelint, fip::requires(i < j, j < i))]
pub fn contradiction(i: usize, j: usize) -> usize {
    i ^ j
}

/// On a struct.
#[cfg_attr(fip_prelint, fip::requires(0 < 1))]
pub struct NotAFunction;
