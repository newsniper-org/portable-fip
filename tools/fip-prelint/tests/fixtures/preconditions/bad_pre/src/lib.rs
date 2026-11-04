// SPDX-License-Identifier: MIT OR Apache-2.0
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

/// An access path behind a mutable reference.
#[cfg_attr(fip_prelint, fip::requires(i < w.0))]
pub fn path_mut(w: &mut (usize, usize), i: usize) -> usize {
    i ^ w.1
}

/// An access path through a type with interior mutability.
#[cfg_attr(fip_prelint, fip::requires(i < w.0))]
pub fn path_cell(w: &(usize, core::cell::Cell<usize>), i: usize) -> usize {
    i ^ w.0
}

/// No such field.
#[cfg_attr(fip_prelint, fip::requires(i < w.2))]
pub fn path_no_field(w: &(usize, usize), i: usize) -> usize {
    i ^ w.0
}

/// An index through a further reference.
#[cfg_attr(fip_prelint, fip::requires(i < w.0[0]))]
pub fn path_through_ref(w: &(&[usize], usize), i: usize) -> usize {
    i ^ w.1
}
