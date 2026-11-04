// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The attribute only as text: in comments and in a raw string. Not exported: the
//! driver must pass it through to the real rustc (the text test took it for exported
//! and compiled it with the driver's flags, which the `compile_error!` below shows).
// #![cfg_attr(fip_prelint, fip::export)]
/* #![fip::export] */

/// The attribute's text in a raw string.
pub const TEXT: &str = r#"#![cfg_attr(fip_prelint, fip::export)]"#;

#[cfg(fip_prelint)]
compile_error!("fip-prelint fixture: dep_text_only was compiled with the driver's flags although it declares no `fip::export`");

/// Allocation-free; non-generic, not `#[inline]`.
pub fn twice(x: u32) -> u32 {
    x.wrapping_mul(2)
}
