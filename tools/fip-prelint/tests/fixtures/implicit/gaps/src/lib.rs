// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Functions the token-level `#[fip]` of `fip-macros` accepts
//! (`crates/fip-macros/tests/strict_gaps.rs`); `fip-macros` emits `fip::mark`.

use fip_macros::fip;

/// Implicit `Drop` of the `Box` argument: a free.
#[fip]
pub fn consume(b: Box<u8>) -> u8 {
    *b
}

/// Borrows the box: passes.
#[fip]
pub fn peek(b: &mut Box<u8>) -> u8 {
    **b
}
