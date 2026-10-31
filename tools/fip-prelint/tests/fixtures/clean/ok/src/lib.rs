// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Every root passes; the marks come from `fip-macros` (`#[fip]`, `#[fip(N)]`,
//! `#[fbip]`, `strict = true` with `param(..)`).

use fip_macros::{fbip, fip};
use fip_strict::FipFn;

/// In place.
#[fip]
pub fn double(x: &mut u32) {
    *x = x.wrapping_mul(2);
}

/// One allocation under `fip(1)`.
#[fip(1)]
pub fn boxed(x: u32) -> Box<u32> {
    Box::new(x)
}

/// Recursion is allowed under `fbip`.
#[fbip]
pub fn count(n: u32) -> u32 {
    if n == 0 { 0 } else { count(n - 1).wrapping_add(1) }
}

/// A callable parameter with a declared bound.
#[fip(strict = true, param(g = 0))]
pub fn apply<F: FipFn<(u8,), Output = u8>>(g: F) -> u8 {
    g.call((1,))
}
