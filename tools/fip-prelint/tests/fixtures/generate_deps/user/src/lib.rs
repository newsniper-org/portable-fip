// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Std-summary generation of a crate with a proc-macro dependency: listing the
//! functions of every dependency must skip the proc-macro crate (it was an ICE in
//! `rustc_metadata`).

use fip_macros::{fip, fip_fn};
use fip_strict::FipFn;

/// A root with a default `fip_fn!`.
#[fip]
pub fn ok() -> u32 {
    let f = fip_fn!(|x: u32| x);
    f.call((1,))
}
