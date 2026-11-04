// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A root calling a dependency that mentions `fip::export` only in comments and a
//! string: unresolved (`⊤`), and the dependency is compiled by the real rustc.

/// Through `dep_text_only` (not exported): `⊤`, reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn twice_text(x: u32) -> u32 {
    dep_text_only::twice(x)
}
