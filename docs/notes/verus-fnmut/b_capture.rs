// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)
// Probe for docs/notes/verus-fnmut-monadic-workaround.md; run: verus b_capture.rs
use vstd::prelude::*;
verus! {
// (B) closure that mutably captures a local
fn main() {
    let mut c: u32 = 0;
    let mut bump = || { if c < 100 { c = c + 1; } };
    bump();
    bump();
}
}
