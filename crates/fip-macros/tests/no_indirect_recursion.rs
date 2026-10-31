// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `#[fip]` rejects only direct self-recursion; this checks the `#[fip]` functions in
//! this crate's tests are not part of any call cycle either.

#[test]
fn fip_functions_are_not_recursive() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let cycles = fip_testkit::callgraph::fip_cycles(&dir);
    assert_eq!(cycles, Vec::<fip_testkit::callgraph::Cycle>::new());
}
