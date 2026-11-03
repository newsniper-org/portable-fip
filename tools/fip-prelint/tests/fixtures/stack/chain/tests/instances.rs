// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! A test target instantiating the generic root `chain::generic` with `u8` (top plan
//! T8f): with `--tests`, its objects contribute the instance `chain::generic::<u8>`.

#[test]
fn generic_u8() {
    assert_eq!(chain::generic(3u8), 3);
}
