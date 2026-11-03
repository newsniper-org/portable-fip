// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Depends on `drvdep`, whose driver-mode construction does not compile.

/// Calls into the exported dependency.
pub fn value() -> u32 {
    drvdep::dep_value()
}
