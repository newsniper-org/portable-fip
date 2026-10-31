// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `assert_fip_all_threads!` must fail when the expression allocates on another
//! thread, which the per-thread `assert_fip!` cannot see. Own binary, one test.

use std::hint::black_box;

fip_testkit::install!();

#[test]
#[should_panic(expected = "fip (all threads) violated")]
fn allocation_on_another_thread_is_rejected() {
    fip_testkit::assert_fip_all_threads!(std::thread::scope(|sc| {
        sc.spawn(|| drop(black_box(Box::new(1_u8))));
    }));
}
