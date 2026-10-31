// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Process-wide counting. One test per binary so nothing else runs concurrently.

use fip_testkit::measure_all_threads;
use std::hint::black_box;

fip_testkit::install!();

#[test]
fn work_on_other_threads_is_counted_and_in_place_work_passes() {
    let ((), s) = measure_all_threads(|| {
        std::thread::scope(|sc| {
            sc.spawn(|| {
                for _ in 0..100 {
                    drop(black_box(Box::new(1_u8)));
                }
            });
        });
    });
    assert!(s.allocs >= 100 && s.frees >= 100, "{s:?}");

    let mut xs = [3, 1, 2];
    let n = fip_testkit::assert_fip_all_threads!(fip_core::compact(&mut xs, |v| *v > 1));
    assert_eq!(&xs[..n], &[3, 2]);
}
