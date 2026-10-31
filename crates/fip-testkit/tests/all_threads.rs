// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Process-wide counting. One test in this binary, so nothing else runs
//! concurrently and the global counters see only the measured work.

use fip_testkit::{measure, measure_all_threads};
use std::hint::black_box;

fip_testkit::install!();

const N: u64 = 100;

fn spawn_and_join(allocations: u64) {
    std::thread::scope(|sc| {
        sc.spawn(move || {
            for _ in 0..allocations {
                drop(black_box(Box::new(1_u8)));
            }
        });
    });
}

#[test]
fn all_threads_counts_child_work_and_per_thread_does_not() {
    // Baselines: spawning a thread allocates by itself.
    let ((), base_all) = measure_all_threads(|| spawn_and_join(0));
    let ((), base_one) = measure(|| spawn_and_join(0));

    let ((), with_all) = measure_all_threads(|| spawn_and_join(N));
    let ((), with_one) = measure(|| spawn_and_join(N));

    assert!(
        with_all.allocs >= base_all.allocs + N && with_all.frees >= base_all.frees + N,
        "process-wide counting missed the child's work: base {base_all:?}, with {with_all:?}"
    );
    assert!(
        with_one.allocs < base_one.allocs + N,
        "per-thread counting saw the child's work: base {base_one:?}, with {with_one:?}"
    );

    // In-place work passes the process-wide assertion.
    let mut xs = [3, 1, 2];
    let n = fip_testkit::assert_fip_all_threads!(fip_core::compact(&mut xs, |v| *v > 1));
    assert_eq!(&xs[..n], &[3, 2]);
}
