<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `unsafe` in `fip-testkit`: the counting global allocator

**Status:** ACCEPTED, 2026-10-31.

## Decision

`fip-testkit` implements `GlobalAlloc` for `CountingAlloc`, which requires
`unsafe impl` and `unsafe` calls into `std::alloc::System`. The crate is
`#![deny(unsafe_code)]`; the one `impl` carries `#[allow(unsafe_code)]`.

## Invariant upheld

Every `GlobalAlloc` method forwards its arguments **unchanged** to `System` and
returns `System`'s result unchanged. The only additions are counter updates:

- a `thread_local!` `Cell<AllocStats>` with `const` initialisation, which never
  allocates (no lazy initialisation, no destructor registration);
- four process-wide `AtomicU64` counters (`Relaxed` increments) for
  `measure_all_threads`, which never allocate.

Neither unwinds (plain integer arithmetic on `Copy` data). The atomics are confined
to this test-only crate and never reach a `no_std` or verified crate.

During thread teardown the slot may be inaccessible; `try_with` then skips the
update. Such events are outside every measured region.

## Tests that would fail if the invariant were violated

`crates/fip-testkit/tests/counts.rs`:

- `realloc_preserves_contents_and_is_counted` — a forwarded `realloc` with a wrong
  layout or size would corrupt or lose the 1000 written values;
- `zeroed_allocation_is_zero` — `alloc_zeroed` must reach `System.alloc_zeroed`;
- `box_new_and_drop_are_counted_exactly` — exact counts and byte sizes;
- `other_threads_are_not_counted` — per-thread isolation;
- `tests/all_threads.rs` — process-wide counting sees work on other threads.

## Scope

Test builds only. `fip-testkit` is a `dev-dependency`; it never enters a verified
or `no_std` crate.

## What would reopen this

A need to count allocations in `no_std` targets (no `thread_local!`).
