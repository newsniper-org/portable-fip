<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `unsafe` in `fip-arch`: inline prefetch hints

**Status:** ACCEPTED, 2026-10-31.

## Decision

`fip_arch::prefetch_read` emits one instruction through `core::arch::asm!`:

| target | instruction | reference |
|---|---|---|
| `x86_64` | `prefetcht0 [p]` | Intel SDM Vol. 2, PREFETCHh (baseline x86-64) |
| `aarch64` | `prfm pldl1keep, [p]` | Arm ARM, PRFM (baseline `ARMv8`-A) |
| others | nothing | — |

The crate is `#![deny(unsafe_code)]`; each `asm!` block carries
`#[allow(unsafe_code)]` and a `SAFETY` comment.

## Invariant upheld

The instruction is a pure hint: for every address, including null and unmapped
ones, it raises no exception and changes no register, flag or memory. The `asm!`
options state this to the compiler: `nostack`, `preserves_flags`, `readonly`.

## Why not `core::arch::x86_64::_mm_prefetch`

It is `#[target_feature(enable = "sse")]`. On `x86_64-unknown-none` (SSE off, a
typical kernel target) it cannot be inlined and every hint becomes a call, which
defeats the purpose. `prefetcht0` itself needs no SSE. An earlier in-house
implementation shipped exactly this defect.

## Checks

- `prefetch_accepts_any_pointer` calls the hint with a valid pointer, null and
  `usize::MAX`.
- Measured 2026-10-31: a caller built with `--release` for `x86_64-unknown-none`
  contains `prefetcht0` and no call to `prefetch_read`; same for `aarch64`
  (`prfm`, no `bl`).
- `riscv64`: `prefetch.r` belongs to Zicbop and is not assumed; the hint is a
  no-op there.

## Cache-line size

`CACHE_LINE` defaults to 128 bytes on Apple `aarch64` and 64 bytes elsewhere, and can
be set per build with `--cfg fip_cache_line="N"` (32, 64 or 128). A `cfg` predicate
can only test listed values, so `build.rs` rejects any other value, a bare
`fip_cache_line`, or two values (`just arch-override`).

## What would reopen this

A target where the hint can fault, or a decision to assume Zicbop on RISC-V.
