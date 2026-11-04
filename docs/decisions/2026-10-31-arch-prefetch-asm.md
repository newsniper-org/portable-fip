<!-- SPDX-License-Identifier: MIT OR Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) -->

# `unsafe` in `fip-arch`: inline prefetch hints

**Status:** ACCEPTED, 2026-10-31.

## Decision

`fip_arch::prefetch_read` emits one instruction through `core::arch::asm!`:

| target | instruction | reference |
|---|---|---|
| `x86_64` | `prefetcht0 [p]` | Intel SDM Vol. 2, PREFETCHh (baseline x86-64) |
| `aarch64` | `prfm pldl1keep, [p]` | Arm ARM, PRFM (baseline `ARMv8`-A) |
| `riscv64` | `ori x0, p, 1` (= Zicbop `prefetch.r 0(p)`; amendment 2026-11-04) | RISC-V Unprivileged ISA, HINT instructions; CMO extension, Zicbop |
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
- `riscv64`: `prefetch.r` belongs to Zicbop and is not assumed; until 2026-11-04 the
  hint was a no-op there (see the amendment).

## Cache-line size

`CACHE_LINE` defaults to 128 bytes on Apple `aarch64` and 64 bytes elsewhere, and can
be set per build with `--cfg fip_cache_line="N"` (32, 64 or 128). A `cfg` predicate
can only test listed values, so `build.rs` rejects any other value, a bare
`fip_cache_line`, or two values (`just arch-override`).

## Amendment 2026-11-04: `prefetch.r` on riscv64

`riscv64` now emits Zicbop's `prefetch.r 0(p)` through its base-ISA encoding
`ori x0, p, 1` (third audited `asm!`, same options). Zicbop is still not assumed: an
`ORI` with `rd = x0` is a HINT in RV64I (writes no register, accesses no memory), so
on a core without Zicbop it is a no-op, and with Zicbop the prefetch raises no
exception and changes no architectural state, for any address. The invariant above
holds either way.

Measured with rustc 1.99.1 (LLVM of that release):

- The assembler takes both spellings without `+zicbop` on
  `riscv64gc-unknown-none-elf` and `riscv64gc-unknown-linux-gnu`, and both give the
  same word, `0x00156013` for `p = a0` (`llvm-objdump`: `prefetch.r 0x0(a0)`). The
  `ori` spelling is kept because accepting `prefetch.r` without the extension is an
  assembler leniency the ISA does not promise, while `ori` is valid for every RV64I
  assembler.
- A `--release` caller (`no_mangle` loop prefetching 16 elements ahead) built for
  `riscv64gc-unknown-none-elf`, `riscv64gc-unknown-linux-gnu` and
  `riscv64gc-unknown-linux-musl` contains the word inline (`0x00166013`, `p = a2`)
  and no call to `prefetch_read`.
- `cargo test -p fip-arch --lib --target riscv64gc-unknown-linux-musl` (statically
  linked with `rust-lld`) under `qemu-riscv64` 11.0.0: 3 passed, debug and release,
  with `QEMU_CPU=rv64,zicbop=false`, `rv64,zicbop=true` and `max`
  (`prefetch_accepts_any_pointer` passes null and `usize::MAX`). Recipe
  `just arch-qemu-riscv64` (not in `ci`: needs `qemu-riscv64`); `just cross` checks
  the three riscv64 targets.

## What would reopen this

A target where the hint can fault, or a RISC-V core on which `ORI` with `rd = x0` is
not a HINT (none in the ratified ISA).
