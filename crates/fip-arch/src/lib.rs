// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-arch — per-ISA tuning for in-place loops
//!
//! One crate for every target. The realisation is chosen by `cfg(target_arch)`, so
//! there is nothing to select by hand and no way to link the wrong ISA's module.
//!
//! | target | `CACHE_LINE` | `prefetch_read` |
//! |---|---|---|
//! | `x86_64` | 64 | `prefetcht0` (baseline x86-64, no SSE needed) |
//! | `aarch64` | 64 | `prfm pldl1keep` (baseline `ARMv8`-A) |
//! | `riscv64` | 64 | no-op (`prefetch.r` needs Zicbop; not assumed) |
//! | other | 64 | no-op |
//!
//! `CACHE_LINE` is the common L1 line size. Some cores use 128 bytes (e.g. Apple
//! M-series); there is no override mechanism yet.
//!
//! `#![no_std]`, no `alloc`, no dependencies. `unsafe` is confined to the two inline
//! `asm!` hints and justified in `docs/decisions/2026-10-31-arch-prefetch-asm.md`.

#![no_std]
#![deny(unsafe_code)]

/// Name of the target architecture this build was compiled for.
#[cfg(target_arch = "x86_64")]
pub const ARCH: &str = "x86_64";
/// Name of the target architecture this build was compiled for.
#[cfg(target_arch = "aarch64")]
pub const ARCH: &str = "aarch64";
/// Name of the target architecture this build was compiled for.
#[cfg(target_arch = "riscv64")]
pub const ARCH: &str = "riscv64";
/// Name of the target architecture this build was compiled for.
#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "riscv64"
)))]
pub const ARCH: &str = "other";

/// Typical L1 cache-line size in bytes for [`ARCH`].
pub const CACHE_LINE: usize = 64;

/// How many `T` fit in one cache line, for sizing batches of an in-place loop.
///
/// Never 0: a `T` larger than a line gives 1. A zero-sized `T` gives `usize::MAX`.
///
/// ```
/// assert_eq!(fip_arch::per_cache_line::<u32>(), fip_arch::CACHE_LINE / 4);
/// assert_eq!(fip_arch::per_cache_line::<[u8; 200]>(), 1);
/// assert_eq!(fip_arch::per_cache_line::<()>(), usize::MAX);
/// ```
#[must_use]
pub const fn per_cache_line<T>() -> usize {
    let size = core::mem::size_of::<T>();
    if size == 0 {
        usize::MAX
    } else if size >= CACHE_LINE {
        1
    } else {
        CACHE_LINE / size
    }
}

/// Hints that the cache line containing `p` will be read soon.
///
/// A pure hint: it never faults, for any pointer value, and changes no
/// architectural state. On targets without a baseline prefetch instruction it does
/// nothing.
#[allow(
    clippy::inline_always,
    reason = "a prefetch hint emitted as an out-of-line call is useless; it must be inlined"
)]
#[inline(always)]
pub fn prefetch_read<T>(p: *const T) {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: `prefetcht0` is in the x86-64 baseline ISA; it raises no exception for
    // any address and modifies no registers, flags or memory (Intel SDM Vol. 2,
    // PREFETCHh). Hence `nostack`, `preserves_flags`, `readonly`.
    #[allow(unsafe_code)]
    unsafe {
        core::arch::asm!(
            "prefetcht0 [{0}]",
            in(reg) p,
            options(nostack, preserves_flags, readonly),
        );
    }
    #[cfg(target_arch = "aarch64")]
    // SAFETY: `PRFM` is in the ARMv8-A baseline; a prefetch to any address does not
    // generate a synchronous abort and changes no architectural state (Arm ARM,
    // "Prefetch memory").
    #[allow(unsafe_code)]
    unsafe {
        core::arch::asm!(
            "prfm pldl1keep, [{0}]",
            in(reg) p,
            options(nostack, preserves_flags, readonly),
        );
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    let _ = p;
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    #[test]
    fn per_cache_line_bounds() {
        assert_eq!(per_cache_line::<u8>(), CACHE_LINE);
        assert_eq!(per_cache_line::<u64>(), CACHE_LINE / 8);
        assert_eq!(per_cache_line::<[u8; 64]>(), 1);
        assert_eq!(per_cache_line::<[u8; 65]>(), 1);
        assert_eq!(per_cache_line::<[u8; 128]>(), 1);
        assert_eq!(per_cache_line::<()>(), usize::MAX);
    }

    #[test]
    fn prefetch_accepts_any_pointer() {
        let x = 5_u32;
        prefetch_read(&raw const x);
        prefetch_read(core::ptr::null::<u32>());
        prefetch_read(usize::MAX as *const u8);
        assert_eq!(ARCH, std::env::consts::ARCH);
    }
}
