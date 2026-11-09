// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `total` marks (decision 2026-11-06-redesign-verus-allocates, 7.5 step 2): the
//! driver discharges one only if the Verus sidecar lists the function with the literal
//! bound `allocates 0` (a sidecar is used only with `--no-cheating -V alloc-check`) and
//! its own allocation, free, recursion and panic checks pass for the root. The marks
//! are written by hand, as `#[fip_macros::fip(total)]` emits them under the driver.

#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Listed with `allocates 0`, no free, no panic: discharged.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false, total = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == a / 2,
    no_unwind
    allocates 0
))]
pub fn ok(a: u32) -> u32 {
    a / 2
}

/// A loop with a proved `decreases`, listed with `allocates 0`: discharged (its
/// overflow check is discharged by Verus as well).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false, total = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == n,
    no_unwind
    allocates 0
))]
pub fn ok_loop(n: u32) -> u32 {
    let mut i: u32 = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            i <= n,
        decreases n - i,
    ))]
    while i < n {
        i = i + 1;
    }
    i
}

/// Listed, but with `allocates 1`: refused (⊤).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false, total = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == 7,
    no_unwind
    allocates 1
))]
pub fn bound_one() -> u32 {
    7
}

/// Not verified by Verus (`external`), so not listed: refused (⊤).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false, total = true))]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn unlisted(a: u32) -> u32 {
    a / 2
}

/// Not listed and with a loop: refused (⊤), the reason names the unchecked termination
/// (P4).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false, total = true))]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn unlisted_loop(n: u32) -> u32 {
    let mut i: u32 = 0;
    while i < n {
        i = i.wrapping_add(1);
    }
    i
}

/// Listed with `allocates 0` (frees are not counted by `allocates`), but it frees its
/// `Box`: the driver's F2 check rejects it.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false, total = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == *b,
    allocates 0
))]
pub fn frees(b: Box<u32>) -> u32 {
    *b
}

/// Listed with `allocates 0` and a proved `decreases`, but recursive: the driver's
/// stack check (no recursion) rejects it.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false, total = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == 0,
    decreases n,
    no_unwind
    allocates 0
))]
pub fn recurses(n: u32) -> u32 {
    if n == 0 { 0 } else { recurses(n - 1) }
}

/// Listed with `allocates 0`; Verus proves the `unwrap` safe under its `requires`,
/// which the driver does not know (no `fip::requires`): the panic path of `unwrap`
/// stays a reachable panic path, an error under `total`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", n = 0, strict = true, panic_macros = false, total = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        x.is_some(),
    ensures
        r == x.unwrap(),
    allocates 0
))]
pub fn panics(x: Option<u32>) -> u32 {
    x.unwrap()
}
