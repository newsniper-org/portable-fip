// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Verus as an oracle for panic freedom (top plan T13.4). Verified with
//! `verus --no-cheating` (`just verify-core` writes `verus-verified.txt`); the module
//! `plain` is not seen by Verus. Roots are strict, so panic paths are notes.

#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Nonlinear: `a * b` cannot overflow under `a < 1000, b < 1000`. The driver's
/// difference bounds cannot show it; Verus does (nonlinear arithmetic). Its note is
/// dropped.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
#[cfg_attr(verus_keep_ghost, verifier::nonlinear)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        a < 1000,
        b < 1000,
))]
pub fn mul(a: u32, b: u32) -> u32 {
    a * b
}

/// `xs[i]` under a relational precondition only Verus reads: its bounds check is
/// dropped.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        i < j,
        j <= xs@.len(),
))]
pub fn pick(xs: &[u8], i: usize, j: usize) -> u8 {
    xs[i]
}

/// A Verus caller: Verus checked `mul`'s precondition at this call (under this
/// function's own `requires`), so neither the call nor `mul`'s body is reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        a < 10,
))]
pub fn square_small(a: u32) -> u32 {
    mul(a, a)
}

/// No `requires`: `a / 2 + b / 2` cannot overflow; callers have no obligation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == a / 2 + b / 2,
))]
pub fn halves(a: u32, b: u32) -> u32 {
    a / 2 + b / 2
}

/// The same body without any Verus attribute: outside `verus!` Verus skips an
/// unannotated function (it is not in the VIR, so not listed); its note stays.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
pub fn halves_unannotated(a: u32, b: u32) -> u32 {
    a / 2 + b / 2
}

/// Impl methods (top plan item 8). The sidecar names them `vside::{impl}::<name>` and
/// the driver matches them by that path, file and line, not by the impl number: this
/// crate's plain build has one impl block more than its Verus build (the one below),
/// so rustc's `{impl#N}` and Verus's `impl&%N` differ.
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub struct Acc {
    pub n: u32,
}

/// Only in the plain build: it shifts the plain build's impl numbers by one.
#[cfg(not(verus_keep_ghost))]
impl Acc {
    /// Not seen by Verus: its overflow note stays.
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
    pub fn add_plain(&self, a: u32) -> u32 {
        self.n + a
    }
}

impl Acc {
    /// Verified under `requires`: its overflow site is discharged.
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            self.n < 1000,
            a < 1000,
    ))]
    pub fn add(&self, a: u32) -> u32 {
        self.n + a
    }

    /// Verified without `requires`: its overflow site is discharged.
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r == self.n / 2 + self.n / 4,
    ))]
    pub fn three_quarters(&self) -> u32 {
        self.n / 2 + self.n / 4
    }
}

/// Not seen by Verus.
#[cfg(not(verus_keep_ghost))]
pub mod plain {
    /// A non-verified function with the same name as the verified `mul`: its overflow
    /// note stays (not in the sidecar).
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
    pub fn mul(a: u32, b: u32) -> u32 {
        a * b
    }

    /// A call of the verified `mul` that Verus did not check: `mul`'s body sites are
    /// discharged under its `requires`, so the call carries that precondition as a
    /// note.
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
    pub fn use_mul(a: u32) -> u32 {
        super::mul(a, 3)
    }

    /// `halves` has no `requires`: nothing to establish here, no note.
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
    pub fn use_halves(a: u32) -> u32 {
        super::halves(a, a)
    }

    /// A call of the verified method `Acc::add` that Verus did not check: it carries
    /// `add`'s precondition as a note.
    #[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
    pub fn use_add(a: u32) -> u32 {
        super::Acc { n: a }.add(3)
    }
}
