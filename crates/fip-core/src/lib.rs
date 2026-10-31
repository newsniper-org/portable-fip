// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! # fip-core — allocation-free, in-place building blocks
//!
//! Building blocks for code written in the style of *FP²: Fully in-Place
//! Functional Programming* (Lorenzen, Leijen, Swierstra, ICFP 2023).
//!
//! ## What this crate guarantees, and how
//!
//! - **No heap allocation, by construction.** The crate is `#![no_std]`, does not
//!   link `alloc`, and has no dependencies. There is no allocator API it could call.
//!   This is a crate-boundary guarantee, not a lint.
//! - **No `unsafe`** (`#![forbid(unsafe_code)]`).
//! - **Functional correctness, by proof.** Every public function carries a Verus
//!   specification (`#[cfg_attr(verus_keep_ghost, verus_spec(..))]`) and is verified
//!   with `verus --no-cheating`. A plain `cargo` build never sees the specifications:
//!   the `verus_keep_ghost` cfg is set only by the `verus` driver, so the crate has
//!   no build-time dependency on Verus or `vstd`.
//!
//! ## What it does not guarantee
//!
//! - Bounded stack depth is not proved. No function here recurses, and every loop has a
//!   proved `decreases` measure, but that is termination, not a stack bound.
//! - Closures passed in (`keep`, `f`) are the caller's code; this crate makes no claim
//!   about what they allocate.
//!
//! ## Placeholders
//!
//! Functions that move a value out of a `&mut` slot need something to leave behind.
//! This crate never manufactures one (no `Default` bound, no `mem::take`): the caller
//! passes a `hole` value and gets it back. A capability-like type therefore never has
//! to be minted just to satisfy a placeholder.

#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]

// Plain builds: proof-only blocks expand to nothing. Under `verus` the real macros
// come from `vstd::prelude`.
#[cfg(not(verus_keep_ghost))]
macro_rules! proof {
    ($($t:tt)*) => {};
}
#[cfg(not(verus_keep_ghost))]
macro_rules! proof_decl {
    ($($t:tt)*) => {};
}

pub mod slice;
pub mod slot;
#[cfg(verus_keep_ghost)]
pub mod spec;

pub use slice::{compact, map_in_place, swap};
pub use slot::{replace, update};
