// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! In-place updates of a single `&mut` slot.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Replaces `*slot` with `new` and returns the previous value.
///
/// Same behaviour as `core::mem::replace`, written with `core::mem::swap` because
/// `vstd` specifies `swap` but not `replace`; this keeps the crate verifiable with
/// `--no-cheating` and no trusted specifications of its own.
///
/// ```
/// let mut x = 1;
/// assert_eq!(fip_core::replace(&mut x, 2), 1);
/// assert_eq!(x, 2);
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        *final(slot) == new,
        r == *old(slot),
))]
#[inline]
pub fn replace<T>(slot: &mut T, new: T) -> T {
    let mut v = new;
    core::mem::swap(slot, &mut v);
    v
}

/// Transforms `*slot` in place with `f`, using `hole` as the temporary occupant,
/// and returns `hole`.
///
/// No `Default` bound and no value is manufactured: the caller supplies the
/// placeholder and gets the same value back, so it can be reused for the next call.
/// If `f` panics, `*slot` holds `hole` (a valid value), never a moved-from one.
///
/// ```
/// let mut x = 5_i32;
/// let hole = fip_core::update(&mut x, 0, |v| v * 2);
/// assert_eq!((x, hole), (10, 0));
/// ```
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        f.requires((*old(slot),)),
    ensures
        f.ensures((*old(slot),), *final(slot)),
        r == hole,
))]
#[inline]
pub fn update<T, F: FnOnce(T) -> T>(slot: &mut T, hole: T, f: F) -> T {
    let prev = replace(slot, hole);
    let next = f(prev);
    replace(slot, next)
}

/// Strict certificate for [`replace`]; made and justified in `fip_strict::certs`.
#[cfg(not(verus_keep_ghost))]
#[doc(hidden)]
pub use fip_strict::certs::__fip_strict_replace;
