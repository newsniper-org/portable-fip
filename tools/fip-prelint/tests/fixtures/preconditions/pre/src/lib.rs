// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Declared preconditions (`fip::requires`) and callee contexts (limits plan L1).
//! Strict roots with `panic_macros = false`: a panic path is an error.

/// `xs[i]` and `xs[j]` are safe under `i < j < xs.len()`.
#[cfg_attr(fip_prelint, fip::requires(i < j, j < xs.len()))]
fn pick(xs: &[u8], i: usize, j: usize) -> u8 {
    xs[i] ^ xs[j]
}

/// The precondition is established by the guards: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn guarded_caller(xs: &[u8], i: usize, j: usize) -> u8 {
    if i < j && j < xs.len() { pick(xs, i, j) } else { 0 }
}

/// Control: `j <= xs.len()` does not establish `j < xs.len()`: the call site is
/// reported ("precondition not established"), and `pick` is analysed without its
/// precondition there, so its bounds checks are reported too.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn unguarded_caller(xs: &[u8], i: usize, j: usize) -> u8 {
    if i < j && j <= xs.len() { pick(xs, i, j) } else { 0 }
}

/// A root with a precondition is checked under it: passes ("under
/// `fip::requires(..)`").
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
#[cfg_attr(fip_prelint, fip::requires(i < xs.len()))]
pub fn get_at(xs: &[u8], i: usize) -> u8 {
    xs[i]
}

/// Calls of a public function with a precondition: constant arguments on an array
/// of 4 establish it (passes).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn constant_caller(xs: &[u8; 4]) -> u8 {
    get_at(xs, 3)
}

/// Control: index 4 on an array of 4: reported at the call site.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn constant_caller_off(xs: &[u8; 4]) -> u8 {
    get_at(xs, 4)
}

/// Taken as a function pointer, `get_at`'s precondition cannot be checked where the
/// pointer is called: a panic path where it is taken (an error under
/// `panic_macros = false`).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn reified() -> fn(&[u8], usize) -> u8 {
    get_at
}

/// Passed as a callable value: reported the same way (a note: `panic_macros` is
/// left at its default); inside, the call through the `Fn` shim establishes nothing
/// and `get_at` is analysed without its precondition (two more notes).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
pub fn as_value(xs: &[u8]) -> u8 {
    apply(get_at, xs)
}

fn apply(f: impl Fn(&[u8], usize) -> u8, xs: &[u8]) -> u8 {
    f(xs, 0)
}

/// A callee that allocates only when its precondition is broken.
#[cfg_attr(fip_prelint, fip::requires(i < n))]
fn boxes_if_broken(i: usize, n: usize) -> usize {
    if i >= n {
        drop(Box::new(i));
    }
    i
}

/// The precondition holds: the branch with the allocation is infeasible: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn alloc_guarded(i: usize, n: usize) -> usize {
    if i < n { boxes_if_broken(i, n) } else { 0 }
}

/// Control: unguarded, the precondition is not assumed at this call, so the
/// allocation and the free are counted (a broken contract never hides an
/// allocation): errors.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn alloc_unguarded(i: usize, n: usize) -> usize {
    boxes_if_broken(i, n)
}

/// Contexts without a declared precondition: `split_at_mut` (from `core`) is
/// analysed in the caller's state `j < xs.len()`, so its panic branch (`mid > len`)
/// is infeasible, and its summary gives the halves' lengths `j` and `len - j ≥ 1`:
/// passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn split_guarded(xs: &mut [u8], j: usize) -> u8 {
    if j < xs.len() {
        let (a, b) = xs.split_at_mut(j);
        b[0] ^ a.len() as u8
    } else {
        0
    }
}

/// Control: `j <= xs.len()`: the second half may be empty: reported (bounds check).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn split_unguarded(xs: &mut [u8], j: usize) -> u8 {
    if j <= xs.len() {
        let (_, b) = xs.split_at_mut(j);
        b[0]
    } else {
        0
    }
}

/// Control: no guard at all: `split_at_mut`'s panic (`mid > len`) is reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn split_no_guard(xs: &mut [u8], j: usize) -> usize {
    let (a, _) = xs.split_at_mut(j);
    a.len()
}

/// A callee without a precondition, analysed in each caller's context.
fn third(xs: &[u8], k: usize) -> u8 {
    xs[k + 2]
}

/// `k + 2 < xs.len()` at the call: the callee's bounds and overflow checks pass.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn context_guarded(xs: &[u8], k: usize) -> u8 {
    if k < 10 && k + 2 < xs.len() { third(xs, k) } else { 0 }
}

/// Control: `k < xs.len()` only: the callee's bounds check is reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn context_short(xs: &[u8], k: usize) -> u8 {
    if k < xs.len() { third(xs, k) } else { 0 }
}

/// Control: a root's precondition does not cover `xs[i + 1]`: reported, with the
/// precondition named in the verdict.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
#[cfg_attr(fip_prelint, fip::requires(i < xs.len()))]
pub fn get_next(xs: &[u8], i: usize) -> u8 {
    xs[i + 1]
}
