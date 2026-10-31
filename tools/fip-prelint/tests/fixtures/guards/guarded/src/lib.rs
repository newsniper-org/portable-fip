// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Bounds and overflow checks behind guards. Every root is strict with
//! `panic_macros = false`, so a check that the value analysis cannot prove is an
//! error; a proved one is not reported.

/// `xs[i]` under `i < xs.len()`: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn guarded_index(xs: &[u8], i: usize) -> u8 {
    if i < xs.len() { xs[i] } else { 0 }
}

/// `while i < xs.len() { xs[i]; i += 1 }`: index and counter pass.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn while_loop(xs: &[u8]) -> u32 {
    let mut s = 0u32;
    let mut i = 0;
    while i < xs.len() {
        s = s.wrapping_add(u32::from(xs[i]));
        i += 1;
    }
    s
}

/// The same through `&mut [u8]` and a length read once before the loop: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn while_len_once(xs: &mut [u8]) {
    let n = xs.len();
    let mut i = 0;
    while i < n {
        xs[i] = 0;
        i += 1;
    }
}

/// A second counter that never overtakes the first (`w <= r`): `w += 1` passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn count_nonzero(xs: &[u8]) -> usize {
    let mut w = 0;
    let mut r = 0;
    while r < xs.len() {
        if xs[r] != 0 {
            w += 1;
        }
        r += 1;
    }
    w
}

/// `xs[w - 1]` with `1 <= w <= r < xs.len()`: subtraction and index pass.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn previous_kept(xs: &[u8]) -> u8 {
    if xs.is_empty() {
        return 0;
    }
    let mut w = 1;
    let mut r = 1;
    let mut last = 0;
    while r < xs.len() {
        last = xs[w - 1];
        if xs[r] != last {
            w += 1;
        }
        r += 1;
    }
    last
}

/// `for i in 0..xs.len() { xs[i] }`: passes (`Range::next` is modelled).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn for_range(xs: &[u8]) -> u32 {
    let mut s = 0u32;
    for i in 0..xs.len() {
        s = s.wrapping_add(u32::from(xs[i]));
    }
    s
}

/// `for i in 1..xs.len() { xs[i - 1] }`: subtraction and index pass.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn for_range_from_one(xs: &[u8]) -> u32 {
    let mut s = 0u32;
    for i in 1..xs.len() {
        s = s.wrapping_add(u32::from(xs[i - 1]));
    }
    s
}

/// Index into an array under `i < 4`: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn array_index(a: &[u8; 4], i: usize) -> u8 {
    if i < 4 { a[i] } else { 0 }
}

/// `i + 1` under `i < u32::MAX`: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn inc_guarded(i: u32) -> u32 {
    if i < u32::MAX { i + 1 } else { 0 }
}

/// `x - 1` after `if x == 0 { return }`: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn dec_nonzero(x: u8) -> u8 {
    if x == 0 {
        return 0;
    }
    x - 1
}

/// `n / d` under `d != 0`: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn div_guarded(n: u32, d: u32) -> u32 {
    if d != 0 { n / d } else { 0 }
}

/// Unguarded index: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn unguarded(xs: &[u8], i: usize) -> u8 {
    xs[i]
}

/// The guard is on `j`, the index is `i`: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn other_var(xs: &[u8], i: usize, j: usize) -> u8 {
    if j < xs.len() { xs[i] } else { 0 }
}

/// Off by one (`i <= xs.len()`): reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn off_by_one(xs: &[u8], i: usize) -> u8 {
    if i <= xs.len() { xs[i] } else { 0 }
}

/// Unguarded `i + 1`: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn inc_unguarded(i: u32) -> u32 {
    i + 1
}

/// Unguarded division: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn div_unguarded(n: u32, d: u32) -> u32 {
    n / d
}

/// Moves `i` past the end.
pub fn bump(i: &mut usize) {
    *i = i.wrapping_add(1);
}

/// The guarded index changes through `&mut i` after the guard: reported (a local
/// whose address is taken is not tracked).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn changed_through_reference(xs: &[u8], mut i: usize) -> u8 {
    if i < xs.len() {
        bump(&mut i);
        xs[i]
    } else {
        0
    }
}

/// The slice is replaced after the guard: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn slice_replaced<'a>(mut xs: &'a [u8], ys: &'a [u8], i: usize) -> u8 {
    if i < xs.len() {
        xs = ys;
        xs[i]
    } else {
        0
    }
}

/// `for i in 0..=xs.len() { xs[i] }` (a real off-by-one; `RangeInclusive` is not
/// modelled): reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn for_inclusive(xs: &[u8]) -> u32 {
    let mut s = 0u32;
    for i in 0..=xs.len() {
        s = s.wrapping_add(u32::from(xs[i]));
    }
    s
}

/// `for i in 0..n { xs[i] }` with `n` unrelated to the length: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn for_other_bound(xs: &[u8], n: usize) -> u32 {
    let mut s = 0u32;
    for i in 0..n {
        s = s.wrapping_add(u32::from(xs[i]));
    }
    s
}

/// `xs[i + 1]` in `for i in 0..xs.len()`: the addition passes, the index is
/// reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn for_next_index(xs: &[u8]) -> u32 {
    let mut s = 0u32;
    for i in 0..xs.len() {
        s = s.wrapping_add(u32::from(xs[i + 1]));
    }
    s
}

/// A counter stepping by 2 under `i < xs.len()`: `xs[i]` after the step is
/// reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn step_two(xs: &[u8]) -> u32 {
    let mut s = 0u32;
    let mut i = 0;
    while i < xs.len() {
        i = i.wrapping_add(2);
        s = s.wrapping_add(u32::from(xs[i]));
    }
    s
}

/// Counting down from `xs.len()`: `i -= 1` under `i > 0` and `xs[i]` pass.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn countdown(xs: &[u8]) -> u32 {
    let mut s = 0u32;
    let mut i = xs.len();
    while i > 0 {
        i -= 1;
        s = s.wrapping_add(u32::from(xs[i]));
    }
    s
}

/// Signed `i - 1` under `i < 0` (overflows at `i32::MIN`): reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn signed_dec(i: i32) -> i32 {
    if i < 0 { i - 1 } else { 0 }
}
