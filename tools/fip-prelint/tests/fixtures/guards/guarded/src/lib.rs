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

/// `panic!` under `i < n` and `i >= n`: no feasible path reaches it, so it is not a
/// panic path (limits plan L11): passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn infeasible_panic(i: usize, n: usize) -> usize {
    if i < n && i >= n {
        panic!("unreachable");
    }
    i
}

/// `Box::new` (and its drop) on the same infeasible branch, under `#[fip]`: no
/// allocation and no free are counted: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn infeasible_box(i: usize, n: usize) -> usize {
    if i < n {
        if i >= n {
            let b = Box::new(i);
            return *b;
        }
    }
    0
}

/// Control: `panic!` under `i < n` and `i > 0` is feasible: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn feasible_panic(i: usize, n: usize) -> usize {
    if i < n && i > 0 {
        panic!("reachable");
    }
    i
}

/// Control: `Box::new` under `i < n` and `i >= 1` is feasible: one allocation and a
/// free, reported.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn feasible_box(i: usize, n: usize) -> usize {
    if i < n {
        if i >= 1 {
            let b = Box::new(i);
            return *b;
        }
    }
    0
}

// Values returned by calls (limits plan L2): return summaries from the callee's MIR.

/// `xs[usize::from(i)]` on a `&[u8; 256]`, `i: u8`: `usize::from` returns its
/// argument (a widening cast in its body): passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn from_u8(xs: &[u8; 256], i: u8) -> u8 {
    xs[usize::from(i)]
}

/// Control: `usize::from(i)` of a `u16` can exceed 255: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn from_u16(xs: &[u8; 256], i: u16) -> u8 {
    xs[usize::from(i)]
}

/// A wrapper whose `len` and `get` go through a `Vec` field.
pub struct Wrap(pub Vec<u8>);

impl Wrap {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn get(&self) -> &[u8] {
        &self.0
    }
}

/// `if i < w.len() { w.get()[i] }`: both calls return `(*w).0.len` (an access path
/// through a shared reference to a `Freeze` type): passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn wrapper_len(w: &Wrap, i: usize) -> u8 {
    if i < w.len() { w.get()[i] } else { 0 }
}

/// Control: the guard is on `w.len()` but the index is `i + 1`: reported (bounds).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn wrapper_len_off(w: &Wrap, i: usize) -> u8 {
    if i < w.len() && i < usize::MAX { w.get()[i + 1] } else { 0 }
}

/// `xs.len() - 1` after `!xs.is_empty()`: `is_empty` returns `len == 0`: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn last_index(xs: &[u8]) -> usize {
    if xs.is_empty() { 0 } else { xs.len() - 1 }
}

/// The same through the wrapper: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn wrapper_last(w: &Wrap) -> u8 {
    if w.is_empty() { 0 } else { w.get()[w.len() - 1] }
}

/// Control: `len() - 1` without the `is_empty` guard: reported (overflow).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn last_index_unguarded(xs: &[u8]) -> usize {
    xs.len() - 1
}

/// A length behind interior mutability may change between the guard and the use.
pub struct CellLen(pub core::cell::Cell<usize>, pub Vec<u8>);

impl CellLen {
    pub fn len(&self) -> usize {
        self.0.get()
    }
}

/// Control: `CellLen` is not `Freeze`, so `c.len()` is not an access path: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn cell_len(c: &CellLen, xs: &[u8; 8], i: usize) -> u8 {
    if i < c.len() && c.len() <= 8 { xs[i] } else { 0 }
}

/// Control: the reference is replaced between the guard and the use: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn wrapper_replaced<'a>(mut w: &'a Wrap, other: &'a Wrap, i: usize) -> u8 {
    if i < w.len() {
        w = other;
        w.get()[i]
    } else {
        0
    }
}

/// Control: through `&mut`, the vector may change between the guard and the use
/// (each call reborrows anew): reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn wrapper_mut(w: &mut Wrap, i: usize) -> u8 {
    if i < w.len() {
        w.0.clear();
        w.get()[i]
    } else {
        0
    }
}

/// `u32::count_ones` calls the intrinsic `ctpop`, which has no MIR: its result is at
/// most 32 (audited table `fip_lint_rules::mir::INTRINSIC_RESULT_BOUNDS`): passes on
/// a 33-element array.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn count_ones_index(xs: &[u8; 33], x: u32) -> u8 {
    xs[x.count_ones() as usize]
}

/// Control: the same on a 32-element array (`x = u32::MAX` gives 32): reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn count_ones_off(xs: &[u8; 32], x: u32) -> u8 {
    xs[x.count_ones() as usize]
}

// Iterator contracts (limits plan L3).

/// `for i in (0..xs.len()).rev() { xs[i] }`: `Rev<Range>` yields `end - 1` while
/// `start < end`: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn rev_index(xs: &[u8]) -> u8 {
    let mut s = 0u8;
    for i in (0..xs.len()).rev() {
        s ^= xs[i];
    }
    s
}

/// Control: `(1..xs.len() + 1).rev()` starts one past the end: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn rev_off_by_one(xs: &[u8]) -> u8 {
    let mut s = 0u8;
    if xs.len() < usize::MAX {
        for i in (1..xs.len() + 1).rev() {
            s ^= xs[i];
        }
    }
    s
}

/// `for i in 0..=xs.len() - 1` after `is_empty()`: `RangeInclusive` yields values
/// up to `end`: passes (overflow and bounds).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn inclusive_last(xs: &[u8]) -> u8 {
    let mut s = 0u8;
    if xs.is_empty() {
        return 0;
    }
    for i in 0..=xs.len() - 1 {
        s ^= xs[i];
    }
    s
}

/// `for (i, x) in xs.iter().enumerate() { ys[i] }` with `ys.len() >= xs.len()`:
/// `Enumerate` yields indices below `xs.len()`: passes.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn enumerate_index(xs: &[u8], ys: &[u8]) -> u8 {
    let mut s = 0u8;
    if ys.len() < xs.len() {
        return 0;
    }
    for (i, x) in xs.iter().enumerate() {
        s ^= *x ^ ys[i];
    }
    s
}

/// Control: `ys` may be shorter (`ys.len() + 1 >= xs.len()`): reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn enumerate_short(xs: &[u8], ys: &[u8]) -> u8 {
    let mut s = 0u8;
    if ys.len() < usize::MAX && ys.len() + 1 < xs.len() {
        return 0;
    }
    for (i, x) in xs.iter().enumerate() {
        s ^= *x ^ ys[i];
    }
    s
}

/// `zip` stops at the shorter slice: a counter of its items indexes `out` (as long
/// as `xs`): passes (and `Iterator::zip`'s `size_of::<T>()` assert is decided for
/// `T = u8`).
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn zip_count(xs: &[u8], ys: &[u8], out: &mut [u8]) {
    if out.len() < xs.len() {
        return;
    }
    let mut i = 0;
    for (x, y) in xs.iter().zip(ys) {
        out[i] = *x ^ *y;
        i += 1;
    }
}

/// Control: `out` may be one shorter than both: reported.
#[cfg_attr(
    fip_prelint,
    fip::mark(kind = "fip", strict = true, panic_macros = false)
)]
pub fn zip_count_short(xs: &[u8], ys: &[u8], out: &mut [u8]) {
    if out.len() < usize::MAX && out.len() + 1 < xs.len() {
        return;
    }
    let mut i = 0;
    for (x, y) in xs.iter().zip(ys) {
        out[i] = *x ^ *y;
        i += 1;
    }
}
