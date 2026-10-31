// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Overloaded operators, indexing and method calls.

/// A type whose `+` allocates.
pub struct Big(pub Box<u64>);

impl core::ops::Add for Big {
    type Output = Big;
    fn add(self, o: Big) -> Big {
        Big(Box::new(self.0.wrapping_add(*o.0)))
    }
}

/// `a + b` calls `<Big as Add>::add`: violation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn sum(a: Big, b: Big) -> Big {
    a + b
}

/// A type whose `+` does not allocate.
pub struct Small(pub u64);

impl core::ops::Add for Small {
    type Output = Small;
    fn add(self, o: Small) -> Small {
        Small(self.0.wrapping_add(o.0))
    }
}

/// `a + b` on `Small`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn sum_small(a: Small, b: Small) -> Small {
    a + b
}

/// Indexing may panic; `panic_macros = false`: error.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn get(xs: &[u8], i: usize) -> u8 {
    xs[i]
}

/// The same with `panic_macros` allowed: a note only.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true))]
pub fn get_noted(xs: &[u8], i: usize) -> u8 {
    xs[i]
}

/// No panic path through `<[u8]>::get`: passes under `panic_macros = false`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn get_or_zero(xs: &[u8], i: usize) -> u8 {
    match xs.get(i) {
        Some(v) => *v,
        None => 0,
    }
}

/// A guarded index still has its bounds check in MIR at opt-level 0 (the guard is
/// not used): reported, a known imprecision.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn get_guarded(xs: &[u8], i: usize) -> u8 {
    if i < xs.len() { xs[i] } else { 0 }
}

/// Two types with a method of the same name; only `Boxing::value` allocates.
pub struct Plain(pub u32);
/// See [`Plain`].
pub struct Boxing(pub u32);

impl Plain {
    /// Allocation-free.
    pub fn value(&self) -> u32 {
        self.0
    }
}

impl Boxing {
    /// Allocates.
    pub fn value(&self) -> Box<u32> {
        Box::new(self.0)
    }
}

/// Resolves to `Plain::value`: passes (no over-report).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn method_plain(p: &Plain) -> u32 {
    p.value()
}

/// Resolves to `Boxing::value`: violation.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn method_boxing(p: &Boxing) -> Box<u32> {
    p.value()
}
