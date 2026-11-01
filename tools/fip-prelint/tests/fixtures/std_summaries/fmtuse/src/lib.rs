// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Formatting through `core::fmt::write` and `alloc::fmt::format::format_inner`, which
//! the shipped standard library has no MIR for.

use core::fmt::{self, Write};

/// A fixed buffer; writing never allocates.
pub struct Buf {
    pub b: [u8; 64],
    pub n: usize,
}

impl Write for Buf {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for &c in s.as_bytes() {
            if self.n >= self.b.len() {
                return Err(fmt::Error);
            }
            self.b[self.n] = c;
            self.n = self.n.wrapping_add(1);
        }
        Ok(())
    }
}

/// Formats through the `Formatter`'s methods.
pub struct Pair(pub u32, pub i64);

impl fmt::Display for Pair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("(")?;
        write!(f, "{}, {}", self.0, self.1)?;
        f.pad(")")
    }
}

#[derive(Debug)]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

/// `write!` of integers and a string into the buffer: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_values(b: &mut Buf, x: u32, y: i64, s: &str) -> fmt::Result {
    write!(b, "{x} {y} {s} {x:x}")
}

/// A user `Display` writing through the `Formatter`: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_pair(b: &mut Buf, p: &Pair) -> fmt::Result {
    write!(b, "{p}")
}

/// `format!` builds a `String`: allocations and a free, no `⊤`.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn format_value(x: u32) -> String {
    format!("{x}")
}

/// `{:?}` of a derived `Debug`: `core` calls the fields through `&dyn Debug`
/// (`⊤`, reported).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_debug(b: &mut Buf, p: &Point) -> fmt::Result {
    write!(b, "{p:?}")
}

/// Under `strict = true, panic_macros = false`: the bounds checks inside `core`'s
/// integer formatting are panic paths (errors).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip", strict = true, panic_macros = false))]
pub fn write_strict(b: &mut Buf, x: u8) -> fmt::Result {
    write!(b, "{x}")
}
