// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Seed roots of the std summaries: the formatting paths that analysed code uses
//! (`format!`, `write!` into a buffer, `Display`/`Debug` of the primitive types,
//! formatting options, user `Display` impls that write through the `Formatter`).
//! Every standard-library function without shipped MIR reached from here, and from
//! those, is summarised. Add a root here to cover a new path.

use core::fmt::{self, Write};

/// A fixed buffer.
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
            self.n += 1;
        }
        Ok(())
    }
}

/// A user type formatted through the `Formatter`'s methods.
pub struct P(pub u32, pub i64);

impl fmt::Display for P {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("(")?;
        f.write_char('<')?;
        write!(f, "{}, {}", self.0, self.1)?;
        f.pad("x")?;
        f.pad_integral(true, "", "1")?;
        f.write_fmt(format_args!("{:?}", self.0))
    }
}

impl fmt::Debug for P {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("P").field("a", &self.0).field("b", &self.1).finish()
    }
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_ints(b: &mut Buf, a: u8, c: u16, d: u32, e: u64, g: usize, h: i8, i: i16, j: i32, k: i64, l: isize) -> fmt::Result {
    write!(b, "{a}{c}{d}{e}{g}{h}{i}{j}{k}{l}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_radix(b: &mut Buf, x: u32, y: u64, z: usize) -> fmt::Result {
    write!(b, "{x:x}{x:X}{x:o}{x:b}{y:x}{y:#x}{z:x}{x:08}{x:>8}{x:<8}{x:^8}{x:+}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_debug(b: &mut Buf, x: u32, y: i64, s: &str, c: char, t: bool) -> fmt::Result {
    write!(b, "{x:?}{y:?}{s:?}{c:?}{t:?}{x:#?}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_text(b: &mut Buf, s: &str, c: char, t: bool) -> fmt::Result {
    write!(b, "{s}{c}{t}{s:>10}")?;
    b.write_str(s)?;
    b.write_char(c)
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_user(b: &mut Buf, p: &P) -> fmt::Result {
    write!(b, "{p} {p:?}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn format_ints(a: u32, b: i64, s: &str) -> String {
    format!("{a}{b}{s}{a:x}{a:?}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn format_user(p: &P) -> String {
    format!("{p}{p:?}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn format_literal() -> String {
    format!("literal")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn to_string_int(a: u32) -> String {
    a.to_string()
}
