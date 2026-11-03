// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Seed roots of the std summaries: the formatting paths that analysed code uses
//! (`format!`, `write!` into a buffer, `Display`/`Debug` of the primitive types
//! including floats and 128-bit integers, the radix and exponent formats of every
//! integer type, formatting options, user `Display` impls that write through the
//! `Formatter`). Every standard-library function without shipped MIR reached from
//! here, and from those, is summarised. Add a root here to cover a new path.

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

// Top plan T7c: floating-point `Display`, precision, exponent and `Debug` formats.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_floats(b: &mut Buf, x: f64, y: f32) -> fmt::Result {
    write!(b, "{x}{y}{x:.3}{y:.3}{x:e}{y:e}{x:E}{y:E}{x:?}{y:?}{x:#?}{x:>10.2}{x:+}{x:08.1}")
}

// Top plan T7e: 128-bit integers and the radix, exponent and `Debug` formats of every
// integer type.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_wide(b: &mut Buf, x: u128, y: i128) -> fmt::Result {
    write!(b, "{x}{y}{x:x}{x:X}{x:o}{x:b}{y:x}{y:X}{y:o}{y:b}{x:?}{y:?}{x:e}{x:E}{y:e}{x:#x}{x:08}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_radix_unsigned(b: &mut Buf, a: u8, c: u16, d: u32, e: u64, g: usize) -> fmt::Result {
    write!(b, "{a:x}{a:X}{a:o}{a:b}{c:x}{c:X}{c:o}{c:b}{d:x}{d:X}{d:o}{d:b}")?;
    write!(b, "{e:x}{e:X}{e:o}{e:b}{g:x}{g:X}{g:o}{g:b}")?;
    write!(b, "{a:?}{c:?}{d:?}{e:?}{g:?}{a:e}{c:e}{d:e}{e:e}{g:e}{d:E}{e:E}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_radix_signed(b: &mut Buf, h: i8, i: i16, j: i32, k: i64, l: isize) -> fmt::Result {
    write!(b, "{h:x}{h:X}{h:o}{h:b}{i:x}{i:X}{i:o}{i:b}{j:x}{j:X}{j:o}{j:b}")?;
    write!(b, "{k:x}{k:X}{k:o}{k:b}{l:x}{l:X}{l:o}{l:b}")?;
    write!(b, "{h:?}{i:?}{j:?}{k:?}{l:?}{h:e}{i:e}{j:e}{k:e}{l:e}{j:E}{k:E}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn format_floats(x: f64, y: f32, z: u128) -> String {
    format!("{x}{y}{x:.2}{x:e}{x:?}{z}")
}

// Top plan T7a/b: derived `Debug` (the `debug_struct_fieldN_finish` /
// `debug_tuple_fieldN_finish` helpers, 1 to 5 fields), slices, arrays, `Option`,
// `Result`, tuples, and the `DebugList`/`DebugSet`/`DebugMap` builders, each with
// `{:?}` and `{:#?}` (the `PadAdapter` path).
#[derive(Debug)]
pub struct S1 {
    pub a: u8,
}
#[derive(Debug)]
pub struct S2 {
    pub a: u8,
    pub b: u16,
}
#[derive(Debug)]
pub struct S3 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}
#[derive(Debug)]
pub struct S4 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
    pub d: u64,
}
#[derive(Debug)]
pub struct S5 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
    pub d: u64,
    pub e: i8,
}
#[derive(Debug)]
pub struct T1(pub u8);
#[derive(Debug)]
pub struct T2(pub u8, pub u16);
#[derive(Debug)]
pub struct T3(pub u8, pub u16, pub u32);
#[derive(Debug)]
pub struct T4(pub u8, pub u16, pub u32, pub u64);
#[derive(Debug)]
pub struct T5(pub u8, pub u16, pub u32, pub u64, pub i8);
#[derive(Debug)]
pub struct Unit;
#[derive(Debug)]
pub enum E {
    A,
    B(u8),
    C { x: u8, y: u16 },
}

/// A user `Debug` through the list, set and map builders.
pub struct Coll(pub [u8; 2]);

impl fmt::Debug for Coll {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entry(&self.0[0]).entries(self.0.iter()).finish()?;
        f.debug_set().entry(&self.0[0]).entries(self.0.iter()).finish()?;
        f.debug_map()
            .entry(&self.0[0], &self.0[1])
            .key(&self.0[0])
            .value(&self.0[1])
            .entries(self.0.iter().map(|x| (x, x)))
            .finish()?;
        f.debug_struct("C").field("a", &self.0[0]).finish_non_exhaustive()?;
        f.debug_tuple("C").field(&self.0[0]).finish()
    }
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_derived(b: &mut Buf, s1: &S1, s2: &S2, s3: &S3, s4: &S4, s5: &S5) -> fmt::Result {
    write!(b, "{s1:?}{s2:?}{s3:?}{s4:?}{s5:?}")?;
    write!(b, "{s1:#?}{s2:#?}{s3:#?}{s4:#?}{s5:#?}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_derived_tuple(b: &mut Buf, t1: &T1, t2: &T2, t3: &T3, t4: &T4, t5: &T5) -> fmt::Result {
    write!(b, "{t1:?}{t2:?}{t3:?}{t4:?}{t5:?}")?;
    write!(b, "{t1:#?}{t2:#?}{t3:#?}{t4:#?}{t5:#?}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_derived_other(b: &mut Buf, u: &Unit, e: &E, c: &Coll) -> fmt::Result {
    write!(b, "{u:?}{e:?}{c:?}{u:#?}{e:#?}{c:#?}")
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn write_std_debug(
    b: &mut Buf,
    s: &[u8],
    a: &[u16; 3],
    o: Option<u8>,
    r: Result<u8, i8>,
    t: (u8, u16),
    st: &str,
) -> fmt::Result {
    write!(b, "{s:?}{a:?}{o:?}{r:?}{t:?}{st:?}")?;
    write!(b, "{s:#?}{a:#?}{o:#?}{r:#?}{t:#?}")
}
