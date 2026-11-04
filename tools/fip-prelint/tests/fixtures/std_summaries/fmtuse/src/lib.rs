// SPDX-License-Identifier: MIT OR Apache-2.0
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

/// `{:?}` of a derived `Debug`: `core` calls the fields through `&dyn Debug`, each
/// resolved to the field's type at this call (top plan T7a): passes.
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

/// `f64` and `f32` `Display`, precision and exponent formats (top plan T7c): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_float(b: &mut Buf, x: f64, y: f32) -> fmt::Result {
    write!(b, "{x} {y} {x:.3} {x:e} {y:?}")
}

/// `u128` and `i128` formats (top plan T7e): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_wide(b: &mut Buf, x: u128, y: i128) -> fmt::Result {
    write!(b, "{x} {y} {x:x} {y:?}")
}

/// Float math intrinsics (top plan T7d, an audited table entry): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn float_math(x: f64, y: f32) -> f64 {
    x.sqrt() + x.sin() + x.powi(3) + x.floor() + f64::from(y.cos().abs())
}

/// `f64::tan` calls the C library through a foreign declaration inside `std`
/// (`cmath::tan`), which is neither certified nor excluded: an error, not the table.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn float_tan(x: f64) -> f64 {
    x.tan()
}

/// A hasher without random state.
#[derive(Default)]
pub struct Fnv(pub u64);

impl core::hash::Hasher for Fnv {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &c in bytes {
            self.0 = (self.0 ^ u64::from(c)).wrapping_mul(0x100_0000_01b3);
        }
    }
}

type FnvMap = std::collections::HashMap<u8, u8, core::hash::BuildHasherDefault<Fnv>>;

/// An empty map dropped: `hashbrown`, a dependency of `std`, is analysed like `std`
/// (top plan T7h). It may free (`#[fbip]` allows that) and does not allocate: passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn empty_map_len() -> usize {
    let m: FnvMap = FnvMap::default();
    m.len()
}

/// The same under `#[fip]`: the drop may free (an error, not `⊤`).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn empty_map_fip() -> usize {
    let m: FnvMap = FnvMap::default();
    m.len()
}

/// `{:#?}` of a derived `Debug`: the fields are written through a `PadAdapter` over
/// the buffer (top plan T7b): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_debug_alt(b: &mut Buf, p: &Point) -> fmt::Result {
    write!(b, "{p:#?}")
}

#[derive(Debug)]
pub enum Shape {
    Dot,
    Line(u8),
    Rect { w: u8, h: u8 },
}

/// Slices, arrays, `Option`, `Result`, tuples and a derived enum: pass.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_debug_std(
    b: &mut Buf,
    s: &[u8],
    o: Option<u16>,
    r: Result<u8, i8>,
    t: (u8, u32),
    e: &Shape,
) -> fmt::Result {
    write!(b, "{s:?} {o:?} {r:?} {t:?} {e:?} {s:#?} {e:#?}")
}

/// A user `Debug` through `Formatter::debug_list`/`debug_map` and their builders:
/// passes.
pub struct Pairs(pub [u8; 2]);

impl fmt::Debug for Pairs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()?;
        f.debug_map().entry(&self.0[0], &self.0[1]).finish()
    }
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_debug_builders(b: &mut Buf, p: &Pairs) -> fmt::Result {
    write!(b, "{p:?} {p:#?}")
}

/// A `&dyn Debug` read from data: its concrete type is not known (`⊤`, a control).
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_debug_dyn(b: &mut Buf, v: &[&dyn fmt::Debug]) -> fmt::Result {
    match v.first() {
        Some(d) => write!(b, "{d:?}"),
        None => Ok(()),
    }
}

/// More than five fields: `debug_struct_fields_finish` takes a slice of `&dyn
/// Debug` (not seeded; `⊤`, a control).
#[derive(Debug)]
pub struct Six {
    pub a: u8,
    pub b: u8,
    pub c: u8,
    pub d: u8,
    pub e: u8,
    pub f: u8,
}

#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn write_debug_six(b: &mut Buf, s: &Six) -> fmt::Result {
    write!(b, "{s:?}")
}

std::thread_local! {
    static COUNTER: core::cell::Cell<u32> = const { core::cell::Cell::new(0) };
    static LAZY: core::cell::Cell<u32> = core::cell::Cell::new(u32::from(u8::MAX));
}

/// A `const` thread local: `LocalKey::with` calls the accessor read from the
/// `static` key (top plan T7g): passes.
#[cfg_attr(fip_prelint, fip::mark(kind = "fip"))]
pub fn thread_local_get() -> u32 {
    COUNTER.with(core::cell::Cell::get)
}

/// A lazily initialised thread local: its first access registers a destructor.
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn thread_local_lazy() -> u32 {
    LAZY.with(core::cell::Cell::get)
}

/// `HashMap::new` reads the thread-local random keys, initialised from the
/// operating system's random source (foreign functions inside `std`).
#[cfg_attr(fip_prelint, fip::mark(kind = "fbip"))]
pub fn hashmap_new() -> usize {
    std::collections::HashMap::<u8, u8>::new().len()
}
