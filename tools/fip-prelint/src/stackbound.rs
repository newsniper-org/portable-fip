// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Stack bounds from a build (limits plan L9; `cargo fip-prelint --stack`), without
//! dependencies: an `ar` reader for rlibs, a little-endian ELF reader for their
//! objects (`.stack_sizes` from `-Zemit-stack-sizes`, symbols, relocations; ELF64
//! x86_64 and AArch64, top plan T8a; ELF32 i386 and ARM), and the longest path over
//! the call graph.
//!
//! **Graph.** Nodes are the functions defined in the objects of the build's rlibs
//! (one `.text.<symbol>` section per function). Edges are the direct calls of the
//! machine code: the relocations of a function's section that name a function (a
//! defined function, the section of one, or an undefined symbol). Machine code
//! is used, not the MIR call graph, because codegen calls functions MIR does not
//! explore (measured: `precondition_check` functions at opt-level 0) and runtime
//! functions (`memcpy`, `memset`).
//!
//! **MIR mapping.** Every function a bound passes through must be listed in the
//! `.fip-stack` file of a crate of the build (written by the driver, `src/stack.rs`):
//! it is then the symbol of a MIR instance rustc codegened, whose body has no call
//! through a function pointer, no dynamic call, no unresolved call and no inline
//! assembly (calls a relocation cannot show). Otherwise the root is `⊤`.
//!
//! **Bound.** `Σ (frame + return address)` over the longest path from the root's
//! symbol, frames from `.stack_sizes` (a symbol in several objects: its maximum), the
//! return address 8 bytes on x86_64 and 4 on i386 (pushed by `call`; on i386 a
//! function without callees counts 4 more, [`leaf_extra`]) and 0 on AArch64 and ARM
//! (`bl` puts it in the link register; a callee that saves it pushes a frame record,
//! which its `.stack_sizes` value includes); other machines, Thumb code and other
//! formats are `⊤`. A symbol
//! without a frame size that the root's crate declares with `fip::stack_leaf` counts
//! the declared bytes (trusted, top plan T8b). `⊤` with the reason
//! for: recursion (a cycle), a call of a symbol not defined in the build's objects
//! (precompiled `std`, foreign or runtime functions), a function without a frame size
//! or without a MIR instance, an indirect call (above), a generic root. Calls of
//! diverging `core`/`alloc`/`std` functions (panic paths) are excluded, and the claim
//! says so; so are unwinding, signal and interrupt contexts.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

/// A bound and its longest path (labels with frames), or why there is none.
type Found = Result<(u64, Vec<(String, u64)>), String>;

const EM_386: u16 = 3;
const EM_ARM: u16 = 40;
const EM_X86_64: u16 = 62;
const EM_AARCH64: u16 = 183;

/// Bytes a call adds besides the callee's frame: the return address `call` pushes on
/// x86_64 (8) and i386 (4); none on AArch64 and ARM (`bl` puts it in the link
/// register; a callee that saves it pushes it inside its frame, measured on ARMv7:
/// `push {r11, lr}` is part of the `.stack_sizes` value).
pub fn return_address(machine: u16) -> Option<u64> {
    match machine {
        EM_X86_64 => Some(8),
        EM_386 => Some(4),
        EM_AARCH64 | EM_ARM => Some(0),
        _ => None,
    }
}

/// Bytes below its frame that a function without callees may still use: on i386,
/// position-independent code reads the PC with a `call` of the next instruction and a
/// `pop` (4 bytes, outside `.stack_sizes`; measured at opt-level 0). A function with
/// a callee covers them with that callee's return address.
pub fn leaf_extra(machine: u16) -> u64 {
    if machine == EM_386 { 4 } else { 0 }
}

/// The machine's name in messages.
pub fn machine_name(machine: u16) -> &'static str {
    match machine {
        EM_X86_64 => "x86_64",
        EM_AARCH64 => "AArch64",
        EM_386 => "i386",
        EM_ARM => "ARM",
        _ => "unknown",
    }
}

fn u16_at(b: &[u8], o: usize) -> Option<u16> {
    Some(u16::from_le_bytes(b.get(o..o + 2)?.try_into().ok()?))
}
fn u32_at(b: &[u8], o: usize) -> Option<u32> {
    Some(u32::from_le_bytes(b.get(o..o + 4)?.try_into().ok()?))
}
fn u64_at(b: &[u8], o: usize) -> Option<u64> {
    Some(u64::from_le_bytes(b.get(o..o + 8)?.try_into().ok()?))
}

/// Members of an `ar` archive (GNU format, as rustc writes rlibs): (name, data).
pub fn ar_members(data: &[u8]) -> Result<Vec<(String, &[u8])>, String> {
    if !data.starts_with(b"!<arch>\n") {
        return Err("not an ar archive".to_string());
    }
    let mut out = Vec::new();
    let mut long_names: &[u8] = &[];
    let mut pos = 8;
    while pos + 60 <= data.len() {
        let h = &data[pos..pos + 60];
        let name = String::from_utf8_lossy(&h[0..16]).trim_end().to_string();
        let size: usize = String::from_utf8_lossy(&h[48..58])
            .trim()
            .parse()
            .map_err(|_| "bad ar member size".to_string())?;
        let start = pos + 60;
        let end = start
            .checked_add(size)
            .filter(|&e| e <= data.len())
            .ok_or("truncated ar member")?;
        let body = &data[start..end];
        if name == "//" {
            long_names = body;
        } else if name != "/" && name != "/SYM64/" {
            let name = if let Some(off) = name.strip_prefix('/') {
                let off: usize = off.parse().map_err(|_| "bad ar long name")?;
                let rest = long_names.get(off..).ok_or("bad ar long name offset")?;
                let n = rest.iter().position(|&c| c == b'\n').unwrap_or(rest.len());
                String::from_utf8_lossy(&rest[..n])
                    .trim_end_matches('/')
                    .to_string()
            } else {
                name.trim_end_matches('/').to_string()
            };
            out.push((name, body));
        }
        pos = end + (end & 1);
    }
    Ok(out)
}

struct Section {
    name: String,
    kind: u32,
    flags: u64,
    offset: usize,
    size: usize,
    link: u32,
    info: u32,
}

#[derive(Clone)]
struct Sym {
    name: String,
    kind: u8,
    shndx: u16,
    value: u64,
    size: u64,
}

const SHT_SYMTAB: u32 = 2;
const SHT_RELA: u32 = 4;
const SHT_REL: u32 = 9;
const SHF_EXECINSTR: u64 = 4;
const STT_FUNC: u8 = 2;
const STT_SECTION: u8 = 3;

/// What one object contributes: per defined function, its frame size (if any) and
/// the functions its code refers to (by symbol name).
#[derive(Default, Debug)]
pub struct Object {
    pub machine: u16,
    pub frames: HashMap<String, u64>,
    pub calls: HashMap<String, BTreeSet<String>>,
    pub defined: HashSet<String>,
}

fn cstr(b: &[u8], o: usize) -> String {
    let rest = b.get(o..).unwrap_or(&[]);
    let n = rest.iter().position(|&c| c == 0).unwrap_or(rest.len());
    String::from_utf8_lossy(&rest[..n]).into_owned()
}

fn uleb(b: &[u8], mut o: usize) -> Option<(u64, usize)> {
    let mut v = 0u64;
    let mut shift = 0;
    loop {
        let byte = *b.get(o)?;
        o += 1;
        v |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Some((v, o));
        }
        shift += 7;
        if shift > 63 {
            return None;
        }
    }
}

/// Reads a relocatable little-endian ELF object: ELF64 x86_64 or AArch64 (`RELA`
/// relocations), ELF32 i386 or ARM (`REL` relocations, addends in the relocated data;
/// top plan T8 residue).
pub fn read_object(b: &[u8]) -> Result<Object, String> {
    if !b.starts_with(b"\x7fELF") || b.get(5) != Some(&1) {
        return Err("not a little-endian ELF object".to_string());
    }
    let wide = match b.get(4) {
        Some(2) => true,
        Some(1) => false,
        _ => return Err("not an ELF32 or ELF64 object".to_string()),
    };
    let machine = u16_at(b, 18).ok_or("truncated ELF header")?;
    if return_address(machine).is_none() {
        return Err(format!(
            "ELF machine {machine}: only x86_64, AArch64, i386 and ARM objects are supported"
        ));
    }
    if wide != matches!(machine, EM_X86_64 | EM_AARCH64) {
        return Err(format!(
            "ELF machine {machine} in an object of the other class"
        ));
    }
    // A word (address, offset, size) of the object's class.
    let word = |o: usize| -> Option<u64> {
        if wide {
            u64_at(b, o)
        } else {
            u32_at(b, o).map(u64::from)
        }
    };
    let to_usize = |v: u64| usize::try_from(v).unwrap_or(usize::MAX);
    let (shoff, shentsize, shnum, shstrndx) = if wide {
        (
            word(0x28).ok_or("truncated")?,
            u16_at(b, 0x3A).ok_or("truncated")?,
            u16_at(b, 0x3C).ok_or("truncated")?,
            u16_at(b, 0x3E).ok_or("truncated")?,
        )
    } else {
        (
            word(0x20).ok_or("truncated")?,
            u16_at(b, 0x2E).ok_or("truncated")?,
            u16_at(b, 0x30).ok_or("truncated")?,
            u16_at(b, 0x32).ok_or("truncated")?,
        )
    };
    let (shoff, shentsize, shnum, shstrndx) = (
        to_usize(shoff),
        usize::from(shentsize),
        usize::from(shnum),
        usize::from(shstrndx),
    );
    // Section header fields: flags, offset, size, link, info.
    let (f_flags, f_off, f_size, f_link, f_info) = if wide {
        (8, 24, 32, 40, 44)
    } else {
        (8, 16, 20, 24, 28)
    };
    let mut secs = Vec::with_capacity(shnum);
    for i in 0..shnum {
        let o = shoff + i * shentsize;
        secs.push(Section {
            name: String::new(),
            kind: u32_at(b, o + 4).ok_or("truncated section header")?,
            flags: word(o + f_flags).ok_or("truncated section header")?,
            offset: to_usize(word(o + f_off).ok_or("truncated section header")?),
            size: to_usize(word(o + f_size).ok_or("truncated section header")?),
            link: u32_at(b, o + f_link).ok_or("truncated section header")?,
            info: u32_at(b, o + f_info).ok_or("truncated section header")?,
        });
        let name_off = u32_at(b, o).ok_or("truncated section header")?;
        secs[i].name = name_off.to_string();
    }
    let shstr = secs.get(shstrndx).ok_or("no section name table")?;
    let (so, ss) = (shstr.offset, shstr.size);
    let shstr_data = b
        .get(so..so + ss)
        .ok_or("truncated section names")?
        .to_vec();
    for s in &mut secs {
        let off: usize = s.name.parse().unwrap_or(0);
        s.name = cstr(&shstr_data, off);
    }
    // Symbols.
    let symtab = secs
        .iter()
        .find(|s| s.kind == SHT_SYMTAB)
        .ok_or("no symbol table")?;
    let strtab = secs.get(symtab.link as usize).ok_or("no string table")?;
    let strdata = b
        .get(strtab.offset..strtab.offset + strtab.size)
        .ok_or("truncated string table")?;
    let sym_size = if wide { 24 } else { 16 };
    let mut syms = Vec::new();
    for k in 0..symtab.size / sym_size {
        let o = symtab.offset + k * sym_size;
        let name = cstr(strdata, u32_at(b, o).ok_or("truncated symbol")? as usize);
        let sym = if wide {
            Sym {
                name,
                kind: b.get(o + 4).ok_or("truncated symbol")? & 0xf,
                shndx: u16_at(b, o + 6).ok_or("truncated symbol")?,
                value: u64_at(b, o + 8).ok_or("truncated symbol")?,
                size: u64_at(b, o + 16).ok_or("truncated symbol")?,
            }
        } else {
            Sym {
                name,
                kind: b.get(o + 12).ok_or("truncated symbol")? & 0xf,
                shndx: u16_at(b, o + 14).ok_or("truncated symbol")?,
                value: u64::from(u32_at(b, o + 4).ok_or("truncated symbol")?),
                size: u64::from(u32_at(b, o + 8).ok_or("truncated symbol")?),
            }
        };
        syms.push(sym);
    }
    let exec = |idx: u16| {
        secs.get(usize::from(idx))
            .is_some_and(|s| s.flags & SHF_EXECINSTR != 0)
    };
    // Functions per executable section.
    let mut funcs_in: HashMap<u16, Vec<&Sym>> = HashMap::new();
    let mut obj = Object {
        machine,
        ..Object::default()
    };
    for s in &syms {
        if s.kind == STT_FUNC && s.shndx != 0 && exec(s.shndx) {
            funcs_in.entry(s.shndx).or_default().push(s);
            obj.defined.insert(s.name.clone());
        }
    }
    let func_at = |sec: u16, off: u64| -> Vec<&Sym> {
        funcs_in
            .get(&sec)
            .map(|fs| {
                fs.iter()
                    .filter(|f| off >= f.value && (off < f.value + f.size.max(1)))
                    .copied()
                    .collect()
            })
            .unwrap_or_default()
    };
    for rs in &secs {
        let explicit = rs.kind == SHT_RELA;
        if !(explicit || rs.kind == SHT_REL) || rs.link as usize >= secs.len() {
            continue;
        }
        let target = rs.info as usize;
        let Some(tsec) = secs.get(target) else {
            continue;
        };
        let tdata = b.get(tsec.offset..tsec.offset + tsec.size).unwrap_or(&[]);
        // (offset, symbol, type, addend) of each relocation.
        let ent = match (wide, explicit) {
            (true, true) => 24,
            (true, false) => 16,
            (false, true) => 12,
            (false, false) => 8,
        };
        let mut relocs: Vec<(u64, usize, u32, i64)> = Vec::new();
        for k in 0..rs.size / ent {
            let o = rs.offset + k * ent;
            let (off, sym, rtype) = if wide {
                let info = u64_at(b, o + 8).ok_or("truncated relocation")?;
                (
                    u64_at(b, o).ok_or("truncated relocation")?,
                    usize::try_from(info >> 32).map_err(|e| e.to_string())?,
                    u32::try_from(info & 0xffff_ffff).map_err(|e| e.to_string())?,
                )
            } else {
                let info = u32_at(b, o + 4).ok_or("truncated relocation")?;
                (
                    u64::from(u32_at(b, o).ok_or("truncated relocation")?),
                    usize::try_from(info >> 8).map_err(|e| e.to_string())?,
                    info & 0xff,
                )
            };
            // Thumb branches encode their offset differently: not read (`⊤`).
            if machine == EM_ARM && matches!(rtype, 10 | 30 | 102 | 103) {
                return Err(format!(
                    "ARM relocation type {rtype} (a Thumb branch) is not supported"
                ));
            }
            let addend = match (wide, explicit) {
                (true, true) => i64::from_le_bytes(
                    b.get(o + 16..o + 24)
                        .and_then(|s| s.try_into().ok())
                        .ok_or("truncated relocation")?,
                ),
                (false, true) => i64::from(i32::from_le_bytes(
                    b.get(o + 8..o + 12)
                        .and_then(|s| s.try_into().ok())
                        .ok_or("truncated relocation")?,
                )),
                // `REL`: the addend is stored in the relocated data.
                _ => usize::try_from(off)
                    .ok()
                    .and_then(|p| implicit_addend(machine, rtype, tdata, p))
                    .ok_or("relocation outside its section")?,
            };
            relocs.push((off, sym, rtype, addend));
        }
        if tsec.name == ".stack_sizes" {
            // Entries: an address of the class's size (relocated) and a ULEB128 size.
            let addr = if wide { 8 } else { 4 };
            for (off, si, _, addend) in &relocs {
                let Some(sym) = syms.get(*si) else { continue };
                let Some((size, _)) = usize::try_from(*off + addr)
                    .ok()
                    .and_then(|p| uleb(tdata, p))
                else {
                    continue;
                };
                let names: Vec<String> = if sym.kind == STT_SECTION {
                    func_at(sym.shndx, u64::try_from(*addend).unwrap_or(0))
                        .iter()
                        .map(|f| f.name.clone())
                        .collect()
                } else {
                    vec![sym.name.clone()]
                };
                for n in names {
                    let e = obj.frames.entry(n).or_insert(0);
                    *e = (*e).max(size);
                }
            }
            continue;
        }
        if !exec(u16::try_from(target).unwrap_or(0)) {
            continue;
        }
        for (off, si, rtype, addend) in &relocs {
            let Some(sym) = syms.get(*si) else { continue };
            let callers = func_at(u16::try_from(target).unwrap_or(0), *off);
            // PC-relative relocations address `S + A - P`: the target's offset in its
            // section is `A` plus the distance from the place to the PC the
            // instruction uses (x86_64 and i386: the end of the 4-byte field; ARM
            // `BL`/`B`: the place plus 8). AArch64 and absolute relocations: `A`.
            let bias = match machine {
                EM_X86_64 if matches!(rtype, 2 | 4 | 9 | 41 | 42) => 4,
                EM_386 if matches!(rtype, 2 | 4) => 4,
                EM_ARM if matches!(rtype, 28 | 29) => 8,
                _ => 0,
            };
            let callees: Vec<String> = if sym.shndx == 0 {
                // The GOT's address (`R_386_GOTPC`, `R_ARM_GOTPC`) is data, not code.
                if sym.name.is_empty() || sym.name == "_GLOBAL_OFFSET_TABLE_" {
                    Vec::new()
                } else {
                    vec![sym.name.clone()]
                }
            } else if sym.kind == STT_FUNC {
                vec![sym.name.clone()]
            } else if sym.kind == STT_SECTION && exec(sym.shndx) {
                let t = u64::try_from(*addend + bias).unwrap_or(0);
                func_at(sym.shndx, t)
                    .iter()
                    .filter(|f| {
                        // A reference into the caller's own body (a label) is not a call.
                        !(usize::from(sym.shndx) == target
                            && callers.iter().any(|c| c.name == f.name)
                            && t != f.value)
                    })
                    .map(|f| f.name.clone())
                    .collect()
            } else {
                Vec::new()
            };
            for c in &callers {
                for t in &callees {
                    obj.calls
                        .entry(c.name.clone())
                        .or_default()
                        .insert(t.clone());
                }
            }
        }
    }
    Ok(obj)
}

/// The addend of a `REL` relocation of `rtype` at `off` in the relocated data `data`
/// (ELF32 i386 and ARM); `None` if the data is too short.
fn implicit_addend(machine: u16, rtype: u32, data: &[u8], off: usize) -> Option<i64> {
    let w = u32_at(data, off)?;
    match (machine, rtype) {
        // `R_ARM_CALL`, `R_ARM_JUMP24`: `imm24 << 2`, sign-extended.
        (EM_ARM, 28 | 29) => {
            let imm = i64::from(w & 0x00ff_ffff) << 2;
            Some(if imm & (1 << 25) != 0 {
                imm - (1 << 26)
            } else {
                imm
            })
        }
        // A 32-bit word (`R_386_32`, `R_386_PC32`, `R_386_PLT32`, `R_ARM_ABS32`,
        // `R_ARM_REL32`, ..): sign-extended.
        _ => Some(i64::from(i32::from_le_bytes(w.to_le_bytes()))),
    }
}

/// The path of a Rust v0 symbol made of nested values and a crate root only
/// (`_RNvCs<disambiguator>_7___rustc12___rust_alloc` is `__rustc::__rust_alloc`);
/// `None` for anything else (generic arguments, impls, Punycode).
pub fn v0_path(sym: &str) -> Option<String> {
    fn ident(s: &[u8], i: &mut usize) -> Option<String> {
        let start = *i;
        while s.get(*i)?.is_ascii_digit() {
            *i += 1;
        }
        let n: usize = std::str::from_utf8(&s[start..*i]).ok()?.parse().ok()?;
        if s.get(*i) == Some(&b'_') {
            *i += 1;
        }
        let id = s.get(*i..*i + n)?;
        *i += n;
        String::from_utf8(id.to_vec()).ok()
    }
    fn disambiguator(s: &[u8], i: &mut usize) -> Option<()> {
        if s.get(*i) == Some(&b's') {
            *i += 1;
            while *s.get(*i)? != b'_' {
                *i += 1;
            }
            *i += 1;
        }
        Some(())
    }
    fn path(s: &[u8], i: &mut usize, depth: usize) -> Option<Vec<String>> {
        if depth > 16 {
            return None;
        }
        match *s.get(*i)? {
            b'C' => {
                *i += 1;
                disambiguator(s, i)?;
                Some(vec![ident(s, i)?])
            }
            b'N' => {
                *i += 2;
                let mut p = path(s, i, depth + 1)?;
                disambiguator(s, i)?;
                p.push(ident(s, i)?);
                Some(p)
            }
            _ => None,
        }
    }
    let s = sym.strip_prefix("_R")?.as_bytes();
    let mut i = 0;
    let p = path(s, &mut i, 0)?;
    // A trailing instantiating crate is allowed; anything else is not read.
    (i == s.len() || s.get(i) == Some(&b'C')).then(|| p.join("::"))
}

/// A `.fip-stack` file of one crate (see `src/stack.rs`).
#[derive(Default, Debug)]
pub struct Record {
    pub krate: String,
    pub target: String,
    pub opt_level: String,
    pub rlib: String,
    /// (label, symbol or the reason it has none).
    pub roots: Vec<(String, Result<String, String>)>,
    /// symbol → (label, reason it cannot be bounded).
    pub fns: Vec<(String, String, Option<String>)>,
    pub div: Vec<String>,
    /// symbol → label of a function called but not codegened in the crate.
    pub ext: Vec<(String, String)>,
    /// Declared stack leaves: (symbol, bytes, evidence).
    pub leaves: Vec<(String, u64, String)>,
    /// Generic roots: (label, key).
    pub generics: Vec<(String, String)>,
    /// Instances of generic roots codegened here: (key, label, symbol).
    pub insts: Vec<(String, String, String)>,
    /// An executable's objects: (directory, file stem).
    pub objs: Option<(String, String)>,
}

pub fn parse_record(text: &str) -> Result<Record, String> {
    let mut r = Record::default();
    let mut lines = text.lines();
    if lines.next() != Some("fip-prelint stack 2") {
        return Err("unknown .fip-stack format".to_string());
    }
    for l in lines {
        let f: Vec<&str> = l.split('\t').collect();
        match f.as_slice() {
            ["crate", v] => r.krate = (*v).to_string(),
            ["target", v] => r.target = (*v).to_string(),
            ["opt-level", v] => r.opt_level = (*v).to_string(),
            ["rlib", v] => r.rlib = (*v).to_string(),
            ["root", label, "-", why] => r
                .roots
                .push(((*label).to_string(), Err((*why).to_string()))),
            ["root", label, sym] => r.roots.push(((*label).to_string(), Ok((*sym).to_string()))),
            ["fn", sym, label] => r.fns.push(((*sym).to_string(), (*label).to_string(), None)),
            ["fn", sym, label, why] => r.fns.push((
                (*sym).to_string(),
                (*label).to_string(),
                Some((*why).to_string()),
            )),
            ["div", sym] => r.div.push((*sym).to_string()),
            ["ext", sym, label] => r.ext.push(((*sym).to_string(), (*label).to_string())),
            ["leaf", sym, bytes, evidence] => r.leaves.push((
                (*sym).to_string(),
                bytes
                    .parse()
                    .map_err(|_| format!("malformed .fip-stack line: {l}"))?,
                (*evidence).to_string(),
            )),
            ["generic", label, key] => r.generics.push(((*label).to_string(), (*key).to_string())),
            ["inst", key, label, sym] => {
                r.insts
                    .push(((*key).to_string(), (*label).to_string(), (*sym).to_string()))
            }
            ["objs", dir, stem] => r.objs = Some(((*dir).to_string(), (*stem).to_string())),
            _ => return Err(format!("malformed .fip-stack line: {l}")),
        }
    }
    Ok(r)
}

/// The whole build: functions of every object, and the MIR facts of every record.
#[derive(Default)]
pub struct Build {
    machine: Option<u16>,
    frames: HashMap<String, u64>,
    calls: HashMap<String, BTreeSet<String>>,
    defined: HashSet<String>,
    mapped: HashMap<String, (String, Option<String>)>,
    labels: HashMap<String, String>,
    div: HashSet<String>,
    /// Objects that could not be read: every bound is `⊤`.
    pub unreadable: Vec<String>,
}

impl Build {
    pub fn add_object(&mut self, o: Object) {
        match self.machine {
            None => self.machine = Some(o.machine),
            Some(m) if m != o.machine => self.unreadable.push(format!(
                "objects of two machines ({} and {})",
                machine_name(m),
                machine_name(o.machine)
            )),
            Some(_) => {}
        }
        for (n, f) in o.frames {
            let e = self.frames.entry(n).or_insert(0);
            *e = (*e).max(f);
        }
        for (n, cs) in o.calls {
            self.calls.entry(n).or_default().extend(cs);
        }
        self.defined.extend(o.defined);
    }

    pub fn add_rlib(&mut self, path: &Path) {
        let data = match std::fs::read(path) {
            Ok(d) => d,
            Err(e) => {
                self.unreadable.push(format!("{}: {e}", path.display()));
                return;
            }
        };
        let members = match ar_members(&data) {
            Ok(m) => m,
            Err(e) => {
                self.unreadable.push(format!("{}: {e}", path.display()));
                return;
            }
        };
        for (name, body) in members {
            if !body.starts_with(b"\x7fELF") {
                continue;
            }
            match read_object(body) {
                Ok(o) => self.add_object(o),
                Err(e) => self
                    .unreadable
                    .push(format!("{}({name}): {e}", path.display())),
            }
        }
    }

    /// The objects of an executable (`<dir>/<stem>.*.rcgu.o`, kept by `-Csave-temps`).
    pub fn add_objects(&mut self, dir: &Path, stem: &str) {
        let prefix = format!("{stem}.");
        let mut files: Vec<std::path::PathBuf> = match std::fs::read_dir(dir) {
            Ok(rd) => rd
                .flatten()
                .map(|e| e.path())
                .filter(|p| {
                    p.file_name().is_some_and(|n| {
                        let n = n.to_string_lossy();
                        n.starts_with(&prefix) && n.ends_with(".rcgu.o")
                    })
                })
                .collect(),
            Err(e) => {
                self.unreadable.push(format!("{}: {e}", dir.display()));
                return;
            }
        };
        files.sort();
        if files.is_empty() {
            self.unreadable.push(format!(
                "{}: no objects `{prefix}*.rcgu.o` (`-Csave-temps`)",
                dir.display()
            ));
        }
        for f in files {
            match std::fs::read(&f)
                .map_err(|e| e.to_string())
                .and_then(|b| read_object(&b))
            {
                Ok(o) => self.add_object(o),
                Err(e) => self.unreadable.push(format!("{}: {e}", f.display())),
            }
        }
    }

    /// Return-address bytes per call for the build's machine.
    pub fn return_address(&self) -> u64 {
        self.machine.and_then(return_address).unwrap_or(0)
    }

    /// The build's machine, for messages.
    /// [`leaf_extra`] of the build's machine.
    pub fn leaf_extra(&self) -> u64 {
        self.machine.map_or(0, leaf_extra)
    }

    pub fn machine(&self) -> &'static str {
        self.machine.map_or("unknown", machine_name)
    }

    pub fn add_record(&mut self, r: &Record) {
        for (sym, label, why) in &r.fns {
            self.mapped
                .insert(sym.clone(), (label.clone(), why.clone()));
        }
        self.div.extend(r.div.iter().cloned());
        for (sym, label) in &r.ext {
            self.labels.insert(sym.clone(), label.clone());
        }
    }

    fn label<'a>(&'a self, sym: &'a str) -> &'a str {
        self.mapped
            .get(sym)
            .map(|(l, _)| l.as_str())
            .or_else(|| self.labels.get(sym).map(String::as_str))
            .unwrap_or(sym)
    }

    /// The bound of the function `sym` and its longest path (labels with frames), or
    /// why there is none.
    #[cfg(test)]
    pub fn bound(&self, sym: &str) -> Found {
        self.bound_with(sym, &HashMap::new())
    }

    /// [`Build::bound`] with the declared stack leaves of the root's crate:
    /// symbol → bytes (the return address included).
    pub fn bound_with(&self, sym: &str, leaves: &HashMap<String, u64>) -> Found {
        if let Some(u) = self.unreadable.first() {
            return Err(format!("an object of the build could not be read: {u}"));
        }
        if !self.defined.contains(sym) {
            return Err(
                "the root has no symbol in the objects of this build (not codegened on its own: inlined, or kept only for cross-crate inlining at this opt-level)"
                    .to_string(),
            );
        }
        let mut memo: HashMap<String, Found> = HashMap::new();
        let mut on_path: Vec<String> = Vec::new();
        self.visit(sym, leaves, &mut memo, &mut on_path)
    }

    fn visit(
        &self,
        sym: &str,
        leaves: &HashMap<String, u64>,
        memo: &mut HashMap<String, Found>,
        on_path: &mut Vec<String>,
    ) -> Found {
        if let Some(r) = memo.get(sym) {
            return r.clone();
        }
        if let Some(i) = on_path.iter().position(|s| s == sym) {
            let cycle: Vec<&str> = on_path[i..]
                .iter()
                .map(|s| self.label(s))
                .chain(std::iter::once(self.label(sym)))
                .collect();
            return Err(format!("recursion: `{}`", cycle.join("` -> `")));
        }
        let r = self.visit_new(sym, leaves, memo, on_path);
        memo.insert(sym.to_string(), r.clone());
        r
    }

    fn visit_new(
        &self,
        sym: &str,
        leaves: &HashMap<String, u64>,
        memo: &mut HashMap<String, Found>,
        on_path: &mut Vec<String>,
    ) -> Found {
        if !self.defined.contains(sym)
            && let Some(&bytes) = leaves.get(sym)
        {
            return Ok((
                bytes,
                vec![(format!("{} (declared stack leaf)", self.label(sym)), bytes)],
            ));
        }
        if !self.defined.contains(sym) {
            return Err(format!(
                "`{}` has no frame size: it is not defined in the objects of this build (precompiled standard library, foreign or runtime function)",
                self.label(sym)
            ));
        }
        let Some((label, why)) = self.mapped.get(sym) else {
            let shown = match v0_path(sym) {
                // The allocator shim rustc generates for an executable (top plan T8f).
                Some(p) if p.starts_with("__rustc::") => {
                    format!("`{p}` (the allocator shim of the executable, symbol `{sym}`)")
                }
                Some(p) => format!("`{p}` (symbol `{sym}`)"),
                None => format!("`{sym}`"),
            };
            return Err(format!(
                "{shown} is defined in the build but is not a function rustc codegened from MIR for a crate the driver compiled"
            ));
        };
        if let Some(why) = why {
            return Err(format!("`{label}` contains {why}"));
        }
        let Some(&frame) = self.frames.get(sym) else {
            return Err(format!("`{label}` has no `.stack_sizes` entry"));
        };
        on_path.push(sym.to_string());
        let mut best: (u64, Vec<(String, u64)>) = (0, Vec::new());
        let callees: Vec<String> = self
            .calls
            .get(sym)
            .map(|c| c.iter().cloned().collect())
            .unwrap_or_default();
        for c in callees {
            if self.div.contains(&c) {
                continue;
            }
            match self.visit(&c, leaves, memo, on_path) {
                Ok(b) if b.0 > best.0 || best.1.is_empty() => best = b,
                Ok(_) => {}
                Err(e) => {
                    on_path.pop();
                    return Err(e);
                }
            }
        }
        on_path.pop();
        let mut path = vec![(label.clone(), frame)];
        path.extend(best.1);
        let extra = self.leaf_extra();
        Ok((frame + self.return_address() + best.0.max(extra), path))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v0_paths() {
        assert_eq!(
            v0_path("_RNvCs5fGHjzWXRav_7___rustc12___rust_alloc").as_deref(),
            Some("__rustc::__rust_alloc")
        );
        assert_eq!(
            v0_path("_RNvCskTneyE8Q88p_5chain9chain_top").as_deref(),
            Some("chain::chain_top")
        );
        assert_eq!(
            v0_path("_RINvNtCs5yrd3dq0xpX_4core4hint9black_boxQAyj20_E"),
            None
        );
        assert_eq!(v0_path("memcpy"), None);
    }

    #[test]
    fn uleb128() {
        assert_eq!(uleb(&[0x08], 0), Some((8, 1)));
        assert_eq!(uleb(&[0x98, 0x02], 0), Some((280, 2)));
        assert_eq!(uleb(&[0x80], 0), None);
    }

    #[test]
    fn ar_long_names() {
        let mut a = b"!<arch>\n".to_vec();
        let mut member = |name: &str, body: &[u8]| {
            let mut h = format!(
                "{name:<16}{:<12}{:<6}{:<6}{:<8}{:<10}`\n",
                0,
                0,
                0,
                644,
                body.len()
            );
            h.truncate(60);
            a.extend_from_slice(h.as_bytes());
            a.extend_from_slice(body);
            if body.len() % 2 == 1 {
                a.push(b'\n');
            }
        };
        member("//", b"a-very-long-member-name.rcgu.o/\n");
        member("/0", b"\x7fELF");
        member("lib.rmeta/", b"meta");
        let m = ar_members(&a).unwrap();
        assert_eq!(m.len(), 2);
        assert_eq!(m[0].0, "a-very-long-member-name.rcgu.o");
        assert_eq!(m[0].1, b"\x7fELF");
        assert_eq!(m[1].0, "lib.rmeta");
    }

    #[test]
    fn record_round_trip() {
        let r = parse_record(
            "fip-prelint stack 2\ncrate\tc\ntarget\tx86_64-unknown-linux-gnu\nopt-level\tNo\nrlib\t/x/libc.rlib\nroot\tc::f\t_RNv1f\nroot\tc::g\t-\tgeneric\nfn\t_RNv1f\tc::f\nfn\t_RNv1h\tc::h\ta call through a function pointer\ndiv\t_RNvpanic\n",
        )
        .unwrap();
        assert_eq!(r.roots.len(), 2);
        assert_eq!(r.roots[1].1, Err("generic".to_string()));
        assert_eq!(
            r.fns[1].2.as_deref(),
            Some("a call through a function pointer")
        );
        assert!(parse_record("fip-prelint stack 1\n").is_err());
        let r = parse_record(
            "fip-prelint stack 2\nleaf\tmemcpy\t64\taudit\ngeneric\tc::g\tk1\ninst\tk1\tc::g::<u8>\t_RIg\nobjs\t/d\tc-1\n",
        )
        .unwrap();
        assert_eq!(r.leaves[0].1, 64);
        assert_eq!(r.insts[0].0, r.generics[0].1);
        assert_eq!(r.objs, Some(("/d".to_string(), "c-1".to_string())));
    }

    fn build(edges: &[(&str, &[&str])], frames: &[(&str, u64)]) -> Build {
        let mut b = Build {
            machine: Some(EM_X86_64),
            ..Build::default()
        };
        for (f, cs) in edges {
            b.calls.insert(
                (*f).to_string(),
                cs.iter().map(|c| (*c).to_string()).collect(),
            );
        }
        for (f, n) in frames {
            b.frames.insert((*f).to_string(), *n);
            b.defined.insert((*f).to_string());
            b.mapped.insert((*f).to_string(), ((*f).to_string(), None));
        }
        b
    }

    #[test]
    fn longest_path() {
        let b = build(
            &[
                ("top", &["mid", "small"]),
                ("mid", &["leaf"]),
                ("small", &[]),
            ],
            &[("top", 8), ("mid", 104), ("leaf", 296), ("small", 500)],
        );
        // top + max(mid + leaf, small), each with its return address.
        let (n, path) = b.bound("top").unwrap();
        assert_eq!(n, (8 + 8) + (500 + 8));
        assert_eq!(path[1].0, "small");
        let (n, _) = b.bound("mid").unwrap();
        assert_eq!(n, (104 + 8) + (296 + 8));
    }

    #[test]
    fn tops() {
        let mut b = build(&[("a", &["b"]), ("b", &["a"])], &[("a", 8), ("b", 8)]);
        assert!(b.bound("a").unwrap_err().starts_with("recursion"));
        b.calls
            .insert("c".to_string(), ["memset".to_string()].into());
        b.frames.insert("c".to_string(), 0);
        b.defined.insert("c".to_string());
        b.mapped.insert("c".to_string(), ("c".to_string(), None));
        assert!(
            b.bound("c")
                .unwrap_err()
                .contains("not defined in the objects")
        );
        let leaves: HashMap<String, u64> = [("memset".to_string(), 40)].into();
        assert_eq!(b.bound_with("c", &leaves).unwrap().0, 8 + 40);
        b.machine = Some(EM_AARCH64);
        assert_eq!(b.bound_with("c", &leaves).unwrap().0, 40);
        b.machine = Some(EM_X86_64);
        b.div.insert("memset".to_string());
        assert_eq!(b.bound("c").unwrap().0, 8);
        b.mapped.insert(
            "c".to_string(),
            ("c".to_string(), Some("inline assembly".to_string())),
        );
        assert!(b.bound("c").unwrap_err().contains("inline assembly"));
    }
}
