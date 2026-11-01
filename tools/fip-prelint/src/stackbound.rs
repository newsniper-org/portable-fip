// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Stack bounds from a build (limits plan L9; `cargo fip-prelint --stack`), without
//! dependencies: an `ar` reader for rlibs, an ELF64 little-endian reader for their
//! objects (`.stack_sizes` from `-Zemit-stack-sizes`, symbols, relocations), and the
//! longest path over the call graph.
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
//! return address 8 bytes (x86_64; other machines are `⊤`). `⊤` with the reason
//! for: recursion (a cycle), a call of a symbol not defined in the build's objects
//! (precompiled `std`, foreign or runtime functions), a function without a frame size
//! or without a MIR instance, an indirect call (above), a generic root. Calls of
//! diverging `core`/`alloc`/`std` functions (panic paths) are excluded, and the claim
//! says so; so are unwinding, signal and interrupt contexts.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

/// Return address pushed by a call (x86_64).
pub const RETURN_ADDRESS: u64 = 8;
const EM_X86_64: u16 = 62;

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
const SHF_EXECINSTR: u64 = 4;
const STT_FUNC: u8 = 2;
const STT_SECTION: u8 = 3;

/// What one object contributes: per defined function, its frame size (if any) and
/// the functions its code refers to (by symbol name).
#[derive(Default, Debug)]
pub struct Object {
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

/// Reads a relocatable ELF64 little-endian x86_64 object.
pub fn read_object(b: &[u8]) -> Result<Object, String> {
    if !b.starts_with(b"\x7fELF") || b.get(4) != Some(&2) || b.get(5) != Some(&1) {
        return Err("not an ELF64 little-endian object".to_string());
    }
    let machine = u16_at(b, 18).ok_or("truncated ELF header")?;
    if machine != EM_X86_64 {
        return Err(format!(
            "ELF machine {machine}: only x86_64 objects are supported"
        ));
    }
    let shoff = usize::try_from(u64_at(b, 0x28).ok_or("truncated")?).map_err(|e| e.to_string())?;
    let shentsize = usize::from(u16_at(b, 0x3A).ok_or("truncated")?);
    let shnum = usize::from(u16_at(b, 0x3C).ok_or("truncated")?);
    let shstrndx = usize::from(u16_at(b, 0x3E).ok_or("truncated")?);
    let mut secs = Vec::with_capacity(shnum);
    for i in 0..shnum {
        let o = shoff + i * shentsize;
        let to_usize = |v: u64| usize::try_from(v).unwrap_or(usize::MAX);
        secs.push(Section {
            name: String::new(),
            kind: u32_at(b, o + 4).ok_or("truncated section header")?,
            flags: u64_at(b, o + 8).ok_or("truncated section header")?,
            offset: to_usize(u64_at(b, o + 24).ok_or("truncated section header")?),
            size: to_usize(u64_at(b, o + 32).ok_or("truncated section header")?),
            link: u32_at(b, o + 40).ok_or("truncated section header")?,
            info: u32_at(b, o + 44).ok_or("truncated section header")?,
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
    let mut syms = Vec::new();
    for k in 0..symtab.size / 24 {
        let o = symtab.offset + k * 24;
        syms.push(Sym {
            name: cstr(strdata, u32_at(b, o).ok_or("truncated symbol")? as usize),
            kind: b.get(o + 4).ok_or("truncated symbol")? & 0xf,
            shndx: u16_at(b, o + 6).ok_or("truncated symbol")?,
            value: u64_at(b, o + 8).ok_or("truncated symbol")?,
            size: u64_at(b, o + 16).ok_or("truncated symbol")?,
        });
    }
    let exec = |idx: u16| {
        secs.get(usize::from(idx))
            .is_some_and(|s| s.flags & SHF_EXECINSTR != 0)
    };
    // Functions per executable section.
    let mut funcs_in: HashMap<u16, Vec<&Sym>> = HashMap::new();
    let mut obj = Object::default();
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
    for (ri, rs) in secs.iter().enumerate() {
        if rs.kind != SHT_RELA || rs.link as usize >= secs.len() {
            continue;
        }
        let target = rs.info as usize;
        let Some(tsec) = secs.get(target) else {
            continue;
        };
        let _ = ri;
        let relocs: Vec<(u64, usize, u32, i64)> = (0..rs.size / 24)
            .filter_map(|k| {
                let o = rs.offset + k * 24;
                let info = u64_at(b, o + 8)?;
                Some((
                    u64_at(b, o)?,
                    usize::try_from(info >> 32).ok()?,
                    u32::try_from(info & 0xffff_ffff).ok()?,
                    i64::from_le_bytes(b.get(o + 16..o + 24)?.try_into().ok()?),
                ))
            })
            .collect();
        if tsec.name == ".stack_sizes" {
            // Entries: an address (relocated) and a ULEB128 size.
            let data = b
                .get(tsec.offset..tsec.offset + tsec.size)
                .ok_or("truncated .stack_sizes")?;
            for (off, si, _, addend) in &relocs {
                let Some(sym) = syms.get(*si) else { continue };
                let Some((size, _)) = usize::try_from(*off + 8).ok().and_then(|p| uleb(data, p))
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
            // PC-relative relocations address `S + A - P` with `A` = offset - 4.
            let pc_rel = matches!(rtype, 2 | 4 | 9 | 41 | 42);
            let callees: Vec<String> = if sym.shndx == 0 {
                if sym.name.is_empty() {
                    Vec::new()
                } else {
                    vec![sym.name.clone()]
                }
            } else if sym.kind == STT_FUNC {
                vec![sym.name.clone()]
            } else if sym.kind == STT_SECTION && exec(sym.shndx) {
                let t = if pc_rel { *addend + 4 } else { *addend };
                let t = u64::try_from(t).unwrap_or(0);
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
}

pub fn parse_record(text: &str) -> Result<Record, String> {
    let mut r = Record::default();
    let mut lines = text.lines();
    if lines.next() != Some("fip-prelint stack 1") {
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
            _ => return Err(format!("malformed .fip-stack line: {l}")),
        }
    }
    Ok(r)
}

/// The whole build: functions of every object, and the MIR facts of every record.
#[derive(Default)]
pub struct Build {
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
    pub fn bound(&self, sym: &str) -> Result<(u64, Vec<(String, u64)>), String> {
        if let Some(u) = self.unreadable.first() {
            return Err(format!("an object of the build could not be read: {u}"));
        }
        if !self.defined.contains(sym) {
            return Err(
                "the root has no symbol in the objects of this build (not codegened on its own: inlined, or kept only for cross-crate inlining at this opt-level)"
                    .to_string(),
            );
        }
        let mut memo: HashMap<String, Result<(u64, Vec<(String, u64)>), String>> = HashMap::new();
        let mut on_path: Vec<String> = Vec::new();
        self.visit(sym, &mut memo, &mut on_path)
    }

    fn visit(
        &self,
        sym: &str,
        memo: &mut HashMap<String, Result<(u64, Vec<(String, u64)>), String>>,
        on_path: &mut Vec<String>,
    ) -> Result<(u64, Vec<(String, u64)>), String> {
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
        let r = self.visit_new(sym, memo, on_path);
        memo.insert(sym.to_string(), r.clone());
        r
    }

    fn visit_new(
        &self,
        sym: &str,
        memo: &mut HashMap<String, Result<(u64, Vec<(String, u64)>), String>>,
        on_path: &mut Vec<String>,
    ) -> Result<(u64, Vec<(String, u64)>), String> {
        if !self.defined.contains(sym) {
            return Err(format!(
                "`{}` has no frame size: it is not defined in the objects of this build (precompiled standard library, foreign or runtime function)",
                self.label(sym)
            ));
        }
        let Some((label, why)) = self.mapped.get(sym) else {
            return Err(format!(
                "`{sym}` is defined in the build but is not a function rustc codegened from MIR for a crate the driver compiled"
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
            match self.visit(&c, memo, on_path) {
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
        Ok((frame + RETURN_ADDRESS + best.0, path))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
            "fip-prelint stack 1\ncrate\tc\ntarget\tx86_64-unknown-linux-gnu\nopt-level\tNo\nrlib\t/x/libc.rlib\nroot\tc::f\t_RNv1f\nroot\tc::g\t-\tgeneric\nfn\t_RNv1f\tc::f\nfn\t_RNv1h\tc::h\ta call through a function pointer\ndiv\t_RNvpanic\n",
        )
        .unwrap();
        assert_eq!(r.roots.len(), 2);
        assert_eq!(r.roots[1].1, Err("generic".to_string()));
        assert_eq!(
            r.fns[1].2.as_deref(),
            Some("a call through a function pointer")
        );
        assert!(parse_record("fip-prelint stack 2\n").is_err());
    }

    fn build(edges: &[(&str, &[&str])], frames: &[(&str, u64)]) -> Build {
        let mut b = Build::default();
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
        b.div.insert("memset".to_string());
        assert_eq!(b.bound("c").unwrap().0, 8);
        b.mapped.insert(
            "c".to_string(),
            ("c".to_string(), Some("inline assembly".to_string())),
        );
        assert!(b.bound("c").unwrap_err().contains("inline assembly"));
    }
}
