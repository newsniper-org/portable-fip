// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! The driver's use of Verus sidecars (top plan T13.4, format in [`crate::verus`]).
//!
//! A package opts in by declaring its sidecar in its manifest:
//!
//! ```toml
//! [package.metadata.fip-prelint]
//! verus-sidecar = "verus-verified.txt"
//! ```
//!
//! For a function of that package's library crate the driver finds the sidecar from
//! the function's source file (the nearest `Cargo.toml` above it) and uses an entry
//! only if all of these hold, else the function's panic sites stay reported with the
//! reason appended:
//!
//! - the file exists and parses; its stamp is the trusted Verus build and Z3
//!   (`verus-trusted.txt`, compiled into the driver) with `--no-cheating`;
//! - every source file it lists has the recorded SHA-256 (a callee's spec, a spec
//!   function or an imported crate's source that changed invalidates every entry);
//! - the function's path is listed, in the same file, and the SHA-256 of its item text
//!   (outer attributes and doc comments through the body) equals the entry's.
//!
//! Then an `Assert` panic site (overflow, bounds, division checks) of the function
//! whose span lies inside the item text and does not come from a macro expansion is
//! discharged. Calls, allocations, frees, recursion and `⊤` are unchanged. A listed
//! function with a Verus `requires` passes that obligation to its callers
//! (`crate::analysis`). `FIP_PRELINT_NO_VERUS=1` (`cargo fip-prelint --no-verus`)
//! ignores every sidecar.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::{FileName, Span};

use crate::verus::{self, Sidecar, Trusted};

/// The trusted Verus build (the pin a sidecar's stamp must equal).
pub const TRUSTED: &str = include_str!("../verus-trusted.txt");

/// Environment variable switching every sidecar off.
pub const OFF_ENV: &str = "FIP_PRELINT_NO_VERUS";

/// Per sidecar crate: its stamp and the discharged sites (file and byte offset).
type Discharged = BTreeMap<String, (String, BTreeSet<(PathBuf, usize)>)>;

struct Loaded {
    sidecar: Sidecar,
    dir: PathBuf,
}

/// What the sidecars say about one function.
#[derive(Clone, Debug)]
pub enum Verdict {
    /// Its package declares no sidecar (or sidecars are switched off, or it belongs to
    /// another crate of the package than the sidecar's).
    NoSidecar,
    /// Verified by Verus; the item text is `lo..hi` of `file`.
    Listed {
        path: String,
        requires: bool,
        file: PathBuf,
        lo: usize,
        hi: usize,
        krate: String,
        stamp: String,
    },
    /// Its package declares a sidecar, but it cannot be used for this function.
    NotListed(String),
}

/// An `Assert` site of a function.
pub enum SiteVerdict {
    /// Discharged by Verus; `Some(path)` if the function has a `requires`.
    Discharged(Option<String>),
    /// Kept; with the reason Verus does not discharge it, if the package declares a
    /// sidecar.
    Kept(Option<String>),
}

pub struct VerusTrust {
    off: bool,
    trusted: Result<Trusted, String>,
    /// Package directory → (declared sidecar, library crate name).
    manifests: RefCell<HashMap<PathBuf, Option<(PathBuf, String)>>>,
    loaded: RefCell<HashMap<PathBuf, Rc<Result<Loaded, String>>>>,
    verdicts: RefCell<HashMap<DefId, Verdict>>,
    discharged: RefCell<Discharged>,
    /// Sidecars that were consulted and refused: shown path → reason.
    refused: RefCell<BTreeMap<String, String>>,
}

/// Local path of a source file name, made absolute and canonical.
fn real_path(name: &FileName) -> Option<PathBuf> {
    let p = name.clone().into_local_path()?;
    let p = if p.is_relative() {
        std::env::current_dir().ok()?.join(p)
    } else {
        p
    };
    std::fs::canonicalize(&p).ok()
}

/// `p` relative to the current directory when it is below it.
fn shown(p: &Path) -> String {
    std::env::current_dir()
        .ok()
        .and_then(|d| std::fs::canonicalize(d).ok())
        .and_then(|d| p.strip_prefix(d).ok().map(Path::to_path_buf))
        .unwrap_or_else(|| p.to_path_buf())
        .display()
        .to_string()
}

impl VerusTrust {
    pub fn new() -> VerusTrust {
        VerusTrust {
            off: std::env::var_os(OFF_ENV).is_some_and(|v| v == "1"),
            trusted: Trusted::parse(TRUSTED),
            manifests: RefCell::new(HashMap::new()),
            loaded: RefCell::new(HashMap::new()),
            verdicts: RefCell::new(HashMap::new()),
            discharged: RefCell::new(BTreeMap::new()),
            refused: RefCell::new(BTreeMap::new()),
        }
    }

    /// The sidecar declared by the package whose directory is the nearest one above
    /// `file` holding a `Cargo.toml`, with the package's library crate name.
    fn declared_for(&self, file: &Path) -> Option<(PathBuf, String)> {
        let mut dir = file.parent()?;
        loop {
            if let Some(v) = self.manifests.borrow().get(dir) {
                return v.clone();
            }
            let m = dir.join("Cargo.toml");
            if m.is_file() {
                let v = std::fs::read_to_string(&m).ok().and_then(|t| {
                    Some((
                        dir.join(verus::declared_sidecar(&t)?),
                        verus::lib_crate_name(&t)?,
                    ))
                });
                self.manifests
                    .borrow_mut()
                    .insert(dir.to_path_buf(), v.clone());
                return v;
            }
            dir = dir.parent()?;
        }
    }

    fn load(&self, path: &Path) -> Rc<Result<Loaded, String>> {
        if let Some(l) = self.loaded.borrow().get(path) {
            return Rc::clone(l);
        }
        let r = self.load_uncached(path);
        if let Err(why) = &r {
            self.refused.borrow_mut().insert(shown(path), why.clone());
        }
        let r = Rc::new(r);
        self.loaded
            .borrow_mut()
            .insert(path.to_path_buf(), Rc::clone(&r));
        r
    }

    fn load_uncached(&self, path: &Path) -> Result<Loaded, String> {
        let trusted = self
            .trusted
            .as_ref()
            .map_err(|e| format!("the driver's trusted Verus pin is unusable: {e}"))?;
        let text = std::fs::read_to_string(path)
            .map_err(|e| format!("declared, but cannot be read ({e})"))?;
        let sidecar = Sidecar::parse(&text)?;
        sidecar.check_stamp(trusted)?;
        let dir = path.parent().unwrap_or(Path::new(".")).to_path_buf();
        for (file, hash) in &sidecar.sources {
            let bytes = std::fs::read(dir.join(file))
                .map_err(|_| format!("source `{file}` of the verification run is missing"))?;
            if verus::sha256_hex(&bytes) != *hash {
                return Err(format!(
                    "source `{file}` changed since the verification run (regenerate with `just verify`)"
                ));
            }
        }
        Ok(Loaded { sidecar, dir })
    }

    /// The verdict for function `d`, whose MIR body spans `body_span`.
    pub fn verdict(&self, tcx: TyCtxt<'_>, d: DefId, body_span: Span) -> Verdict {
        if let Some(v) = self.verdicts.borrow().get(&d) {
            return v.clone();
        }
        let v = self.verdict_uncached(tcx, d, body_span);
        self.verdicts.borrow_mut().insert(d, v.clone());
        v
    }

    fn verdict_uncached(&self, tcx: TyCtxt<'_>, d: DefId, body_span: Span) -> Verdict {
        if self.off {
            return Verdict::NoSidecar;
        }
        let sm = tcx.sess.source_map();
        let def_span = tcx.def_span(d);
        let start = sm.lookup_byte_offset(def_span.lo());
        let Some(file) = real_path(&start.sf.name) else {
            return Verdict::NoSidecar;
        };
        let Some((sidecar_path, lib)) = self.declared_for(&file) else {
            return Verdict::NoSidecar;
        };
        let krate = tcx.crate_name(d.krate).to_string();
        // Another crate of the package (a test, an example): not covered.
        if krate != lib {
            return Verdict::NoSidecar;
        }
        let loaded = self.load(&sidecar_path);
        let loaded = match loaded.as_ref() {
            Ok(l) => l,
            Err(why) => {
                return Verdict::NotListed(format!(
                    "Verus sidecar `{}` not used: {why}",
                    shown(&sidecar_path)
                ));
            }
        };
        if loaded.sidecar.krate != krate {
            return Verdict::NotListed(format!(
                "Verus sidecar `{}` is for crate `{}`",
                shown(&sidecar_path),
                loaded.sidecar.krate
            ));
        }
        if !matches!(tcx.def_kind(d), DefKind::Fn | DefKind::AssocFn) {
            return Verdict::NotListed(format!(
                "a {} is not listed in the Verus sidecar",
                tcx.def_descr(d)
            ));
        }
        let path = format!("{krate}{}", tcx.def_path(d).to_string_no_crate_verbose());
        let Some(entry) = loaded.sidecar.fns.iter().find(|e| e.path == path) else {
            return Verdict::NotListed(format!(
                "`{path}` is not in the Verus sidecar (not verified by Verus)"
            ));
        };
        let entry_file = std::fs::canonicalize(loaded.dir.join(&entry.file)).ok();
        if entry_file.as_deref() != Some(file.as_path()) {
            return Verdict::NotListed(format!(
                "`{path}` is listed for `{}`, not for this file",
                entry.file
            ));
        }
        let end = sm.lookup_byte_offset(body_span.hi());
        if real_path(&end.sf.name).as_deref() != Some(file.as_path()) {
            return Verdict::NotListed("the body is not in the item's file".to_string());
        }
        let Ok(src) = std::fs::read_to_string(&file) else {
            return Verdict::NotListed("the source file cannot be read".to_string());
        };
        let (s, e) = (start.pos.0 as usize, end.pos.0 as usize);
        let Some((lo, hi)) = verus::item_region(&src, s, e) else {
            return Verdict::NotListed("the item text is not found in its file".to_string());
        };
        if verus::sha256_hex(&src.as_bytes()[lo..hi]) != entry.hash {
            return Verdict::NotListed(format!(
                "the item text of `{path}` differs from the one Verus verified (regenerate with `just verify`)"
            ));
        }
        Verdict::Listed {
            path,
            requires: entry.requires,
            file,
            lo,
            hi,
            krate,
            stamp: loaded.sidecar.stamp(),
        }
    }

    /// Whether `d` is a Verus-verified function (a listed entry that matches).
    pub fn is_listed(&self, tcx: TyCtxt<'_>, d: DefId, body_span: Span) -> Option<(String, bool)> {
        match self.verdict(tcx, d, body_span) {
            Verdict::Listed { path, requires, .. } => Some((path, requires)),
            _ => None,
        }
    }

    /// The verdict for an `Assert` site at `span` in function `d`.
    pub fn site(&self, tcx: TyCtxt<'_>, d: DefId, body_span: Span, span: Span) -> SiteVerdict {
        match self.verdict(tcx, d, body_span) {
            Verdict::NoSidecar => SiteVerdict::Kept(None),
            Verdict::NotListed(why) => SiteVerdict::Kept(Some(why)),
            Verdict::Listed {
                path,
                requires,
                file,
                lo,
                hi,
                krate,
                stamp,
            } => {
                if span.from_expansion() {
                    return SiteVerdict::Kept(Some(
                        "the site comes from a macro expansion".to_string(),
                    ));
                }
                let sm = tcx.sess.source_map();
                let at = sm.lookup_byte_offset(span.lo());
                let to = sm.lookup_byte_offset(span.hi());
                let inside = real_path(&at.sf.name).as_deref() == Some(file.as_path())
                    && (at.pos.0 as usize) >= lo
                    && (to.pos.0 as usize) <= hi
                    && to.sf.start_pos == at.sf.start_pos;
                if !inside {
                    return SiteVerdict::Kept(Some(
                        "the site is outside the verified item text".to_string(),
                    ));
                }
                self.discharged
                    .borrow_mut()
                    .entry(krate)
                    .or_insert_with(|| (stamp, BTreeSet::new()))
                    .1
                    .insert((file, at.pos.0 as usize));
                SiteVerdict::Discharged(requires.then_some(path))
            }
        }
    }

    /// The suffix of the crate summary: the panic sites discharged by Verus per
    /// sidecar, with its stamp, and the sidecars consulted but refused.
    pub fn summary(&self) -> String {
        let mut out = String::new();
        for (krate, (stamp, sites)) in self.discharged.borrow().iter() {
            out.push_str(&format!(
                ", {} panic sites discharged by Verus (sidecar of `{krate}`: {stamp})",
                sites.len()
            ));
        }
        for (path, why) in self.refused.borrow().iter() {
            out.push_str(&format!(", Verus sidecar `{path}` not used: {why}"));
        }
        out
    }
}
