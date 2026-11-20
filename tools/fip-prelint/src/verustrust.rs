// SPDX-License-Identifier: MIT OR Apache-2.0
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
//!   (`verus-trusted.txt`, compiled into the driver) with `--no-cheating` and
//!   `-V alloc-check` (sidecar format 5), and its `flags` record nothing else (in
//!   particular not `--is-vstd`, `--is-core` or `--is-stdlib-outside-of-core`, a run
//!   verifying the crate as a standard-library crate; the fork audit, 2026-11-09);
//! - no source it lists implements an allocator trait (`Allocator`, `GlobalAlloc`, the
//!   marker traits; `verus::allocator_impls`): Verus can prove false facts about memory
//!   of an allocator whose methods touch its state (the fork audit, 2026-11-09), so
//!   such a sidecar is not used at all;
//! - the function's MIR uses no allocator other than `Global`/`System`: no type
//!   outside the standard library implementing `Allocator`/`GlobalAlloc`, no type
//!   parameter bounded by one, no trait object of one (the false facts arise where the
//!   allocator is used, `Box::new_in`, `Vec::*_in`, also in a crate without an
//!   implementation of its own);
//! - every source file it lists has the recorded SHA-256 (a callee's spec, a spec
//!   function or an imported crate's source that changed invalidates every entry), and
//!   none of them tests a cfg other than `verus_keep_ghost` and `feature` or invokes a
//!   macro whose expansion the scan cannot read (`verus::crate_cfg_conflict`);
//! - the build has the sidecar's target and cargo features (its `cfg` line): Verus
//!   compiled the crate for those;
//! - the function's path is listed, in the same file, and the SHA-256 of its item text
//!   (outer attributes and doc comments through the body) equals the entry's, and the
//!   item text holds no `cfg` other than the Verus-only attribute forms
//!   (`verus::cfg_conflict`): the driver compiles with `--cfg fip_prelint`, Verus
//!   without.
//!
//! Then an `Assert` panic site (overflow, bounds, division checks) of the function
//! whose span lies inside the item text and does not come from a macro expansion is
//! discharged, unless the analysed instance calls a trait method implemented, in this
//! build, by a function no sidecar lists (outside the standard library; `Fn*` calls
//! exempt): Verus assumed the trait's specification for it (phase 4 of decision
//! 2026-11-06-redesign-verus-allocates, cfg twins). Calls, frees, recursion and `⊤`
//! are unchanged. A literal proved `allocates K` of a non-generic function without
//! `requires` replaces the driver's count of its body where that count is not a finite
//! number `<= K` and every panic path is an allocation failure; a finite count `> K`
//! is kept and reported as an error (`crate::analysis`, sidecar format 5). A listed
//! function with a Verus `requires` passes that obligation to its callers
//! (`crate::analysis`). `FIP_PRELINT_NO_VERUS=1` (`cargo fip-prelint --no-verus`)
//! ignores every sidecar.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
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
        /// The proved `allocates` bound (stated, not proved, if `encapsulates`).
        allocates: verus::AllocBound,
        /// The `deallocates` bound (stated, not proved, if `encapsulates`).
        deallocates: verus::AllocBound,
        /// The function has `encapsulates alloc(a, d)`.
        encapsulates: bool,
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
    /// Per sidecar crate: its stamp and the functions whose proved literal
    /// `allocates` bound replaced the driver's count (phase 4).
    bounds: RefCell<BTreeMap<String, (String, BTreeSet<String>)>>,
    /// Per sidecar crate: its stamp and the functions whose proved `deallocates` bound
    /// replaced the driver's count.
    free_bounds: RefCell<BTreeMap<String, (String, BTreeSet<String>)>>,
    /// Functions whose driver count exceeds their proved bound.
    exceeded: RefCell<BTreeSet<String>>,
    /// Declared sources whose `encapsulates` clause differs from the declaration.
    mismatched: RefCell<BTreeMap<String, DefId>>,
    /// Proved bounds not taken because the function reaches an allocation source
    /// Verus does not count: the source → the functions.
    uncounted: RefCell<BTreeMap<String, BTreeSet<String>>>,
    /// The allocator traits (`core::alloc::Allocator`, `GlobalAlloc`), the types
    /// outside the standard library implementing one, and whether some such
    /// implementation is not for a named type (computed on first use).
    allocators: RefCell<Option<Allocators>>,
}

/// See [`VerusTrust::allocators`].
#[derive(Clone)]
struct Allocators {
    traits: Vec<DefId>,
    types: HashSet<DefId>,
    blanket: Option<String>,
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
            bounds: RefCell::new(BTreeMap::new()),
            free_bounds: RefCell::new(BTreeMap::new()),
            exceeded: RefCell::new(BTreeSet::new()),
            uncounted: RefCell::new(BTreeMap::new()),
            mismatched: RefCell::new(BTreeMap::new()),
            allocators: RefCell::new(None),
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
        let mut texts = Vec::new();
        for (file, hash) in &sidecar.sources {
            let bytes = std::fs::read(dir.join(file))
                .map_err(|_| format!("source `{file}` of the verification run is missing"))?;
            if verus::sha256_hex(&bytes) != *hash {
                return Err(format!(
                    "source `{file}` changed since the verification run (regenerate with `just verify`)"
                ));
            }
            texts.push((file, String::from_utf8_lossy(&bytes).into_owned()));
        }
        // Every listed source, also one outside `src/` (a `#[path]` module, re-audit
        // N4) and an imported crate's (which passed the same scan in its own run):
        // none may test a cfg the stamp does not record or expand a macro the scan
        // cannot read.
        let local: Vec<String> = texts
            .iter()
            .flat_map(|(_, t)| verus::macro_rules_names(t))
            .collect();
        for (file, text) in &texts {
            if let Some(c) = verus::crate_cfg_conflict(text, &local) {
                return Err(format!(
                    "source `{file}` has {c}: the driver's build and Verus's may differ"
                ));
            }
        }
        // An allocator implementation (`Allocator`, `GlobalAlloc`, the marker traits)
        // in a listed source: Verus can prove false facts about memory managed by an
        // allocator whose methods touch its state (the fork audit, 2026-11-09), so no
        // result of the run is used, neither panic facts nor `allocates` bounds.
        if let Some(at) = texts.iter().find_map(|(file, text)| {
            verus::allocator_impls(text)
                .first()
                .map(|(t, at)| format!("`impl {t}` at {file}:{}", verus::line_of(text, *at)))
        }) {
            return Err(format!(
                "its sources implement an allocator trait ({at}): Verus results about memory of such an allocator may be false, so none is used"
            ));
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
        // Verus compiled the crate for one target with one set of features.
        let target = tcx.sess.opts.target_triple.tuple().to_string();
        let mut features: Vec<String> = tcx
            .sess
            .config
            .iter()
            .filter(|(k, _)| *k == rustc_span::sym::feature)
            .filter_map(|(_, v)| v.map(|v| v.to_string()))
            .collect();
        features.sort();
        features.dedup();
        if loaded.sidecar.target != target || loaded.sidecar.features != features {
            let show = |f: &[String]| {
                if f.is_empty() {
                    "none".to_string()
                } else {
                    f.join(", ")
                }
            };
            let why = format!(
                "verified for target `{}` with features {}, this build is `{target}` with features {}",
                loaded.sidecar.target,
                show(&loaded.sidecar.features),
                show(&features)
            );
            self.refused
                .borrow_mut()
                .insert(shown(&sidecar_path), why.clone());
            return Verdict::NotListed(format!(
                "Verus sidecar `{}` not used: {why}",
                shown(&sidecar_path)
            ));
        }
        if !matches!(tcx.def_kind(d), DefKind::Fn | DefKind::AssocFn) {
            return Verdict::NotListed(format!(
                "a {} is not listed in the Verus sidecar",
                tcx.def_descr(d)
            ));
        }
        // Impl blocks are `{impl}` on both sides: rustc's and Verus's impl numbers are
        // disambiguators of two different builds (see `crate::verus`), so an impl
        // method is identified by its file and the line of its item text.
        let path = verus::impl_key(&format!(
            "{krate}{}",
            tcx.def_path(d).to_string_no_crate_verbose()
        ));
        let candidates: Vec<&verus::Entry> = loaded
            .sidecar
            .fns
            .iter()
            .filter(|e| e.path == path)
            .collect();
        if candidates.is_empty() {
            return Verdict::NotListed(format!(
                "`{path}` is not in the Verus sidecar (not verified by Verus)"
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
        let line = verus::line_of(&src, lo);
        let Some(entry) = candidates.iter().find(|e| {
            e.line == line
                && std::fs::canonicalize(loaded.dir.join(&e.file))
                    .ok()
                    .as_deref()
                    == Some(file.as_path())
        }) else {
            let at: Vec<String> = candidates
                .iter()
                .map(|e| format!("{}:{}", e.file, e.line))
                .collect();
            return Verdict::NotListed(format!(
                "`{path}` is listed for `{}`, not for this item (line {line})",
                at.join("`, `")
            ));
        };
        if verus::sha256_hex(&src.as_bytes()[lo..hi]) != entry.hash {
            return Verdict::NotListed(format!(
                "the item text of `{path}` differs from the one Verus verified (regenerate with `just verify`)"
            ));
        }
        if let Some(c) = verus::cfg_conflict(&src[lo..hi]) {
            return Verdict::NotListed(format!(
                "the item text of `{path}` has {c}: the driver's build and Verus's may differ"
            ));
        }
        if let Some(a) = self.custom_allocator(tcx, d) {
            return Verdict::NotListed(format!(
                "`{path}` uses {a}, an allocator other than `Global`/`System`: Verus results about memory of such an allocator may be false"
            ));
        }
        // An impl method also depends on its impl block's header (generics, `Self`,
        // the trait): it must not be configured differently for Verus.
        if let Some(imp) = tcx.opt_parent(d)
            && matches!(tcx.def_kind(imp), DefKind::Impl { .. })
        {
            let h = tcx.def_span(imp);
            let (hs, he) = (sm.lookup_byte_offset(h.lo()), sm.lookup_byte_offset(h.hi()));
            let header = (real_path(&hs.sf.name).as_deref() == Some(file.as_path())
                && hs.sf.start_pos == he.sf.start_pos)
                .then(|| {
                    let a = verus::attrs_start(&src, hs.pos.0 as usize)?;
                    src.get(a..he.pos.0 as usize)
                })
                .flatten();
            let Some(header) = header else {
                return Verdict::NotListed(
                    "the impl block's header is not found in the item's file".to_string(),
                );
            };
            if let Some(c) = verus::cfg_conflict(header) {
                return Verdict::NotListed(format!(
                    "the impl block's header has {c}: the driver's build and Verus's may differ"
                ));
            }
        }
        Verdict::Listed {
            path,
            requires: entry.requires,
            file,
            lo,
            hi,
            krate,
            stamp: loaded.sidecar.stamp(),
            allocates: entry.allocates.clone(),
            deallocates: entry.deallocates.clone(),
            encapsulates: entry.encapsulates,
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
                ..
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

    /// The literal `allocates` bound Verus proved for `d` and the function's path, if
    /// `d` is listed with one and has no `requires` (decision
    /// 2026-11-06-redesign-verus-allocates, phase 4): the fork assumes a callee's bound
    /// only under its precondition, which a caller Verus did not verify may break.
    /// Parameter-linear and opaque bounds are not evaluated (`None`).
    pub fn literal_alloc_bound(
        &self,
        tcx: TyCtxt<'_>,
        d: DefId,
        body_span: Span,
    ) -> Option<(u64, String)> {
        match self.verdict(tcx, d, body_span) {
            // (the counts of an `encapsulates` function are stated, not proved)
            Verdict::Listed {
                path,
                requires: false,
                allocates,
                encapsulates: false,
                ..
            } => allocates.literal().map(|k| (k, path)),
            _ => None,
        }
    }

    /// The literal `deallocates` bound Verus proved for `d` and the function's path,
    /// under the conditions of [`VerusTrust::literal_alloc_bound`].
    pub fn literal_dealloc_bound(
        &self,
        tcx: TyCtxt<'_>,
        d: DefId,
        body_span: Span,
    ) -> Option<(u64, String)> {
        match self.verdict(tcx, d, body_span) {
            Verdict::Listed {
                path,
                requires: false,
                deallocates,
                encapsulates: false,
                ..
            } => deallocates.literal().map(|k| (k, path)),
            _ => None,
        }
    }

    /// Records that the proved `deallocates` bound of `path` replaced the driver's
    /// count.
    pub fn free_bound_used(&self, tcx: TyCtxt<'_>, d: DefId, body_span: Span, path: &str) {
        if let Verdict::Listed { krate, stamp, .. } = self.verdict(tcx, d, body_span) {
            self.free_bounds
                .borrow_mut()
                .entry(krate)
                .or_insert_with(|| (stamp, BTreeSet::new()))
                .1
                .insert(path.to_string());
        }
    }

    /// The counts `(a, d)` of `d` if a Verus sidecar lists it with `encapsulates
    /// alloc(a, d)`: what Verus charges a verified caller for one call of `d` (stated by
    /// the clause, with or without a `requires`; Verus does not check the body against
    /// them). `None` if no sidecar lists `d` or it has no such clause.
    pub fn encapsulated(
        &self,
        tcx: TyCtxt<'_>,
        d: DefId,
        body_span: Span,
    ) -> Option<(verus::AllocBound, verus::AllocBound)> {
        match self.verdict(tcx, d, body_span) {
            Verdict::Listed {
                allocates,
                deallocates,
                encapsulates: true,
                ..
            } => Some((allocates, deallocates)),
            _ => None,
        }
    }

    /// The allocator traits and the types outside `core`/`alloc`/`std` implementing
    /// one of them, from every crate of the build.
    fn allocators(&self, tcx: TyCtxt<'_>) -> Allocators {
        if let Some(a) = self.allocators.borrow().as_ref() {
            return a.clone();
        }
        let path = |d: DefId| {
            rustc_middle::ty::print::with_no_visible_paths!(
                rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(d))
            )
        };
        let traits: Vec<DefId> = tcx
            .all_traits_including_private()
            .filter(|t| {
                tcx.crate_name(t.krate).as_str() == "core"
                    && matches!(
                        path(*t).as_str(),
                        "core::alloc::Allocator" | "core::alloc::global::GlobalAlloc"
                    )
            })
            .collect();
        let mut types = HashSet::new();
        let mut blanket = None;
        for t in &traits {
            for imp in tcx.all_impls(*t) {
                if matches!(tcx.crate_name(imp.krate).as_str(), "core" | "alloc" | "std") {
                    continue;
                }
                let mut ty = tcx.type_of(imp).instantiate_identity().skip_norm_wip();
                while let rustc_middle::ty::Ref(_, inner, _) = ty.kind() {
                    ty = *inner;
                }
                match ty.kind() {
                    rustc_middle::ty::Adt(def, _) => {
                        types.insert(def.did());
                    }
                    _ => {
                        blanket.get_or_insert_with(|| format!("`{}`", path(imp)));
                    }
                }
            }
        }
        let a = Allocators {
            traits,
            types,
            blanket,
        };
        *self.allocators.borrow_mut() = Some(a.clone());
        a
    }

    /// A type of `d`'s MIR (its locals and the generic arguments of its callees) that
    /// may be an allocator other than `Global`/`System`, shown: a type outside the
    /// standard library implementing `Allocator`/`GlobalAlloc`, a type parameter
    /// bounded by one, a trait object of one; or any type if some such implementation
    /// is not for a named type (fail closed). The fork audit (2026-11-09): Verus can
    /// prove false facts about memory of an allocator whose methods touch its state,
    /// in the crate that uses it (`Box::new_in`, `Vec::*_in`, ..), not only in the
    /// crate implementing it.
    fn custom_allocator(&self, tcx: TyCtxt<'_>, d: DefId) -> Option<String> {
        let a = self.allocators(tcx);
        if a.traits.is_empty() {
            return None;
        }
        if !tcx.is_mir_available(d) {
            return Some("an allocator the driver cannot rule out (no MIR)".to_string());
        }
        let body = tcx.optimized_mir(d);
        let env = tcx.param_env(d);
        let mut tys: Vec<rustc_middle::ty::Ty<'_>> =
            body.local_decls.iter().map(|l| l.ty).collect();
        for bb in body.basic_blocks.iter() {
            if let rustc_middle::mir::TerminatorKind::Call { func, .. } = &bb.terminator().kind {
                tys.push(func.ty(&body.local_decls, tcx));
            }
        }
        for ty in tys {
            for arg in ty.walk() {
                let Some(t) = arg.as_type() else {
                    continue;
                };
                let found = match t.kind() {
                    rustc_middle::ty::Adt(def, _) => a.types.contains(&def.did()),
                    rustc_middle::ty::Param(_) => env.caller_bounds().any(|c| {
                        c.as_trait_clause().is_some_and(|p| {
                            a.traits.contains(&p.def_id()) && p.self_ty().skip_binder() == t
                        })
                    }),
                    rustc_middle::ty::Dynamic(preds, ..) => preds
                        .principal_def_id()
                        .is_some_and(|p| a.traits.contains(&p)),
                    _ => false,
                };
                if found {
                    return Some(format!("the allocator type `{t}`"));
                }
                if let Some(b) = &a.blanket
                    && matches!(t.kind(), rustc_middle::ty::Param(_))
                {
                    return Some(format!(
                        "the type parameter `{t}`, which the blanket allocator implementation {b} may cover"
                    ));
                }
            }
        }
        None
    }

    /// Records that the proved bound of `path` replaced the driver's count.
    pub fn bound_used(&self, tcx: TyCtxt<'_>, d: DefId, body_span: Span, path: &str) {
        if let Verdict::Listed { krate, stamp, .. } = self.verdict(tcx, d, body_span) {
            self.bounds
                .borrow_mut()
                .entry(krate)
                .or_insert_with(|| (stamp, BTreeSet::new()))
                .1
                .insert(path.to_string());
        }
    }

    /// Records that the declared source `d` (`s`) has `encapsulates alloc(a, dl)` with
    /// other counts in its sidecar: one of the two trusted declarations is wrong.
    pub fn source_mismatch(
        &self,
        tcx: TyCtxt<'_>,
        d: DefId,
        a: &verus::AllocBound,
        dl: &verus::AllocBound,
        s: crate::marks::Source,
    ) {
        let declared = format!("{} allocation(s) and {} deallocation(s)", s.alloc, s.frees);
        self.mismatched.borrow_mut().insert(
            format!(
                "`{}` is declared a source of {declared}, and has `encapsulates alloc({}, {})` for Verus: the two trusted declarations must state the same counts (literal numbers: `a` the `n` of `fip::alloc_source`, `d` the `n` of `fip::free_source`, 0 without the attribute)",
                tcx.def_path_str(d),
                a.render(),
                dl.render()
            ),
            d,
        );
    }

    /// The declared sources whose `encapsulates` clause differs from their declaration.
    pub fn mismatched(&self) -> Vec<(DefId, String)> {
        self.mismatched
            .borrow()
            .iter()
            .map(|(m, d)| (*d, m.clone()))
            .collect()
    }

    /// Records that the driver's count of `path` exceeds its proved bound.
    pub fn bound_exceeded(&self, path: &str) {
        self.exceeded.borrow_mut().insert(path.to_string());
    }

    /// Records that the proved bound of `path` was not taken: the function reaches
    /// (or is) `source`, a declared source whose calls Verus does not count as
    /// declared, or a function with `encapsulates` that is not a declared source.
    pub fn bound_uncounted(&self, path: &str, source: &str) {
        self.uncounted
            .borrow_mut()
            .entry(source.to_string())
            .or_default()
            .insert(path.to_string());
    }

    /// The suffix of the crate summary: the panic sites discharged by Verus per
    /// sidecar, with its stamp, the allocation bounds taken from it, the bounds the
    /// driver's count exceeds, and the sidecars consulted but refused.
    pub fn summary(&self) -> String {
        let mut out = String::new();
        for (krate, (stamp, sites)) in self.discharged.borrow().iter() {
            out.push_str(&format!(
                ", {} panic sites discharged by Verus (sidecar of `{krate}`: {stamp})",
                sites.len()
            ));
        }
        for (krate, (stamp, fns)) in self.bounds.borrow().iter() {
            out.push_str(&format!(
                ", {} allocation bounds taken from Verus (sidecar of `{krate}`: {stamp})",
                fns.len()
            ));
        }
        for (krate, (stamp, fns)) in self.free_bounds.borrow().iter() {
            out.push_str(&format!(
                ", {} deallocation bounds taken from Verus (sidecar of `{krate}`: {stamp})",
                fns.len()
            ));
        }
        let exceeded = self.exceeded.borrow();
        if !exceeded.is_empty() {
            out.push_str(&format!(
                ", {} Verus allocation bounds exceeded by the driver's count ({})",
                exceeded.len(),
                exceeded
                    .iter()
                    .map(|p| format!("`{p}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        let uncounted = self.uncounted.borrow();
        if !uncounted.is_empty() {
            let fns: BTreeSet<&String> = uncounted.values().flatten().collect();
            out.push_str(&format!(
                ", {} Verus allocation bounds not taken, through functions whose calls Verus counts otherwise (a declared source needs `encapsulates alloc(a, d)` equal to its declaration in its crate's sidecar, on the impl method for a trait method; a function with `encapsulates` must be a declared source): {}",
                fns.len(),
                uncounted
                    .iter()
                    .map(|(src, fs)| format!(
                        "{src} ({})",
                        fs.iter()
                            .map(|p| format!("`{p}`"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                    .collect::<Vec<_>>()
                    .join("; ")
            ));
        }
        for (path, why) in self.refused.borrow().iter() {
            out.push_str(&format!(", Verus sidecar `{path}` not used: {why}"));
        }
        out
    }
}
