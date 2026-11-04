// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Pool hints (top plan T17; `cargo fip-prelint --pool-hints`, `FIP_PRELINT_POOL_HINTS=1`).
//!
//! A **heuristic**, off by default. It never changes a verdict, the exit status or the
//! summary counts: it only prints `note: fip-prelint: heuristic: ..` for methods of a
//! package the driver checks (with or without `fip::export`) or of a dependency that
//! declares `fip::export`, that look like an unmarked pure-Rust allocator
//! (a pool handing out slots of its own buffer, which the analysis treats as ordinary
//! allocation-free code: the declared assumption of limits plan L7).
//!
//! A candidate is an unmarked method `m` of a type `T` (no `fip::alloc_source` /
//! `fip::free_source` on it or on the trait method it implements) such that:
//!
//! - `m` takes `&mut self` and returns `Option<X>` or `Result<X, _>` with `X` a mutable
//!   borrow (`&mut [E]`, `&mut E`) or `usize`;
//! - its body writes an integer field of `self` (a bump index or free-list head) or
//!   an element of an array/slice field of `self` (a slot);
//! - for a borrow, its body mutably borrows (part of) an array/slice field of `self`;
//!   for `usize`, it writes or indexes an element of an array/slice field of `self`;
//! - another `&mut self` method of `T` resets that integer field to a constant,
//!   writes `None` below `self`, or calls `Option::take` (the release side).
//!
//! Ring buffers, fixed-capacity vectors and parsers can match the same shape, which is
//! why the note is opt-in and labelled heuristic (the property is intent, L7).

use std::collections::{BTreeSet, HashMap};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{self, BorrowKind, Operand, ProjectionElem, Rvalue, StatementKind};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Span;

/// Set by `cargo fip-prelint --pool-hints`.
pub const POOL_HINTS_ENV: &str = "FIP_PRELINT_POOL_HINTS";

pub fn enabled() -> bool {
    std::env::var_os(POOL_HINTS_ENV).is_some_and(|v| v == "1")
}

/// What a method's return type hands out.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Ret {
    Borrow,
    Index,
}

/// What one `&mut self` method's body does to `self`.
#[derive(Default)]
struct Facts {
    /// Integer fields of `self` assigned (`self.f = ..`).
    int_writes: BTreeSet<usize>,
    /// Integer fields of `self` assigned a constant (`self.f = 0`).
    const_writes: BTreeSet<usize>,
    /// Array/slice fields of `self` one of whose elements is assigned.
    slot_writes: BTreeSet<usize>,
    /// Array/slice fields of `self` indexed (read or written).
    indexed: BTreeSet<usize>,
    /// Array/slice fields of `self` (or parts of them) borrowed mutably.
    borrowed: BTreeSet<usize>,
    /// `None` assigned below `self`.
    writes_none: bool,
    /// `Option::take` called.
    takes: bool,
}

fn is_marked_source(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let has = |d: DefId| {
        #[allow(
            deprecated,
            reason = "tool attributes are unparsed; `find_attr!` covers parsed ones only"
        )]
        let attrs = tcx.get_all_attrs(d);
        attrs.iter().any(|a| match a {
            rustc_hir::Attribute::Unparsed(item) => {
                let segs: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
                segs == ["fip", "alloc_source"] || segs == ["fip", "free_source"]
            }
            _ => false,
        })
    };
    has(def_id) || tcx.trait_item_of(def_id).is_some_and(has)
}

/// `Option<X>`/`Result<X, _>` with `X` a mutable borrow or `usize`.
fn ret_kind<'tcx>(tcx: TyCtxt<'tcx>, out: Ty<'tcx>) -> Option<Ret> {
    let ty::Adt(def, args) = *out.kind() else {
        return None;
    };
    let path = tcx.def_path_str(def.did());
    if !matches!(
        path.as_str(),
        "std::option::Option"
            | "core::option::Option"
            | "std::result::Result"
            | "core::result::Result"
    ) {
        return None;
    }
    let x = args.type_at(0);
    match *x.kind() {
        ty::Ref(_, _, ty::Mutability::Mut) => Some(Ret::Borrow),
        ty::Uint(ty::UintTy::Usize) => Some(Ret::Index),
        _ => None,
    }
}

fn is_option(tcx: TyCtxt<'_>, def: ty::AdtDef<'_>) -> bool {
    matches!(
        tcx.def_path_str(def.did()).as_str(),
        "std::option::Option" | "core::option::Option"
    )
}

/// The field of `self` a place below `*_1` starts with, and the projections after it.
fn self_field<'a, 'tcx>(
    place: &'a mir::Place<'tcx>,
) -> Option<(usize, &'a [mir::PlaceElem<'tcx>])> {
    if place.local.as_usize() != 1 {
        return None;
    }
    match place.projection.as_slice() {
        [
            ProjectionElem::Deref,
            ProjectionElem::Field(f, _),
            rest @ ..,
        ] => Some((f.as_usize(), rest)),
        _ => None,
    }
}

fn facts<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>, fields: &[Ty<'tcx>]) -> Facts {
    let mut f = Facts::default();
    let is_int = |i: usize| fields.get(i).is_some_and(|t| t.is_integral());
    let is_buf = |i: usize| {
        fields
            .get(i)
            .is_some_and(|t| matches!(t.kind(), ty::Array(..) | ty::Slice(..)))
    };
    let note_index = |f: &mut Facts, place: &mir::Place<'tcx>| {
        if let Some((g, rest)) = self_field(place)
            && is_buf(g)
            && matches!(
                rest.first(),
                Some(ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
            )
        {
            f.indexed.insert(g);
        }
    };
    // `None` written by an aggregate, or as a constant (a field-less variant is a
    // constant in optimized MIR).
    let is_none = |rv: &Rvalue<'tcx>| match rv {
        Rvalue::Aggregate(kind, _) => match **kind {
            mir::AggregateKind::Adt(did, variant, ..) => {
                let def = tcx.adt_def(did);
                is_option(tcx, def) && def.variant(variant).name.as_str() == "None"
            }
            _ => false,
        },
        Rvalue::Use(Operand::Constant(c), _) => {
            let ty = c.const_.ty();
            if let ty::Adt(def, _) = *ty.kind()
                && is_option(tcx, def)
                && let Ok(val) = c.const_.eval(
                    tcx,
                    ty::TypingEnv::post_analysis(tcx, body.source.def_id()),
                    c.span,
                )
                && let Some(d) = tcx.try_destructure_mir_constant_for_user_output(val, ty)
            {
                d.variant
                    .is_some_and(|v| def.variant(v).name.as_str() == "None")
            } else {
                false
            }
        }
        _ => false,
    };
    let mut none_locals: std::collections::HashSet<mir::Local> = Default::default();
    // Locals holding `None` first (a block may write the slot before the order of
    // blocks reaches the assignment).
    for data in body.basic_blocks.iter() {
        for st in &data.statements {
            if let StatementKind::Assign(assign) = &st.kind
                && assign.0.projection.is_empty()
                && is_none(&assign.1)
            {
                none_locals.insert(assign.0.local);
            }
        }
    }
    for data in body.basic_blocks.iter() {
        for st in &data.statements {
            let StatementKind::Assign(assign) = &st.kind else {
                continue;
            };
            let (place, rv) = &**assign;
            if let Some((g, rest)) = self_field(place) {
                if rest.is_empty() && is_int(g) {
                    f.int_writes.insert(g);
                    if matches!(rv, Rvalue::Use(Operand::Constant(_), _)) {
                        f.const_writes.insert(g);
                    }
                }
                if is_buf(g)
                    && matches!(
                        rest.first(),
                        Some(ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
                    )
                {
                    f.slot_writes.insert(g);
                    f.indexed.insert(g);
                }
            }
            if is_none(rv) {
                if place.local.as_usize() == 1
                    && place.projection.first() == Some(&ProjectionElem::Deref)
                {
                    f.writes_none = true;
                } else if place.projection.is_empty() {
                    none_locals.insert(place.local);
                }
            }
            // `_7 = None; (*_1).slots[i] = move _7`.
            if place.local.as_usize() == 1
                && place.projection.first() == Some(&ProjectionElem::Deref)
                && let Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _) = rv
                && p.projection.is_empty()
                && none_locals.contains(&p.local)
            {
                f.writes_none = true;
            }
            match rv {
                Rvalue::Ref(_, BorrowKind::Mut { .. }, p) => {
                    if let Some((g, _)) = self_field(p)
                        && is_buf(g)
                    {
                        f.borrowed.insert(g);
                    }
                    note_index(&mut f, p);
                }
                Rvalue::Ref(_, _, p) | Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _) => {
                    note_index(&mut f, p);
                }
                _ => {}
            }
        }
        if let Some(term) = &data.terminator
            && let mir::TerminatorKind::Call { func, .. } = &term.kind
            && let Some((d, _)) = func.const_fn_def()
            && tcx.opt_item_name(d).is_some_and(|n| n.as_str() == "take")
            && tcx
                .impl_of_assoc(d)
                .and_then(|i| {
                    tcx.type_of(i)
                        .instantiate_identity()
                        .skip_norm_wip()
                        .ty_adt_def()
                })
                .is_some_and(|a| is_option(tcx, a))
        {
            f.takes = true;
        }
    }
    f
}

/// The pool hints of the local crate: `(span, message)`.
pub fn hints(tcx: TyCtxt<'_>) -> Vec<(Span, String)> {
    // `&mut self` methods per self type: (method, facts, return kind).
    let mut by_type: HashMap<DefId, Vec<(DefId, Facts, Option<Ret>)>> = HashMap::new();
    for local in tcx.mir_keys(()).iter() {
        let m = local.to_def_id();
        if tcx.def_kind(m) != DefKind::AssocFn || !tcx.is_mir_available(m) {
            continue;
        }
        let Some(imp) = tcx.impl_of_assoc(m) else {
            continue;
        };
        let self_ty = tcx.type_of(imp).instantiate_identity().skip_norm_wip();
        let ty::Adt(adt, args) = *self_ty.kind() else {
            continue;
        };
        if !adt.is_struct() {
            continue;
        }
        let sig = tcx.fn_sig(m).instantiate_identity().skip_binder();
        let Some(&first) = sig.inputs().first() else {
            continue;
        };
        let ty::Ref(_, inner, ty::Mutability::Mut) = *first.kind() else {
            continue;
        };
        if inner != self_ty {
            continue;
        }
        let fields: Vec<Ty<'_>> = adt
            .non_enum_variant()
            .fields
            .iter()
            .map(|fd| fd.ty(tcx, args).skip_norm_wip())
            .collect();
        let body = tcx.optimized_mir(m);
        let f = facts(tcx, body, &fields);
        by_type
            .entry(adt.did())
            .or_default()
            .push((m, f, ret_kind(tcx, sig.output())));
    }
    let mut out = Vec::new();
    for (adt_id, methods) in &by_type {
        let adt = tcx.adt_def(*adt_id);
        let name = |i: usize| {
            adt.non_enum_variant()
                .fields
                .iter()
                .nth(i)
                .map_or_else(|| i.to_string(), |fd| fd.name.to_string())
        };
        for (m, f, ret) in methods {
            let Some(ret) = *ret else {
                continue;
            };
            if is_marked_source(tcx, *m) {
                continue;
            }
            if f.int_writes.is_empty() && f.slot_writes.is_empty() {
                continue;
            }
            let buf = match ret {
                Ret::Borrow => f.borrowed.iter().next(),
                Ret::Index => f
                    .slot_writes
                    .iter()
                    .next()
                    .or_else(|| f.indexed.iter().next()),
            };
            let Some(&buf) = buf else {
                continue;
            };
            // The release side: another method resetting a written integer field,
            // writing `None` below `self`, or calling `Option::take`.
            let release = methods.iter().find_map(|(m2, f2, _)| {
                if m2 == m || is_marked_source(tcx, *m2) {
                    return None;
                }
                if let Some(&g) = f2.const_writes.intersection(&f.int_writes).next() {
                    return Some((*m2, format!("resets `self.{}`", name(g))));
                }
                if f2.writes_none {
                    return Some((*m2, "writes `None` into `self`".to_string()));
                }
                if f2.takes {
                    return Some((*m2, "calls `Option::take`".to_string()));
                }
                None
            });
            let Some((m2, what2)) = release else {
                continue;
            };
            let writes: Vec<String> = f
                .int_writes
                .iter()
                .map(|g| format!("`self.{}`", name(*g)))
                .chain(
                    f.slot_writes
                        .iter()
                        .map(|g| format!("a slot of `self.{}`", name(*g))),
                )
                .collect();
            let hands = match ret {
                Ret::Borrow => format!("returns a borrow of `self.{}`", name(buf)),
                Ret::Index => format!("returns an index into `self.{}`", name(buf)),
            };
            out.push((
                tcx.def_span(*m),
                format!(
                    "heuristic: `{}` looks like an unmarked pool allocation (it writes {} and {hands}; `{}` {what2}): if it hands out memory, mark it `fip::alloc_source` and its release `fip::free_source`; otherwise ignore this note (`--pool-hints`; it changes no verdict)",
                    tcx.def_path_str(*m),
                    writes.join(", "),
                    tcx.def_path_str(m2)
                ),
            ));
        }
    }
    out.sort_by_key(|(sp, _)| *sp);
    out
}

/// Prints the pool hints of the local crate, if enabled: for a package the driver
/// checks (`primary`, its own roots use its pools), and for a dependency only if it
/// declares `fip::export` (the driver compiles no other dependency). Notes only: no
/// count, no exit status.
pub fn report(tcx: TyCtxt<'_>, primary: bool) {
    if !enabled()
        || !(primary
            || crate::analysis::declares_export(tcx, rustc_hir::def_id::CRATE_DEF_ID.to_def_id()))
    {
        return;
    }
    for (sp, msg) in hints(tcx) {
        tcx.dcx().span_note(sp, format!("fip-prelint: {msg}"));
    }
}
