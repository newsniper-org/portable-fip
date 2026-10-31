// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Source model behind [`crate::callgraph`] and [`crate::summaries`].
//!
//! Lexes the given sources (with file and line per token), splices `include!("..")`
//! files, builds the module tree from `mod` declarations (`#[path]` honoured), parses
//! functions keyed by crate, module path and `impl` owner, scans their bodies for
//! calls, allocation sites, loops and closures, and resolves call paths. Lexical
//! only: no types, no macro expansion beyond `macro_rules!` bodies defined in the
//! scanned sources.

mod lex;
mod parse;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};

use fip_lint_rules::{in_core_table, is_drop_function};

use lex::{Tok, group_end, id, is_id, is_open, is_p, lit};
use parse::{Builder, Scope};

/// FIP marker on a function.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum MarkKind {
    #[default]
    None,
    /// `#[fip]` / `#[fip(N)]` (with `n = N`, 0 for plain `#[fip]`).
    Fip,
    Fbip,
}

/// Marker with its arguments.
#[derive(Clone, Debug, Default)]
pub(crate) struct Mark {
    pub(crate) kind: MarkKind,
    pub(crate) n: u64,
    /// `param(g = K)` declarations.
    pub(crate) params: Vec<(String, u64)>,
}

/// A non-`self` parameter.
#[derive(Clone, Debug)]
pub(crate) struct Param {
    pub(crate) name: String,
    /// Closure, `fn` pointer, `Fn*`/`FipFn` value.
    pub(crate) callable: bool,
}

/// A function, closure literal or `const`/`static` initializer.
#[derive(Clone, Debug)]
pub(crate) struct FnDef {
    pub(crate) name: String,
    pub(crate) display: String,
    pub(crate) unit: usize,
    pub(crate) module: Vec<String>,
    pub(crate) owner: Option<String>,
    pub(crate) generics: Vec<String>,
    pub(crate) mark: Mark,
    pub(crate) has_self: bool,
    pub(crate) params: Vec<Param>,
    /// Enclosing function of a closure literal.
    pub(crate) closure_of: Option<usize>,
    /// Pseudo-function for a `const`/`static` initializer.
    pub(crate) item_init: bool,
    pub(crate) file: usize,
    pub(crate) line: u32,
    pub(crate) events: Vec<Event>,
}

/// Something a body does, at a source line.
#[derive(Clone, Debug)]
pub(crate) struct Event {
    pub(crate) ev: Ev,
    pub(crate) file: usize,
    pub(crate) line: u32,
    /// Inside a loop body or a `while` condition.
    pub(crate) in_loop: bool,
}

#[derive(Clone, Debug)]
pub(crate) enum Ev {
    /// Allocation site (`Box::new`, `vec!`, ...), described.
    Site(String),
    /// `name(..)` / `path::name(..)`.
    Call {
        segs: Vec<String>,
        name: String,
        args: Vec<Arg>,
        res: Res,
    },
    /// `recv.name(..)`, or `<T>::name(..)` (`qualified`, first argument is the
    /// receiver if the callee takes `self`).
    Method {
        name: String,
        args: Vec<Arg>,
        /// Name in `ALLOC_METHODS`.
        site: bool,
        qualified: bool,
        res: Res,
    },
    /// Call of a callable parameter of the enclosing named function.
    ParamCall(String),
    /// Call of a local bound to this closure literal.
    ClosureCall(usize),
    /// Closure literal used as a value other than a call argument.
    Escape(usize),
    /// Call through an expression or a non-closure local.
    Indirect,
    /// Something the checker cannot see into (external macro, `?`, unread include).
    Unknown(String),
    /// A name used as a value (possible function pointer).
    Value {
        segs: Vec<String>,
        name: String,
        res: Res,
    },
}

/// A call argument, as far as the checker needs it.
#[derive(Clone, Debug)]
pub(crate) enum Arg {
    Closure(usize),
    Param(String),
    Named {
        segs: Vec<String>,
        name: String,
        res: Res,
    },
    Other,
}

/// Resolution of a path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Res {
    Pending,
    Fns(Vec<usize>),
    /// No definition in scope; these are the functions of that name in the crate
    /// (name-match fallback: edges for the call graph, `⊤` for allocation bounds).
    Guess(Vec<usize>),
    /// `core`/`std`/`alloc` path: `Some(0)` if in the audited table or a drop.
    External {
        cost: Option<u64>,
        frees: bool,
    },
    /// Tuple-struct or enum-variant constructor (capitalised, not a defined function).
    Constructor,
    Unresolved,
}

struct FileSrc {
    path: PathBuf,
    group: usize,
    text: String,
    toks: Option<Vec<Tok>>,
    busy: bool,
    included: bool,
}

/// Lexical normalisation (`.` and `..` removed).
fn normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                if !out.pop() {
                    out.push("..");
                }
            }
            other => out.push(other.as_os_str()),
        }
    }
    out
}

struct Files {
    files: Vec<FileSrc>,
}

impl Files {
    fn add(&mut self, group: usize, path: &Path, text: String) -> usize {
        self.files.push(FileSrc {
            path: normalize(path),
            group,
            text,
            toks: None,
            busy: false,
            included: false,
        });
        self.files.len() - 1
    }

    fn find(&self, group: usize, path: &Path) -> Option<usize> {
        self.files
            .iter()
            .position(|f| f.group == group && f.path == path)
    }

    fn find_or_read(&mut self, group: usize, path: &Path) -> Option<usize> {
        if let Some(f) = self.find(group, path) {
            return Some(f);
        }
        let text = fs::read_to_string(path).ok()?;
        Some(self.add(group, path, text))
    }

    /// Lexes file `f` and splices its `include!("..")` files (relative to `f`).
    fn ensure(&mut self, f: usize, depth: u32) {
        if self.files[f].toks.is_some() || self.files[f].busy || depth > 16 {
            return;
        }
        self.files[f].busy = true;
        let raw = lex::lex(&self.files[f].text, f);
        let dir = self.files[f]
            .path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_default();
        let group = self.files[f].group;
        let mut out = Vec::with_capacity(raw.len());
        let mut i = 0;
        while i < raw.len() {
            if is_id(&raw, i, "include")
                && is_p(&raw, i + 1, '!')
                && is_open(&raw, i + 2)
                && group_end(&raw, i + 2) == i + 5
                && let Some(p) = lit(&raw, i + 3)
                && let Some(tf) = self.find_or_read(group, &normalize(&dir.join(p)))
            {
                self.ensure(tf, depth + 1);
                if let Some(tt) = self.files[tf].toks.clone() {
                    self.files[tf].included = true;
                    out.extend(tt);
                    i += 5;
                    continue;
                }
            }
            out.push(raw[i].clone());
            i += 1;
        }
        self.files[f].toks = Some(out);
        self.files[f].busy = false;
    }

    fn toks(&self, f: usize) -> &[Tok] {
        self.files[f].toks.as_deref().unwrap_or(&[])
    }

    fn name_is_mod_rs(&self, f: usize) -> bool {
        matches!(
            self.files[f].path.file_name().and_then(|n| n.to_str()),
            Some("lib.rs" | "main.rs" | "mod.rs")
        )
    }

    /// File a `mod` declaration in `f` refers to (`mod_rs`: `f` is `lib.rs`,
    /// `main.rs`, `mod.rs` or a crate root). Reads `#[path]` targets from disk.
    fn decl_target(&mut self, f: usize, mod_rs: bool, d: &Decl, read: bool) -> Option<usize> {
        let p = self.files[f].path.clone();
        let group = self.files[f].group;
        let dir = p.parent().map(Path::to_path_buf).unwrap_or_default();
        let mut base = if mod_rs {
            dir.clone()
        } else {
            dir.join(p.file_stem().unwrap_or_default())
        };
        for s in &d.inline {
            base.push(s);
        }
        if let Some(a) = &d.path {
            let from = if d.inline.is_empty() { dir } else { base };
            let target = normalize(&from.join(a));
            return if read {
                let tf = self.find_or_read(group, &target)?;
                self.ensure(tf, 0);
                Some(tf)
            } else {
                self.find(group, &target)
            };
        }
        let c1 = normalize(&base.join(format!("{}.rs", d.name)));
        let c2 = normalize(&base.join(&d.name).join("mod.rs"));
        self.find(group, &c1).or_else(|| self.find(group, &c2))
    }
}

/// `mod name;` declaration (with the inline modules around it and `#[path]`).
struct Decl {
    inline: Vec<String>,
    name: String,
    path: Option<String>,
}

fn mod_decls(t: &[Tok], from: usize, to: usize, inline: &mut Vec<String>, out: &mut Vec<Decl>) {
    let mut i = from;
    let mut path = None;
    while i < to {
        if is_p(t, i, '#') && is_p(t, i + 1, '[') {
            let e = group_end(t, i + 1);
            if let Some(p) = parse::attr(t, i + 2, e - 1).path {
                path = Some(p);
            }
            i = e;
            continue;
        }
        if is_id(t, i, "mod")
            && let Some(n) = id(t, i + 1)
        {
            if is_p(t, i + 2, ';') {
                out.push(Decl {
                    inline: inline.clone(),
                    name: n.to_string(),
                    path: path.take(),
                });
                i += 3;
                continue;
            }
            if is_p(t, i + 2, '{') {
                let e = group_end(t, i + 2);
                inline.push(n.to_string());
                mod_decls(t, i + 3, e - 1, inline, out);
                inline.pop();
                path = None;
                i = e;
                continue;
            }
        }
        if is_open(t, i) {
            if is_p(t, i, '{') {
                path = None;
            }
            i = group_end(t, i);
            continue;
        }
        if is_p(t, i, ';') {
            path = None;
        }
        i += 1;
    }
}

/// Assignment of files to compilation units and module paths.
struct Tree {
    unit_of: Vec<Option<usize>>,
    module_of: Vec<Vec<String>>,
    /// Per unit: (group, root file).
    units: Vec<(usize, usize)>,
}

impl Tree {
    fn grow(&mut self, n: usize) {
        while self.unit_of.len() < n {
            self.unit_of.push(None);
            self.module_of.push(Vec::new());
        }
    }

    fn root(&mut self, fl: &Files, f: usize, queue: &mut Vec<usize>) {
        self.unit_of[f] = Some(self.units.len());
        self.units.push((fl.files[f].group, f));
        queue.push(f);
    }

    fn bfs(&mut self, fl: &mut Files, queue: &mut Vec<usize>) {
        while let Some(f) = queue.pop() {
            let unit = self.unit_of[f].unwrap_or(0);
            let is_root = self.units[unit].1 == f;
            let mod_rs = fl.name_is_mod_rs(f) || is_root;
            let mut decls = Vec::new();
            mod_decls(fl.toks(f), 0, fl.toks(f).len(), &mut Vec::new(), &mut decls);
            for d in decls {
                let Some(tf) = fl.decl_target(f, mod_rs, &d, true) else {
                    continue;
                };
                self.grow(fl.files.len());
                if self.unit_of[tf].is_some() || fl.files[tf].included {
                    continue;
                }
                let mut m = self.module_of[f].clone();
                m.extend(d.inline.iter().cloned());
                m.push(d.name.clone());
                self.unit_of[tf] = Some(unit);
                self.module_of[tf] = m;
                queue.push(tf);
            }
        }
    }

    fn build(fl: &mut Files) -> Self {
        let n0 = fl.files.len();
        let mut declared = BTreeSet::new();
        for f in 0..n0 {
            if fl.files[f].included {
                continue;
            }
            let mut decls = Vec::new();
            mod_decls(fl.toks(f), 0, fl.toks(f).len(), &mut Vec::new(), &mut decls);
            let mod_rs = fl.name_is_mod_rs(f);
            for d in decls {
                if let Some(tf) = fl.decl_target(f, mod_rs, &d, false) {
                    declared.insert(tf);
                }
            }
        }
        let mut tree = Tree {
            unit_of: Vec::new(),
            module_of: Vec::new(),
            units: Vec::new(),
        };
        tree.grow(fl.files.len());
        let mut queue = Vec::new();
        for f in 0..n0 {
            if !fl.files[f].included && !declared.contains(&f) {
                tree.root(fl, f, &mut queue);
            }
        }
        tree.bfs(fl, &mut queue);
        let mut f = 0;
        while f < fl.files.len() {
            tree.grow(fl.files.len());
            if tree.unit_of[f].is_none() && !fl.files[f].included {
                tree.root(fl, f, &mut queue);
                tree.bfs(fl, &mut queue);
            }
            f += 1;
        }
        tree
    }
}

/// `macro_rules! name { (..) => { body }; .. }` bodies in all files.
fn collect_macros(toks: &[Vec<Tok>]) -> BTreeMap<String, Vec<(usize, usize, usize)>> {
    let mut out: BTreeMap<String, Vec<(usize, usize, usize)>> = BTreeMap::new();
    for (f, t) in toks.iter().enumerate() {
        for i in 0..t.len() {
            if !(is_id(t, i, "macro_rules") && is_p(t, i + 1, '!') && is_open(t, i + 3)) {
                continue;
            }
            let Some(name) = id(t, i + 2) else { continue };
            let e = group_end(t, i + 3);
            let mut k = i + 4;
            while k < e - 1 {
                if is_open(t, k) && is_p(t, group_end(t, k), '=') {
                    let arrow = group_end(t, k);
                    let body = arrow + 2;
                    if is_open(t, body) {
                        let be = group_end(t, body);
                        out.entry(name.to_string())
                            .or_default()
                            .push((f, body + 1, be - 1));
                        k = be;
                        continue;
                    }
                }
                k += 1;
            }
        }
    }
    out
}

/// `use` imports per (unit, module): alias and imported path.
type Uses = BTreeMap<(usize, Vec<String>), Vec<(String, Vec<String>)>>;

/// Context for resolving a path.
struct RCtx<'b> {
    unit: usize,
    module: &'b [String],
    owner: Option<&'b str>,
    generics: &'b [String],
}

/// The parsed and resolved sources.
pub(crate) struct Program {
    pub(crate) fns: Vec<FnDef>,
    files: Vec<PathBuf>,
    groups: Vec<String>,
    primary: Vec<Option<usize>>,
    unit_group: Vec<usize>,
    unit_name: Vec<String>,
    modules: BTreeSet<(usize, Vec<String>)>,
    uses: Uses,
    globs: BTreeMap<(usize, Vec<String>), Vec<Vec<String>>>,
    by_module: BTreeMap<(usize, Vec<String>, String), Vec<usize>>,
    by_owner: BTreeMap<(usize, String, String), Vec<usize>>,
    owned: BTreeMap<String, Vec<usize>>,
    methods: BTreeMap<String, Vec<usize>>,
    by_name_unit: BTreeMap<(usize, String), Vec<usize>>,
    by_name_group: BTreeMap<(usize, String), Vec<usize>>,
}

/// One scanned crate: its name and its sources (path, text).
pub(crate) type Group = (String, Vec<(PathBuf, String)>);

/// Parses and resolves `groups`. With `multi`, displayed names carry the crate name.
pub(crate) fn build(groups: &[Group], multi: bool) -> Program {
    let mut fl = Files { files: Vec::new() };
    for (g, (_, srcs)) in groups.iter().enumerate() {
        for (p, s) in srcs {
            fl.add(g, p, s.clone());
        }
    }
    let mut f = 0;
    while f < fl.files.len() {
        fl.ensure(f, 0);
        f += 1;
    }
    let tree = Tree::build(&mut fl);
    let toks: Vec<Vec<Tok>> = fl
        .files
        .iter()
        .map(|x| x.toks.clone().unwrap_or_default())
        .collect();
    let macros = collect_macros(&toks);
    let mut b = Builder {
        toks: &toks,
        macros: &macros,
        fns: Vec::new(),
        modules: BTreeSet::new(),
        uses: BTreeMap::new(),
        globs: BTreeMap::new(),
    };
    for (f, t) in toks.iter().enumerate() {
        let Some(unit) = tree.unit_of.get(f).copied().flatten() else {
            continue;
        };
        let module = tree.module_of[f].clone();
        for k in 0..=module.len() {
            b.modules.insert((unit, module[..k].to_vec()));
        }
        let sc = Scope {
            unit,
            module,
            owner: None,
            generics: Vec::new(),
        };
        b.items(t, 0, t.len(), &sc);
    }
    let unit_group: Vec<usize> = tree.units.iter().map(|u| u.0).collect();
    let primary = (0..groups.len())
        .map(|g| primary_unit(&fl, &tree, g))
        .collect::<Vec<_>>();
    let unit_name = tree
        .units
        .iter()
        .enumerate()
        .map(|(u, &(g, root))| {
            if primary[g] == Some(u) {
                groups[g].0.clone()
            } else {
                fl.files[root]
                    .path
                    .file_stem()
                    .map(|s| s.to_string_lossy().into_owned())
                    .unwrap_or_default()
            }
        })
        .collect();
    let mut p = Program {
        fns: b.fns,
        files: fl.files.iter().map(|x| x.path.clone()).collect(),
        groups: groups.iter().map(|g| g.0.clone()).collect(),
        primary,
        unit_group,
        unit_name,
        modules: b.modules,
        uses: b.uses,
        globs: b.globs,
        by_module: BTreeMap::new(),
        by_owner: BTreeMap::new(),
        owned: BTreeMap::new(),
        methods: BTreeMap::new(),
        by_name_unit: BTreeMap::new(),
        by_name_group: BTreeMap::new(),
    };
    p.index();
    p.resolve_all();
    p.displays(multi);
    p
}

/// `lib.rs` unit of group `g`, else `main.rs`, else its only unit.
fn primary_unit(fl: &Files, tree: &Tree, g: usize) -> Option<usize> {
    let units: Vec<usize> = (0..tree.units.len())
        .filter(|&u| tree.units[u].0 == g)
        .collect();
    for want in ["lib.rs", "main.rs"] {
        if let Some(&u) = units.iter().find(|&&u| {
            fl.files[tree.units[u].1]
                .path
                .file_name()
                .is_some_and(|n| n == want)
        }) {
            return Some(u);
        }
    }
    (units.len() == 1).then(|| units[0])
}

impl Program {
    fn index(&mut self) {
        for (k, f) in self.fns.iter().enumerate() {
            if f.closure_of.is_some() || f.item_init {
                continue;
            }
            let g = self.unit_group[f.unit];
            match &f.owner {
                None => self
                    .by_module
                    .entry((f.unit, f.module.clone(), f.name.clone()))
                    .or_default()
                    .push(k),
                Some(o) => {
                    self.by_owner
                        .entry((g, o.clone(), f.name.clone()))
                        .or_default()
                        .push(k);
                    self.owned.entry(f.name.clone()).or_default().push(k);
                }
            }
            if f.has_self {
                self.methods.entry(f.name.clone()).or_default().push(k);
            }
            self.by_name_unit
                .entry((f.unit, f.name.clone()))
                .or_default()
                .push(k);
            self.by_name_group
                .entry((g, f.name.clone()))
                .or_default()
                .push(k);
        }
    }

    fn resolve_all(&mut self) {
        for k in 0..self.fns.len() {
            let mut events = std::mem::take(&mut self.fns[k].events);
            for e in &mut events {
                self.resolve_event(k, &mut e.ev);
            }
            self.fns[k].events = events;
        }
    }

    fn rctx(&self, k: usize) -> RCtx<'_> {
        let f = &self.fns[k];
        RCtx {
            unit: f.unit,
            module: &f.module,
            owner: f.owner.as_deref(),
            generics: &f.generics,
        }
    }

    fn resolve_event(&self, k: usize, ev: &mut Ev) {
        let cx = self.rctx(k);
        match ev {
            Ev::Call {
                segs,
                name,
                args,
                res,
            } => {
                *res = self.resolve(&cx, segs, name, 0);
                self.resolve_args(&cx, args);
            }
            Ev::Method {
                name,
                args,
                qualified,
                res,
                ..
            } => {
                let table = if *qualified {
                    &self.owned
                } else {
                    &self.methods
                };
                *res = Res::Fns(table.get(name.as_str()).cloned().unwrap_or_default());
                self.resolve_args(&cx, args);
            }
            Ev::Value { segs, name, res } => *res = self.value_res(&cx, segs, name),
            _ => {}
        }
    }

    fn resolve_args(&self, cx: &RCtx<'_>, args: &mut [Arg]) {
        for a in args {
            if let Arg::Named { segs, name, res } = a {
                *res = self.value_res(cx, segs, name);
            }
        }
    }

    /// A name used as a value: like a call, but unqualified names only match free
    /// functions (not methods).
    fn value_res(&self, cx: &RCtx<'_>, segs: &[String], name: &str) -> Res {
        let keep = |v: Vec<usize>| -> Vec<usize> {
            v.into_iter()
                .filter(|&f| !segs.is_empty() || !self.fns[f].has_self)
                .collect()
        };
        match self.resolve(cx, segs, name, 0) {
            Res::Fns(v) if !keep(v.clone()).is_empty() => Res::Fns(keep(v)),
            Res::Guess(v) if !keep(v.clone()).is_empty() => Res::Guess(keep(v)),
            _ => Res::Unresolved,
        }
    }

    fn has_module(&self, unit: usize, m: &[String]) -> bool {
        self.modules.contains(&(unit, m.to_vec()))
    }

    fn use_alias(&self, unit: usize, m: &[String], name: &str) -> Option<&Vec<String>> {
        self.uses
            .get(&(unit, m.to_vec()))?
            .iter()
            .find(|(a, _)| a == name)
            .map(|(_, p)| p)
    }

    fn group_by_name(&self, name: &str) -> Option<usize> {
        self.groups.iter().position(|g| g == name)
    }

    fn resolve(&self, cx: &RCtx<'_>, segs: &[String], name: &str, depth: u32) -> Res {
        if depth > 8 {
            return Res::Unresolved;
        }
        let Some(first) = segs.first() else {
            return self
                .in_module(cx.unit, cx.module, name, depth)
                .unwrap_or_else(|| self.fallback(cx.unit, name));
        };
        let rest = &segs[1..];
        let group = self.unit_group[cx.unit];
        match first.as_str() {
            "core" | "std" | "alloc" if !self.has_module(cx.unit, &segs[..1]) => {
                let rest: Vec<&str> = rest.iter().map(String::as_str).collect();
                let drop = is_drop_function(first, &rest, name);
                let cost = (in_core_table(first, &rest, name) || drop).then_some(0);
                Res::External { cost, frees: drop }
            }
            "crate" | "$crate" => self.walk(cx.unit, Vec::new(), rest, name, depth),
            "self" => self.walk(cx.unit, cx.module.to_vec(), rest, name, depth),
            "super" => {
                let mut m = cx.module.to_vec();
                let mut k = 0;
                while segs.get(k).is_some_and(|s| s == "super") {
                    m.pop();
                    k += 1;
                }
                self.walk(cx.unit, m, &segs[k..], name, depth)
            }
            "Self" if rest.is_empty() => {
                let v = cx
                    .owner
                    .and_then(|o| self.by_owner.get(&(group, o.to_string(), name.to_string())));
                match v {
                    Some(v) => Res::Fns(v.clone()),
                    None => self.owned_or_fallback(cx.unit, name),
                }
            }
            g if rest.is_empty() && cx.generics.iter().any(|x| x == g) => {
                // `T::f()` for a generic `T`: only methods inside `impl`/`trait` blocks;
                // a unique one is taken as the target, several are a guess
                match self.owned.get(name) {
                    Some(v) if v.len() == 1 => Res::Fns(v.clone()),
                    Some(v) => Res::Guess(v.clone()),
                    None => Res::Unresolved,
                }
            }
            _ => self.relative(cx, segs, name, depth),
        }
    }

    fn owned_or_fallback(&self, unit: usize, name: &str) -> Res {
        match self.owned.get(name) {
            Some(v) => Res::Guess(v.clone()),
            None => self.fallback(unit, name),
        }
    }

    /// `first::..::name` with `first` not a keyword root.
    fn relative(&self, cx: &RCtx<'_>, segs: &[String], name: &str, depth: u32) -> Res {
        let first = &segs[0];
        let rest = &segs[1..];
        let mut local = cx.module.to_vec();
        local.push(first.clone());
        if self.has_module(cx.unit, &local) {
            return self.walk(cx.unit, cx.module.to_vec(), segs, name, depth);
        }
        if let Some(path) = self.use_alias(cx.unit, cx.module, first) {
            let mut p = path.clone();
            p.extend(rest.iter().cloned());
            let inner = RCtx {
                unit: cx.unit,
                module: cx.module,
                owner: None,
                generics: &[],
            };
            return self.resolve(&inner, &p, name, depth + 1);
        }
        if self.has_module(cx.unit, &segs[..1]) {
            return self.walk(cx.unit, Vec::new(), segs, name, depth);
        }
        if let Some(g) = self.group_by_name(first) {
            return self.in_group(g, rest, name, depth);
        }
        let group = self.unit_group[cx.unit];
        if rest.is_empty()
            && let Some(v) = self.by_owner.get(&(group, first.clone(), name.to_string()))
        {
            return Res::Fns(v.clone());
        }
        self.fallback(cx.unit, name)
    }

    fn in_group(&self, g: usize, segs: &[String], name: &str, depth: u32) -> Res {
        match self.primary[g] {
            // a name match inside a scanned crate stands for a definition there
            Some(u) => match self.walk(u, Vec::new(), segs, name, depth + 1) {
                Res::Guess(v) => Res::Fns(v),
                r => r,
            },
            None => match self.by_name_group.get(&(g, name.to_string())) {
                Some(v) => Res::Fns(v.clone()),
                None => Res::Unresolved,
            },
        }
    }

    /// Walks `segs` as modules from `base` in `unit`, then looks `name` up.
    fn walk(&self, unit: usize, base: Vec<String>, segs: &[String], name: &str, depth: u32) -> Res {
        let group = self.unit_group[unit];
        let mut m = base;
        for (k, s) in segs.iter().enumerate() {
            let mut next = m.clone();
            next.push(s.clone());
            if self.has_module(unit, &next) {
                m = next;
                continue;
            }
            if let Some(path) = self.use_alias(unit, &m, s) {
                let mut p = path.clone();
                p.extend(segs[k + 1..].iter().cloned());
                let inner = RCtx {
                    unit,
                    module: &m,
                    owner: None,
                    generics: &[],
                };
                return self.resolve(&inner, &p, name, depth + 1);
            }
            if k + 1 == segs.len()
                && let Some(v) = self.by_owner.get(&(group, s.clone(), name.to_string()))
            {
                return Res::Fns(v.clone());
            }
            return self.fallback(unit, name);
        }
        self.in_module(unit, &m, name, depth)
            .unwrap_or_else(|| self.fallback(unit, name))
    }

    /// `name` defined in, or imported into, module `m` of `unit`.
    fn in_module(&self, unit: usize, m: &[String], name: &str, depth: u32) -> Option<Res> {
        if let Some(v) = self.by_module.get(&(unit, m.to_vec(), name.to_string())) {
            return Some(Res::Fns(v.clone()));
        }
        if depth > 8 {
            return None;
        }
        let inner = RCtx {
            unit,
            module: m,
            owner: None,
            generics: &[],
        };
        if let Some(path) = self.use_alias(unit, m, name)
            && let Some((last, init)) = path.split_last()
        {
            let r = self.resolve(&inner, init, last, depth + 1);
            if r != Res::Unresolved {
                return Some(r);
            }
        }
        for g in self.globs.get(&(unit, m.to_vec())).into_iter().flatten() {
            if let Some((u, gm)) = self.glob_module(unit, m, g)
                && let Some(r) = self.in_module(u, &gm, name, depth + 1)
            {
                return Some(r);
            }
        }
        None
    }

    /// Module named by a glob import `g::*` written in module `m`.
    fn glob_module(&self, unit: usize, m: &[String], g: &[String]) -> Option<(usize, Vec<String>)> {
        let first = g.first()?;
        let (u, mut base, rest) = match first.as_str() {
            "crate" => (unit, Vec::new(), &g[1..]),
            "self" => (unit, m.to_vec(), &g[1..]),
            "super" => {
                let mut b = m.to_vec();
                let mut k = 0;
                while g.get(k).is_some_and(|s| s == "super") {
                    b.pop();
                    k += 1;
                }
                (unit, b, &g[k..])
            }
            _ => {
                let mut local = m.to_vec();
                local.push(first.clone());
                if self.has_module(unit, &local) {
                    (unit, m.to_vec(), g)
                } else {
                    (
                        self.primary[self.group_by_name(first)?]?,
                        Vec::new(),
                        &g[1..],
                    )
                }
            }
        };
        for s in rest {
            base.push(s.clone());
        }
        self.has_module(u, &base).then_some((u, base))
    }

    /// Name match: within the unit, then the crate; capitalised names are
    /// constructors; the prelude `drop` frees.
    fn fallback(&self, unit: usize, name: &str) -> Res {
        if let Some(v) = self.by_name_unit.get(&(unit, name.to_string())) {
            return Res::Guess(v.clone());
        }
        let g = self.unit_group[unit];
        if let Some(v) = self.by_name_group.get(&(g, name.to_string())) {
            return Res::Guess(v.clone());
        }
        if name.starts_with(char::is_uppercase) {
            return Res::Constructor;
        }
        if is_drop_function("", &[], name) {
            return Res::External {
                cost: Some(0),
                frees: true,
            };
        }
        Res::Unresolved
    }

    fn displays(&mut self, multi: bool) {
        for k in 0..self.fns.len() {
            let f = &self.fns[k];
            let d = if f.closure_of.is_some() {
                format!("{{closure@{}}}", self.loc(f.file, f.line))
            } else if f.item_init {
                format!("{{initializer@{}}}", self.loc(f.file, f.line))
            } else {
                let mut parts: Vec<&str> = Vec::new();
                if multi {
                    parts.push(&self.unit_name[f.unit]);
                }
                parts.extend(f.module.iter().map(String::as_str));
                if let Some(o) = &f.owner {
                    parts.push(o);
                }
                parts.push(&f.name);
                parts.join("::")
            };
            self.fns[k].display = d;
        }
    }

    /// `file:line`.
    pub(crate) fn loc(&self, file: usize, line: u32) -> String {
        format!("{}:{line}", self.files[file].display())
    }

    /// Outermost named function of a closure (itself otherwise).
    pub(crate) fn outer(&self, mut f: usize) -> usize {
        while let Some(p) = self.fns[f].closure_of {
            f = p;
        }
        f
    }

    /// Functions marked `#[fip]`/`#[fip(N)]`/`#[fbip]`.
    pub(crate) fn roots(&self) -> Vec<usize> {
        (0..self.fns.len())
            .filter(|&k| {
                self.fns[k].mark.kind != MarkKind::None && self.fns[k].closure_of.is_none()
            })
            .collect()
    }

    /// Functions whose name is used as a value anywhere, and closures passed as
    /// arguments or used as values.
    fn value_used(&self) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        for f in &self.fns {
            for e in &f.events {
                match &e.ev {
                    Ev::Value {
                        res: Res::Fns(v) | Res::Guess(v),
                        ..
                    } => out.extend(v.iter().copied()),
                    Ev::Escape(c) => {
                        out.insert(*c);
                    }
                    Ev::Call { args, .. } | Ev::Method { args, .. } => {
                        out.extend(args.iter().filter_map(|a| match a {
                            Arg::Closure(c) => Some(*c),
                            _ => None,
                        }));
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// Call graph over all functions and closures (a closure is a node of its own,
    /// reached from the function that contains it). Calls through expressions and
    /// parameters in `#[fip]` functions reach every value-used function.
    pub(crate) fn graph(&self) -> Vec<BTreeSet<usize>> {
        let vu = self.value_used();
        let mut g = vec![BTreeSet::new(); self.fns.len()];
        for (k, f) in self.fns.iter().enumerate() {
            let fip = self.fns[self.outer(k)].mark.kind == MarkKind::Fip;
            for e in &f.events {
                match &e.ev {
                    Ev::Call { args, res, .. } | Ev::Method { args, res, .. } => {
                        if let Res::Fns(v) | Res::Guess(v) = res {
                            g[k].extend(v.iter().copied());
                        }
                        g[k].extend(args.iter().filter_map(|a| match a {
                            Arg::Closure(c) => Some(*c),
                            _ => None,
                        }));
                    }
                    Ev::Value {
                        res: Res::Fns(v) | Res::Guess(v),
                        ..
                    } => g[k].extend(v.iter().copied()),
                    Ev::ClosureCall(c) | Ev::Escape(c) => {
                        g[k].insert(*c);
                    }
                    Ev::Indirect | Ev::ParamCall(_) if fip => g[k].extend(vu.iter().copied()),
                    _ => {}
                }
            }
            if let Some(p) = f.closure_of {
                g[p].insert(k);
            }
        }
        g
    }

    /// Cycles reachable from `root` in `g`, as display names (closures folded into
    /// the function that contains them; first name repeated at the end).
    pub(crate) fn cycles_from(&self, g: &[BTreeSet<usize>], root: usize) -> BTreeSet<Vec<String>> {
        let mut out = BTreeSet::new();
        let mut stack = vec![root];
        let mut budget = 2_000_000_u64;
        self.dfs(g, &mut stack, &mut out, &mut budget);
        out
    }

    fn dfs(
        &self,
        g: &[BTreeSet<usize>],
        stack: &mut Vec<usize>,
        out: &mut BTreeSet<Vec<String>>,
        budget: &mut u64,
    ) {
        let cur = stack.last().copied().unwrap_or_default();
        for &c in &g[cur] {
            if *budget == 0 {
                return;
            }
            *budget -= 1;
            if let Some(pos) = stack.iter().position(|&s| s == c) {
                out.insert(self.cycle_names(&stack[pos..]));
                continue;
            }
            stack.push(c);
            self.dfs(g, stack, out, budget);
            stack.pop();
        }
    }

    /// Shortest call chain in `g` from `root` to a function displayed as `target`
    /// (closures folded into their function), as display names.
    pub(crate) fn chain_to(&self, g: &[BTreeSet<usize>], root: usize, target: &str) -> Vec<String> {
        let mut prev = vec![usize::MAX; g.len()];
        let mut seen = vec![false; g.len()];
        let mut queue = std::collections::VecDeque::from([root]);
        seen[root] = true;
        let mut hit = None;
        while let Some(n) = queue.pop_front() {
            if self.fns[self.outer(n)].display == target {
                hit = Some(n);
                break;
            }
            for &c in &g[n] {
                if !seen[c] {
                    seen[c] = true;
                    prev[c] = n;
                    queue.push_back(c);
                }
            }
        }
        let mut ids = Vec::new();
        let mut cur = hit;
        while let Some(n) = cur {
            ids.push(self.outer(n));
            cur = (prev[n] != usize::MAX).then_some(prev[n]);
        }
        ids.reverse();
        ids.dedup();
        ids.iter().map(|&k| self.fns[k].display.clone()).collect()
    }

    fn cycle_names(&self, nodes: &[usize]) -> Vec<String> {
        let mut ids: Vec<usize> = nodes.iter().map(|&n| self.outer(n)).collect();
        ids.dedup();
        while ids.len() > 1 && ids.first() == ids.last() {
            ids.pop();
        }
        let mut names: Vec<String> = ids.iter().map(|&k| self.fns[k].display.clone()).collect();
        let min = names
            .iter()
            .enumerate()
            .min_by(|a, b| a.1.cmp(b.1))
            .map_or(0, |(i, _)| i);
        names.rotate_left(min);
        if let Some(first) = names.first().cloned() {
            names.push(first);
        }
        names
    }
}

/// Every `.rs` file under `dir`, sorted, with its text.
///
/// # Panics
///
/// Panics if `dir` or a file in it cannot be read.
pub(crate) fn read_dir_sources(dir: &Path) -> Vec<(PathBuf, String)> {
    let mut files = Vec::new();
    collect(dir, &mut files);
    files.sort();
    files
        .into_iter()
        .map(|p| {
            let s = fs::read_to_string(&p).expect("read source file");
            (p, s)
        })
        .collect()
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in fs::read_dir(dir).expect("read source dir") {
        let p = e.expect("dir entry").path();
        if p.is_dir() {
            collect(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
}
