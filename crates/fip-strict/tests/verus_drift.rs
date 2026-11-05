// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `FipBound`, `FipFn` and `Certified` are declared twice in `src/lib.rs`: plainly,
//! and inside `verus! { }` for the `verus` driver (the constructors
//! `Certified::assume` / `assume_no_panic_macros` are one shared source with their
//! Verus specification in `cfg_attr`, so they are not compared here). The Verus declarations may only
//! add ghost items (`spec fn`, `requires`/`ensures`/`allocates`, named returns);
//! everything that exists at run time must be the same. This test strips the ghost
//! parts and compares.
//!
//! Verus-only additions of the allocation check (decision
//! 2026-11-06-redesign-verus-allocates, phase 3), also stripped: the bound
//! `: vstd::alloc_check::AllocFreeDrop` on type parameters (the plain marker holds for
//! every type), the `unsafe impl .. vstd::alloc_check::AllocFreeDrop for ..` markers
//! with an empty body, and the per-arity `FipFn` impls of `Compose`
//! (`compose_fip_fn!`), compared with the plain impl generic over `Args`.

/// The checked source; `FIP_DRIFT_SRC` overrides it (the `verify-negative` recipe
/// uses that to show the test fails on a mutated copy).
fn src() -> &'static str {
    match std::env::var("FIP_DRIFT_SRC") {
        Ok(p) => Box::leak(
            std::fs::read_to_string(p)
                .expect("read FIP_DRIFT_SRC")
                .into_boxed_str(),
        ),
        Err(_) => include_str!("../src/lib.rs"),
    }
}

/// Removes `//` comments and attributes, ghost items and clauses, named returns and
/// all whitespace.
fn normalize(item: &str) -> String {
    let no_comments: String = item
        .lines()
        .map(|l| l.split("//").next().unwrap_or(""))
        .collect::<Vec<_>>()
        .join(" ");
    let mut s = remove_balanced(&no_comments, "#[", '[', ']');
    s = remove_spec_fns(&s);
    for kw in ["requires", "ensures", "allocates"] {
        s = remove_clause(&s, kw);
    }
    s = unname_returns(&s);
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    s.replace(",}", "}")
        .replace(",)", ")")
        .replace(",;", ";")
        .replace(VERUS_DROP_BOUND, "")
}

/// The drop bound of `-V alloc-check` on a type parameter (whitespace removed).
const VERUS_DROP_BOUND: &str = ":vstd::alloc_check::AllocFreeDrop";

/// A Verus-only drop marker impl (normalized): no run-time content.
fn is_drop_marker(item: &str) -> bool {
    item.starts_with("unsafeimpl<")
        && item.contains(">vstd::alloc_check::AllocFreeDropfor")
        && item.ends_with("{}")
}

/// Index just past the delimiter matching the opener at `open_at`.
fn matching(s: &str, open_at: usize, open: char, close: char) -> usize {
    let mut depth = 0;
    for (k, c) in s[open_at..].char_indices() {
        if c == open {
            depth += 1;
        } else if c == close {
            depth -= 1;
            if depth == 0 {
                return open_at + k + c.len_utf8();
            }
        }
    }
    s.len()
}

fn remove_balanced(s: &str, start: &str, open: char, close: char) -> String {
    let mut out = String::new();
    let mut rest = s;
    while let Some(p) = rest.find(start) {
        out.push_str(&rest[..p]);
        let open_at = p + start.len() - open.len_utf8();
        let end = matching(rest, open_at, open, close);
        rest = &rest[end..];
    }
    out.push_str(rest);
    out
}

/// End of an item starting at `from`: its `;`, or the end of its `{ .. }` body.
fn item_end(s: &str, from: usize) -> usize {
    let mut paren = 0;
    let mut prev = ' ';
    for (k, c) in s[from..].char_indices() {
        match c {
            '(' | '<' => paren += 1,
            ')' => paren -= 1,
            '>' if prev != '-' && prev != '=' => paren -= 1,
            ';' if paren == 0 => return from + k + 1,
            '{' if paren == 0 => return matching(s, from + k, '{', '}'),
            _ => {}
        }
        prev = c;
    }
    s.len()
}

fn remove_spec_fns(s: &str) -> String {
    let mut s = s.to_string();
    while let Some(p) = s.find("spec fn") {
        let mut start = p;
        for prefix in ["open ", "closed ", "pub "] {
            if s[..start].trim_end().ends_with(prefix.trim_end()) {
                start = s[..start].trim_end().len() - prefix.trim_end().len();
            }
        }
        let end = item_end(&s, p);
        s.replace_range(start..end, "");
    }
    s
}

/// Removes `kw ...` up to (not including) the next `;` or `{` outside parentheses.
fn remove_clause(s: &str, kw: &str) -> String {
    let mut s = s.to_string();
    while let Some(p) = find_word(&s, kw) {
        let mut paren = 0;
        let mut end = s.len();
        for (k, c) in s[p..].char_indices() {
            match c {
                '(' => paren += 1,
                ')' => paren -= 1,
                ';' | '{' if paren == 0 => {
                    end = p + k;
                    break;
                }
                _ => {}
            }
        }
        s.replace_range(p..end, "");
    }
    s
}

fn find_word(s: &str, w: &str) -> Option<usize> {
    let mut from = 0;
    while let Some(k) = s[from..].find(w) {
        let p = from + k;
        let before = s[..p].chars().next_back();
        let after = s[p + w.len()..].chars().next();
        let boundary = |c: Option<char>| c.is_none_or(|c| !(c.is_alphanumeric() || c == '_'));
        if boundary(before) && boundary(after) {
            return Some(p);
        }
        from = p + w.len();
    }
    None
}

/// `-> (r: T)` becomes `-> T`.
fn unname_returns(s: &str) -> String {
    let mut s = s.to_string();
    let mut from = 0;
    while let Some(k) = s[from..].find("-> (") {
        let p = from + k;
        let open = p + 3;
        let close = matching(&s, open, '(', ')');
        let inner = s[open + 1..close - 1].to_string();
        if let Some((name, ty)) = inner.split_once(':')
            && name.trim().chars().all(|c| c.is_alphanumeric() || c == '_')
            && !ty.starts_with(':')
        {
            s.replace_range(open..close, ty.trim());
        }
        from = p + 3;
    }
    s
}

/// Text between two marker comments.
fn region(start: &str, end: &str) -> &'static str {
    let src = src();
    let a = src.find(start).expect("start marker");
    let b = src[a..].find(end).expect("end marker") + a;
    &src[a..b]
}

/// Top-level items of a region (lines starting at column 0 with `pub`, `impl`,
/// `unsafe impl`, or indented by one level inside `verus! { }`), normalized. An
/// `impl` block that holds only ghost items (empty once normalized, e.g. the Verus
/// `impl<..> Certified<..> { closed spec fn inner .. }`) has no run-time content and
/// is left out.
fn items(region: &str) -> Vec<String> {
    let heads = [
        "pub unsafe trait",
        "pub trait",
        "pub struct",
        "impl<",
        "unsafe impl<",
    ];
    let mut out = Vec::new();
    let mut k = 0;
    while k < region.len() {
        let line_end = region[k..].find('\n').map_or(region.len(), |e| k + e + 1);
        let line = &region[k..line_end];
        if heads.iter().any(|h| line.starts_with(h)) {
            let end = item_end(region, k);
            let item = normalize(&region[k..end]);
            if !(item.starts_with("impl<") && item.ends_with("{}")) {
                out.push(item);
            }
            k = end;
        } else {
            k = line_end;
        }
    }
    out
}

#[test]
fn verus_declarations_match_the_plain_ones() {
    let mut plain = items(region(
        "// ---- Plain declarations",
        "// ---- Verus declarations",
    ));
    // The shared items after the `verus!` block (one source for both builds, e.g.
    // `Certified::assume`) are not twins and are not compared.
    let verus_decls = region("// ---- Verus declarations", "// ---- Shared items");
    let (markers, verus): (Vec<String>, Vec<String>) = items(verus_decls)
        .into_iter()
        .partition(|i| is_drop_marker(i));
    assert_eq!(plain.len(), 13, "plain items: {plain:#?}");
    assert_eq!(
        markers.len(),
        4,
        "drop markers (Certified, Stateless, Compose, Then): {markers:#?}"
    );
    // `Compose`'s `FipFn` impl is per arity under Verus (`compose_fip_fn!`).
    let compose = plain
        .iter()
        .position(|i| i.contains("FipFn<Args>forCompose<F,G>"))
        .expect("plain Compose impl");
    plain.remove(compose);
    assert_eq!(plain, verus);
}

#[test]
fn compose_impls_match_the_plain_one() {
    let plain = items(region(
        "// ---- Plain declarations",
        "// ---- Verus declarations",
    ))
    .into_iter()
    .find(|i| i.contains("FipFn<Args>forCompose<F,G>"))
    .expect("plain Compose impl");
    let mac = region(
        "macro_rules! compose_fip_fn",
        "#[cfg(verus_keep_ghost)]\ncompose_fip_fn!();",
    );
    let p = mac.find("impl<").expect("impl in compose_fip_fn!");
    // `$($A,)*` (the arity's argument types) read as one type parameter `Args`.
    let verus = normalize(&mac[p..item_end(mac, p)])
        .replace("impl<$($A)*", "impl<Args,")
        .replace("($($A)*)", "Args");
    assert_eq!(plain, verus);
    // One impl per closure arity `0..=MAX_ARITY`, as for `Certified`.
    let src = src();
    let arities = |name: &str| src.lines().filter(|l| l.starts_with(name)).count();
    assert_eq!(arities("compose_fip_fn!("), arities("certified_fip_fn!("));
    assert_eq!(arities("certified_fip_fn!("), fip_strict::MAX_ARITY + 1);
}

#[test]
fn certified_impls_match_in_both_arms() {
    let mac = region("macro_rules! certified_fip_fn", "certified_fip_fn!();");
    let starts: Vec<usize> = mac.match_indices("impl<").map(|(p, _)| p).collect();
    assert_eq!(starts.len(), 2);
    let arms: Vec<String> = starts
        .iter()
        .map(|&p| normalize(&mac[p..item_end(mac, p)]))
        .collect();
    assert_eq!(arms[0], arms[1]);
}

#[test]
fn normalization_removes_only_ghost_parts() {
    assert_eq!(
        normalize("fn call(&self, a: A) -> (r: B)\n requires p(a),\n ensures q(a, r),\n ;"),
        normalize("fn call(&self, a: A) -> B;")
    );
    assert_eq!(
        normalize("trait T { type O; open spec fn pre(&self) -> bool { true } fn f(&self); }"),
        normalize("trait T { type O; fn f(&self); }")
    );
    // The drop bound is Verus-only; another bound is not normalized away.
    assert_eq!(
        normalize("impl<A: vstd::alloc_check::AllocFreeDrop, B> T for S<A, B> {}"),
        normalize("impl<A, B> T for S<A, B> {}")
    );
    assert_ne!(
        normalize("impl<A: Copy, B> T for S<A, B> {}"),
        normalize("impl<A, B> T for S<A, B> {}")
    );
    assert_eq!(
        normalize("fn call(&self, a: A) -> (r: B)\n requires p(a),\n allocates self.allocs()\n ;"),
        normalize("fn call(&self, a: A) -> B;")
    );
    // An exec difference is not normalized away.
    assert_ne!(
        normalize("fn call(&self, a: A) -> (r: B);"),
        normalize("fn call(&self, a: A) -> C;")
    );
    assert_ne!(
        normalize("fn f(&self, a: (A,)) {}"),
        normalize("fn f(&self, a: (A, B)) {}")
    );
}
