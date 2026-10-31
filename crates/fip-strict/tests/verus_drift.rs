// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `FipBound`, `FipFn` and `Certified` are declared twice in `src/lib.rs`: plainly,
//! and inside `verus! { }` for the `verus` driver. The Verus declarations may only
//! add ghost items (`spec fn`, `requires`/`ensures`, named returns); everything that
//! exists at run time must be the same. This test strips the ghost parts and compares.

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
    for kw in ["requires", "ensures"] {
        s = remove_clause(&s, kw);
    }
    s = unname_returns(&s);
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    s.replace(",}", "}").replace(",)", ")").replace(",;", ";")
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
/// `unsafe impl`, or indented by one level inside `verus! { }`), normalized.
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
            out.push(normalize(&region[k..end]));
            k = end;
        } else {
            k = line_end;
        }
    }
    out
}

#[test]
fn verus_declarations_match_the_plain_ones() {
    let plain = items(region(
        "// ---- Plain declarations",
        "// ---- Verus declarations",
    ));
    let verus_decls = region(
        "// ---- Verus declarations",
        "macro_rules! certified_fip_fn",
    );
    let verus = items(verus_decls);
    assert_eq!(plain.len(), 5, "plain items: {plain:#?}");
    assert_eq!(plain, verus);
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
