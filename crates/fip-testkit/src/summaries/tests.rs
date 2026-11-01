// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! Unit tests of the summary fixpoint (acceptance list of
//! `TODOs/callgraph-fip-summaries.md`).

use super::*;

fn report(src: &str) -> Report {
    fip_violations_in(&[(PathBuf::from("x.rs"), src.to_string())])
}

fn kinds(r: &Report) -> Vec<ViolationKind> {
    r.violations.iter().map(|v| v.kind.clone()).collect()
}

fn summary_of<'r>(r: &'r Report, root: &str) -> &'r str {
    r.roots
        .iter()
        .find(|s| s.root == root)
        .map_or("", |s| s.summary.as_str())
}

const HELPER: &str = "fn helper() -> Box<u8> {\n    Box::new(1)\n}\n";

#[test]
fn allocation_in_a_callee_violates_fip() {
    let r = report(&format!(
        "{HELPER}#[fip]\nfn a() {{ let _b = helper(); }}\n"
    ));
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Finite(1),
            allowed: 0
        }]
    );
    assert_eq!(
        r.violations[0].witness,
        "a -> helper: allocation site `Box::new` at x.rs:2"
    );
}

#[test]
fn fip_one_with_one_allocating_call_passes() {
    let r = report(&format!(
        "{HELPER}#[fip(1)]\nfn a() -> Box<u8> {{ helper() }}\n"
    ));
    assert_eq!(r.violations, Vec::new());
    assert_eq!(summary_of(&r, "a"), "1");
}

#[test]
fn fip_one_with_two_allocating_calls_is_two() {
    let r = report(&format!(
        "{HELPER}#[fip(1)]\nfn a() -> (Box<u8>, Box<u8>) {{ (helper(), helper()) }}\n"
    ));
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Finite(2),
            allowed: 1
        }]
    );
}

#[test]
fn allocating_call_in_a_loop_is_unbounded() {
    let r = report(&format!(
        "{HELPER}#[fip(3)]\nfn a(n: u8) {{\n    for _ in 0..n {{\n        let _b = helper();\n    }}\n}}\n"
    ));
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Infinite,
            allowed: 3
        }]
    );
    assert_eq!(
        r.violations[0].witness,
        "a -> helper (in loop): allocation site `Box::new` at x.rs:2"
    );
}

#[test]
fn witness_marks_the_loop_on_the_chain() {
    let r = report(
        "#[fip(2)]\nfn a() { for i in 0..3 { b(i) } }\nfn b(i: u8) { c(i) }\nfn c(i: u8) {\n    let _x = Box::new(i);\n}\n",
    );
    assert_eq!(
        r.violations[0].witness,
        "a -> b (in loop) -> c: allocation site `Box::new` at x.rs:5"
    );
}

#[test]
fn zero_cost_calls_in_loops_stay_zero() {
    let r = report(
        "#[fip]\nfn a(xs: &mut [u8]) { let mut i = 0; while i < xs.len() { b(xs, i); i += 1; } }\nfn b(xs: &mut [u8], i: usize) { core::mem::swap(&mut xs[i], &mut 0) }\n",
    );
    assert_eq!(r.violations, Vec::new());
    assert_eq!(summary_of(&r, "a"), "0");
}

#[test]
fn allocation_under_fbip_callers_only_does_not_affect_fip_roots() {
    let r = report(&format!(
        "{HELPER}#[fip]\nfn a() -> u8 {{ 1 }}\n#[fbip]\nfn c(n: u8) {{ if n > 0 {{ let _x = helper(); c(n - 1) }} }}\n"
    ));
    assert!(r.violations.iter().all(|v| v.root == "c"), "{r}");
    assert_eq!(summary_of(&r, "a"), "0");
    // `#[fbip]` may recurse but must not allocate: the recursion widens to ∞
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Infinite,
            allowed: 0
        }]
    );
}

#[test]
fn recursive_fbip_without_allocation_passes() {
    let r = report(
        "#[fbip]\nfn count_down(n: u32) -> u32 { if n == 0 { 0 } else { count_down(n - 1) } }\n",
    );
    assert_eq!(r.violations, Vec::new());
    assert_eq!(summary_of(&r, "count_down"), "0");
}

#[test]
fn undefined_function_is_unknown_not_zero() {
    let r = report("#[fip]\nfn a() {\n    mystery()\n}\n");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::Unresolved {
            what: "unresolved call `mystery`".to_string(),
            at: "x.rs:3".to_string()
        }]
    );
    assert_eq!(summary_of(&r, "a"), "⊤");
}

#[test]
fn every_unresolved_leaf_is_listed() {
    let r = report("#[fip]\nfn a() { b(); m2() }\nfn b() { m1() }\n");
    let whats: Vec<String> = r.violations.iter().map(|v| v.witness.clone()).collect();
    assert_eq!(
        whats,
        vec![
            "a -> b: unresolved call `m1` at x.rs:3".to_string(),
            "a: unresolved call `m2` at x.rs:2".to_string()
        ]
    );
}

const EACH: &str = "#[fip]\nfn each<G: Fn(u8) -> u8>(xs: &mut [u8], g: G) {\n    let mut i = 0;\n    while i < xs.len() {\n        xs[i] = g(xs[i]);\n        i += 1;\n    }\n}\n";

#[test]
fn higher_order_root_is_conditional() {
    let r = report(EACH);
    assert_eq!(r.violations, Vec::new());
    assert_eq!(
        r.conditional,
        vec![Conditional {
            root: "each".to_string(),
            attribute: "#[fip]".to_string(),
            summary: "∞·alloc(g)".to_string()
        }]
    );
}

#[test]
fn closure_arguments_instantiate_the_parameter() {
    let r = report(&format!(
        "{EACH}#[fip]\nfn good(xs: &mut [u8]) {{ each(xs, |x| x + 1) }}\n#[fip]\nfn bad(xs: &mut [u8]) {{\n    each(xs, |x| *Box::new(x))\n}}\n"
    ));
    assert_eq!(summary_of(&r, "good"), "0");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Infinite,
            allowed: 0
        }]
    );
    assert_eq!(r.violations[0].root, "bad");
    assert_eq!(
        r.violations[0].witness,
        "bad -> each -> {closure@x.rs:13} (argument for `g`) (in loop): allocation site `Box::new` at x.rs:13"
    );
}

#[test]
fn named_function_and_forwarded_parameter_arguments() {
    let r = report(&format!(
        "{EACH}fn inc(x: u8) -> u8 {{ x + 1 }}\n#[fip]\nfn named(xs: &mut [u8]) {{ each(xs, inc) }}\n#[fip]\nfn fwd<H: Fn(u8) -> u8>(xs: &mut [u8], h: H) {{ each(xs, h) }}\n"
    ));
    assert_eq!(summary_of(&r, "named"), "0");
    assert_eq!(summary_of(&r, "fwd"), "∞·alloc(h)");
    let r = report(&format!(
        "{EACH}#[fip]\nfn opaque(xs: &mut [u8], k: u8) {{ each(xs, make(k)) }}\nfn make(k: u8) -> fn(u8) -> u8 {{ todo_free(k) }}\n"
    ));
    assert!(
        r.violations
            .iter()
            .any(|v| v.root == "opaque" && matches!(v.kind, ViolationKind::Unresolved { .. })),
        "{r}"
    );
}

#[test]
fn declared_parameter_bounds_resolve_the_root() {
    let src = "use fip_strict::FipFn;\n#[fip(strict = true, param(g = 0))]\nfn each<G: FipFn<(u8,), Output = u8>>(xs: &mut [u8], g: G) {\n    let mut i = 0;\n    while i < xs.len() {\n        xs[i] = g.call((xs[i],));\n        i += 1;\n    }\n}\n";
    let r = report(src);
    assert_eq!(r.violations, Vec::new());
    assert_eq!(r.conditional, Vec::new());
    assert_eq!(summary_of(&r, "each"), "0");
    let r = report(&src.replace("g = 0", "g = 1"));
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Infinite,
            allowed: 0
        }]
    );
    assert!(
        r.violations[0]
            .witness
            .contains("call to parameter `g` (bound 1) (in loop)")
    );
}

#[test]
fn arguments_are_checked_against_declared_bounds() {
    let src = "#[fip(1, strict = true, param(make = 1))]\nfn make_once<F>(make: F, x: u32) -> Box<u32>\nwhere\n    F: FipFn<(u32,), Output = Box<u32>>,\n{\n    FipFn::call(&make, (x,))\n}\nfn user() {\n    let mk = fip_macros::fip_fn!(|x: u32| Box::new(x));\n    let _a = make_once(mk, 1);\n    let _b = make_once(fip_fn!(|x: u32| { let _y = Box::new(x); Box::new(x) }), 2);\n}\n";
    let r = report(src);
    assert_eq!(summary_of(&r, "make_once"), "1");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::ArgumentExceedsDeclared {
            caller: "user".to_string(),
            param: "make".to_string(),
            declared: 1,
            bound: Bound::Finite(2),
            at: "x.rs:11".to_string()
        }]
    );
}

#[test]
fn fip_fn_with_a_crate_path_is_a_closure() {
    let src = "#[fip(1, strict = true, param(make = 1), crate = f::fip_strict)]\nfn make_once<F>(make: F, x: u32) -> Box<u32>\nwhere\n    F: FipFn<(u32,), Output = Box<u32>>,\n{\n    FipFn::call(&make, (x,))\n}\nfn user() {\n    let mk = fip_macros::fip_fn!(crate = f::fip_strict, |x: u32| Box::new(x));\n    let _a = make_once(mk, 1);\n    let _b = make_once(fip_fn!(crate = \"f::fip_strict\", move |x: u32| { let _y = Box::new(x); Box::new(x) }), 2);\n}\n";
    let r = report(src);
    assert_eq!(summary_of(&r, "make_once"), "1");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::ArgumentExceedsDeclared {
            caller: "user".to_string(),
            param: "make".to_string(),
            declared: 1,
            bound: Bound::Finite(2),
            at: "x.rs:11".to_string()
        }]
    );
}

#[test]
fn method_calls_resolve_by_name() {
    let r = report(
        "struct S;\nimpl S {\n    fn grow(&self) -> Box<u8> { Box::new(1) }\n}\n#[fip]\nfn a(s: &S) { let _b = s.grow(); }\n",
    );
    assert_eq!(
        r.violations[0].witness,
        "a -> S::grow: allocation site `Box::new` at x.rs:3"
    );
    let r = report("#[fip]\nfn a(x: &[u8]) -> usize { x.len() + <[u8]>::len(x) }\n");
    assert_eq!(r.violations, Vec::new());
    let r = report("#[fip]\nfn a(x: &[u8]) -> usize { x.iter().count() }\n");
    assert_eq!(
        kinds(&r)
            .into_iter()
            .map(|k| match k {
                ViolationKind::Unresolved { what, .. } => what,
                other => format!("{other:?}"),
            })
            .collect::<Vec<_>>(),
        vec![
            "unresolved method `.iter()`".to_string(),
            "unresolved method `.count()`".to_string()
        ]
    );
}

#[test]
fn local_method_named_like_an_alloc_free_one_is_used() {
    let r = report(
        "struct L;\nimpl L {\n    fn len(&self) -> usize { let _b = Box::new(1); 1 }\n}\n#[fip]\nfn a(x: &[u8]) -> usize { x.len() }\n",
    );
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Finite(1),
            allowed: 0
        }]
    );
}

#[test]
fn allocation_methods_count_once() {
    let r = report("#[fip(1)]\nfn a(x: &String) -> String { x.clone() }\n");
    assert_eq!(r.violations, Vec::new());
    assert_eq!(summary_of(&r, "a"), "1");
}

#[test]
fn recursion_is_reported_for_fip_roots() {
    let r = report("#[fip]\nfn f(n: u32) -> u32 { if n == 0 { 0 } else { f(n - 1) } }\n");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::Recursion {
            cycle: vec!["f".to_string(), "f".to_string()]
        }]
    );
}

#[test]
fn recursion_witness_starts_at_the_root() {
    let r = report("#[fip]\nfn a() { b() }\nfn b() { c() }\nfn c() { b() }\n");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::Recursion {
            cycle: vec!["b".to_string(), "c".to_string(), "b".to_string()]
        }]
    );
    assert_eq!(r.violations[0].witness, "a -> b -> c -> b");
}

#[test]
fn macros_core_table_and_drops() {
    let r = report("#[fip]\nfn a() { println!(\"x\") }\n");
    assert!(
        matches!(&kinds(&r)[..], [ViolationKind::Unresolved { what, .. }] if what.contains("println"))
    );
    let r = report(
        "#[fip]\nfn a(x: u8) { assert!(x > 0); debug_assert_eq!(x, 1); let _m = matches!(x, 1); }\n",
    );
    assert_eq!(r.violations, Vec::new());
    let r = report("#[fip]\nfn a(x: Option<u8>) -> Option<u8> { let y = x?; Some(y) }\n");
    assert!(
        matches!(&kinds(&r)[..], [ViolationKind::Unresolved { what, .. }] if what.contains('?'))
    );
    let r = report(
        "#[fip]\nfn a(x: &mut u8, y: &mut u8) { core::mem::swap(x, y); std::mem::replace(x, 1); }\n",
    );
    assert_eq!(r.violations, Vec::new());
    let r = report("#[fip]\nfn a(x: u8, y: u8) -> u8 { core::cmp::min(x, y) }\n");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::Unresolved {
            what: "unresolved call `core::cmp::min`".to_string(),
            at: "x.rs:2".to_string()
        }]
    );
    let r = report("#[fbip]\nfn a(b: Box<u8>) { drop(b) }\n");
    assert_eq!(r.violations, Vec::new());
    assert!(r.roots[0].may_free);
}

#[test]
fn local_macros_expand_into_the_caller() {
    let r = report(
        "macro_rules! mk { ($x:expr) => { Box::new($x) } }\n#[fip]\nfn a() { let _b = mk!(1); }\n",
    );
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Finite(1),
            allowed: 0
        }]
    );
}

#[test]
fn calls_through_expressions_are_unknown() {
    let r = report(
        "struct H { f: fn() }\n#[fip]\nfn a(h: &H) { (h.f)() }\nfn b() { let h = H { f: c }; a(&h) }\nfn c() { b() }\n",
    );
    assert!(
        kinds(&r).contains(&ViolationKind::Unresolved {
            what: "call through an expression".to_string(),
            at: "x.rs:3".to_string()
        }),
        "{r}"
    );
    assert!(
        kinds(&r)
            .iter()
            .any(|k| matches!(k, ViolationKind::Recursion { .. })),
        "{r}"
    );
}

#[test]
fn closures_called_through_locals() {
    let r = report("#[fip(1)]\nfn a() { let k = || Box::new(1); let _x = k(); }\n");
    assert_eq!(r.violations, Vec::new());
    let r =
        report("#[fip(1)]\nfn a() { let k = || Box::new(1); for _ in 0..2 { let _x = k(); } }\n");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::BoundExceeded {
            bound: Bound::Infinite,
            allowed: 1
        }]
    );
}

#[test]
fn crates_resolve_through_pub_use() {
    let core = [(
        PathBuf::from("core_src/lib.rs"),
        "mod slot;\npub use slot::replace;\n".to_string(),
    )];
    let slot = (
        PathBuf::from("core_src/slot.rs"),
        "pub fn replace<T>(s: &mut T, v: T) -> T { let mut v = v; core::mem::swap(s, &mut v); v }\npub fn boxed() -> Box<u8> { Box::new(1) }\n".to_string(),
    );
    let core = [core[0].clone(), slot];
    let app = [(
        PathBuf::from("app/lib.rs"),
        "#[fip]\npub fn a(x: &mut u8) -> u8 { mylib::replace(x, 0) }\n#[fip]\npub fn b() { let _x = mylib::slot::boxed(); }\n".to_string(),
    )];
    let r = fip_violations_in_crates(&[("mylib", &core), ("app", &app)]);
    assert_eq!(summary_of(&r, "app::a"), "0");
    assert_eq!(
        r.violations
            .iter()
            .map(|v| v.witness.clone())
            .collect::<Vec<_>>(),
        vec![
            "app::b -> mylib::slot::boxed: allocation site `Box::new` at core_src/slot.rs:2"
                .to_string()
        ]
    );
}

#[test]
fn name_only_matches_are_unknown_for_bounds() {
    // `ext::f` is not in the scanned sources; the local `m::f` matches only by name
    let r = report("mod m { pub fn f() {} }\n#[fip]\nfn a() { ext::f() }\n");
    assert_eq!(
        kinds(&r),
        vec![ViolationKind::Unresolved {
            what: "unresolved call `ext::f` (only name matches: m::f)".to_string(),
            at: "x.rs:3".to_string()
        }]
    );
    let r = report("mod m { pub fn g() {} }\nuse ext::g;\n#[fip]\nfn a() { g() }\n");
    assert!(
        matches!(&kinds(&r)[..], [ViolationKind::Unresolved { what, .. }] if what.contains("`g`")),
        "{r}"
    );
    // resolved paths are exact
    let r =
        report("mod m { pub fn f() {} }\n#[fip]\nfn a() { m::f(); self::m::f(); crate::m::f() }\n");
    assert_eq!(r.violations, Vec::new());
}

#[test]
fn for_loops_call_the_iterator_implicitly() {
    let r = report("#[fip]\nfn a(n: u8) -> u8 { let mut s = 0; for i in 0..n { s += i; } s }\n");
    assert_eq!(r.violations, Vec::new());
    let r = report("#[fip]\nfn a(xs: &[u8]) -> u8 { let mut s = 0; for x in xs { s += *x; } s }\n");
    assert!(
        kinds(&r).contains(&ViolationKind::Unresolved {
            what: "unresolved method `.next()` (in loop)".to_string(),
            at: "x.rs:2".to_string()
        }),
        "{r}"
    );
}
