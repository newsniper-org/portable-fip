// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN)

//! `fip_lint_rules::NON_ALLOCATING_CONSTRUCTORS`: `#[fip]` and strict functions using
//! them are accepted, and the counting allocator measures 0 allocations and 0 frees
//! for every entry. `fip-prelint` analyses this crate in its self-check
//! (`tools/fip-prelint/tests/selfcheck.expected`, crate `non_allocating_ctors`): every
//! root passes, so the MIR checker agrees.

#![allow(
    clippy::mem_replace_with_default,
    clippy::linkedlist,
    reason = "the constructors are measured as written (`mem::take` calls `Default::default`)"
)]

use std::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};

use fip_lint_rules::NON_ALLOCATING_CONSTRUCTORS;
use fip_macros::fip;
use fip_testkit::assert_fip;

fip_testkit::install!();

/// The motivating case: take a vector out, leaving an empty one.
#[fip]
fn take(v: &mut Vec<u8>) -> Vec<u8> {
    core::mem::replace(v, Vec::new())
}

#[fip]
fn vec_new() -> Vec<u8> {
    Vec::new()
}

#[fip]
fn vec_default() -> Vec<u8> {
    Vec::default()
}

#[fip]
fn string_new() -> String {
    String::new()
}

#[fip]
fn string_default() -> String {
    String::default()
}

#[fip]
fn vec_deque_new() -> VecDeque<u8> {
    VecDeque::new()
}

#[fip]
fn vec_deque_default() -> VecDeque<u8> {
    VecDeque::default()
}

#[fip]
fn btree_map_new() -> BTreeMap<u8, u8> {
    BTreeMap::new()
}

#[fip]
fn btree_map_default() -> BTreeMap<u8, u8> {
    BTreeMap::default()
}

#[fip]
fn btree_set_new() -> BTreeSet<u8> {
    BTreeSet::new()
}

#[fip]
fn btree_set_default() -> BTreeSet<u8> {
    BTreeSet::default()
}

#[fip]
fn linked_list_new() -> LinkedList<u8> {
    LinkedList::new()
}

#[fip]
fn linked_list_default() -> LinkedList<u8> {
    LinkedList::default()
}

#[fip]
fn binary_heap_new() -> BinaryHeap<u8> {
    BinaryHeap::new()
}

#[fip]
fn binary_heap_default() -> BinaryHeap<u8> {
    BinaryHeap::default()
}

/// Strict mode accepts them without a certificate, with bound 0, also by full path.
#[fip(strict = true)]
fn strict_take(v: &mut Vec<u8>, s: &mut String) -> (Vec<u8>, String) {
    let old = core::mem::replace(v, std::vec::Vec::new());
    (old, core::mem::replace(s, alloc_string()))
}

/// `alloc::` path, as `no_std` code writes it.
#[fip(strict = true)]
fn alloc_string() -> String {
    String::default()
}

extern crate alloc;

#[fip(strict = true)]
fn strict_queue() -> (alloc::collections::VecDeque<u8>, BinaryHeap<u8>) {
    (alloc::collections::VecDeque::new(), BinaryHeap::default())
}

/// Each entry of the table with the function measuring it.
const MEASURED: &[(&str, &str)] = &[
    ("Vec", "new"),
    ("Vec", "default"),
    ("String", "new"),
    ("String", "default"),
    ("VecDeque", "new"),
    ("VecDeque", "default"),
    ("BTreeMap", "new"),
    ("BTreeMap", "default"),
    ("BTreeSet", "new"),
    ("BTreeSet", "default"),
    ("LinkedList", "new"),
    ("LinkedList", "default"),
    ("BinaryHeap", "new"),
    ("BinaryHeap", "default"),
];

#[test]
fn every_table_entry_is_measured() {
    assert_eq!(MEASURED, NON_ALLOCATING_CONSTRUCTORS);
}

#[test]
fn constructors_do_not_allocate() {
    assert_eq!(assert_fip!(vec_new()).len(), 0);
    assert_eq!(assert_fip!(vec_default()).len(), 0);
    assert_eq!(assert_fip!(string_new()).len(), 0);
    assert_eq!(assert_fip!(string_default()).len(), 0);
    assert_eq!(assert_fip!(vec_deque_new()).len(), 0);
    assert_eq!(assert_fip!(vec_deque_default()).len(), 0);
    assert_eq!(assert_fip!(btree_map_new()).len(), 0);
    assert_eq!(assert_fip!(btree_map_default()).len(), 0);
    assert_eq!(assert_fip!(btree_set_new()).len(), 0);
    assert_eq!(assert_fip!(btree_set_default()).len(), 0);
    assert_eq!(assert_fip!(linked_list_new()).len(), 0);
    assert_eq!(assert_fip!(linked_list_default()).len(), 0);
    assert_eq!(assert_fip!(binary_heap_new()).len(), 0);
    assert_eq!(assert_fip!(binary_heap_default()).len(), 0);
}

#[test]
fn the_empty_values_stay_allocation_free_when_dropped() {
    let ((), s) = fip_testkit::measure(|| {
        drop(vec_new());
        drop(string_new());
        drop(vec_deque_new());
        drop(btree_map_new());
        drop(btree_set_new());
        drop(linked_list_new());
        drop(binary_heap_new());
    });
    assert_eq!((s.allocs, s.reallocs, s.frees), (0, 0, 0), "{s:?}");
}

#[test]
fn take_moves_the_buffer_out() {
    let mut v = vec![1_u8, 2, 3];
    let old = assert_fip!(take(&mut v));
    assert_eq!(old, [1, 2, 3]);
    assert_eq!(v.len(), 0);
}

#[test]
fn strict_bounds_are_zero() {
    assert_eq!(__fip_strict_strict_take.allocs_for("strict_take"), 0);
    assert_eq!(__fip_strict_alloc_string.allocs_for("alloc_string"), 0);
    assert_eq!(__fip_strict_strict_queue.allocs_for("strict_queue"), 0);
    let (mut v, mut s) = (vec![7_u8], String::from("x"));
    let (old_v, old_s) = assert_fip!(strict_take(&mut v, &mut s));
    assert_eq!((old_v, old_s.as_str()), (vec![7], "x"));
    let (q, h) = assert_fip!(strict_queue());
    assert!(q.is_empty() && h.is_empty());
}
