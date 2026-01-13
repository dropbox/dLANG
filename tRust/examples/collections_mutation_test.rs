// Test BTreeMap/BTreeSet mutation tracking (Phase 10.1)
//
// Tests that BTreeMap/BTreeSet mutation operations properly update tracked lengths:
// - insert: length bounded [old_len, old_len+1] (key may or may not exist)
// - remove: length bounded [old_len-1, old_len] (key may or may not exist)
// - clear: length = 0
// - append: self length >= old, other length = 0
// - pop_first/pop_last: length bounded [old_len-1, old_len]
//
// Note: Unlike Vec, insert/remove don't guarantee exact length changes.
// We test exact results when the outcome is known (e.g., after clear).
//
// HashMap/HashSet mutation tracking is similar but already tested implicitly.

#![allow(unused)]

use std::collections::{BTreeMap, BTreeSet};

// =============================================================================
// BTreeMap::clear() tests - length becomes 0
// =============================================================================

// After clear, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn btreemap_clear_len_zero() -> BTreeMap<i32, i32> {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 10);
    m.insert(2, 20);
    m.clear();
    m
}

// After clear, is_empty is true
// VERIFIED
#[ensures("result.is_empty()")]
fn btreemap_clear_is_empty() -> BTreeMap<i32, i32> {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 10);
    m.clear();
    m
}

// =============================================================================
// BTreeMap::insert() tests - length bounded by [old_len, old_len+1]
// =============================================================================

// Insert on empty map: length bounded [0, 1], so <= 1
// VERIFIED
#[ensures("result.len() <= 1")]
fn btreemap_insert_one_bounded() -> BTreeMap<i32, i32> {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 10);
    m
}

// Multiple inserts with distinct keys: length bounded by number of inserts
// After 3 inserts on empty map: len <= 3
// VERIFIED
#[ensures("result.len() <= 3")]
fn btreemap_insert_three_bounded() -> BTreeMap<i32, i32> {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 10);
    m.insert(2, 20);
    m.insert(3, 30);
    m
}

// After insert on known empty map, not empty
// VERIFIED
#[ensures("!result.is_empty()")]
fn btreemap_insert_not_empty() -> BTreeMap<i32, i32> {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(42, 100);
    m
}

// =============================================================================
// BTreeMap::remove() tests - length bounded by [old_len-1, old_len]
// =============================================================================

// After clear and one insert, remove bounds: len <= 1
// VERIFIED
#[ensures("result.len() <= 1")]
fn btreemap_remove_bounded() -> BTreeMap<i32, i32> {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 10);
    m.remove(&1);  // May or may not remove (here it does)
    m
}

// =============================================================================
// BTreeMap combined operations
// =============================================================================

// Clear then insert: length bounded [0, 1], so not empty
// VERIFIED
#[ensures("!result.is_empty()")]
fn btreemap_clear_then_insert() -> BTreeMap<i32, i32> {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 10);
    m.insert(2, 20);
    m.clear();  // len = 0
    m.insert(3, 30);  // len bounded [0, 1], so >= 0
    m
}

// =============================================================================
// BTreeSet::clear() tests - length becomes 0
// =============================================================================

// After clear, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn btreeset_clear_len_zero() -> BTreeSet<i32> {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(1);
    s.insert(2);
    s.clear();
    s
}

// After clear, is_empty is true
// VERIFIED
#[ensures("result.is_empty()")]
fn btreeset_clear_is_empty() -> BTreeSet<i32> {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(1);
    s.clear();
    s
}

// =============================================================================
// BTreeSet::insert() tests - length bounded by [old_len, old_len+1]
// =============================================================================

// Insert on empty set: length bounded [0, 1], so <= 1
// VERIFIED
#[ensures("result.len() <= 1")]
fn btreeset_insert_one_bounded() -> BTreeSet<i32> {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(1);
    s
}

// Multiple inserts: length bounded by number of inserts
// After 3 inserts on empty set: len <= 3
// VERIFIED
#[ensures("result.len() <= 3")]
fn btreeset_insert_three_bounded() -> BTreeSet<i32> {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(1);
    s.insert(2);
    s.insert(3);
    s
}

// After insert on known empty set, not empty
// VERIFIED
#[ensures("!result.is_empty()")]
fn btreeset_insert_not_empty() -> BTreeSet<i32> {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(42);
    s
}

// =============================================================================
// BTreeSet::remove() tests - length bounded by [old_len-1, old_len]
// =============================================================================

// After clear and one insert, remove bounds: len <= 1
// VERIFIED
#[ensures("result.len() <= 1")]
fn btreeset_remove_bounded() -> BTreeSet<i32> {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(1);
    s.remove(&1);  // May or may not remove (here it does)
    s
}

// =============================================================================
// BTreeSet combined operations
// =============================================================================

// Clear then insert: not empty
// VERIFIED
#[ensures("!result.is_empty()")]
fn btreeset_clear_then_insert() -> BTreeSet<i32> {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(1);
    s.insert(2);
    s.clear();  // len = 0
    s.insert(3);  // len bounded [0, 1]
    s
}

// =============================================================================
// BTreeMap::append() tests - self length >= old, other length = 0
// =============================================================================

// After append, other map is empty
// VERIFIED
#[ensures("other.len() == 0")]
#[ensures("other.is_empty()")]
fn btreemap_append_other_empty(other: &mut BTreeMap<i32, i32>) {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 10);
    m.append(other);
    // other is now empty (drained into m)
}

// =============================================================================
// BTreeSet::append() tests - self length >= old, other length = 0
// =============================================================================

// After append, other set is empty
// VERIFIED
#[ensures("other.len() == 0")]
#[ensures("other.is_empty()")]
fn btreeset_append_other_empty(other: &mut BTreeSet<i32>) {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(1);
    s.append(other);
    // other is now empty (drained into s)
}

fn main() {
    // BTreeMap clear tests
    assert_eq!(btreemap_clear_len_zero().len(), 0);
    assert!(btreemap_clear_is_empty().is_empty());

    // BTreeMap insert tests
    assert!(btreemap_insert_one_bounded().len() <= 1);
    assert!(btreemap_insert_three_bounded().len() <= 3);
    assert!(!btreemap_insert_not_empty().is_empty());

    // BTreeMap remove tests
    assert!(btreemap_remove_bounded().len() <= 1);

    // BTreeMap combined tests
    assert!(!btreemap_clear_then_insert().is_empty());

    // BTreeSet clear tests
    assert_eq!(btreeset_clear_len_zero().len(), 0);
    assert!(btreeset_clear_is_empty().is_empty());

    // BTreeSet insert tests
    assert!(btreeset_insert_one_bounded().len() <= 1);
    assert!(btreeset_insert_three_bounded().len() <= 3);
    assert!(!btreeset_insert_not_empty().is_empty());

    // BTreeSet remove tests
    assert!(btreeset_remove_bounded().len() <= 1);

    // BTreeSet combined tests
    assert!(!btreeset_clear_then_insert().is_empty());

    // BTreeMap append tests
    let mut other_m: BTreeMap<i32, i32> = BTreeMap::new();
    other_m.insert(100, 1000);
    btreemap_append_other_empty(&mut other_m);
    assert!(other_m.is_empty());

    // BTreeSet append tests
    let mut other_s: BTreeSet<i32> = BTreeSet::new();
    other_s.insert(100);
    btreeset_append_other_empty(&mut other_s);
    assert!(other_s.is_empty());

    println!("All collection mutation tests passed at runtime!");
}
