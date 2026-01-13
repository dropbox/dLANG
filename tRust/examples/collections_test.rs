// Collections length-based contract tests (Phase 10.1)
// Tests HashMap, BTreeMap, HashSet, BTreeSet basic contracts.
// All modeled via `(len collection)` - only length properties are verified.

#![allow(unused)]

use std::collections::{HashMap, BTreeMap, HashSet, BTreeSet};

// =============================================================================
// HashMap tests
// =============================================================================

// HashMap::new() creates empty map
#[ensures("result.len() == 0")]
fn hashmap_new_empty() -> HashMap<i32, i32> {
    HashMap::new()
}

#[ensures("result.is_empty()")]
fn hashmap_new_is_empty() -> HashMap<i32, i32> {
    HashMap::new()
}

// HashMap::with_capacity() creates empty map with reserved capacity
#[ensures("result.len() == 0")]
fn hashmap_with_capacity_empty() -> HashMap<i32, i32> {
    HashMap::with_capacity(100)
}

// HashMap::len() returns non-negative value
#[ensures("result >= 0")]
fn hashmap_len_nonneg(m: HashMap<i32, i32>) -> usize {
    m.len()
}

// HashMap::capacity() >= len()
#[ensures("result >= m.len()")]
fn hashmap_capacity_ge_len(m: HashMap<i32, i32>) -> usize {
    m.capacity()
}

// =============================================================================
// BTreeMap tests
// =============================================================================

// BTreeMap::new() creates empty map
#[ensures("result.len() == 0")]
fn btreemap_new_empty() -> BTreeMap<i32, i32> {
    BTreeMap::new()
}

#[ensures("result.is_empty()")]
fn btreemap_new_is_empty() -> BTreeMap<i32, i32> {
    BTreeMap::new()
}

// BTreeMap::len() returns non-negative value
#[ensures("result >= 0")]
fn btreemap_len_nonneg(m: BTreeMap<i32, i32>) -> usize {
    m.len()
}

// =============================================================================
// HashSet tests
// =============================================================================

// HashSet::new() creates empty set
#[ensures("result.len() == 0")]
fn hashset_new_empty() -> HashSet<i32> {
    HashSet::new()
}

#[ensures("result.is_empty()")]
fn hashset_new_is_empty() -> HashSet<i32> {
    HashSet::new()
}

// HashSet::with_capacity() creates empty set
#[ensures("result.len() == 0")]
fn hashset_with_capacity_empty() -> HashSet<i32> {
    HashSet::with_capacity(50)
}

// HashSet::len() returns non-negative value
#[ensures("result >= 0")]
fn hashset_len_nonneg(s: HashSet<i32>) -> usize {
    s.len()
}

// HashSet::capacity() >= len()
#[ensures("result >= s.len()")]
fn hashset_capacity_ge_len(s: HashSet<i32>) -> usize {
    s.capacity()
}

// =============================================================================
// BTreeSet tests
// =============================================================================

// BTreeSet::new() creates empty set
#[ensures("result.len() == 0")]
fn btreeset_new_empty() -> BTreeSet<i32> {
    BTreeSet::new()
}

#[ensures("result.is_empty()")]
fn btreeset_new_is_empty() -> BTreeSet<i32> {
    BTreeSet::new()
}

// BTreeSet::len() returns non-negative value
#[ensures("result >= 0")]
fn btreeset_len_nonneg(s: BTreeSet<i32>) -> usize {
    s.len()
}

fn main() {
    // HashMap tests
    let hm = hashmap_new_empty();
    println!("HashMap new: len={}", hm.len());

    // BTreeMap tests
    let btm = btreemap_new_empty();
    println!("BTreeMap new: len={}", btm.len());

    // HashSet tests
    let hs = hashset_new_empty();
    println!("HashSet new: len={}", hs.len());

    // BTreeSet tests
    let bts = btreeset_new_empty();
    println!("BTreeSet new: len={}", bts.len());
}
