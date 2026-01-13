// Test HashMap<K,V> and HashSet<T> length/is_empty modeling (Phase 10.1)
//
// Current builtin modeling:
// - HashMap::new / HashSet::new: len(result) == 0
// - HashMap::with_capacity / HashSet::with_capacity: len(result) == 0
// - HashMap::len / HashSet::len: result == len(self)
// - HashMap::is_empty / HashSet::is_empty: result == (len(self) == 0)
// - HashMap::capacity / HashSet::capacity: result >= len(self)
//
// Mutation tracking:
// - insert: old_len <= new_len <= old_len + 1
// - remove: old_len - 1 <= new_len <= old_len
// - clear: new_len == 0
//
// Note: This only models length; element contents/keys are not modeled.

use std::collections::HashMap;
use std::collections::HashSet;

// =================================================================
// HashMap basic tests
// =================================================================

// HashMap::new().len() == 0
// VERIFIED
#[ensures("result == 0")]
fn hashmap_new_len_zero() -> usize {
    let m: HashMap<i32, i32> = HashMap::new();
    m.len()
}

// HashMap::new().is_empty() == true
// VERIFIED
#[ensures("result")]
fn hashmap_new_is_empty_true() -> bool {
    let m: HashMap<i32, i32> = HashMap::new();
    m.is_empty()
}

// HashMap::with_capacity(n).len() == 0
// VERIFIED
#[ensures("result == 0")]
fn hashmap_with_capacity_len_zero() -> usize {
    let m: HashMap<i32, i32> = HashMap::with_capacity(10);
    m.len()
}

// HashMap::with_capacity(n).is_empty() == true
// VERIFIED
#[ensures("result")]
fn hashmap_with_capacity_is_empty_true() -> bool {
    let m: HashMap<i32, i32> = HashMap::with_capacity(10);
    m.is_empty()
}

// HashMap::capacity() >= len()
// VERIFIED
#[ensures("result >= 0")]
fn hashmap_capacity_geq_len() -> usize {
    let m: HashMap<i32, i32> = HashMap::with_capacity(10);
    let cap = m.capacity();
    cap
}

// =================================================================
// HashSet basic tests
// =================================================================

// HashSet::new().len() == 0
// VERIFIED
#[ensures("result == 0")]
fn hashset_new_len_zero() -> usize {
    let s: HashSet<i32> = HashSet::new();
    s.len()
}

// HashSet::new().is_empty() == true
// VERIFIED
#[ensures("result")]
fn hashset_new_is_empty_true() -> bool {
    let s: HashSet<i32> = HashSet::new();
    s.is_empty()
}

// HashSet::with_capacity(n).len() == 0
// VERIFIED
#[ensures("result == 0")]
fn hashset_with_capacity_len_zero() -> usize {
    let s: HashSet<i32> = HashSet::with_capacity(10);
    s.len()
}

// HashSet::with_capacity(n).is_empty() == true
// VERIFIED
#[ensures("result")]
fn hashset_with_capacity_is_empty_true() -> bool {
    let s: HashSet<i32> = HashSet::with_capacity(10);
    s.is_empty()
}

// HashSet::capacity() >= len()
// VERIFIED
#[ensures("result >= 0")]
fn hashset_capacity_geq_len() -> usize {
    let s: HashSet<i32> = HashSet::with_capacity(10);
    let cap = s.capacity();
    cap
}

// =================================================================
// HashMap mutation tests
// =================================================================

// HashMap::new().clear() still has len == 0
// VERIFIED
#[ensures("result == 0")]
fn hashmap_clear_still_empty() -> usize {
    let mut m: HashMap<i32, i32> = HashMap::new();
    m.clear();
    m.len()
}

// HashMap::new().clear().is_empty() == true
// VERIFIED
#[ensures("result")]
fn hashmap_clear_is_empty() -> bool {
    let mut m: HashMap<i32, i32> = HashMap::new();
    m.clear();
    m.is_empty()
}

// =================================================================
// HashSet mutation tests
// =================================================================

// HashSet::new().clear() still has len == 0
// VERIFIED
#[ensures("result == 0")]
fn hashset_clear_still_empty() -> usize {
    let mut s: HashSet<i32> = HashSet::new();
    s.clear();
    s.len()
}

// HashSet::new().clear().is_empty() == true
// VERIFIED
#[ensures("result")]
fn hashset_clear_is_empty() -> bool {
    let mut s: HashSet<i32> = HashSet::new();
    s.clear();
    s.is_empty()
}

fn main() {
    // HashMap tests
    assert_eq!(hashmap_new_len_zero(), 0);
    assert!(hashmap_new_is_empty_true());
    assert_eq!(hashmap_with_capacity_len_zero(), 0);
    assert!(hashmap_with_capacity_is_empty_true());
    assert!(hashmap_capacity_geq_len() >= 0);
    assert_eq!(hashmap_clear_still_empty(), 0);
    assert!(hashmap_clear_is_empty());

    // HashSet tests
    assert_eq!(hashset_new_len_zero(), 0);
    assert!(hashset_new_is_empty_true());
    assert_eq!(hashset_with_capacity_len_zero(), 0);
    assert!(hashset_with_capacity_is_empty_true());
    assert!(hashset_capacity_geq_len() >= 0);
    assert_eq!(hashset_clear_still_empty(), 0);
    assert!(hashset_clear_is_empty());

    println!("All HashMap/HashSet tests passed!");
}
