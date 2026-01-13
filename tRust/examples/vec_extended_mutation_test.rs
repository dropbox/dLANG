// Test extended Vec mutation tracking (Phase 10.1)
//
// Tests that Vec insert/remove/swap_remove/append operations properly update tracked lengths.
// This complements vec_mutation_test.rs which tests push/clear/pop.

// =================================================================
// Vec::insert() tests - length increases by 1
// =================================================================

// After insert, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vec_insert_one() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.insert(0, 42);
    v
}

// After two inserts, length is 2
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_insert_two() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.insert(0, 1);
    v.insert(1, 2);
    v
}

// Insert after push: length is 2
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_push_then_insert() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.insert(0, 2);  // Insert at beginning
    v
}

// =================================================================
// Vec::remove() tests - length decreases by 1
// =================================================================

// After push then remove, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn vec_push_then_remove() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(42);
    let _ = v.remove(0);
    v
}

// After two pushes then remove, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vec_two_push_one_remove() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    let _ = v.remove(0);
    v
}

// =================================================================
// Vec::swap_remove() tests - length decreases by 1
// =================================================================

// After push then swap_remove, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn vec_push_then_swap_remove() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(42);
    let _ = v.swap_remove(0);
    v
}

// After three pushes then swap_remove, length is 2
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_three_push_one_swap_remove() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let _ = v.swap_remove(1);
    v
}

// =================================================================
// Combined operations tests
// =================================================================

// Insert then remove: net zero change, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vec_insert_then_remove() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);       // len = 1
    v.insert(0, 2);  // len = 2
    let _ = v.remove(0); // len = 1
    v
}

// Complex sequence: push, insert, remove, swap_remove
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_complex_sequence() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);       // len = 1
    v.push(2);       // len = 2
    v.insert(0, 3);  // len = 3
    v.push(4);       // len = 4
    let _ = v.remove(0);      // len = 3
    let _ = v.swap_remove(0); // len = 2
    v
}

// =================================================================
// Vec::append() test - length is sum of both vecs
// =================================================================

// After append, self gets all elements
// VERIFIED
#[ensures("result.len() == 3")]
fn vec_append_basic() -> Vec<i32> {
    let mut v1: Vec<i32> = Vec::new();
    v1.push(1);
    v1.push(2);

    let mut v2: Vec<i32> = Vec::new();
    v2.push(3);

    v1.append(&mut v2);
    v1
}

fn main() {
    // Insert tests
    assert_eq!(vec_insert_one().len(), 1);
    assert_eq!(vec_insert_two().len(), 2);
    assert_eq!(vec_push_then_insert().len(), 2);

    // Remove tests
    assert_eq!(vec_push_then_remove().len(), 0);
    assert_eq!(vec_two_push_one_remove().len(), 1);

    // Swap remove tests
    assert_eq!(vec_push_then_swap_remove().len(), 0);
    assert_eq!(vec_three_push_one_swap_remove().len(), 2);

    // Combined tests
    assert_eq!(vec_insert_then_remove().len(), 1);
    assert_eq!(vec_complex_sequence().len(), 2);

    // Append test
    assert_eq!(vec_append_basic().len(), 3);
}
