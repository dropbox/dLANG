// Test Vec mutation tracking (Phase 10.1)
//
// Tests that Vec mutation operations properly update tracked lengths:
// - push: length += 1
// - clear: length = 0
// - pop: length = max(0, length - 1)
// - truncate: length = min(current, n)
// - resize: length = n
//
// This enables verification of postconditions that depend on Vec length changes.
//
// Note: This requires linear code analysis (no loops) for accurate tracking.

// =================================================================
// Vec::push() tests - length increases by 1
// =================================================================

// After one push, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vec_push_one() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(42);
    v
}

// After two pushes, length is 2
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_push_two() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v
}

// After three pushes, length is 3
// VERIFIED
#[ensures("result.len() == 3")]
fn vec_push_three() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v
}

// Push makes vec non-empty
// VERIFIED
#[ensures("!result.is_empty()")]
fn vec_push_not_empty() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(42);
    v
}

// =================================================================
// Vec::clear() tests - length becomes 0
// =================================================================

// After clear, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn vec_clear_len_zero() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.clear();
    v
}

// After clear, is_empty is true
// VERIFIED
#[ensures("result.is_empty()")]
fn vec_clear_is_empty() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.clear();
    v
}

// Push after clear gives length 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vec_clear_then_push() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.clear();
    v.push(3);
    v
}

// =================================================================
// Vec::pop() tests - length decreases by 1 (if non-empty)
// =================================================================

// Pop on single-element vec leaves length 0
// VERIFIED (using tracked length after pop)
#[ensures("result.len() == 0")]
fn vec_pop_to_empty() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(42);
    let _ = v.pop();
    v
}

// Pop on two-element vec leaves length 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vec_pop_to_one() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    let _ = v.pop();
    v
}

// Two pops on three-element vec leaves length 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vec_pop_twice() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let _ = v.pop();
    let _ = v.pop();
    v
}

// =================================================================
// Combined operations tests
// =================================================================

// Push, pop, push sequence: length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vec_push_pop_push() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    let _ = v.pop();
    v.push(2);
    v
}

// Multiple operations: final length is 2
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_complex_ops() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);  // len = 1
    v.push(2);  // len = 2
    v.push(3);  // len = 3
    let _ = v.pop();  // len = 2
    v.push(4);  // len = 3
    v.clear();  // len = 0
    v.push(5);  // len = 1
    v.push(6);  // len = 2
    v
}

// =================================================================
// Vec::truncate() tests - length becomes min(current, n)
// =================================================================

// Truncate larger vec to smaller size
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_truncate_to_two() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);  // len = 1
    v.push(2);  // len = 2
    v.push(3);  // len = 3
    v.push(4);  // len = 4
    v.truncate(2);  // len = min(4, 2) = 2
    v
}

// Truncate to zero makes vec empty
// VERIFIED
#[ensures("result.is_empty()")]
fn vec_truncate_to_zero() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.truncate(0);  // len = 0
    v
}

// Truncate with larger n does nothing
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_truncate_larger() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);  // len = 1
    v.push(2);  // len = 2
    v.truncate(10);  // len = min(2, 10) = 2
    v
}

// =================================================================
// Vec::resize() tests - length becomes exactly n
// =================================================================

// Resize to grow vec
// VERIFIED
#[ensures("result.len() == 5")]
fn vec_resize_grow() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);  // len = 1
    v.push(2);  // len = 2
    v.resize(5, 0);  // len = 5
    v
}

// Resize to shrink vec
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_resize_shrink() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    v.resize(2, 0);  // len = 2
    v
}

// Resize to zero makes vec empty
// VERIFIED
#[ensures("result.is_empty()")]
fn vec_resize_to_zero() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.resize(0, 0);  // len = 0
    v
}

// =================================================================
// Combined operations with truncate and resize
// =================================================================

// Complex sequence with all mutation operations
// VERIFIED
#[ensures("result.len() == 3")]
fn vec_all_mutations() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);      // len = 1
    v.push(2);      // len = 2
    v.resize(5, 0); // len = 5
    v.truncate(4);  // len = min(5, 4) = 4
    let _ = v.pop();// len = 3
    v.push(10);     // len = 4
    v.clear();      // len = 0
    v.resize(3, 0); // len = 3
    v
}

fn main() {
    // Push tests
    assert_eq!(vec_push_one().len(), 1);
    assert_eq!(vec_push_two().len(), 2);
    assert_eq!(vec_push_three().len(), 3);
    assert!(!vec_push_not_empty().is_empty());

    // Clear tests
    assert_eq!(vec_clear_len_zero().len(), 0);
    assert!(vec_clear_is_empty().is_empty());
    assert_eq!(vec_clear_then_push().len(), 1);

    // Pop tests
    assert_eq!(vec_pop_to_empty().len(), 0);
    assert_eq!(vec_pop_to_one().len(), 1);
    assert_eq!(vec_pop_twice().len(), 1);

    // Combined tests
    assert_eq!(vec_push_pop_push().len(), 1);
    assert_eq!(vec_complex_ops().len(), 2);

    // Truncate tests
    assert_eq!(vec_truncate_to_two().len(), 2);
    assert!(vec_truncate_to_zero().is_empty());
    assert_eq!(vec_truncate_larger().len(), 2);

    // Resize tests
    assert_eq!(vec_resize_grow().len(), 5);
    assert_eq!(vec_resize_shrink().len(), 2);
    assert!(vec_resize_to_zero().is_empty());

    // All mutations combined test
    assert_eq!(vec_all_mutations().len(), 3);
}
