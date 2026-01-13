// String mutation tracking integration test (Phase 10.1)
// Tests String mutation methods update length tracking for verification.
// Note: Tests use owned String with known initial state (String::new())

#![allow(unused)]

// =============================================================================
// String::new creates empty string
// =============================================================================

#[ensures("result.len() == 0")]
fn string_new_empty() -> String {
    String::new()
}

#[ensures("result.is_empty()")]
fn string_new_is_empty() -> String {
    String::new()
}

// =============================================================================
// String::with_capacity creates empty string with capacity
// =============================================================================

#[ensures("result.len() == 0")]
fn string_with_capacity_empty() -> String {
    String::with_capacity(100)
}

// =============================================================================
// String::push increases length
// =============================================================================

#[ensures("result.len() == 1")]
fn string_push_one() -> String {
    let mut s = String::new();
    s.push('a');
    s
}

#[ensures("result.len() >= 2")]
fn string_push_two() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s
}

#[ensures("!result.is_empty()")]
fn string_push_nonempty() -> String {
    let mut s = String::new();
    s.push('x');
    s
}

#[ensures("result.len() > 0")]
fn string_with_capacity_then_push() -> String {
    let mut s = String::with_capacity(10);
    s.push('x');
    s
}

// =============================================================================
// String::clear sets length to 0
// =============================================================================

#[ensures("result.len() == 0")]
fn string_push_then_clear() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.clear();
    s
}

#[ensures("result.is_empty()")]
fn string_push_clear_empty() -> String {
    let mut s = String::new();
    s.push('x');
    s.clear();
    s
}

// =============================================================================
// Combined: clear then push
// =============================================================================

#[ensures("result.len() == 1")]
fn string_clear_then_push() -> String {
    let mut s = String::new();
    s.push('x');
    s.push('y');
    s.clear();
    s.push('z');
    s
}

#[ensures("!result.is_empty()")]
fn string_clear_then_push_nonempty() -> String {
    let mut s = String::new();
    s.clear();
    s.push('a');
    s
}

// =============================================================================
// Multiple operations sequence
// =============================================================================

#[ensures("result.len() >= 3")]
fn string_many_pushes() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.push('c');
    s
}

#[ensures("result.len() == 2")]
fn string_push_clear_push_push() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.clear();
    s.push('x');
    s.push('y');
    s
}

// =============================================================================
// String::insert increases length by 1
// =============================================================================

#[ensures("result.len() == 1")]
fn string_insert_one() -> String {
    let mut s = String::new();
    s.insert(0, 'x');
    s
}

#[ensures("result.len() >= 3")]
fn string_push_then_insert() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.insert(1, 'x');  // Insert in middle
    s
}

// =============================================================================
// String::remove decreases length by 1 (when non-empty)
// =============================================================================

#[ensures("result.len() == 1")]
fn string_push_push_remove() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.remove(0);  // Remove first char
    s
}

#[ensures("result.len() == 0")]
fn string_push_remove_empty() -> String {
    let mut s = String::new();
    s.push('x');
    s.remove(0);
    s
}

// =============================================================================
// Combined insert/remove sequences
// =============================================================================

#[ensures("result.len() == 2")]
fn string_insert_remove_sequence() -> String {
    let mut s = String::new();
    s.insert(0, 'a');  // len = 1
    s.insert(0, 'b');  // len = 2
    s.insert(0, 'c');  // len = 3
    s.remove(0);       // len = 2
    s
}

// =============================================================================
// String::truncate with tracked length
// =============================================================================

#[ensures("result.len() == 2")]
fn string_truncate_tracked() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.push('c');
    s.push('d');
    s.push('e');       // len = 5
    s.truncate(2);     // len = min(5, 2) = 2
    s
}

#[ensures("result.len() == 3")]
fn string_truncate_no_change() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.push('c');       // len = 3
    s.truncate(10);    // len = min(3, 10) = 3 (no change)
    s
}

// =============================================================================
// String::pop with tracked length
// =============================================================================

#[ensures("result.len() == 4")]
fn string_pop_tracked() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.push('c');
    s.push('d');
    s.push('e');       // len = 5
    s.pop();           // len = 4
    s
}

#[ensures("result.len() == 2")]
fn string_multi_pop() -> String {
    let mut s = String::new();
    s.push('a');
    s.push('b');
    s.push('c');
    s.push('d');       // len = 4
    s.pop();           // len = 3
    s.pop();           // len = 2
    s
}

#[ensures("result.len() == 0")]
fn string_pop_to_empty() -> String {
    let mut s = String::new();
    s.push('a');       // len = 1
    s.pop();           // len = 0
    s
}

fn main() {
    let s1 = string_new_empty();
    println!("New: len={}", s1.len());

    let s2 = string_push_one();
    println!("Push one: len={}", s2.len());

    let s3 = string_push_then_clear();
    println!("Push then clear: len={}", s3.len());

    let s4 = string_clear_then_push();
    println!("Clear then push: len={}", s4.len());
}
