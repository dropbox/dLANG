// Test builtin contracts for checked arithmetic operations (return Option<T>)
// Option is modeled as (is_some: bool, value: T) where:
//   result.is_some() -> result_is_some
//   result.unwrap()  -> result_value
// This tests Phase 10.1 (Verified Core) foundational work for Option modeling.
//
// NOTE: This test demonstrates that Option method parsing works and builtin
// postconditions are generated. Full Option tracking through unwrap() requires
// additional work to connect Option values to unwrap results.

// Test checked_add: returns Some(a + b) if no overflow, None otherwise
// When result is Some, result.unwrap() == a + b
fn use_checked_add(a: u32, b: u32) -> u32 {
    let result = a.checked_add(b);
    if result.is_some() {
        // If Some, the value is a + b (builtin postcondition)
        // We unwrap safely here
        result.unwrap()
    } else {
        0
    }
}

// Test checked_sub: returns Some(a - b) if no overflow, None otherwise
fn use_checked_sub(a: u32, b: u32) -> u32 {
    let result = a.checked_sub(b);
    if result.is_some() {
        result.unwrap()
    } else {
        0
    }
}

// Test checked_mul: returns Some(a * b) if no overflow, None otherwise
fn use_checked_mul(a: u32, b: u32) -> u32 {
    let result = a.checked_mul(b);
    if result.is_some() {
        result.unwrap()
    } else {
        0
    }
}

// Test checked_div: returns Some(a / b) if b != 0 and no overflow, None otherwise
fn use_checked_div(a: u32, b: u32) -> u32 {
    let result = a.checked_div(b);
    if result.is_some() {
        result.unwrap()
    } else {
        0
    }
}

// Test that we can use checked_add result in a specification
// The builtin contract says: result.is_some() ==> result.unwrap() == a + b
// NOTE: This is currently DISPROVEN because we don't yet track:
// 1. When checked_add returns Some (no overflow) vs None (overflow)
// 2. The connection between Option value and unwrap() result
// This demonstrates the Option infrastructure works - full verification requires
// overflow condition modeling and unwrap contract implementation.
#[requires("a <= 100")]
#[requires("b <= 100")]
#[ensures("result == a + b")]
fn safe_add(a: u32, b: u32) -> u32 {
    // With a <= 100 and b <= 100, a + b <= 200, which fits in u32
    // So checked_add will return Some(a + b)
    a.checked_add(b).unwrap()
}

// Test using is_none() - modeled as (not result_is_some)
fn check_overflow(a: u32, b: u32) -> bool {
    let result = a.checked_add(b);
    result.is_none()
}

// Test checked_neg for signed integers
fn use_checked_neg(x: i32) -> i32 {
    let result = x.checked_neg();
    if result.is_some() {
        result.unwrap()
    } else {
        // Overflow occurred (x == i32::MIN)
        0
    }
}

fn main() {
    // Basic usage tests (not verified, just runtime checks)
    assert_eq!(use_checked_add(10, 20), 30);
    assert_eq!(use_checked_sub(50, 30), 20);
    assert_eq!(use_checked_mul(5, 6), 30);
    assert_eq!(use_checked_div(100, 4), 25);
    assert_eq!(safe_add(50, 30), 80);
    assert_eq!(check_overflow(u32::MAX, 1), true);
    assert_eq!(check_overflow(100, 100), false);
    assert_eq!(use_checked_neg(42), -42);

    println!("All checked arithmetic tests passed!");
}
