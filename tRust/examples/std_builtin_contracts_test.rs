//! Test file for builtin contracts of std library functions during modular verification.
//!
//! This tests the extended builtin contracts for:
//! - clamp: Ord::clamp bounds
//! - abs: i32::abs non-negative result
//! - saturating_add: unsigned result >= inputs
//! - saturating_sub: unsigned result <= minuend
//!
//! These builtin contracts are assumed as postconditions when calling these functions,
//! allowing callers to prove their own postconditions based on these assumptions.
//!
//! @expect: VERIFIED

// Test: clamp postcondition - result is bounded by min and max
// The builtin contract: (and (>= result min) (<= result max))
#[requires("min <= max")]
#[ensures("result >= min")]
#[ensures("result <= max")]
fn test_clamp_contract(val: i32, min: i32, max: i32) -> i32 {
    val.clamp(min, max)
}

// Test: using clamp's postcondition to prove caller's postcondition
#[requires("low < high")]
#[requires("high <= 100")]
#[ensures("result <= 100")]
fn use_clamp_bound(x: i32, low: i32, high: i32) -> i32 {
    // clamp guarantees: low <= result <= high
    // Since high <= 100, result <= 100
    x.clamp(low, high)
}

// Test: abs postcondition - result is non-negative
// The builtin contract: (and (>= result 0) (or (= result x) (= result (- 0 x))))
#[ensures("result >= 0")]
fn test_abs_contract(x: i32) -> i32 {
    x.abs()
}

// Test: using abs's postcondition to prove caller's postcondition
#[ensures("result >= 0")]
fn double_abs(x: i32) -> i32 {
    // abs guarantees: result >= 0
    // abs(x) is non-negative, so abs(x) + 0 is non-negative
    let a = x.abs();
    a
}

// Test: saturating_add postcondition for unsigned - result >= both inputs
// The builtin contract: (and (>= result a) (>= result b))
#[ensures("result >= a")]
#[ensures("result >= b")]
fn test_saturating_add_contract(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

// Test: saturating_sub postcondition for unsigned - result <= minuend
// The builtin contract: (and (<= result a) (>= result 0))
#[ensures("result <= a")]
fn test_saturating_sub_contract(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}

// Test: combining clamp with arithmetic using saturating_add
// clamp gives bounds, saturating_add preserves them (no overflow)
#[requires("x_min >= 0 && x_min <= x_max && x_max <= 50")]
#[ensures("result >= 10")]  // clamp >= 0 and saturating_add >= clamp, so result >= 0 + 10 = 10
fn clamp_then_saturating_add(val: i32, x_min: i32, x_max: i32) -> i32 {
    // clamp(val, x_min, x_max) gives x_min <= result <= x_max
    // x_min >= 0, so clamped >= 0
    let clamped = val.clamp(x_min, x_max);
    // saturating_add doesn't have SMT postconditions for i32, so use u32
    (clamped as u32).saturating_add(10) as i32
}

fn main() {
    // Test clamp contracts
    println!("test_clamp_contract(50, 10, 100) = {}", test_clamp_contract(50, 10, 100));
    println!("test_clamp_contract(5, 10, 100) = {}", test_clamp_contract(5, 10, 100));
    println!("test_clamp_contract(200, 10, 100) = {}", test_clamp_contract(200, 10, 100));
    println!("use_clamp_bound(150, 20, 80) = {}", use_clamp_bound(150, 20, 80));

    // Test abs contracts
    println!("test_abs_contract(-42) = {}", test_abs_contract(-42));
    println!("test_abs_contract(42) = {}", test_abs_contract(42));
    println!("double_abs(-10) = {}", double_abs(-10));

    // Test saturating_add contracts
    println!("test_saturating_add_contract(10, 20) = {}", test_saturating_add_contract(10, 20));
    println!("test_saturating_add_contract(u32::MAX, 1) = {}", test_saturating_add_contract(u32::MAX, 1));

    // Test saturating_sub contracts
    println!("test_saturating_sub_contract(100, 30) = {}", test_saturating_sub_contract(100, 30));
    println!("test_saturating_sub_contract(10, 100) = {}", test_saturating_sub_contract(10, 100));

    // Test combined operations
    println!("clamp_then_saturating_add(100, 10, 40) = {}", clamp_then_saturating_add(100, 10, 40));

    println!("All std builtin contracts tests passed!");
}
