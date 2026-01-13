//! Bitwise operator verification test
//!
//! Tests bitwise operators (&, |, ^, <<, >>) in both specs and code.
//! Note: BitAnd/BitOr/BitXor are treated as uninterpreted functions,
//! so proofs involving them are limited. Shifts (<< and >>) are translated
//! to multiplication/division by powers of 2 when the shift amount is constant.
//!
//! @expect shift_left_by_one VERIFIED
//! @expect shift_right_by_one VERIFIED
//! @expect shift_by_two VERIFIED
//! @expect shift_double_check VERIFIED
//! @expect shift_mismatch DISPROVEN

/// Left shift doubles a value (when n << 1 = n * 2)
/// @expect VERIFIED
// #[ensures(result == n * 2)]
fn shift_left_by_one(n: i32) -> i32 {
    n << 1
}

/// Right shift halves a positive value (when n >> 1 = n / 2)
/// @expect VERIFIED
// #[requires(n >= 0)]
// #[ensures(result == n / 2)]
fn shift_right_by_one(n: i32) -> i32 {
    n >> 1
}

/// Left shift by 2 multiplies by 4
/// @expect VERIFIED
// #[ensures(result == n * 4)]
fn shift_by_two(n: i32) -> i32 {
    n << 2
}

/// Double shift: (n << 1) << 1 should equal n * 4
/// @expect VERIFIED
// #[ensures(result == n * 4)]
fn shift_double_check(n: i32) -> i32 {
    (n << 1) << 1
}

/// Incorrect spec: claiming shift left by 2 equals shift left by 1
/// @expect DISPROVEN
// #[ensures(result == n << 1)]
fn shift_mismatch(n: i32) -> i32 {
    n << 2  // This is n * 4, not n * 2
}

fn main() {
    println!("shift_left_by_one(5) = {}", shift_left_by_one(5));  // 10
    println!("shift_right_by_one(10) = {}", shift_right_by_one(10));  // 5
    println!("shift_by_two(3) = {}", shift_by_two(3));  // 12
    println!("shift_double_check(3) = {}", shift_double_check(3));  // 12
    println!("shift_mismatch(3) = {}", shift_mismatch(3));  // 12
}
