//! Real-world validation: `subtle` (dependency-free subset).
//!
//! This file is an integration test for `./run_tests.sh` (picked up via `*_test.rs`),
//! and verifies a small core of `subtle`-style constant-time primitives.

#![allow(dead_code)]

#[path = "real_validation/subtle.rs"]
mod subtle;

use subtle::{Choice, SwapResult, SwapResult32, conditional_select_u8, conditional_swap_u8, ct_eq_u8, ct_ne_u8, ct_lt_u8, ct_gt_u8, ct_le_u8, ct_ge_u8};
use subtle::{ct_eq_u16, ct_ne_u16, ct_lt_u16, ct_gt_u16, ct_le_u16, ct_ge_u16, conditional_select_u16, conditional_swap_u16, SwapResult16};
use subtle::{ct_eq_u32, ct_ne_u32, ct_lt_u32, ct_gt_u32, ct_le_u32, ct_ge_u32, conditional_select_u32, conditional_swap_u32};
use subtle::{ct_eq_u64, ct_ne_u64, ct_lt_u64, ct_gt_u64, ct_le_u64, ct_ge_u64, conditional_select_u64, conditional_swap_u64, SwapResult64};
use subtle::{ct_eq_i8, ct_ne_i8, ct_lt_i8, ct_gt_i8, ct_le_i8, ct_ge_i8, conditional_select_i8, conditional_swap_i8, SwapResultI8};
use subtle::{ct_eq_i16, ct_ne_i16, ct_lt_i16, ct_gt_i16, ct_le_i16, ct_ge_i16, conditional_select_i16, conditional_swap_i16, SwapResultI16};
use subtle::{ct_eq_i32, ct_ne_i32, ct_lt_i32, ct_gt_i32, ct_le_i32, ct_ge_i32, conditional_select_i32, conditional_swap_i32, SwapResultI32};
use subtle::{ct_eq_i64, ct_ne_i64, ct_lt_i64, ct_gt_i64, ct_le_i64, ct_ge_i64, conditional_select_i64, conditional_swap_i64, SwapResultI64};
use subtle::{conditional_negate_i8, conditional_negate_i16, conditional_negate_i32, conditional_negate_i64};
use subtle::{ct_eq_usize, ct_ne_usize, ct_lt_usize, ct_gt_usize, ct_le_usize, ct_ge_usize, conditional_select_usize, conditional_swap_usize, SwapResultUsize};
use subtle::{ct_eq_isize, ct_ne_isize, ct_lt_isize, ct_gt_isize, ct_le_isize, ct_ge_isize, conditional_select_isize, conditional_swap_isize, SwapResultIsize, conditional_negate_isize};
use subtle::{CtOptionU8, CtOptionU32, CtOptionU64};
use subtle::{CtOptionI8, CtOptionI16, CtOptionI32, CtOptionI64};
use subtle::{CtOptionUsize, CtOptionIsize};
use subtle::{ct_eq_bytes_16, ct_eq_bytes_32, ct_eq_bytes_64};
use subtle::{ct_is_zero_u8_pub, ct_is_zero_u16, ct_is_zero_u32, ct_is_zero_u64};
use subtle::{ct_is_zero_i8, ct_is_zero_i16, ct_is_zero_i32, ct_is_zero_i64};
use subtle::{ct_is_zero_usize, ct_is_zero_isize};

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn choice_is_normalized(x: u8) -> Choice {
    Choice::from_u8(x)
}

#[ensures("result.0 == 1")]
pub fn ct_eq_reflexive(x: u8) -> Choice {
    ct_eq_u8(x, x)
}

#[ensures("result == a")]
pub fn select_left(a: u8, b: u8) -> u8 {
    conditional_select_u8(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_right(a: u8, b: u8) -> u8 {
    conditional_select_u8(a, b, Choice(1))
}

// Comparison function tests

#[ensures("result.0 == 1")]
pub fn ct_lt_true() -> Choice {
    ct_lt_u8(5, 10) // 5 < 10 is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_false() -> Choice {
    ct_lt_u8(10, 5) // 10 < 5 is false
}

#[ensures("result.0 == 0")]
pub fn ct_lt_equal() -> Choice {
    ct_lt_u8(7, 7) // 7 < 7 is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_true() -> Choice {
    ct_gt_u8(10, 5) // 10 > 5 is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_false() -> Choice {
    ct_gt_u8(5, 10) // 5 > 10 is false
}

#[ensures("result.0 == 0")]
pub fn ct_gt_equal() -> Choice {
    ct_gt_u8(7, 7) // 7 > 7 is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_true_less() -> Choice {
    ct_le_u8(5, 10) // 5 <= 10 is true
}

#[ensures("result.0 == 1")]
pub fn ct_le_true_equal() -> Choice {
    ct_le_u8(7, 7) // 7 <= 7 is true
}

#[ensures("result.0 == 0")]
pub fn ct_le_false() -> Choice {
    ct_le_u8(10, 5) // 10 <= 5 is false
}

#[ensures("result.0 == 1")]
pub fn ct_ge_true_greater() -> Choice {
    ct_ge_u8(10, 5) // 10 >= 5 is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_true_equal() -> Choice {
    ct_ge_u8(7, 7) // 7 >= 7 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ge_false() -> Choice {
    ct_ge_u8(5, 10) // 5 >= 10 is false
}

// Not-equal function tests (u8)

#[ensures("result.0 == 1")]
pub fn ct_ne_u8_true() -> Choice {
    ct_ne_u8(5, 10) // 5 != 10 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_u8_false(x: u8) -> Choice {
    ct_ne_u8(x, x) // x != x is false
}

// XOR function: Choice::xor is verified in subtle.rs
// Note: Direct test functions omitted due to solver limitation with
// field access on method parameters in spec expressions.
// The underlying function Choice::xor is VERIFIED via its contracts.

// ============================================================================
// u16 comparison function tests
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_u16_reflexive(x: u16) -> Choice {
    ct_eq_u16(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_u16_true() -> Choice {
    ct_lt_u16(100, 1000) // 100 < 1000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_u16_false() -> Choice {
    ct_lt_u16(1000, 100) // 1000 < 100 is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_u16_true() -> Choice {
    ct_gt_u16(1000, 100) // 1000 > 100 is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_u16_false() -> Choice {
    ct_gt_u16(100, 1000) // 100 > 1000 is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_u16_true() -> Choice {
    ct_le_u16(500, 500) // 500 <= 500 is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_u16_true() -> Choice {
    ct_ge_u16(500, 500) // 500 >= 500 is true
}

// Not-equal function tests (u16)

#[ensures("result.0 == 1")]
pub fn ct_ne_u16_true() -> Choice {
    ct_ne_u16(100, 1000) // 100 != 1000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_u16_false(x: u16) -> Choice {
    ct_ne_u16(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_u16_left(a: u16, b: u16) -> u16 {
    conditional_select_u16(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_u16_right(a: u16, b: u16) -> u16 {
    conditional_select_u16(a, b, Choice(1))
}

#[ensures("result.first == 1000")]
#[ensures("result.second == 2000")]
pub fn swap_u16_no_swap() -> SwapResult16 {
    conditional_swap_u16(1000, 2000, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 2000")]
#[ensures("result.second == 1000")]
pub fn swap_u16_do_swap() -> SwapResult16 {
    conditional_swap_u16(1000, 2000, Choice(1)) // choice=1 means swap
}

// Conditional swap tests

#[ensures("result.first == 10")]
#[ensures("result.second == 20")]
pub fn swap_no_swap() -> SwapResult {
    conditional_swap_u8(10, 20, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 20")]
#[ensures("result.second == 10")]
pub fn swap_do_swap() -> SwapResult {
    conditional_swap_u8(10, 20, Choice(1)) // choice=1 means swap
}

// ============================================================================
// u32 comparison function tests
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_u32_reflexive(x: u32) -> Choice {
    ct_eq_u32(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_u32_true() -> Choice {
    ct_lt_u32(100000, 1000000) // 100000 < 1000000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_u32_false() -> Choice {
    ct_lt_u32(1000000, 100000) // 1000000 < 100000 is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_u32_true() -> Choice {
    ct_gt_u32(1000000, 100000) // 1000000 > 100000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_u32_false() -> Choice {
    ct_gt_u32(100000, 1000000) // 100000 > 1000000 is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_u32_true() -> Choice {
    ct_le_u32(500000, 500000) // 500000 <= 500000 is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_u32_true() -> Choice {
    ct_ge_u32(500000, 500000) // 500000 >= 500000 is true
}

// Not-equal function tests (u32)

#[ensures("result.0 == 1")]
pub fn ct_ne_u32_true() -> Choice {
    ct_ne_u32(100000, 1000000) // 100000 != 1000000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_u32_false(x: u32) -> Choice {
    ct_ne_u32(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_u32_left(a: u32, b: u32) -> u32 {
    conditional_select_u32(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_u32_right(a: u32, b: u32) -> u32 {
    conditional_select_u32(a, b, Choice(1))
}

#[ensures("result.first == 100000")]
#[ensures("result.second == 200000")]
pub fn swap_u32_no_swap() -> SwapResult32 {
    conditional_swap_u32(100000, 200000, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 200000")]
#[ensures("result.second == 100000")]
pub fn swap_u32_do_swap() -> SwapResult32 {
    conditional_swap_u32(100000, 200000, Choice(1)) // choice=1 means swap
}

// ============================================================================
// u64 comparison function tests
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_u64_reflexive(x: u64) -> Choice {
    ct_eq_u64(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_u64_true() -> Choice {
    ct_lt_u64(1000000000, 10000000000) // 1B < 10B is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_u64_false() -> Choice {
    ct_lt_u64(10000000000, 1000000000) // 10B < 1B is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_u64_true() -> Choice {
    ct_gt_u64(10000000000, 1000000000) // 10B > 1B is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_u64_false() -> Choice {
    ct_gt_u64(1000000000, 10000000000) // 1B > 10B is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_u64_true() -> Choice {
    ct_le_u64(5000000000, 5000000000) // 5B <= 5B is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_u64_true() -> Choice {
    ct_ge_u64(5000000000, 5000000000) // 5B >= 5B is true
}

// Not-equal function tests (u64)

#[ensures("result.0 == 1")]
pub fn ct_ne_u64_true() -> Choice {
    ct_ne_u64(1000000000, 10000000000) // 1B != 10B is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_u64_false(x: u64) -> Choice {
    ct_ne_u64(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_u64_left(a: u64, b: u64) -> u64 {
    conditional_select_u64(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_u64_right(a: u64, b: u64) -> u64 {
    conditional_select_u64(a, b, Choice(1))
}

#[ensures("result.first == 1000000000")]
#[ensures("result.second == 2000000000")]
pub fn swap_u64_no_swap() -> SwapResult64 {
    conditional_swap_u64(1000000000, 2000000000, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 2000000000")]
#[ensures("result.second == 1000000000")]
pub fn swap_u64_do_swap() -> SwapResult64 {
    conditional_swap_u64(1000000000, 2000000000, Choice(1)) // choice=1 means swap
}

// ============================================================================
// i8 signed integer comparison function tests
// Note: Using positive values due to SMT solver limitation with negative literals
// in function arguments. The underlying signed operations are still verified.
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_i8_reflexive(x: i8) -> Choice {
    ct_eq_i8(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_i8_true() -> Choice {
    ct_lt_i8(5, 10) // 5 < 10 is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_i8_false() -> Choice {
    ct_lt_i8(10, 5) // 10 < 5 is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_i8_true() -> Choice {
    ct_gt_i8(10, 5) // 10 > 5 is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_i8_false() -> Choice {
    ct_gt_i8(5, 10) // 5 > 10 is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_i8_true() -> Choice {
    ct_le_i8(5, 5) // 5 <= 5 is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_i8_true() -> Choice {
    ct_ge_i8(5, 5) // 5 >= 5 is true
}

// Not-equal function tests (i8)

#[ensures("result.0 == 1")]
pub fn ct_ne_i8_true() -> Choice {
    ct_ne_i8(5, 10) // 5 != 10 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_i8_false(x: i8) -> Choice {
    ct_ne_i8(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_i8_left(a: i8, b: i8) -> i8 {
    conditional_select_i8(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_i8_right(a: i8, b: i8) -> i8 {
    conditional_select_i8(a, b, Choice(1))
}

#[ensures("result.first == 10")]
#[ensures("result.second == 20")]
pub fn swap_i8_no_swap() -> SwapResultI8 {
    conditional_swap_i8(10, 20, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 20")]
#[ensures("result.second == 10")]
pub fn swap_i8_do_swap() -> SwapResultI8 {
    conditional_swap_i8(10, 20, Choice(1)) // choice=1 means swap
}

// ============================================================================
// i16 signed integer comparison function tests
// Note: Using positive values due to SMT solver limitation with negative literals
// in function arguments. The underlying signed operations are still verified.
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_i16_reflexive(x: i16) -> Choice {
    ct_eq_i16(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_i16_true() -> Choice {
    ct_lt_i16(100, 1000) // 100 < 1000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_i16_false() -> Choice {
    ct_lt_i16(1000, 100) // 1000 < 100 is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_i16_true() -> Choice {
    ct_gt_i16(1000, 100) // 1000 > 100 is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_i16_false() -> Choice {
    ct_gt_i16(100, 1000) // 100 > 1000 is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_i16_true() -> Choice {
    ct_le_i16(500, 500) // 500 <= 500 is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_i16_true() -> Choice {
    ct_ge_i16(500, 500) // 500 >= 500 is true
}

// Not-equal function tests (i16)

#[ensures("result.0 == 1")]
pub fn ct_ne_i16_true() -> Choice {
    ct_ne_i16(100, 1000) // 100 != 1000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_i16_false(x: i16) -> Choice {
    ct_ne_i16(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_i16_left(a: i16, b: i16) -> i16 {
    conditional_select_i16(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_i16_right(a: i16, b: i16) -> i16 {
    conditional_select_i16(a, b, Choice(1))
}

#[ensures("result.first == 100")]
#[ensures("result.second == 200")]
pub fn swap_i16_no_swap() -> SwapResultI16 {
    conditional_swap_i16(100, 200, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 200")]
#[ensures("result.second == 100")]
pub fn swap_i16_do_swap() -> SwapResultI16 {
    conditional_swap_i16(100, 200, Choice(1)) // choice=1 means swap
}

// ============================================================================
// i32 signed integer comparison function tests
// Note: Using positive values due to SMT solver limitation with negative literals
// in function arguments. The underlying signed operations are still verified.
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_i32_reflexive(x: i32) -> Choice {
    ct_eq_i32(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_i32_true() -> Choice {
    ct_lt_i32(100000, 1000000) // 100000 < 1000000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_i32_false() -> Choice {
    ct_lt_i32(1000000, 100000) // 1000000 < 100000 is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_i32_true() -> Choice {
    ct_gt_i32(1000000, 100000) // 1000000 > 100000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_i32_false() -> Choice {
    ct_gt_i32(100000, 1000000) // 100000 > 1000000 is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_i32_true() -> Choice {
    ct_le_i32(500000, 500000) // 500000 <= 500000 is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_i32_true() -> Choice {
    ct_ge_i32(500000, 500000) // 500000 >= 500000 is true
}

// Not-equal function tests (i32)

#[ensures("result.0 == 1")]
pub fn ct_ne_i32_true() -> Choice {
    ct_ne_i32(100000, 1000000) // 100000 != 1000000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_i32_false(x: i32) -> Choice {
    ct_ne_i32(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_i32_left(a: i32, b: i32) -> i32 {
    conditional_select_i32(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_i32_right(a: i32, b: i32) -> i32 {
    conditional_select_i32(a, b, Choice(1))
}

#[ensures("result.first == 100000")]
#[ensures("result.second == 200000")]
pub fn swap_i32_no_swap() -> SwapResultI32 {
    conditional_swap_i32(100000, 200000, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 200000")]
#[ensures("result.second == 100000")]
pub fn swap_i32_do_swap() -> SwapResultI32 {
    conditional_swap_i32(100000, 200000, Choice(1)) // choice=1 means swap
}

// ============================================================================
// i64 signed integer comparison function tests
// Note: Using positive values due to SMT solver limitation with negative literals
// in function arguments. The underlying signed operations are still verified.
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_i64_reflexive(x: i64) -> Choice {
    ct_eq_i64(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_i64_true() -> Choice {
    ct_lt_i64(1000000000, 10000000000) // 1B < 10B is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_i64_false() -> Choice {
    ct_lt_i64(10000000000, 1000000000) // 10B < 1B is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_i64_true() -> Choice {
    ct_gt_i64(10000000000, 1000000000) // 10B > 1B is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_i64_false() -> Choice {
    ct_gt_i64(1000000000, 10000000000) // 1B > 10B is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_i64_true() -> Choice {
    ct_le_i64(5000000000, 5000000000) // 5B <= 5B is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_i64_true() -> Choice {
    ct_ge_i64(5000000000, 5000000000) // 5B >= 5B is true
}

// Not-equal function tests (i64)

#[ensures("result.0 == 1")]
pub fn ct_ne_i64_true() -> Choice {
    ct_ne_i64(1000000000, 10000000000) // 1B != 10B is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_i64_false(x: i64) -> Choice {
    ct_ne_i64(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_i64_left(a: i64, b: i64) -> i64 {
    conditional_select_i64(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_i64_right(a: i64, b: i64) -> i64 {
    conditional_select_i64(a, b, Choice(1))
}

#[ensures("result.first == 1000000000")]
#[ensures("result.second == 2000000000")]
pub fn swap_i64_no_swap() -> SwapResultI64 {
    conditional_swap_i64(1000000000, 2000000000, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 2000000000")]
#[ensures("result.second == 1000000000")]
pub fn swap_i64_do_swap() -> SwapResultI64 {
    conditional_swap_i64(1000000000, 2000000000, Choice(1)) // choice=1 means swap
}

// =============================================================================
// Conditional negation tests
// =============================================================================
// Note: Only no-negate cases are verified via contracts. The SMT solver cannot
// reason about wrapping_neg() behavior. Actual negation is tested at runtime.

// i8 conditional negation tests
#[ensures("result == 42")]
pub fn negate_i8_no_negate() -> i8 {
    conditional_negate_i8(42, Choice(0)) // choice=0 means no negation
}

// i16 conditional negation tests
#[ensures("result == 1000")]
pub fn negate_i16_no_negate() -> i16 {
    conditional_negate_i16(1000, Choice(0))
}

// i32 conditional negation tests
#[ensures("result == 100000")]
pub fn negate_i32_no_negate() -> i32 {
    conditional_negate_i32(100000, Choice(0))
}

// i64 conditional negation tests
#[ensures("result == 1000000000")]
pub fn negate_i64_no_negate() -> i64 {
    conditional_negate_i64(1000000000, Choice(0))
}

// ============================================================================
// usize (pointer-sized unsigned) comparison function tests
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_usize_reflexive(x: usize) -> Choice {
    ct_eq_usize(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_usize_true() -> Choice {
    ct_lt_usize(100, 1000) // 100 < 1000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_usize_false() -> Choice {
    ct_lt_usize(1000, 100) // 1000 < 100 is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_usize_true() -> Choice {
    ct_gt_usize(1000, 100) // 1000 > 100 is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_usize_false() -> Choice {
    ct_gt_usize(100, 1000) // 100 > 1000 is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_usize_true() -> Choice {
    ct_le_usize(500, 500) // 500 <= 500 is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_usize_true() -> Choice {
    ct_ge_usize(500, 500) // 500 >= 500 is true
}

// Not-equal function tests (usize)

#[ensures("result.0 == 1")]
pub fn ct_ne_usize_true() -> Choice {
    ct_ne_usize(100, 1000) // 100 != 1000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_usize_false(x: usize) -> Choice {
    ct_ne_usize(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_usize_left(a: usize, b: usize) -> usize {
    conditional_select_usize(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_usize_right(a: usize, b: usize) -> usize {
    conditional_select_usize(a, b, Choice(1))
}

#[ensures("result.first == 100")]
#[ensures("result.second == 200")]
pub fn swap_usize_no_swap() -> SwapResultUsize {
    conditional_swap_usize(100, 200, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 200")]
#[ensures("result.second == 100")]
pub fn swap_usize_do_swap() -> SwapResultUsize {
    conditional_swap_usize(100, 200, Choice(1)) // choice=1 means swap
}

// ============================================================================
// isize (pointer-sized signed) comparison function tests
// ============================================================================

#[ensures("result.0 == 1")]
pub fn ct_eq_isize_reflexive(x: isize) -> Choice {
    ct_eq_isize(x, x)
}

#[ensures("result.0 == 1")]
pub fn ct_lt_isize_true() -> Choice {
    ct_lt_isize(100, 1000) // 100 < 1000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_lt_isize_false() -> Choice {
    ct_lt_isize(1000, 100) // 1000 < 100 is false
}

#[ensures("result.0 == 1")]
pub fn ct_gt_isize_true() -> Choice {
    ct_gt_isize(1000, 100) // 1000 > 100 is true
}

#[ensures("result.0 == 0")]
pub fn ct_gt_isize_false() -> Choice {
    ct_gt_isize(100, 1000) // 100 > 1000 is false
}

#[ensures("result.0 == 1")]
pub fn ct_le_isize_true() -> Choice {
    ct_le_isize(500, 500) // 500 <= 500 is true
}

#[ensures("result.0 == 1")]
pub fn ct_ge_isize_true() -> Choice {
    ct_ge_isize(500, 500) // 500 >= 500 is true
}

// Not-equal function tests (isize)

#[ensures("result.0 == 1")]
pub fn ct_ne_isize_true() -> Choice {
    ct_ne_isize(100, 1000) // 100 != 1000 is true
}

#[ensures("result.0 == 0")]
pub fn ct_ne_isize_false(x: isize) -> Choice {
    ct_ne_isize(x, x) // x != x is false
}

#[ensures("result == a")]
pub fn select_isize_left(a: isize, b: isize) -> isize {
    conditional_select_isize(a, b, Choice(0))
}

#[ensures("result == b")]
pub fn select_isize_right(a: isize, b: isize) -> isize {
    conditional_select_isize(a, b, Choice(1))
}

#[ensures("result.first == 100")]
#[ensures("result.second == 200")]
pub fn swap_isize_no_swap() -> SwapResultIsize {
    conditional_swap_isize(100, 200, Choice(0)) // choice=0 means no swap
}

#[ensures("result.first == 200")]
#[ensures("result.second == 100")]
pub fn swap_isize_do_swap() -> SwapResultIsize {
    conditional_swap_isize(100, 200, Choice(1)) // choice=1 means swap
}

// isize conditional negation test (no-negate case)
#[ensures("result == 1000")]
pub fn negate_isize_no_negate() -> isize {
    conditional_negate_isize(1000, Choice(0))
}

// ============================================================================
// CtOptionU8 tests
// ============================================================================
// Note: The verifier has limitations with tracking postconditions from struct
// constructor methods through to test function results. The CtOption methods
// ARE verified (via their #[ensures] contracts in subtle.rs), and we verify
// behavior at runtime in ct_option_runtime_tests().
//
// Test functions here exercise the code paths without complex postconditions
// that the verifier cannot track through struct construction.

/// Test that CtOptionU8::some creates a value.
pub fn ct_option_u8_some() -> CtOptionU8 {
    CtOptionU8::some(42)
}

/// Test that CtOptionU8::none creates an empty option.
pub fn ct_option_u8_none() -> CtOptionU8 {
    CtOptionU8::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_u8_unwrap_or_some() -> u8 {
    let opt = CtOptionU8::new(42, Choice(1));
    opt.unwrap_or(99)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_u8_unwrap_or_none() -> u8 {
    let opt = CtOptionU8::new(0, Choice(0));
    opt.unwrap_or(99)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_u8_unwrap_or_default_some() -> u8 {
    let opt = CtOptionU8::new(42, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_u8_unwrap_or_default_none() -> u8 {
    let opt = CtOptionU8::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_u8_is_some_true() -> Choice {
    let opt = CtOptionU8::new(42, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_u8_is_some_false() -> Choice {
    let opt = CtOptionU8::new(0, Choice(0));
    opt.ct_is_some()
}

/// Test ct_is_none on Some.
pub fn ct_option_u8_is_none_false() -> Choice {
    let opt = CtOptionU8::new(42, Choice(1));
    opt.ct_is_none()
}

/// Test ct_is_none on None.
pub fn ct_option_u8_is_none_true() -> Choice {
    let opt = CtOptionU8::new(0, Choice(0));
    opt.ct_is_none()
}

// ============================================================================
// CtOptionU32 tests
// ============================================================================

/// Test that CtOptionU32::some creates a value.
pub fn ct_option_u32_some() -> CtOptionU32 {
    CtOptionU32::some(100000)
}

/// Test that CtOptionU32::none creates an empty option.
pub fn ct_option_u32_none() -> CtOptionU32 {
    CtOptionU32::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_u32_unwrap_or_some() -> u32 {
    let opt = CtOptionU32::new(100000, Choice(1));
    opt.unwrap_or(999999)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_u32_unwrap_or_none() -> u32 {
    let opt = CtOptionU32::new(0, Choice(0));
    opt.unwrap_or(999999)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_u32_unwrap_or_default_some() -> u32 {
    let opt = CtOptionU32::new(100000, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_u32_unwrap_or_default_none() -> u32 {
    let opt = CtOptionU32::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_u32_is_some_true() -> Choice {
    let opt = CtOptionU32::new(100000, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_u32_is_some_false() -> Choice {
    let opt = CtOptionU32::new(0, Choice(0));
    opt.ct_is_some()
}

// ============================================================================
// CtOptionU64 tests
// ============================================================================

/// Test that CtOptionU64::some creates a value.
pub fn ct_option_u64_some() -> CtOptionU64 {
    CtOptionU64::some(1000000000)
}

/// Test that CtOptionU64::none creates an empty option.
pub fn ct_option_u64_none() -> CtOptionU64 {
    CtOptionU64::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_u64_unwrap_or_some() -> u64 {
    let opt = CtOptionU64::new(1000000000, Choice(1));
    opt.unwrap_or(9999999999)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_u64_unwrap_or_none() -> u64 {
    let opt = CtOptionU64::new(0, Choice(0));
    opt.unwrap_or(9999999999)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_u64_unwrap_or_default_some() -> u64 {
    let opt = CtOptionU64::new(1000000000, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_u64_unwrap_or_default_none() -> u64 {
    let opt = CtOptionU64::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_u64_is_some_true() -> Choice {
    let opt = CtOptionU64::new(1000000000, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_u64_is_some_false() -> Choice {
    let opt = CtOptionU64::new(0, Choice(0));
    opt.ct_is_some()
}

// ============================================================================
// CtOptionI8 tests
// ============================================================================

/// Test that CtOptionI8::some creates a value.
pub fn ct_option_i8_some() -> CtOptionI8 {
    CtOptionI8::some(42)
}

/// Test that CtOptionI8::none creates an empty option.
pub fn ct_option_i8_none() -> CtOptionI8 {
    CtOptionI8::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_i8_unwrap_or_some() -> i8 {
    let opt = CtOptionI8::new(42, Choice(1));
    opt.unwrap_or(-99)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_i8_unwrap_or_none() -> i8 {
    let opt = CtOptionI8::new(0, Choice(0));
    opt.unwrap_or(-99)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_i8_unwrap_or_default_some() -> i8 {
    let opt = CtOptionI8::new(42, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_i8_unwrap_or_default_none() -> i8 {
    let opt = CtOptionI8::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_i8_is_some_true() -> Choice {
    let opt = CtOptionI8::new(42, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_i8_is_some_false() -> Choice {
    let opt = CtOptionI8::new(0, Choice(0));
    opt.ct_is_some()
}

// ============================================================================
// CtOptionI16 tests
// ============================================================================

/// Test that CtOptionI16::some creates a value.
pub fn ct_option_i16_some() -> CtOptionI16 {
    CtOptionI16::some(1000)
}

/// Test that CtOptionI16::none creates an empty option.
pub fn ct_option_i16_none() -> CtOptionI16 {
    CtOptionI16::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_i16_unwrap_or_some() -> i16 {
    let opt = CtOptionI16::new(1000, Choice(1));
    opt.unwrap_or(-9999)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_i16_unwrap_or_none() -> i16 {
    let opt = CtOptionI16::new(0, Choice(0));
    opt.unwrap_or(-9999)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_i16_unwrap_or_default_some() -> i16 {
    let opt = CtOptionI16::new(1000, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_i16_unwrap_or_default_none() -> i16 {
    let opt = CtOptionI16::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_i16_is_some_true() -> Choice {
    let opt = CtOptionI16::new(1000, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_i16_is_some_false() -> Choice {
    let opt = CtOptionI16::new(0, Choice(0));
    opt.ct_is_some()
}

// ============================================================================
// CtOptionI32 tests
// ============================================================================

/// Test that CtOptionI32::some creates a value.
pub fn ct_option_i32_some() -> CtOptionI32 {
    CtOptionI32::some(100000)
}

/// Test that CtOptionI32::none creates an empty option.
pub fn ct_option_i32_none() -> CtOptionI32 {
    CtOptionI32::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_i32_unwrap_or_some() -> i32 {
    let opt = CtOptionI32::new(100000, Choice(1));
    opt.unwrap_or(-999999)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_i32_unwrap_or_none() -> i32 {
    let opt = CtOptionI32::new(0, Choice(0));
    opt.unwrap_or(-999999)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_i32_unwrap_or_default_some() -> i32 {
    let opt = CtOptionI32::new(100000, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_i32_unwrap_or_default_none() -> i32 {
    let opt = CtOptionI32::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_i32_is_some_true() -> Choice {
    let opt = CtOptionI32::new(100000, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_i32_is_some_false() -> Choice {
    let opt = CtOptionI32::new(0, Choice(0));
    opt.ct_is_some()
}

// ============================================================================
// CtOptionI64 tests
// ============================================================================

/// Test that CtOptionI64::some creates a value.
pub fn ct_option_i64_some() -> CtOptionI64 {
    CtOptionI64::some(1000000000)
}

/// Test that CtOptionI64::none creates an empty option.
pub fn ct_option_i64_none() -> CtOptionI64 {
    CtOptionI64::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_i64_unwrap_or_some() -> i64 {
    let opt = CtOptionI64::new(1000000000, Choice(1));
    opt.unwrap_or(-9999999999)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_i64_unwrap_or_none() -> i64 {
    let opt = CtOptionI64::new(0, Choice(0));
    opt.unwrap_or(-9999999999)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_i64_unwrap_or_default_some() -> i64 {
    let opt = CtOptionI64::new(1000000000, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_i64_unwrap_or_default_none() -> i64 {
    let opt = CtOptionI64::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_i64_is_some_true() -> Choice {
    let opt = CtOptionI64::new(1000000000, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_i64_is_some_false() -> Choice {
    let opt = CtOptionI64::new(0, Choice(0));
    opt.ct_is_some()
}

// ============================================================================
// CtOptionUsize tests
// ============================================================================

/// Test that CtOptionUsize::some creates a value.
pub fn ct_option_usize_some() -> CtOptionUsize {
    CtOptionUsize::some(100000)
}

/// Test that CtOptionUsize::none creates an empty option.
pub fn ct_option_usize_none() -> CtOptionUsize {
    CtOptionUsize::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_usize_unwrap_or_some() -> usize {
    let opt = CtOptionUsize::new(100000, Choice(1));
    opt.unwrap_or(999999)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_usize_unwrap_or_none() -> usize {
    let opt = CtOptionUsize::new(0, Choice(0));
    opt.unwrap_or(999999)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_usize_unwrap_or_default_some() -> usize {
    let opt = CtOptionUsize::new(100000, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_usize_unwrap_or_default_none() -> usize {
    let opt = CtOptionUsize::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_usize_is_some_true() -> Choice {
    let opt = CtOptionUsize::new(100000, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_usize_is_some_false() -> Choice {
    let opt = CtOptionUsize::new(0, Choice(0));
    opt.ct_is_some()
}

// ============================================================================
// CtOptionIsize tests
// ============================================================================

/// Test that CtOptionIsize::some creates a value.
pub fn ct_option_isize_some() -> CtOptionIsize {
    CtOptionIsize::some(100000)
}

/// Test that CtOptionIsize::none creates an empty option.
pub fn ct_option_isize_none() -> CtOptionIsize {
    CtOptionIsize::none()
}

/// Test unwrap_or on Some - verified via underlying contracts.
pub fn ct_option_isize_unwrap_or_some() -> isize {
    let opt = CtOptionIsize::new(100000, Choice(1));
    opt.unwrap_or(-999999)
}

/// Test unwrap_or on None - verified via underlying contracts.
pub fn ct_option_isize_unwrap_or_none() -> isize {
    let opt = CtOptionIsize::new(0, Choice(0));
    opt.unwrap_or(-999999)
}

/// Test unwrap_or_default on Some - verified via underlying contracts.
pub fn ct_option_isize_unwrap_or_default_some() -> isize {
    let opt = CtOptionIsize::new(100000, Choice(1));
    opt.unwrap_or_default()
}

/// Test unwrap_or_default on None - verified via underlying contracts.
pub fn ct_option_isize_unwrap_or_default_none() -> isize {
    let opt = CtOptionIsize::new(0, Choice(0));
    opt.unwrap_or_default()
}

/// Test ct_is_some on Some.
pub fn ct_option_isize_is_some_true() -> Choice {
    let opt = CtOptionIsize::new(100000, Choice(1));
    opt.ct_is_some()
}

/// Test ct_is_some on None.
pub fn ct_option_isize_is_some_false() -> Choice {
    let opt = CtOptionIsize::new(0, Choice(0));
    opt.ct_is_some()
}

// Runtime-only tests (verify negation behavior without formal contracts)
fn negate_runtime_tests() {
    // i8 negation tests
    assert_eq!(conditional_negate_i8(42, Choice(1)), -42);
    assert_eq!(conditional_negate_i8(0, Choice(1)), 0);
    assert_eq!(conditional_negate_i8(i8::MIN, Choice(1)), i8::MIN); // wrapping: -(-128) = -128

    // i16 negation tests
    assert_eq!(conditional_negate_i16(1000, Choice(1)), -1000);
    assert_eq!(conditional_negate_i16(0, Choice(1)), 0);

    // i32 negation tests
    assert_eq!(conditional_negate_i32(100000, Choice(1)), -100000);
    assert_eq!(conditional_negate_i32(0, Choice(1)), 0);

    // i64 negation tests
    assert_eq!(conditional_negate_i64(1000000000, Choice(1)), -1000000000);
    assert_eq!(conditional_negate_i64(0, Choice(1)), 0);

    // isize negation tests
    assert_eq!(conditional_negate_isize(1000, Choice(1)), -1000);
    assert_eq!(conditional_negate_isize(0, Choice(1)), 0);
}

// Runtime tests for CtOption functionality
fn ct_option_runtime_tests() {
    // CtOptionU8 tests
    let some = CtOptionU8::some(42);
    let none = CtOptionU8::none();
    assert_eq!(some.value, 42);
    assert_eq!(some.is_some.0, 1);
    assert_eq!(none.value, 0);
    assert_eq!(none.is_some.0, 0);
    assert_eq!(some.unwrap_or(99), 42);
    assert_eq!(none.unwrap_or(99), 99);
    assert_eq!(some.unwrap_or_default(), 42);
    assert_eq!(none.unwrap_or_default(), 0);
    assert_eq!(some.ct_is_some().0, 1);
    assert_eq!(none.ct_is_some().0, 0);
    assert_eq!(some.ct_is_none().0, 0);
    assert_eq!(none.ct_is_none().0, 1);

    // CtOptionU8::new tests
    let new_some = CtOptionU8::new(123, Choice(1));
    let new_none = CtOptionU8::new(0, Choice(0));
    assert_eq!(new_some.value, 123);
    assert_eq!(new_some.is_some.0, 1);
    assert_eq!(new_none.is_some.0, 0);

    // CtOptionU32 tests
    let some32 = CtOptionU32::some(100000);
    let none32 = CtOptionU32::none();
    assert_eq!(some32.value, 100000);
    assert_eq!(some32.is_some.0, 1);
    assert_eq!(none32.is_some.0, 0);
    assert_eq!(some32.unwrap_or(999999), 100000);
    assert_eq!(none32.unwrap_or(999999), 999999);
    assert_eq!(some32.ct_is_some().0, 1);
    assert_eq!(none32.ct_is_none().0, 1);

    // CtOptionU64 tests
    let some64 = CtOptionU64::some(1000000000);
    let none64 = CtOptionU64::none();
    assert_eq!(some64.value, 1000000000);
    assert_eq!(some64.is_some.0, 1);
    assert_eq!(none64.is_some.0, 0);
    assert_eq!(some64.unwrap_or(9999999999), 1000000000);
    assert_eq!(none64.unwrap_or(9999999999), 9999999999);
    assert_eq!(some64.ct_is_some().0, 1);
    assert_eq!(none64.ct_is_none().0, 1);

    // CtOptionI8 tests
    let some_i8 = CtOptionI8::some(42);
    let none_i8 = CtOptionI8::none();
    assert_eq!(some_i8.value, 42);
    assert_eq!(some_i8.is_some.0, 1);
    assert_eq!(none_i8.is_some.0, 0);
    assert_eq!(some_i8.unwrap_or(-99), 42);
    assert_eq!(none_i8.unwrap_or(-99), -99);
    assert_eq!(some_i8.ct_is_some().0, 1);
    assert_eq!(none_i8.ct_is_none().0, 1);

    // CtOptionI16 tests
    let some_i16 = CtOptionI16::some(1000);
    let none_i16 = CtOptionI16::none();
    assert_eq!(some_i16.value, 1000);
    assert_eq!(some_i16.is_some.0, 1);
    assert_eq!(none_i16.is_some.0, 0);
    assert_eq!(some_i16.unwrap_or(-9999), 1000);
    assert_eq!(none_i16.unwrap_or(-9999), -9999);
    assert_eq!(some_i16.ct_is_some().0, 1);
    assert_eq!(none_i16.ct_is_none().0, 1);

    // CtOptionI32 tests
    let some_i32 = CtOptionI32::some(100000);
    let none_i32 = CtOptionI32::none();
    assert_eq!(some_i32.value, 100000);
    assert_eq!(some_i32.is_some.0, 1);
    assert_eq!(none_i32.is_some.0, 0);
    assert_eq!(some_i32.unwrap_or(-999999), 100000);
    assert_eq!(none_i32.unwrap_or(-999999), -999999);
    assert_eq!(some_i32.ct_is_some().0, 1);
    assert_eq!(none_i32.ct_is_none().0, 1);

    // CtOptionI64 tests
    let some_i64 = CtOptionI64::some(1000000000);
    let none_i64 = CtOptionI64::none();
    assert_eq!(some_i64.value, 1000000000);
    assert_eq!(some_i64.is_some.0, 1);
    assert_eq!(none_i64.is_some.0, 0);
    assert_eq!(some_i64.unwrap_or(-9999999999), 1000000000);
    assert_eq!(none_i64.unwrap_or(-9999999999), -9999999999);
    assert_eq!(some_i64.ct_is_some().0, 1);
    assert_eq!(none_i64.ct_is_none().0, 1);

    // CtOptionUsize tests
    let some_usize = CtOptionUsize::some(100000);
    let none_usize = CtOptionUsize::none();
    assert_eq!(some_usize.value, 100000);
    assert_eq!(some_usize.is_some.0, 1);
    assert_eq!(none_usize.is_some.0, 0);
    assert_eq!(some_usize.unwrap_or(999999), 100000);
    assert_eq!(none_usize.unwrap_or(999999), 999999);
    assert_eq!(some_usize.ct_is_some().0, 1);
    assert_eq!(none_usize.ct_is_none().0, 1);

    // CtOptionIsize tests
    let some_isize = CtOptionIsize::some(100000);
    let none_isize = CtOptionIsize::none();
    assert_eq!(some_isize.value, 100000);
    assert_eq!(some_isize.is_some.0, 1);
    assert_eq!(none_isize.is_some.0, 0);
    assert_eq!(some_isize.unwrap_or(-999999), 100000);
    assert_eq!(none_isize.unwrap_or(-999999), -999999);
    assert_eq!(some_isize.ct_is_some().0, 1);
    assert_eq!(none_isize.ct_is_none().0, 1);
}

// =============================================================================
// Byte Array Comparison Tests
// =============================================================================
//
// Note: The verifier currently has trouble with general postconditions over
// `&[u8; N]` parameters. The `ct_eq_bytes_*` helpers are therefore sanity-checked
// with runtime assertions in `ct_eq_bytes_runtime_tests()`.
//
// IMPORTANT: `./run_tests.sh` compiles these tests with `-Zverify` but does not
// execute the produced binaries, so these runtime assertions are not exercised
// by the standard verifier test runner.

/// Test ct_eq_bytes_16 returns 1 for equal arrays.
pub fn ct_eq_bytes_16_equal() -> Choice {
    let a: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let b: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    ct_eq_bytes_16(&a, &b)
}

/// Test ct_eq_bytes_16 returns 0 for different arrays (first byte differs)
pub fn ct_eq_bytes_16_diff_first() -> Choice {
    let a: [u8; 16] = [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let b: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    ct_eq_bytes_16(&a, &b)
}

/// Test ct_eq_bytes_16 returns 0 for different arrays (last byte differs)
pub fn ct_eq_bytes_16_diff_last() -> Choice {
    let a: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let b: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99];
    ct_eq_bytes_16(&a, &b)
}

/// Test ct_eq_bytes_16 returns 0 for different arrays (middle byte differs)
pub fn ct_eq_bytes_16_diff_middle() -> Choice {
    let a: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let b: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 99, 9, 10, 11, 12, 13, 14, 15, 16];
    ct_eq_bytes_16(&a, &b)
}

/// Test ct_eq_bytes_16 returns 1 for all-zero arrays
pub fn ct_eq_bytes_16_zeros() -> Choice {
    let a: [u8; 16] = [0; 16];
    let b: [u8; 16] = [0; 16];
    ct_eq_bytes_16(&a, &b)
}

/// Test ct_eq_bytes_16 returns 0 for arrays with a high-bit difference.
pub fn ct_eq_bytes_16_diff_highbit() -> Choice {
    let a: [u8; 16] = [255; 16];
    let mut b: [u8; 16] = [255; 16];
    b[8] = 0;
    ct_eq_bytes_16(&a, &b)
}

/// Test ct_eq_bytes_32 returns 1 for equal arrays
pub fn ct_eq_bytes_32_equal() -> Choice {
    let a: [u8; 32] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];
    let b: [u8; 32] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];
    ct_eq_bytes_32(&a, &b)
}

/// Test ct_eq_bytes_32 returns 0 for different arrays (first byte differs)
pub fn ct_eq_bytes_32_diff_first() -> Choice {
    let a: [u8; 32] = [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];
    let b: [u8; 32] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];
    ct_eq_bytes_32(&a, &b)
}

/// Test ct_eq_bytes_32 returns 0 for different arrays (last byte differs)
pub fn ct_eq_bytes_32_diff_last() -> Choice {
    let a: [u8; 32] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];
    let b: [u8; 32] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 99];
    ct_eq_bytes_32(&a, &b)
}

/// Test ct_eq_bytes_32 returns 0 for different arrays (middle byte differs)
pub fn ct_eq_bytes_32_diff_middle() -> Choice {
    let a: [u8; 32] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];
    let b: [u8; 32] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 99,
                       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];
    ct_eq_bytes_32(&a, &b)
}

/// Test ct_eq_bytes_32 returns 1 for all-zero arrays
pub fn ct_eq_bytes_32_zeros() -> Choice {
    let a: [u8; 32] = [0; 32];
    let b: [u8; 32] = [0; 32];
    ct_eq_bytes_32(&a, &b)
}

/// Test ct_eq_bytes_32 returns 0 for arrays with a high-bit difference.
pub fn ct_eq_bytes_32_diff_highbit() -> Choice {
    let a: [u8; 32] = [255; 32];
    let mut b: [u8; 32] = [255; 32];
    b[31] = 0;
    ct_eq_bytes_32(&a, &b)
}

/// Test ct_eq_bytes_64 returns 1 for equal arrays
pub fn ct_eq_bytes_64_equal() -> Choice {
    let a: [u8; 64] = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
    ];
    let b: [u8; 64] = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
    ];
    ct_eq_bytes_64(&a, &b)
}

/// Test ct_eq_bytes_64 returns 0 for different arrays (first byte differs)
pub fn ct_eq_bytes_64_diff_first() -> Choice {
    let a: [u8; 64] = [
        0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
    ];
    let b: [u8; 64] = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
    ];
    ct_eq_bytes_64(&a, &b)
}

/// Test ct_eq_bytes_64 returns 0 for different arrays (last byte differs)
pub fn ct_eq_bytes_64_diff_last() -> Choice {
    let a: [u8; 64] = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
    ];
    let b: [u8; 64] = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 99
    ];
    ct_eq_bytes_64(&a, &b)
}

/// Test ct_eq_bytes_64 returns 0 for different arrays (middle byte differs)
pub fn ct_eq_bytes_64_diff_middle() -> Choice {
    let a: [u8; 64] = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
    ];
    let b: [u8; 64] = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 99,
        33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
        49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
    ];
    ct_eq_bytes_64(&a, &b)
}

/// Test ct_eq_bytes_64 returns 1 for all-zero arrays
pub fn ct_eq_bytes_64_zeros() -> Choice {
    let a: [u8; 64] = [0; 64];
    let b: [u8; 64] = [0; 64];
    ct_eq_bytes_64(&a, &b)
}

/// Test ct_eq_bytes_64 returns 0 for arrays with a high-bit difference.
pub fn ct_eq_bytes_64_diff_highbit() -> Choice {
    let a: [u8; 64] = [255; 64];
    let mut b: [u8; 64] = [255; 64];
    b[0] = 0;
    ct_eq_bytes_64(&a, &b)
}

// =============================================================================
// ct_is_zero tests (constant-time zero checking)
// =============================================================================
// Note: These tests verify normalization (result is 0 or 1). Exact values
// are verified at runtime since the verifier doesn't track implication contracts.

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u8_zero() -> Choice {
    ct_is_zero_u8_pub(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u8_nonzero() -> Choice {
    ct_is_zero_u8_pub(42) // 42 != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u16_zero() -> Choice {
    ct_is_zero_u16(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u16_nonzero() -> Choice {
    ct_is_zero_u16(1000) // 1000 != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u32_zero() -> Choice {
    ct_is_zero_u32(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u32_nonzero() -> Choice {
    ct_is_zero_u32(100000) // 100000 != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u64_zero() -> Choice {
    ct_is_zero_u64(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u64_nonzero() -> Choice {
    ct_is_zero_u64(1000000000) // 1B != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i8_zero() -> Choice {
    ct_is_zero_i8(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i8_nonzero() -> Choice {
    ct_is_zero_i8(42) // 42 != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i16_zero() -> Choice {
    ct_is_zero_i16(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i16_nonzero() -> Choice {
    ct_is_zero_i16(100) // 100 != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i32_zero() -> Choice {
    ct_is_zero_i32(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i32_nonzero() -> Choice {
    ct_is_zero_i32(100000) // 100000 != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i64_zero() -> Choice {
    ct_is_zero_i64(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i64_nonzero() -> Choice {
    ct_is_zero_i64(1000000000) // 1B != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_usize_zero() -> Choice {
    ct_is_zero_usize(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_usize_nonzero() -> Choice {
    ct_is_zero_usize(1000) // 1000 != 0, returns Choice(0)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_isize_zero() -> Choice {
    ct_is_zero_isize(0) // 0 == 0, returns Choice(1)
}

#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_isize_nonzero() -> Choice {
    ct_is_zero_isize(1000) // 1000 != 0, returns Choice(0)
}

/// Runtime tests for byte array comparison (testing edge cases)
fn ct_eq_bytes_runtime_tests() {
    // Test 16-byte comparisons
    let a16: [u8; 16] = [255; 16];
    let b16: [u8; 16] = [255; 16];
    assert_eq!(ct_eq_bytes_16(&a16, &b16).0, 1); // All 0xFF equal

    let mut c16: [u8; 16] = [255; 16];
    c16[8] = 0; // Differ at index 8
    assert_eq!(ct_eq_bytes_16(&a16, &c16).0, 0);

    // Test 32-byte comparisons (SHA-256 hash size)
    let a32: [u8; 32] = [0xAB; 32];
    let b32: [u8; 32] = [0xAB; 32];
    assert_eq!(ct_eq_bytes_32(&a32, &b32).0, 1);

    let mut c32: [u8; 32] = [0xAB; 32];
    c32[31] = 0xAC; // Differ at last byte
    assert_eq!(ct_eq_bytes_32(&a32, &c32).0, 0);

    // Test 64-byte comparisons (SHA-512 hash size)
    let a64: [u8; 64] = [0x5A; 64];
    let b64: [u8; 64] = [0x5A; 64];
    assert_eq!(ct_eq_bytes_64(&a64, &b64).0, 1);

    let mut c64: [u8; 64] = [0x5A; 64];
    c64[0] = 0x5B; // Differ at first byte
    assert_eq!(ct_eq_bytes_64(&a64, &c64).0, 0);
}

fn main() {
    let _ = choice_is_normalized(42);
    let _ = ct_eq_reflexive(7);
    let _ = select_left(10, 20);
    let _ = select_right(10, 20);
    let _ = Choice::from_u8(3).not();
    let _ = Choice::from_u8(2).and(Choice::from_u8(1));
    let _ = Choice::from_u8(0).or(Choice::from_u8(1));
    // Comparison function tests
    let _ = ct_lt_true();
    let _ = ct_lt_false();
    let _ = ct_lt_equal();
    let _ = ct_gt_true();
    let _ = ct_gt_false();
    let _ = ct_gt_equal();
    let _ = ct_le_true_less();
    let _ = ct_le_true_equal();
    let _ = ct_le_false();
    let _ = ct_ge_true_greater();
    let _ = ct_ge_true_equal();
    let _ = ct_ge_false();
    // XOR function tests (exercised without spec - underlying Choice::xor is VERIFIED)
    let _ = Choice(0).xor(Choice(0));
    let _ = Choice(0).xor(Choice(1));
    let _ = Choice(1).xor(Choice(0));
    let _ = Choice(1).xor(Choice(1));
    // u16 comparison function tests
    let _ = ct_eq_u16_reflexive(42);
    let _ = ct_lt_u16_true();
    let _ = ct_lt_u16_false();
    let _ = ct_gt_u16_true();
    let _ = ct_gt_u16_false();
    let _ = ct_le_u16_true();
    let _ = ct_ge_u16_true();
    let _ = select_u16_left(100, 200);
    let _ = select_u16_right(100, 200);
    let _ = swap_u16_no_swap();
    let _ = swap_u16_do_swap();
    // Conditional swap tests (u8)
    let _ = swap_no_swap();
    let _ = swap_do_swap();
    // u32 comparison function tests
    let _ = ct_eq_u32_reflexive(42);
    let _ = ct_lt_u32_true();
    let _ = ct_lt_u32_false();
    let _ = ct_gt_u32_true();
    let _ = ct_gt_u32_false();
    let _ = ct_le_u32_true();
    let _ = ct_ge_u32_true();
    let _ = select_u32_left(100000, 200000);
    let _ = select_u32_right(100000, 200000);
    let _ = swap_u32_no_swap();
    let _ = swap_u32_do_swap();
    // u64 comparison function tests
    let _ = ct_eq_u64_reflexive(42);
    let _ = ct_lt_u64_true();
    let _ = ct_lt_u64_false();
    let _ = ct_gt_u64_true();
    let _ = ct_gt_u64_false();
    let _ = ct_le_u64_true();
    let _ = ct_ge_u64_true();
    let _ = select_u64_left(1000000000, 2000000000);
    let _ = select_u64_right(1000000000, 2000000000);
    let _ = swap_u64_no_swap();
    let _ = swap_u64_do_swap();
    // i8 signed integer comparison function tests
    let _ = ct_eq_i8_reflexive(42);
    let _ = ct_lt_i8_true();
    let _ = ct_lt_i8_false();
    let _ = ct_gt_i8_true();
    let _ = ct_gt_i8_false();
    let _ = ct_le_i8_true();
    let _ = ct_ge_i8_true();
    let _ = select_i8_left(10, 20);
    let _ = select_i8_right(10, 20);
    let _ = swap_i8_no_swap();
    let _ = swap_i8_do_swap();
    // i16 signed integer comparison function tests
    let _ = ct_eq_i16_reflexive(42);
    let _ = ct_lt_i16_true();
    let _ = ct_lt_i16_false();
    let _ = ct_gt_i16_true();
    let _ = ct_gt_i16_false();
    let _ = ct_le_i16_true();
    let _ = ct_ge_i16_true();
    let _ = select_i16_left(100, 200);
    let _ = select_i16_right(100, 200);
    let _ = swap_i16_no_swap();
    let _ = swap_i16_do_swap();
    // i32 signed integer comparison function tests
    let _ = ct_eq_i32_reflexive(42);
    let _ = ct_lt_i32_true();
    let _ = ct_lt_i32_false();
    let _ = ct_gt_i32_true();
    let _ = ct_gt_i32_false();
    let _ = ct_le_i32_true();
    let _ = ct_ge_i32_true();
    let _ = select_i32_left(100000, 200000);
    let _ = select_i32_right(100000, 200000);
    let _ = swap_i32_no_swap();
    let _ = swap_i32_do_swap();
    // i64 signed integer comparison function tests
    let _ = ct_eq_i64_reflexive(42);
    let _ = ct_lt_i64_true();
    let _ = ct_lt_i64_false();
    let _ = ct_gt_i64_true();
    let _ = ct_gt_i64_false();
    let _ = ct_le_i64_true();
    let _ = ct_ge_i64_true();
    let _ = select_i64_left(1000000000, 2000000000);
    let _ = select_i64_right(1000000000, 2000000000);
    let _ = swap_i64_no_swap();
    let _ = swap_i64_do_swap();
    // Conditional negation tests (verified no-negate cases)
    let _ = negate_i8_no_negate();
    let _ = negate_i16_no_negate();
    let _ = negate_i32_no_negate();
    let _ = negate_i64_no_negate();
    // usize comparison function tests
    let _ = ct_eq_usize_reflexive(42);
    let _ = ct_lt_usize_true();
    let _ = ct_lt_usize_false();
    let _ = ct_gt_usize_true();
    let _ = ct_gt_usize_false();
    let _ = ct_le_usize_true();
    let _ = ct_ge_usize_true();
    let _ = select_usize_left(100, 200);
    let _ = select_usize_right(100, 200);
    let _ = swap_usize_no_swap();
    let _ = swap_usize_do_swap();
    // isize comparison function tests
    let _ = ct_eq_isize_reflexive(42);
    let _ = ct_lt_isize_true();
    let _ = ct_lt_isize_false();
    let _ = ct_gt_isize_true();
    let _ = ct_gt_isize_false();
    let _ = ct_le_isize_true();
    let _ = ct_ge_isize_true();
    let _ = select_isize_left(100, 200);
    let _ = select_isize_right(100, 200);
    let _ = swap_isize_no_swap();
    let _ = swap_isize_do_swap();
    // isize conditional negation test
    let _ = negate_isize_no_negate();
    // Runtime tests for negation behavior (wrapping_neg not SMT-provable)
    negate_runtime_tests();

    // CtOptionU8 tests
    let _ = ct_option_u8_some();
    let _ = ct_option_u8_none();
    let _ = ct_option_u8_unwrap_or_some();
    let _ = ct_option_u8_unwrap_or_none();
    let _ = ct_option_u8_unwrap_or_default_some();
    let _ = ct_option_u8_unwrap_or_default_none();
    let _ = ct_option_u8_is_some_true();
    let _ = ct_option_u8_is_some_false();
    let _ = ct_option_u8_is_none_false();
    let _ = ct_option_u8_is_none_true();

    // CtOptionU32 tests
    let _ = ct_option_u32_some();
    let _ = ct_option_u32_none();
    let _ = ct_option_u32_unwrap_or_some();
    let _ = ct_option_u32_unwrap_or_none();
    let _ = ct_option_u32_unwrap_or_default_some();
    let _ = ct_option_u32_unwrap_or_default_none();
    let _ = ct_option_u32_is_some_true();
    let _ = ct_option_u32_is_some_false();

    // CtOptionU64 tests
    let _ = ct_option_u64_some();
    let _ = ct_option_u64_none();
    let _ = ct_option_u64_unwrap_or_some();
    let _ = ct_option_u64_unwrap_or_none();
    let _ = ct_option_u64_unwrap_or_default_some();
    let _ = ct_option_u64_unwrap_or_default_none();
    let _ = ct_option_u64_is_some_true();
    let _ = ct_option_u64_is_some_false();

    // CtOptionI8 tests
    let _ = ct_option_i8_some();
    let _ = ct_option_i8_none();
    let _ = ct_option_i8_unwrap_or_some();
    let _ = ct_option_i8_unwrap_or_none();
    let _ = ct_option_i8_unwrap_or_default_some();
    let _ = ct_option_i8_unwrap_or_default_none();
    let _ = ct_option_i8_is_some_true();
    let _ = ct_option_i8_is_some_false();

    // CtOptionI16 tests
    let _ = ct_option_i16_some();
    let _ = ct_option_i16_none();
    let _ = ct_option_i16_unwrap_or_some();
    let _ = ct_option_i16_unwrap_or_none();
    let _ = ct_option_i16_unwrap_or_default_some();
    let _ = ct_option_i16_unwrap_or_default_none();
    let _ = ct_option_i16_is_some_true();
    let _ = ct_option_i16_is_some_false();

    // CtOptionI32 tests
    let _ = ct_option_i32_some();
    let _ = ct_option_i32_none();
    let _ = ct_option_i32_unwrap_or_some();
    let _ = ct_option_i32_unwrap_or_none();
    let _ = ct_option_i32_unwrap_or_default_some();
    let _ = ct_option_i32_unwrap_or_default_none();
    let _ = ct_option_i32_is_some_true();
    let _ = ct_option_i32_is_some_false();

    // CtOptionI64 tests
    let _ = ct_option_i64_some();
    let _ = ct_option_i64_none();
    let _ = ct_option_i64_unwrap_or_some();
    let _ = ct_option_i64_unwrap_or_none();
    let _ = ct_option_i64_unwrap_or_default_some();
    let _ = ct_option_i64_unwrap_or_default_none();
    let _ = ct_option_i64_is_some_true();
    let _ = ct_option_i64_is_some_false();

    // CtOptionUsize tests
    let _ = ct_option_usize_some();
    let _ = ct_option_usize_none();
    let _ = ct_option_usize_unwrap_or_some();
    let _ = ct_option_usize_unwrap_or_none();
    let _ = ct_option_usize_unwrap_or_default_some();
    let _ = ct_option_usize_unwrap_or_default_none();
    let _ = ct_option_usize_is_some_true();
    let _ = ct_option_usize_is_some_false();

    // CtOptionIsize tests
    let _ = ct_option_isize_some();
    let _ = ct_option_isize_none();
    let _ = ct_option_isize_unwrap_or_some();
    let _ = ct_option_isize_unwrap_or_none();
    let _ = ct_option_isize_unwrap_or_default_some();
    let _ = ct_option_isize_unwrap_or_default_none();
    let _ = ct_option_isize_is_some_true();
    let _ = ct_option_isize_is_some_false();

    // Runtime tests for CtOption
    ct_option_runtime_tests();

    // Byte array comparison tests (16, 32, 64 bytes)
    let _ = ct_eq_bytes_16_equal();
    let _ = ct_eq_bytes_16_diff_first();
    let _ = ct_eq_bytes_16_diff_last();
    let _ = ct_eq_bytes_16_diff_middle();
    let _ = ct_eq_bytes_16_zeros();
    let _ = ct_eq_bytes_16_diff_highbit();
    let _ = ct_eq_bytes_32_equal();
    let _ = ct_eq_bytes_32_diff_first();
    let _ = ct_eq_bytes_32_diff_last();
    let _ = ct_eq_bytes_32_diff_middle();
    let _ = ct_eq_bytes_32_zeros();
    let _ = ct_eq_bytes_32_diff_highbit();
    let _ = ct_eq_bytes_64_equal();
    let _ = ct_eq_bytes_64_diff_first();
    let _ = ct_eq_bytes_64_diff_last();
    let _ = ct_eq_bytes_64_diff_middle();
    let _ = ct_eq_bytes_64_zeros();
    let _ = ct_eq_bytes_64_diff_highbit();

    // ct_is_zero tests (constant-time zero checking)
    let _ = ct_is_zero_u8_zero();
    let _ = ct_is_zero_u8_nonzero();
    let _ = ct_is_zero_u16_zero();
    let _ = ct_is_zero_u16_nonzero();
    let _ = ct_is_zero_u32_zero();
    let _ = ct_is_zero_u32_nonzero();
    let _ = ct_is_zero_u64_zero();
    let _ = ct_is_zero_u64_nonzero();
    let _ = ct_is_zero_i8_zero();
    let _ = ct_is_zero_i8_nonzero();
    let _ = ct_is_zero_i16_zero();
    let _ = ct_is_zero_i16_nonzero();
    let _ = ct_is_zero_i32_zero();
    let _ = ct_is_zero_i32_nonzero();
    let _ = ct_is_zero_i64_zero();
    let _ = ct_is_zero_i64_nonzero();
    let _ = ct_is_zero_usize_zero();
    let _ = ct_is_zero_usize_nonzero();
    let _ = ct_is_zero_isize_zero();
    let _ = ct_is_zero_isize_nonzero();

    // Runtime tests for byte array comparisons
    ct_eq_bytes_runtime_tests();
}
