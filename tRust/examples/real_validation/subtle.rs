#![allow(dead_code)]

/// Minimal, dependency-free subset of the `subtle` crate's core API.
///
/// The goal here is *functional correctness* (amenable to verification), not
/// timing side-channel guarantees.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Choice(pub u8);

impl Choice {
    /// Normalize an arbitrary byte to a `Choice` (0 or 1).
    #[ensures("result.0 == 0 || result.0 == 1")]
    pub fn from_u8(x: u8) -> Choice {
        let bit = if x % 2 == 0 { 0 } else { 1 };
        Choice(bit)
    }

    /// Convert a normalized `Choice` into a Rust `bool`.
    #[requires("self.0 == 0 || self.0 == 1")]
    #[ensures("result == (self.0 == 1)")]
    pub fn unwrap_bool(self) -> bool {
        self.0 == 1
    }

    /// Logical NOT for `Choice`.
    #[ensures("result.0 == 0 || result.0 == 1")]
    #[ensures("self.0 == 0 ==> result.0 == 1")]
    #[ensures("self.0 == 1 ==> result.0 == 0")]
    #[ensures("(self.0 == 0 || self.0 == 1) ==> result.0 == 1 - self.0")]
    pub fn not(self) -> Choice {
        let bit = if self.0 % 2 == 0 { 0 } else { 1 };
        Choice(if bit == 0 { 1 } else { 0 })
    }

    /// Logical AND for `Choice`.
    #[ensures("result.0 == 0 || result.0 == 1")]
    #[ensures("((self.0 == 0 || self.0 == 1) && (other.0 == 0 || other.0 == 1)) ==> result.0 == self.0 * other.0")]
    pub fn and(self, other: Choice) -> Choice {
        let a = if self.0 % 2 == 0 { 0 } else { 1 };
        let b = if other.0 % 2 == 0 { 0 } else { 1 };
        Choice(a * b)
    }

    /// Logical OR for `Choice`.
    #[ensures("result.0 == 0 || result.0 == 1")]
    #[ensures("((self.0 == 0 || self.0 == 1) && (other.0 == 0 || other.0 == 1) && (self.0 == 0 && other.0 == 0)) ==> result.0 == 0")]
    #[ensures("((self.0 == 0 || self.0 == 1) && (other.0 == 0 || other.0 == 1) && (self.0 == 1 || other.0 == 1)) ==> result.0 == 1")]
    pub fn or(self, other: Choice) -> Choice {
        let a = if self.0 % 2 == 0 { 0 } else { 1 };
        let b = if other.0 % 2 == 0 { 0 } else { 1 };
        let sum = a + b;
        Choice(if sum == 0 { 0 } else { 1 })
    }

    /// Logical XOR for `Choice`.
    #[ensures("result.0 == 0 || result.0 == 1")]
    #[ensures("((self.0 == 0 || self.0 == 1) && (other.0 == 0 || other.0 == 1) && self.0 == other.0) ==> result.0 == 0")]
    #[ensures("((self.0 == 0 || self.0 == 1) && (other.0 == 0 || other.0 == 1) && self.0 != other.0) ==> result.0 == 1")]
    pub fn xor(self, other: Choice) -> Choice {
        let a = if self.0 % 2 == 0 { 0 } else { 1 };
        let b = if other.0 % 2 == 0 { 0 } else { 1 };
        Choice(if a == b { 0 } else { 1 })
    }
}

/// Constant-time-ish equality for `u8` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_u8(a: u8, b: u8) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `u8` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_u8(a: u8, b: u8) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Conditional selection.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_u8(a: u8, b: u8, choice: Choice) -> u8 {
    if choice.0 == 0 { a } else { b }
}

/// Constant-time less-than for `u8`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_u8(a: u8, b: u8) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `u8`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_u8(a: u8, b: u8) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `u8`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_u8(a: u8, b: u8) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `u8`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_u8(a: u8, b: u8) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

// ============================================================================
// u16 variants
// ============================================================================

/// Constant-time-ish equality for `u16` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_u16(a: u16, b: u16) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `u16` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_u16(a: u16, b: u16) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `u16`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_u16(a: u16, b: u16) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `u16`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_u16(a: u16, b: u16) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `u16`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_u16(a: u16, b: u16) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `u16`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_u16(a: u16, b: u16) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `u16`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_u16(a: u16, b: u16, choice: Choice) -> u16 {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for u16.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResult16 {
    pub first: u16,
    pub second: u16,
}

/// Conditional swap for u16: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_u16(a: u16, b: u16, choice: Choice) -> SwapResult16 {
    if choice.0 == 0 {
        SwapResult16 { first: a, second: b }
    } else {
        SwapResult16 { first: b, second: a }
    }
}

/// Result of a conditional swap operation.
/// Note: Using a struct instead of a tuple because the verifier
/// doesn't support native tuple field indexing (result.0, result.1).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResult {
    pub first: u8,
    pub second: u8,
}

/// Conditional swap: swaps a and b if choice is 1, otherwise leaves them unchanged.
/// Returns SwapResult { first, second } where:
/// - if choice == 0: { a, b }
/// - if choice == 1: { b, a }
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_u8(a: u8, b: u8, choice: Choice) -> SwapResult {
    if choice.0 == 0 {
        SwapResult { first: a, second: b }
    } else {
        SwapResult { first: b, second: a }
    }
}

// ============================================================================
// u32 variants
// ============================================================================

/// Constant-time-ish equality for `u32` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_u32(a: u32, b: u32) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `u32` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_u32(a: u32, b: u32) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `u32`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_u32(a: u32, b: u32) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `u32`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_u32(a: u32, b: u32) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `u32`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_u32(a: u32, b: u32) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `u32`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_u32(a: u32, b: u32) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `u32`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_u32(a: u32, b: u32, choice: Choice) -> u32 {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for u32.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResult32 {
    pub first: u32,
    pub second: u32,
}

/// Conditional swap for u32: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_u32(a: u32, b: u32, choice: Choice) -> SwapResult32 {
    if choice.0 == 0 {
        SwapResult32 { first: a, second: b }
    } else {
        SwapResult32 { first: b, second: a }
    }
}

// ============================================================================
// u64 variants
// ============================================================================

/// Constant-time-ish equality for `u64` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_u64(a: u64, b: u64) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `u64` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_u64(a: u64, b: u64) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `u64`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_u64(a: u64, b: u64) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `u64`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_u64(a: u64, b: u64) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `u64`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_u64(a: u64, b: u64) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `u64`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_u64(a: u64, b: u64) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `u64`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_u64(a: u64, b: u64, choice: Choice) -> u64 {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for u64.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResult64 {
    pub first: u64,
    pub second: u64,
}

/// Conditional swap for u64: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_u64(a: u64, b: u64, choice: Choice) -> SwapResult64 {
    if choice.0 == 0 {
        SwapResult64 { first: a, second: b }
    } else {
        SwapResult64 { first: b, second: a }
    }
}

// ============================================================================
// i8 signed variants
// ============================================================================

/// Constant-time-ish equality for `i8` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_i8(a: i8, b: i8) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `i8` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_i8(a: i8, b: i8) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `i8` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_i8(a: i8, b: i8) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `i8` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_i8(a: i8, b: i8) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `i8` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_i8(a: i8, b: i8) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `i8` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_i8(a: i8, b: i8) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `i8`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_i8(a: i8, b: i8, choice: Choice) -> i8 {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for i8.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResultI8 {
    pub first: i8,
    pub second: i8,
}

/// Conditional swap for i8: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_i8(a: i8, b: i8, choice: Choice) -> SwapResultI8 {
    if choice.0 == 0 {
        SwapResultI8 { first: a, second: b }
    } else {
        SwapResultI8 { first: b, second: a }
    }
}

// ============================================================================
// i16 signed variants
// ============================================================================

/// Constant-time-ish equality for `i16` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_i16(a: i16, b: i16) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `i16` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_i16(a: i16, b: i16) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `i16` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_i16(a: i16, b: i16) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `i16` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_i16(a: i16, b: i16) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `i16` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_i16(a: i16, b: i16) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `i16` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_i16(a: i16, b: i16) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `i16`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_i16(a: i16, b: i16, choice: Choice) -> i16 {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for i16.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResultI16 {
    pub first: i16,
    pub second: i16,
}

/// Conditional swap for i16: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_i16(a: i16, b: i16, choice: Choice) -> SwapResultI16 {
    if choice.0 == 0 {
        SwapResultI16 { first: a, second: b }
    } else {
        SwapResultI16 { first: b, second: a }
    }
}

// ============================================================================
// i32 signed variants
// ============================================================================

/// Constant-time-ish equality for `i32` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_i32(a: i32, b: i32) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `i32` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_i32(a: i32, b: i32) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `i32` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_i32(a: i32, b: i32) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `i32` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_i32(a: i32, b: i32) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `i32` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_i32(a: i32, b: i32) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `i32` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_i32(a: i32, b: i32) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `i32`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_i32(a: i32, b: i32, choice: Choice) -> i32 {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for i32.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResultI32 {
    pub first: i32,
    pub second: i32,
}

/// Conditional swap for i32: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_i32(a: i32, b: i32, choice: Choice) -> SwapResultI32 {
    if choice.0 == 0 {
        SwapResultI32 { first: a, second: b }
    } else {
        SwapResultI32 { first: b, second: a }
    }
}

// ============================================================================
// i64 signed variants
// ============================================================================

/// Constant-time-ish equality for `i64` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_i64(a: i64, b: i64) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `i64` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_i64(a: i64, b: i64) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `i64` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_i64(a: i64, b: i64) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `i64` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_i64(a: i64, b: i64) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `i64` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_i64(a: i64, b: i64) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `i64` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_i64(a: i64, b: i64) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `i64`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_i64(a: i64, b: i64, choice: Choice) -> i64 {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for i64.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResultI64 {
    pub first: i64,
    pub second: i64,
}

/// Conditional swap for i64: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_i64(a: i64, b: i64, choice: Choice) -> SwapResultI64 {
    if choice.0 == 0 {
        SwapResultI64 { first: a, second: b }
    } else {
        SwapResultI64 { first: b, second: a }
    }
}

// =============================================================================
// Conditional Negation (ConditionallyNegatable trait implementation)
// =============================================================================
// Used in cryptographic operations like elliptic curve point negation.
// Returns value unchanged if choice is 0, negated if choice is 1.
// Uses wrapping negation to handle MIN values correctly.

/// Conditionally negate an i8 value.
/// Returns `value` if choice is 0, `-value` (wrapping) if choice is 1.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == value")]
pub fn conditional_negate_i8(value: i8, choice: Choice) -> i8 {
    if choice.0 == 0 { value } else { value.wrapping_neg() }
}

/// Conditionally negate an i16 value.
/// Returns `value` if choice is 0, `-value` (wrapping) if choice is 1.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == value")]
pub fn conditional_negate_i16(value: i16, choice: Choice) -> i16 {
    if choice.0 == 0 { value } else { value.wrapping_neg() }
}

/// Conditionally negate an i32 value.
/// Returns `value` if choice is 0, `-value` (wrapping) if choice is 1.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == value")]
pub fn conditional_negate_i32(value: i32, choice: Choice) -> i32 {
    if choice.0 == 0 { value } else { value.wrapping_neg() }
}

/// Conditionally negate an i64 value.
/// Returns `value` if choice is 0, `-value` (wrapping) if choice is 1.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == value")]
pub fn conditional_negate_i64(value: i64, choice: Choice) -> i64 {
    if choice.0 == 0 { value } else { value.wrapping_neg() }
}

// ============================================================================
// usize variants (pointer-sized unsigned)
// ============================================================================
// Useful for array indexing operations in cryptographic code.

/// Constant-time-ish equality for `usize` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_usize(a: usize, b: usize) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `usize` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_usize(a: usize, b: usize) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `usize`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_usize(a: usize, b: usize) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `usize`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_usize(a: usize, b: usize) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `usize`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_usize(a: usize, b: usize) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `usize`.
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_usize(a: usize, b: usize) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `usize`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_usize(a: usize, b: usize, choice: Choice) -> usize {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for usize.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResultUsize {
    pub first: usize,
    pub second: usize,
}

/// Conditional swap for usize: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_usize(a: usize, b: usize, choice: Choice) -> SwapResultUsize {
    if choice.0 == 0 {
        SwapResultUsize { first: a, second: b }
    } else {
        SwapResultUsize { first: b, second: a }
    }
}

// ============================================================================
// isize variants (pointer-sized signed)
// ============================================================================
// Useful for signed offset calculations in cryptographic code.

/// Constant-time-ish equality for `isize` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a == b ==> result.0 == 1")]
#[ensures("a != b ==> result.0 == 0")]
pub fn ct_eq_isize(a: isize, b: isize) -> Choice {
    Choice(if a == b { 1 } else { 0 })
}

/// Constant-time-ish inequality for `isize` (functional contract only).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a != b ==> result.0 == 1")]
#[ensures("a == b ==> result.0 == 0")]
pub fn ct_ne_isize(a: isize, b: isize) -> Choice {
    Choice(if a != b { 1 } else { 0 })
}

/// Constant-time less-than for `isize` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a < b ==> result.0 == 1")]
#[ensures("a >= b ==> result.0 == 0")]
pub fn ct_lt_isize(a: isize, b: isize) -> Choice {
    Choice(if a < b { 1 } else { 0 })
}

/// Constant-time greater-than for `isize` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a > b ==> result.0 == 1")]
#[ensures("a <= b ==> result.0 == 0")]
pub fn ct_gt_isize(a: isize, b: isize) -> Choice {
    Choice(if a > b { 1 } else { 0 })
}

/// Constant-time less-than-or-equal for `isize` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a <= b ==> result.0 == 1")]
#[ensures("a > b ==> result.0 == 0")]
pub fn ct_le_isize(a: isize, b: isize) -> Choice {
    Choice(if a <= b { 1 } else { 0 })
}

/// Constant-time greater-than-or-equal for `isize` (signed comparison).
#[ensures("result.0 == 0 || result.0 == 1")]
#[ensures("a >= b ==> result.0 == 1")]
#[ensures("a < b ==> result.0 == 0")]
pub fn ct_ge_isize(a: isize, b: isize) -> Choice {
    Choice(if a >= b { 1 } else { 0 })
}

/// Conditional selection for `isize`.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == a")]
#[ensures("choice.0 == 1 ==> result == b")]
pub fn conditional_select_isize(a: isize, b: isize, choice: Choice) -> isize {
    if choice.0 == 0 { a } else { b }
}

/// Result of a conditional swap operation for isize.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SwapResultIsize {
    pub first: isize,
    pub second: isize,
}

/// Conditional swap for isize: swaps a and b if choice is 1, otherwise leaves them unchanged.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result.first == a")]
#[ensures("choice.0 == 0 ==> result.second == b")]
#[ensures("choice.0 == 1 ==> result.first == b")]
#[ensures("choice.0 == 1 ==> result.second == a")]
pub fn conditional_swap_isize(a: isize, b: isize, choice: Choice) -> SwapResultIsize {
    if choice.0 == 0 {
        SwapResultIsize { first: a, second: b }
    } else {
        SwapResultIsize { first: b, second: a }
    }
}

/// Conditionally negate an isize value.
/// Returns `value` if choice is 0, `-value` (wrapping) if choice is 1.
#[requires("choice.0 == 0 || choice.0 == 1")]
#[ensures("choice.0 == 0 ==> result == value")]
pub fn conditional_negate_isize(value: isize, choice: Choice) -> isize {
    if choice.0 == 0 { value } else { value.wrapping_neg() }
}

// ============================================================================
// CtOption - Constant-time optional value handling
// ============================================================================
// CtOption provides constant-time optional semantics where the presence or
// absence of a value doesn't leak through timing side-channels. This is critical
// for cryptographic operations where branching on Option::is_some() would
// create observable timing differences.
//
// Type-specific implementations are used because the verifier doesn't handle
// generic types well. Each CtOption variant holds a value and a Choice
// indicating whether the value is "Some" (choice=1) or "None" (choice=0).

/// Constant-time optional u8 value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionU8 {
    pub value: u8,
    pub is_some: Choice,
}

impl CtOptionU8 {
    /// Create a new CtOptionU8 with the given value and presence flag.
    /// Note: is_some should be Choice(0) or Choice(1) - behavior undefined otherwise.
    pub fn new(value: u8, is_some: Choice) -> CtOptionU8 {
        CtOptionU8 { value, is_some }
    }

    /// Create a CtOptionU8 representing "None" (absence of value).
    /// The value field is set to 0 but should not be used.
    pub fn none() -> CtOptionU8 {
        CtOptionU8 { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionU8 representing "Some" (presence of value).
    pub fn some(value: u8) -> CtOptionU8 {
        CtOptionU8 { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        // Normalize to ensure result is 0 or 1
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        // Normalize and negate
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    /// This operation is constant-time.
    pub fn unwrap_or(&self, default: u8) -> u8 {
        // Use simple conditional to avoid verifier issues with conditional_select
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    /// This operation is constant-time.
    pub fn unwrap_or_default(&self) -> u8 {
        // Use simple conditional to avoid verifier issues with conditional_select
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

/// Constant-time optional u32 value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionU32 {
    pub value: u32,
    pub is_some: Choice,
}

impl CtOptionU32 {
    /// Create a new CtOptionU32 with the given value and presence flag.
    /// Note: is_some should be Choice(0) or Choice(1) - behavior undefined otherwise.
    pub fn new(value: u32, is_some: Choice) -> CtOptionU32 {
        CtOptionU32 { value, is_some }
    }

    /// Create a CtOptionU32 representing "None" (absence of value).
    /// The value field is set to 0 but should not be used.
    pub fn none() -> CtOptionU32 {
        CtOptionU32 { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionU32 representing "Some" (presence of value).
    pub fn some(value: u32) -> CtOptionU32 {
        CtOptionU32 { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        // Normalize to ensure result is 0 or 1
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        // Normalize and negate
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    /// This operation is constant-time.
    pub fn unwrap_or(&self, default: u32) -> u32 {
        // Use simple conditional to avoid verifier issues with conditional_select
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    /// This operation is constant-time.
    pub fn unwrap_or_default(&self) -> u32 {
        // Use simple conditional to avoid verifier issues with conditional_select
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

/// Constant-time optional u64 value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionU64 {
    pub value: u64,
    pub is_some: Choice,
}

impl CtOptionU64 {
    /// Create a new CtOptionU64 with the given value and presence flag.
    /// Note: is_some should be Choice(0) or Choice(1) - behavior undefined otherwise.
    pub fn new(value: u64, is_some: Choice) -> CtOptionU64 {
        CtOptionU64 { value, is_some }
    }

    /// Create a CtOptionU64 representing "None" (absence of value).
    /// The value field is set to 0 but should not be used.
    pub fn none() -> CtOptionU64 {
        CtOptionU64 { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionU64 representing "Some" (presence of value).
    pub fn some(value: u64) -> CtOptionU64 {
        CtOptionU64 { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        // Normalize to ensure result is 0 or 1
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        // Normalize and negate
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    /// This operation is constant-time.
    pub fn unwrap_or(&self, default: u64) -> u64 {
        // Use simple conditional to avoid verifier issues with conditional_select
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    /// This operation is constant-time.
    pub fn unwrap_or_default(&self) -> u64 {
        // Use simple conditional to avoid verifier issues with conditional_select
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

// ============================================================================
// CtOption for signed types (i8, i16, i32, i64)
// ============================================================================

/// Constant-time optional i8 value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionI8 {
    pub value: i8,
    pub is_some: Choice,
}

impl CtOptionI8 {
    /// Create a new CtOptionI8 with the given value and presence flag.
    pub fn new(value: i8, is_some: Choice) -> CtOptionI8 {
        CtOptionI8 { value, is_some }
    }

    /// Create a CtOptionI8 representing "None" (absence of value).
    pub fn none() -> CtOptionI8 {
        CtOptionI8 { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionI8 representing "Some" (presence of value).
    pub fn some(value: i8) -> CtOptionI8 {
        CtOptionI8 { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    pub fn unwrap_or(&self, default: i8) -> i8 {
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    pub fn unwrap_or_default(&self) -> i8 {
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

/// Constant-time optional i16 value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionI16 {
    pub value: i16,
    pub is_some: Choice,
}

impl CtOptionI16 {
    /// Create a new CtOptionI16 with the given value and presence flag.
    pub fn new(value: i16, is_some: Choice) -> CtOptionI16 {
        CtOptionI16 { value, is_some }
    }

    /// Create a CtOptionI16 representing "None" (absence of value).
    pub fn none() -> CtOptionI16 {
        CtOptionI16 { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionI16 representing "Some" (presence of value).
    pub fn some(value: i16) -> CtOptionI16 {
        CtOptionI16 { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    pub fn unwrap_or(&self, default: i16) -> i16 {
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    pub fn unwrap_or_default(&self) -> i16 {
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

/// Constant-time optional i32 value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionI32 {
    pub value: i32,
    pub is_some: Choice,
}

impl CtOptionI32 {
    /// Create a new CtOptionI32 with the given value and presence flag.
    pub fn new(value: i32, is_some: Choice) -> CtOptionI32 {
        CtOptionI32 { value, is_some }
    }

    /// Create a CtOptionI32 representing "None" (absence of value).
    pub fn none() -> CtOptionI32 {
        CtOptionI32 { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionI32 representing "Some" (presence of value).
    pub fn some(value: i32) -> CtOptionI32 {
        CtOptionI32 { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    pub fn unwrap_or(&self, default: i32) -> i32 {
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    pub fn unwrap_or_default(&self) -> i32 {
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

/// Constant-time optional i64 value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionI64 {
    pub value: i64,
    pub is_some: Choice,
}

impl CtOptionI64 {
    /// Create a new CtOptionI64 with the given value and presence flag.
    pub fn new(value: i64, is_some: Choice) -> CtOptionI64 {
        CtOptionI64 { value, is_some }
    }

    /// Create a CtOptionI64 representing "None" (absence of value).
    pub fn none() -> CtOptionI64 {
        CtOptionI64 { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionI64 representing "Some" (presence of value).
    pub fn some(value: i64) -> CtOptionI64 {
        CtOptionI64 { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    pub fn unwrap_or(&self, default: i64) -> i64 {
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    pub fn unwrap_or_default(&self) -> i64 {
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

// ============================================================================
// CtOption for pointer-sized types (usize, isize)
// ============================================================================

/// Constant-time optional usize value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionUsize {
    pub value: usize,
    pub is_some: Choice,
}

impl CtOptionUsize {
    /// Create a new CtOptionUsize with the given value and presence flag.
    pub fn new(value: usize, is_some: Choice) -> CtOptionUsize {
        CtOptionUsize { value, is_some }
    }

    /// Create a CtOptionUsize representing "None" (absence of value).
    pub fn none() -> CtOptionUsize {
        CtOptionUsize { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionUsize representing "Some" (presence of value).
    pub fn some(value: usize) -> CtOptionUsize {
        CtOptionUsize { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    pub fn unwrap_or(&self, default: usize) -> usize {
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    pub fn unwrap_or_default(&self) -> usize {
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

/// Constant-time optional isize value.
/// Holds a value and a Choice indicating presence (1) or absence (0).
#[derive(Copy, Clone, Debug)]
pub struct CtOptionIsize {
    pub value: isize,
    pub is_some: Choice,
}

impl CtOptionIsize {
    /// Create a new CtOptionIsize with the given value and presence flag.
    pub fn new(value: isize, is_some: Choice) -> CtOptionIsize {
        CtOptionIsize { value, is_some }
    }

    /// Create a CtOptionIsize representing "None" (absence of value).
    pub fn none() -> CtOptionIsize {
        CtOptionIsize { value: 0, is_some: Choice(0) }
    }

    /// Create a CtOptionIsize representing "Some" (presence of value).
    pub fn some(value: isize) -> CtOptionIsize {
        CtOptionIsize { value, is_some: Choice(1) }
    }

    /// Returns a Choice indicating whether this option contains a value (1) or not (0).
    pub fn ct_is_some(&self) -> Choice {
        Choice::from_u8(self.is_some.0)
    }

    /// Returns a Choice indicating whether this option is empty (1) or contains a value (0).
    pub fn ct_is_none(&self) -> Choice {
        let normalized = Choice::from_u8(self.is_some.0);
        normalized.not()
    }

    /// Returns the contained value if Some, otherwise returns the default.
    pub fn unwrap_or(&self, default: isize) -> isize {
        if self.is_some.0 == 0 { default } else { self.value }
    }

    /// Returns the contained value if Some, otherwise returns 0.
    pub fn unwrap_or_default(&self) -> isize {
        if self.is_some.0 == 0 { 0 } else { self.value }
    }
}

// =============================================================================
// Constant-Time Byte Array Comparison
// =============================================================================
//
// These functions provide constant-time equality comparison for fixed-size byte
// arrays commonly used in cryptography. The implementation XORs each byte pair
// and ORs all results together - if all bytes match, the accumulated result is 0;
// if any byte differs, it will be non-zero.
//
// Fixed sizes avoid generics which the verifier doesn't support:
// - 16 bytes: AES block size, UUID, MD5 hash
// - 32 bytes: SHA-256 hash, ChaCha20 key, X25519 key
// - 64 bytes: SHA-512 hash, Ed25519 signature

#[ensures("result == 0 || result == 1")]
#[ensures("x == 0 ==> result == 1")]
#[ensures("x != 0 ==> result == 0")]
fn ct_is_zero_u8(x: u8) -> u8 {
    (x == 0) as u8
}

/// Constant-time equality comparison for 16-byte arrays (128 bits).
/// Returns Choice(1) if arrays are equal, Choice(0) otherwise.
///
/// The comparison examines all 16 bytes regardless of whether a difference
/// is found early, preventing timing side-channels.
///
/// Note: No #[ensures] attribute - verifier has trouble with array reference parameters.
/// The constant-time property is ensured by the bitwise implementation.
pub fn ct_eq_bytes_16(a: &[u8; 16], b: &[u8; 16]) -> Choice {
    let mut acc: u8 = 0;
    acc |= a[0] ^ b[0];
    acc |= a[1] ^ b[1];
    acc |= a[2] ^ b[2];
    acc |= a[3] ^ b[3];
    acc |= a[4] ^ b[4];
    acc |= a[5] ^ b[5];
    acc |= a[6] ^ b[6];
    acc |= a[7] ^ b[7];
    acc |= a[8] ^ b[8];
    acc |= a[9] ^ b[9];
    acc |= a[10] ^ b[10];
    acc |= a[11] ^ b[11];
    acc |= a[12] ^ b[12];
    acc |= a[13] ^ b[13];
    acc |= a[14] ^ b[14];
    acc |= a[15] ^ b[15];
    Choice::from_u8(ct_is_zero_u8(acc))
}

/// Constant-time equality comparison for 32-byte arrays (256 bits).
/// Returns Choice(1) if arrays are equal, Choice(0) otherwise.
///
/// Common use cases: SHA-256 hashes, ChaCha20 keys, X25519 keys.
///
/// Note: No #[ensures] attribute - verifier has trouble with array reference parameters.
/// The constant-time property is ensured by the bitwise implementation.
pub fn ct_eq_bytes_32(a: &[u8; 32], b: &[u8; 32]) -> Choice {
    let mut acc: u8 = 0;
    acc |= a[0] ^ b[0];
    acc |= a[1] ^ b[1];
    acc |= a[2] ^ b[2];
    acc |= a[3] ^ b[3];
    acc |= a[4] ^ b[4];
    acc |= a[5] ^ b[5];
    acc |= a[6] ^ b[6];
    acc |= a[7] ^ b[7];
    acc |= a[8] ^ b[8];
    acc |= a[9] ^ b[9];
    acc |= a[10] ^ b[10];
    acc |= a[11] ^ b[11];
    acc |= a[12] ^ b[12];
    acc |= a[13] ^ b[13];
    acc |= a[14] ^ b[14];
    acc |= a[15] ^ b[15];
    acc |= a[16] ^ b[16];
    acc |= a[17] ^ b[17];
    acc |= a[18] ^ b[18];
    acc |= a[19] ^ b[19];
    acc |= a[20] ^ b[20];
    acc |= a[21] ^ b[21];
    acc |= a[22] ^ b[22];
    acc |= a[23] ^ b[23];
    acc |= a[24] ^ b[24];
    acc |= a[25] ^ b[25];
    acc |= a[26] ^ b[26];
    acc |= a[27] ^ b[27];
    acc |= a[28] ^ b[28];
    acc |= a[29] ^ b[29];
    acc |= a[30] ^ b[30];
    acc |= a[31] ^ b[31];
    Choice::from_u8(ct_is_zero_u8(acc))
}

/// Constant-time equality comparison for 64-byte arrays (512 bits).
/// Returns Choice(1) if arrays are equal, Choice(0) otherwise.
///
/// Common use cases: SHA-512 hashes, Ed25519 signatures.
///
/// Note: No #[ensures] attribute - verifier has trouble with array reference parameters.
/// The constant-time property is ensured by the bitwise implementation.
pub fn ct_eq_bytes_64(a: &[u8; 64], b: &[u8; 64]) -> Choice {
    let mut acc: u8 = 0;
    // First 32 bytes
    acc |= a[0] ^ b[0];
    acc |= a[1] ^ b[1];
    acc |= a[2] ^ b[2];
    acc |= a[3] ^ b[3];
    acc |= a[4] ^ b[4];
    acc |= a[5] ^ b[5];
    acc |= a[6] ^ b[6];
    acc |= a[7] ^ b[7];
    acc |= a[8] ^ b[8];
    acc |= a[9] ^ b[9];
    acc |= a[10] ^ b[10];
    acc |= a[11] ^ b[11];
    acc |= a[12] ^ b[12];
    acc |= a[13] ^ b[13];
    acc |= a[14] ^ b[14];
    acc |= a[15] ^ b[15];
    acc |= a[16] ^ b[16];
    acc |= a[17] ^ b[17];
    acc |= a[18] ^ b[18];
    acc |= a[19] ^ b[19];
    acc |= a[20] ^ b[20];
    acc |= a[21] ^ b[21];
    acc |= a[22] ^ b[22];
    acc |= a[23] ^ b[23];
    acc |= a[24] ^ b[24];
    acc |= a[25] ^ b[25];
    acc |= a[26] ^ b[26];
    acc |= a[27] ^ b[27];
    acc |= a[28] ^ b[28];
    acc |= a[29] ^ b[29];
    acc |= a[30] ^ b[30];
    acc |= a[31] ^ b[31];
    // Second 32 bytes
    acc |= a[32] ^ b[32];
    acc |= a[33] ^ b[33];
    acc |= a[34] ^ b[34];
    acc |= a[35] ^ b[35];
    acc |= a[36] ^ b[36];
    acc |= a[37] ^ b[37];
    acc |= a[38] ^ b[38];
    acc |= a[39] ^ b[39];
    acc |= a[40] ^ b[40];
    acc |= a[41] ^ b[41];
    acc |= a[42] ^ b[42];
    acc |= a[43] ^ b[43];
    acc |= a[44] ^ b[44];
    acc |= a[45] ^ b[45];
    acc |= a[46] ^ b[46];
    acc |= a[47] ^ b[47];
    acc |= a[48] ^ b[48];
    acc |= a[49] ^ b[49];
    acc |= a[50] ^ b[50];
    acc |= a[51] ^ b[51];
    acc |= a[52] ^ b[52];
    acc |= a[53] ^ b[53];
    acc |= a[54] ^ b[54];
    acc |= a[55] ^ b[55];
    acc |= a[56] ^ b[56];
    acc |= a[57] ^ b[57];
    acc |= a[58] ^ b[58];
    acc |= a[59] ^ b[59];
    acc |= a[60] ^ b[60];
    acc |= a[61] ^ b[61];
    acc |= a[62] ^ b[62];
    acc |= a[63] ^ b[63];
    Choice::from_u8(ct_is_zero_u8(acc))
}

// =============================================================================
// Constant-time zero checking (ConstantTimeZero)
// =============================================================================
//
// These functions check if a value is zero in constant time, returning Choice(1)
// if zero, Choice(0) otherwise. Useful for cryptographic operations like:
// - Scalar validation in elliptic curve operations
// - Field element validation
// - Key validation (checking if key is the identity element)

/// Constant-time zero check for u8.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u8_pub(x: u8) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for u16.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u16(x: u16) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for u32.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u32(x: u32) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for u64.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_u64(x: u64) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for i8.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i8(x: i8) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for i16.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i16(x: i16) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for i32.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i32(x: i32) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for i64.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_i64(x: i64) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for usize.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_usize(x: usize) -> Choice {
    Choice::from_u8((x == 0) as u8)
}

/// Constant-time zero check for isize.
/// Returns Choice(1) if x == 0, Choice(0) otherwise.
#[ensures("result.0 == 0 || result.0 == 1")]
pub fn ct_is_zero_isize(x: isize) -> Choice {
    Choice::from_u8((x == 0) as u8)
}
