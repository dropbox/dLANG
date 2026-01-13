//! Integration test for Standard Library Refined Types (Phase 12.5)
//!
//! This module defines standard refined type aliases that provide type-level
//! guarantees through refinement predicates. These types complement Rust's
//! standard library with verification-aware variants.
//!
//! Categories:
//! 1. Non-zero integers (NonZeroI32, NonZeroU64, etc.)
//! 2. Percentage types (Percentage, PercentageFrac)
//! 3. Bounded indices (Index4, Index8, Index16, Index32, Index64, Index128)
//! 4. Refined Option patterns (VerifiedSome)
//! 5. Refined Result patterns (VerifiedOk)
//!
//! NOTE: Rust type aliases cannot be parameterized with const generics in a way
//! that allows attaching refinements like `#[refined("x < N")]`. Therefore,
//! we provide concrete bounded index types for common sizes.

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Non-Zero Integer Types
// ============================================================================

/// Non-zero signed 8-bit integer
#[trust::refined("x != 0")]
type NonZeroI8 = i8;

/// Non-zero signed 16-bit integer
#[trust::refined("x != 0")]
type NonZeroI16 = i16;

/// Non-zero signed 32-bit integer
#[trust::refined("x != 0")]
type NonZeroI32 = i32;

/// Non-zero signed 64-bit integer
#[trust::refined("x != 0")]
type NonZeroI64 = i64;

/// Non-zero unsigned 8-bit integer
#[trust::refined("x != 0")]
type NonZeroU8 = u8;

/// Non-zero unsigned 16-bit integer
#[trust::refined("x != 0")]
type NonZeroU16 = u16;

/// Non-zero unsigned 32-bit integer
#[trust::refined("x != 0")]
type NonZeroU32 = u32;

/// Non-zero unsigned 64-bit integer
#[trust::refined("x != 0")]
type NonZeroU64 = u64;

/// Non-zero usize
#[trust::refined("x != 0")]
type NonZeroUsize = usize;

/// Non-zero isize
#[trust::refined("x != 0")]
type NonZeroIsize = isize;

// ============================================================================
// Part 2: Positive Integer Types
// ============================================================================

/// Positive signed 32-bit integer (x > 0)
#[trust::refined("x > 0")]
type PositiveI32 = i32;

/// Positive signed 64-bit integer (x > 0)
#[trust::refined("x > 0")]
type PositiveI64 = i64;

/// Positive usize (x > 0)
#[trust::refined("x > 0")]
type PositiveUsize = usize;

// ============================================================================
// Part 3: Non-Negative Integer Types
// ============================================================================

/// Non-negative signed 32-bit integer (x >= 0)
#[trust::refined("x >= 0")]
type NonNegativeI32 = i32;

/// Non-negative signed 64-bit integer (x >= 0)
#[trust::refined("x >= 0")]
type NonNegativeI64 = i64;

// ============================================================================
// Part 4: Percentage Types
// ============================================================================

/// Percentage value 0-100 (inclusive)
#[trust::refined("x >= 0 && x <= 100")]
type Percentage = u8;

/// Percentage as u16 for computations (0-100)
#[trust::refined("x >= 0 && x <= 100")]
type Percentage16 = u16;

/// Percentage as i32 for signed operations (0-100)
#[trust::refined("x >= 0 && x <= 100")]
type PercentageI32 = i32;

// ============================================================================
// Part 5: Bounded Index Types
// ============================================================================

/// Index valid for arrays of size 4
#[trust::refined("x < 4")]
type Index4 = usize;

/// Index valid for arrays of size 8
#[trust::refined("x < 8")]
type Index8 = usize;

/// Index valid for arrays of size 16
#[trust::refined("x < 16")]
type Index16 = usize;

/// Index valid for arrays of size 32
#[trust::refined("x < 32")]
type Index32 = usize;

/// Index valid for arrays of size 64
#[trust::refined("x < 64")]
type Index64 = usize;

/// Index valid for arrays of size 128
#[trust::refined("x < 128")]
type Index128 = usize;

/// Index valid for arrays of size 256
#[trust::refined("x < 256")]
type Index256 = usize;

/// Index valid for arrays of size 1024
#[trust::refined("x < 1024")]
type Index1K = usize;

// ============================================================================
// Part 6: Network-Related Types
// ============================================================================

/// Valid TCP/UDP port number (1-65535)
#[trust::refined("x >= 1 && x <= 65535")]
type PortNumber = u16;

/// Privileged port number (1-1023)
#[trust::refined("x >= 1 && x <= 1023")]
type PrivilegedPort = u16;

/// User port number (1024-65535)
#[trust::refined("x >= 1024 && x <= 65535")]
type UserPort = u16;

/// IPv4 octet (0-255)
#[trust::refined("x >= 0 && x <= 255")]
type Octet = u8;

// ============================================================================
// Part 7: Functions Using Non-Zero Types
// ============================================================================

/// Safe division using NonZeroI32 divisor
#[requires("divisor != 0")]
fn safe_divide_i32(dividend: i32, divisor: NonZeroI32) -> i32 {
    dividend / divisor
}

/// Safe division using NonZeroU64 divisor
#[requires("divisor != 0")]
fn safe_divide_u64(dividend: u64, divisor: NonZeroU64) -> u64 {
    dividend / divisor
}

/// Safe modulo using NonZeroU32 divisor
#[requires("divisor != 0")]
fn safe_modulo(dividend: u32, divisor: NonZeroU32) -> u32 {
    dividend % divisor
}

/// Create a NonZeroI32 from a non-zero value
#[requires("value != 0")]
#[ensures("result != 0")]
fn make_nonzero_i32(value: i32) -> NonZeroI32 {
    value
}

/// Convert a positive to a non-zero (always valid)
#[requires("value > 0")]
#[ensures("result != 0")]
fn positive_to_nonzero(value: PositiveI32) -> NonZeroI32 {
    value
}

// ============================================================================
// Part 8: Functions Using Percentage Types
// ============================================================================

/// Clamp a value to a Percentage
#[ensures("result >= 0 && result <= 100")]
fn clamp_percentage(value: i32) -> Percentage {
    if value < 0 {
        0
    } else if value > 100 {
        100
    } else {
        value as u8
    }
}

/// Scale a value by a percentage (uses saturating multiply)
#[requires("pct >= 0 && pct <= 100")]
fn scale_by_percentage(value: i32, pct: Percentage) -> i32 {
    // Use saturating multiply to prevent overflow, then divide
    let pct_bounded = (pct % 101) as i32;  // Ensures pct_bounded <= 100
    value.saturating_mul(pct_bounded) / 100
}

/// Add two percentages, capping at 100
#[requires("a >= 0 && a <= 100")]
#[requires("b >= 0 && b <= 100")]
#[ensures("result >= 0 && result <= 100")]
fn add_percentages_capped(a: Percentage, b: Percentage) -> Percentage {
    // Bound inputs to ensure verifier knows overflow is impossible
    let a_bounded = a % 101;  // verifier knows: a_bounded <= 100
    let b_bounded = b % 101;  // verifier knows: b_bounded <= 100
    let sum = (a_bounded as u16) + (b_bounded as u16);  // max: 200, fits in u16
    if sum > 100 {
        100
    } else {
        sum as u8
    }
}

/// Compute average of two percentages
#[requires("a >= 0 && a <= 100")]
#[requires("b >= 0 && b <= 100")]
#[ensures("result >= 0 && result <= 100")]
fn average_percentage(a: Percentage, b: Percentage) -> Percentage {
    // Bound inputs to ensure verifier knows overflow is impossible
    let a_bounded = a % 101;  // verifier knows: a_bounded <= 100
    let b_bounded = b % 101;  // verifier knows: b_bounded <= 100
    let sum = (a_bounded as u16) + (b_bounded as u16);  // max: 200, fits in u16
    (sum / 2) as u8
}

// ============================================================================
// Part 9: Functions Using Bounded Index Types
// ============================================================================

/// Get element at Index8 from an 8-element array
#[requires("idx < 8")]
fn get_at_index8(arr: &[i32; 8], idx: Index8) -> i32 {
    arr[idx]
}

/// Set element at Index16 in a 16-element array
#[requires("idx < 16")]
fn set_at_index16(arr: &mut [i32; 16], idx: Index16, value: i32) {
    arr[idx] = value;
}

/// Convert Index8 to Index16 (always valid since 8 < 16)
#[requires("idx < 8")]
#[ensures("result < 16")]
fn index8_to_index16(idx: Index8) -> Index16 {
    idx
}

/// Create an Index4 from a value, wrapping if needed
#[ensures("result < 4")]
fn wrap_to_index4(value: usize) -> Index4 {
    value % 4
}

/// Create an Index8 from a value, clamping if needed
#[ensures("result < 8")]
fn clamp_to_index8(value: usize) -> Index8 {
    if value >= 8 {
        7
    } else {
        value
    }
}

// ============================================================================
// Part 10: Functions Using Network Types
// ============================================================================

/// Check if a port is privileged
#[requires("port >= 1 && port <= 65535")]
fn is_privileged(port: PortNumber) -> bool {
    port <= 1023
}

/// Convert a privileged port to a general port
#[requires("port >= 1 && port <= 1023")]
#[ensures("result >= 1 && result <= 65535")]
fn privileged_to_port(port: PrivilegedPort) -> PortNumber {
    port
}

/// Create a user port from a value
#[requires("value >= 1024 && value <= 65535")]
#[ensures("result >= 1024 && result <= 65535")]
fn make_user_port(value: u16) -> UserPort {
    value
}

// ============================================================================
// Part 11: Refined Option Patterns
// ============================================================================

/// A verified Some value - represents Option that is known to be Some
/// This pattern is useful when analysis can prove the Option is non-None
#[requires("value > 0")]
#[ensures("result.is_some()")]
fn make_verified_some(value: i32) -> Option<i32> {
    Some(value)
}

/// Unwrap a verified Some value safely
#[requires("opt.is_some()")]
fn verified_unwrap(opt: Option<i32>) -> i32 {
    opt.unwrap()
}

/// Map over a verified Some value
#[requires("opt.is_some()")]
#[ensures("result.is_some()")]
fn verified_map(opt: Option<i32>, f: impl Fn(i32) -> i32) -> Option<i32> {
    opt.map(f)
}

// ============================================================================
// Part 12: Refined Result Patterns
// ============================================================================

/// A verified Ok value - represents Result that is known to be Ok
#[requires("value >= 0")]
#[ensures("result.is_ok()")]
fn make_verified_ok(value: i32) -> Result<i32, &'static str> {
    Ok(value)
}

/// Unwrap a verified Ok value safely
#[requires("res.is_ok()")]
fn verified_ok_unwrap(res: Result<i32, &'static str>) -> i32 {
    res.unwrap()
}

/// Map over a verified Ok value
#[requires("res.is_ok()")]
#[ensures("result.is_ok()")]
fn verified_ok_map(
    res: Result<i32, &'static str>,
    f: impl Fn(i32) -> i32,
) -> Result<i32, &'static str> {
    res.map(f)
}

// ============================================================================
// Part 13: Iterator-Related Refined Types
// ============================================================================

/// Length-preserving iterator count - result equals original length
#[requires("len > 0")]
#[ensures("result > 0")]
fn preserved_length(len: usize) -> usize {
    len
}

/// Non-empty iterator minimum length
#[trust::refined("x > 0")]
type NonEmptyLen = usize;

/// Compute the length after filter (may decrease)
#[requires("original_len >= 0")]
#[requires("kept <= original_len")]
#[ensures("result <= original_len")]
fn filtered_length(original_len: usize, kept: usize) -> usize {
    kept
}

/// Compute the length after chain (sum of both)
#[requires("len1 >= 0")]
#[requires("len2 >= 0")]
#[ensures("result >= len1")]
#[ensures("result >= len2")]
fn chained_length(len1: usize, len2: usize) -> usize {
    len1.saturating_add(len2)
}

// ============================================================================
// Main: Test all refined types
// ============================================================================

fn main() {
    // Test non-zero types
    let nz: NonZeroI32 = 42;
    assert!(nz != 0);
    let div_result = safe_divide_i32(100, 10);
    assert!(div_result == 10);

    let nz_u64: NonZeroU64 = 1;
    let div_u64 = safe_divide_u64(1000, nz_u64);
    assert!(div_u64 == 1000);

    let mod_result = safe_modulo(17, 5);
    assert!(mod_result == 2);

    let made = make_nonzero_i32(7);
    assert!(made == 7);

    let pos: PositiveI32 = 5;
    let converted = positive_to_nonzero(pos);
    assert!(converted == 5);

    // Test percentage types
    let pct = clamp_percentage(150);
    assert!(pct == 100);

    let pct_low = clamp_percentage(-10);
    assert!(pct_low == 0);

    let scaled = scale_by_percentage(200, 50);
    assert!(scaled == 100);

    let sum_pct = add_percentages_capped(60, 60);
    assert!(sum_pct == 100);

    let avg = average_percentage(40, 60);
    assert!(avg == 50);

    // Test bounded index types
    let arr8 = [1, 2, 3, 4, 5, 6, 7, 8];
    let elem = get_at_index8(&arr8, 3);
    assert!(elem == 4);

    let mut arr16 = [0i32; 16];
    set_at_index16(&mut arr16, 10, 42);
    assert!(arr16[10] == 42);

    let idx8: Index8 = 5;
    let idx16 = index8_to_index16(idx8);
    assert!(idx16 == 5);

    let wrapped = wrap_to_index4(17);
    assert!(wrapped == 1);

    let clamped = clamp_to_index8(100);
    assert!(clamped == 7);

    // Test network types
    let port: PortNumber = 8080;
    let is_priv = is_privileged(port);
    assert!(!is_priv);

    let priv_port: PrivilegedPort = 80;
    let general = privileged_to_port(priv_port);
    assert!(general == 80);

    let user_port = make_user_port(8080);
    assert!(user_port == 8080);

    // Test verified Option patterns
    let some_val = make_verified_some(10);
    assert!(some_val.is_some());
    let unwrapped = verified_unwrap(some_val);
    assert!(unwrapped == 10);

    let mapped = verified_map(Some(5), |x| x * 2);
    assert!(mapped == Some(10));

    // Test verified Result patterns
    let ok_val = make_verified_ok(42);
    assert!(ok_val.is_ok());
    let ok_unwrapped = verified_ok_unwrap(ok_val);
    assert!(ok_unwrapped == 42);

    let ok_mapped = verified_ok_map(Ok(5), |x| x + 10);
    assert!(ok_mapped == Ok(15));

    // Test iterator-related types
    let len: NonEmptyLen = 10;
    let preserved = preserved_length(len);
    assert!(preserved == 10);

    let filtered = filtered_length(100, 50);
    assert!(filtered == 50);

    let chained = chained_length(10, 20);
    assert!(chained == 30);

    println!("All standard refined type tests passed!");
}
