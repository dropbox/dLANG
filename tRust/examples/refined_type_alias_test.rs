//! Integration test for refined type aliases (Phase 12.1)
//!
//! Refined type aliases attach predicates to type definitions, enabling automatic
//! verification at assignment and usage sites. This test validates the basic syntax
//! parsing for refined type aliases:
//!
//! Syntax:
//!   #[trust::refined("predicate")]  -- refinement on a type alias
//!   type AliasName = UnderlyingType;
//!
//! NOTE: Phase 12.1 only implements syntax parsing. The refinement attributes
//! are parsed and stored but do not yet generate automatic verification conditions.
//! Phase 12.2 will add automatic VC generation from refined type aliases.
//!
//! This test demonstrates that:
//! 1. The refined type alias syntax is parsed correctly (no parse errors)
//! 2. Functions using refined type aliases verify correctly with explicit contracts

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Basic refined type aliases
// ============================================================================

/// A positive integer type (value > 0)
/// NOTE: In Phase 12.1, the refinement is parsed but not yet used for VC generation
#[trust::refined("x > 0")]
type Positive = i32;

/// A non-negative integer type (value >= 0)
#[trust::refined("x >= 0")]
type NonNegative = i32;

/// A non-zero integer type (value != 0)
#[trust::refined("x != 0")]
type NonZero = i32;

/// A percentage type (0 <= value <= 100)
#[trust::refined("x >= 0 && x <= 100")]
type Percentage = u8;

/// A bounded index type (value < N for some N)
#[trust::refined("x < 10")]
type SmallIndex = usize;

// ============================================================================
// Part 2: Functions using refined type aliases
// ============================================================================

/// Identity function for Positive - requires explicit contract until Phase 12.2
#[requires("n > 0")]
#[ensures("result > 0")]
fn positive_identity(n: Positive) -> Positive {
    n
}

/// Convert NonNegative to Positive by adding 1
#[requires("n >= 0 && n < 1000")]
#[ensures("result > 0")]
fn nonneg_to_positive(n: NonNegative) -> Positive {
    n + 1
}

/// Safe division using NonZero divisor
#[requires("divisor != 0")]
fn safe_divide(dividend: i32, divisor: NonZero) -> i32 {
    dividend / divisor
}

/// Clamp a value to a Percentage
#[ensures("result >= 0 && result <= 100")]
fn clamp_percentage(value: i32) -> Percentage {
    if value < 0 { 0 }
    else if value > 100 { 100 }
    else { value as u8 }
}

/// Create a SmallIndex from a value (clamped)
#[ensures("result < 10")]
fn make_small_index(value: usize) -> SmallIndex {
    if value >= 10 { 9 } else { value }
}

// ============================================================================
// Part 3: Refined type aliases with generic predicates
// ============================================================================

/// A bounded value between min and max (inclusive)
/// Note: Uses "x" as the canonical refinement variable
#[trust::refined("x >= 1 && x <= 10")]
type OneToTen = i32;

/// Create a bounded value
#[requires("value >= 1 && value <= 10")]
#[ensures("result >= 1 && result <= 10")]
fn make_one_to_ten(value: i32) -> OneToTen {
    value
}

/// Clamp to bounded range
#[ensures("result >= 1 && result <= 10")]
fn clamp_one_to_ten(value: i32) -> OneToTen {
    if value < 1 { 1 }
    else if value > 10 { 10 }
    else { value }
}

// ============================================================================
// Part 4: Nested refined type aliases (for documentation, not yet semantic)
// ============================================================================

/// Even positive number
#[trust::refined("x > 0 && x % 2 == 0")]
type EvenPositive = i32;

/// Unsigned non-zero
#[trust::refined("x > 0")]
type UnsignedPositive = u32;

/// Functions demonstrating these types
#[requires("n > 0")]
#[requires("n % 2 == 0")]
fn double_even_positive(n: EvenPositive) -> EvenPositive {
    // n * 2 would overflow check, so use a simpler operation
    // This demonstrates the type is parsed, not full VC generation
    n
}

#[requires("n > 0")]
#[ensures("result > 0")]
fn unsigned_positive_identity(n: UnsignedPositive) -> UnsignedPositive {
    n
}

// ============================================================================
// Part 5: Real-world use case patterns
// ============================================================================

/// Array index that's valid for a fixed-size buffer
#[trust::refined("idx < 8")]
type BufferIndex = usize;

/// Access a buffer element safely
#[requires("idx < 8")]
fn get_buffer_element(buffer: &[i32; 8], idx: BufferIndex) -> i32 {
    buffer[idx]
}

/// Port number in valid range
#[trust::refined("port >= 1 && port <= 65535")]
type PortNumber = u16;

/// Check if port is privileged (< 1024)
#[requires("port >= 1 && port <= 65535")]
fn is_privileged_port(port: PortNumber) -> bool {
    port < 1024
}

fn main() {
    // Part 1: Basic type aliases - just verify they compile
    let _p: Positive = 5;
    let _nn: NonNegative = 0;
    let _nz: NonZero = -1;
    let _pct: Percentage = 50;
    let _idx: SmallIndex = 3;

    // Part 2: Functions with refined type aliases
    let p1 = positive_identity(10);
    assert!(p1 > 0);

    let p2 = nonneg_to_positive(5);
    assert!(p2 > 0);

    let div_result = safe_divide(100, 10);
    assert!(div_result == 10);

    let pct = clamp_percentage(150);
    assert!(pct == 100);

    let idx = make_small_index(15);
    assert!(idx < 10);

    // Part 3: Bounded values
    let bounded = make_one_to_ten(5);
    assert!(bounded >= 1 && bounded <= 10);

    let clamped = clamp_one_to_ten(100);
    assert!(clamped == 10);

    // Part 4: More complex refinements
    let even = double_even_positive(4);
    assert!(even == 4);

    let upos = unsigned_positive_identity(42);
    assert!(upos > 0);

    // Part 5: Real-world patterns
    let buffer = [1, 2, 3, 4, 5, 6, 7, 8];
    let elem = get_buffer_element(&buffer, 3);
    assert!(elem == 4);

    let port: PortNumber = 80;
    let is_priv = is_privileged_port(port);
    assert!(is_priv);

    println!("All refined type alias tests passed!");
}
