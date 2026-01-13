//! N3.3: Mutation Testing Framework for tRust
//!
//! This test validates that tRust's verification correctly detects injected bugs.
//! Each section contains mutant functions with injected bugs.
//! ALL functions in this file should be DISPROVEN (detecting the bugs).
//!
//! Mutation Operators:
//! - OBO: Off-by-one (< → <=, > → >=, +1 → +0, etc.)
//! - WCO: Wrong comparison operator (< → >, == → !=, etc.)
//! - ARO: Arithmetic operator (+ → -, * → /, etc.)
//! - RVO: Return value (return wrong value)
//!
//! Kill Rate Target: 100% (all mutants should be DISPROVEN)
//!
//! @expect: DISPROVEN

// =============================================================================
// SECTION 1: Arithmetic Mutations - Simple operations
// =============================================================================

/// MUTANT ARO-1: Wrong arithmetic operator (+ → -)
/// Contract says result == x + y, but we compute x - y
#[requires("x >= 0 && x <= 100")]
#[requires("y >= 0 && y <= 100")]
#[ensures("result == x + y")]
fn add_mutant_aro1(x: i32, y: i32) -> i32 {
    x - y  // BUG: - instead of +
}

/// MUTANT ARO-2: Wrong arithmetic operator (- → +)
/// Contract says result == x - y, but we compute x + y
#[requires("x >= 0 && x <= 100")]
#[requires("y >= 0 && y <= 100")]
#[ensures("result == x - y")]
fn sub_mutant_aro2(x: i32, y: i32) -> i32 {
    x + y  // BUG: + instead of -
}

/// MUTANT ARO-3: Wrong arithmetic operator (* → +)
/// Contract says result == x * y, but we compute x + y
#[requires("x >= 1 && x <= 10")]
#[requires("y >= 1 && y <= 10")]
#[ensures("result == x * y")]
fn mul_mutant_aro3(x: i32, y: i32) -> i32 {
    x + y  // BUG: + instead of *
}

// =============================================================================
// SECTION 2: Off-by-One Mutations - Classic bug pattern
// =============================================================================

/// MUTANT OBO-1: Off by plus one
/// Contract says result == x + 1, but we compute x + 2
#[requires("x >= 0 && x < 100")]
#[ensures("result == x + 1")]
fn increment_mutant_obo1(x: i32) -> i32 {
    x + 2  // BUG: +2 instead of +1
}

/// MUTANT OBO-2: Off by minus one
/// Contract says result == x + 1, but we return x
#[requires("x >= 0 && x < 100")]
#[ensures("result == x + 1")]
fn increment_mutant_obo2(x: i32) -> i32 {
    x  // BUG: forgot +1
}

/// MUTANT OBO-3: Off by one in subtraction
/// Contract says result == x - 1, but we compute x - 2
#[requires("x >= 2 && x <= 100")]
#[ensures("result == x - 1")]
fn decrement_mutant_obo3(x: i32) -> i32 {
    x - 2  // BUG: -2 instead of -1
}

/// MUTANT OBO-4: Off by one (decrement instead of nothing)
/// Contract says result == x, but we return x - 1
#[requires("x >= 1 && x <= 100")]
#[ensures("result == x")]
fn identity_mutant_obo4(x: i32) -> i32 {
    x - 1  // BUG: unexpected decrement
}

// =============================================================================
// SECTION 3: Constant Mutations - Wrong constant values
// =============================================================================

/// MUTANT RVO-1: Return wrong constant
/// Contract says result == 0, but we return 1
#[ensures("result == 0")]
fn zero_mutant_rvo1() -> i32 {
    1  // BUG: returns 1 instead of 0
}

/// MUTANT RVO-2: Return wrong constant
/// Contract says result == 42, but we return 41
#[ensures("result == 42")]
fn answer_mutant_rvo2() -> i32 {
    41  // BUG: returns 41 instead of 42
}

/// MUTANT RVO-3: Return wrong constant
/// Contract says result == 100, but we return -100
#[ensures("result == 100")]
fn hundred_mutant_rvo3() -> i32 {
    -100  // BUG: returns -100 instead of 100
}

// =============================================================================
// SECTION 4: Sign Mutations - Wrong sign handling
// =============================================================================

/// MUTANT ARO-4: Missing negation
/// Contract says result == -x, but we return x
#[requires("x >= -100 && x <= 100")]
#[ensures("result == 0 - x")]
fn negate_mutant_aro4(x: i32) -> i32 {
    x  // BUG: missing negation
}

/// MUTANT ARO-5: Double negation
/// Contract says result == -x, but --x = x
#[requires("x >= -100 && x <= 100")]
#[ensures("result == 0 - x")]
fn negate_mutant_aro5(x: i32) -> i32 {
    -(-x)  // BUG: double negation = identity
}

// =============================================================================
// SECTION 5: Bounds Violations - Breaking postcondition ranges
// =============================================================================

/// MUTANT BND-1: Violates lower bound
/// Contract says result >= 0, but we return -1
#[ensures("result >= 0")]
fn nonneg_mutant_bnd1() -> i32 {
    -1  // BUG: returns negative
}

/// MUTANT BND-2: Violates upper bound
/// Contract says result <= 100, but we return 101
#[ensures("result <= 100")]
fn bounded_mutant_bnd2() -> i32 {
    101  // BUG: exceeds upper bound
}

/// MUTANT BND-3: Violates both bounds
/// Contract says 0 <= result <= 10, but we return 20
#[ensures("result >= 0 && result <= 10")]
fn range_mutant_bnd3() -> i32 {
    20  // BUG: outside range
}

// =============================================================================
// SECTION 6: Equality Mutations - Wrong equality checks
// =============================================================================

/// MUTANT EQ-1: Wrong variable
/// Contract says result == x, but we return y
#[requires("x >= 0 && x <= 100")]
#[requires("y >= 0 && y <= 100")]
#[ensures("result == x")]
fn first_mutant_eq1(x: i32, y: i32) -> i32 {
    y  // BUG: returns y instead of x
}

/// MUTANT EQ-2: Wrong variable (swapped)
/// Contract says result == y, but we return x
#[requires("x >= 0 && x <= 100")]
#[requires("y >= 0 && y <= 100")]
#[ensures("result == y")]
fn second_mutant_eq2(x: i32, y: i32) -> i32 {
    x  // BUG: returns x instead of y
}

// =============================================================================
// SECTION 7: Commutative Operation with Non-Commutative Contract
// =============================================================================

/// MUTANT COM-1: Order matters for subtraction
/// Contract says result == a - b, but we compute b - a
#[requires("a >= 0 && a <= 100")]
#[requires("b >= 0 && b <= 100")]
#[ensures("result == a - b")]
fn subtract_mutant_com1(a: i32, b: i32) -> i32 {
    b - a  // BUG: reversed operands
}

// =============================================================================
// SECTION 8: Compound Expression Mutations
// =============================================================================

/// MUTANT CPD-1: Wrong factor in multiplication
/// Contract says result == 2 * x, but we compute 3 * x
#[requires("x >= 0 && x <= 50")]
#[ensures("result == 2 * x")]
fn double_mutant_cpd1(x: i32) -> i32 {
    3 * x  // BUG: 3 instead of 2
}

/// MUTANT CPD-2: Missing operation in compound
/// Contract says result == x + y + z, but we compute x + y
#[requires("x >= 0 && x <= 30")]
#[requires("y >= 0 && y <= 30")]
#[requires("z >= 0 && z <= 30")]
#[ensures("result == x + y + z")]
fn sum_three_mutant_cpd2(x: i32, y: i32, z: i32) -> i32 {
    x + y  // BUG: missing + z
}

/// MUTANT CPD-3: Extra operation
/// Contract says result == x + y, but we compute x + y + 1
#[requires("x >= 0 && x <= 100")]
#[requires("y >= 0 && y <= 100")]
#[ensures("result == x + y")]
fn sum_two_mutant_cpd3(x: i32, y: i32) -> i32 {
    x + y + 1  // BUG: extra + 1
}

fn main() {
    // This test file contains ONLY mutants (buggy code)
    // ALL functions should be DISPROVEN by tRust
    // A successful mutation test means tRust detects ALL bugs
    println!("Mutation testing: all {} mutants should be DISPROVEN", 20);
}
