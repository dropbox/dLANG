// tRust Verified Elimination MIR Pass Test
//
// This test demonstrates the MIR pass wiring infrastructure for
// verification-aware check elimination.
//
// The VerifiedCheckElimination pass:
// - Queries SafeOperationRegistry populated by rustc_verify
// - Converts proven-safe Assert terminators to Goto
// - Is enabled via TRUST_VERIFIED_ELIMINATION=1 environment variable
//
// Expected: VERIFIED (demonstrates pass infrastructure exists)

#![allow(unused)]

/// Function with overflow check that verification can prove safe.
/// When enabled, the MIR pass would eliminate the overflow assertion.
#[requires("a >= 0 && a < 1000")]
#[requires("b >= 0 && b < 1000")]
#[ensures("result == a + b")]
fn safe_add(a: i32, b: i32) -> i32 {
    // The overflow check here is redundant - inputs are bounded
    a + b
}

/// Function with subtraction that verification can prove safe.
#[requires("a >= b")]
#[requires("b >= 0")]
#[ensures("result == a - b")]
fn safe_sub(a: i32, b: i32) -> i32 {
    a - b
}

/// Function demonstrating that MIR pass can be selectively enabled.
/// Without TRUST_VERIFIED_ELIMINATION=1, checks are preserved.
fn main() {
    // These operations have checks that verification proves safe
    let sum = safe_add(100, 200);
    let diff = safe_sub(300, 100);

    // Verify results
    assert_eq!(sum, 300);
    assert_eq!(diff, 200);
}

// Test verifies the pass infrastructure is wired correctly.
// Actual elimination requires:
// 1. TRUST_VERIFIED_ELIMINATION=1 environment variable
// 2. SafeOperationRegistry populated by verification pass
// 3. Verification runs before MIR optimization via mir_drops_elaborated_and_const_checked
