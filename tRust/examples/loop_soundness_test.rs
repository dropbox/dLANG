// Loop Soundness Test
//
// STATUS: EXPECTED_DISPROVEN - tests for soundness bugs in loop handling
//
// CRITICAL SOUNDNESS BUG:
// The CHC solver claims "PROVEN (invariant synthesized)" for loops with
// WRONG postconditions. This is UNSOUND and dangerous.
//
// Example: #[ensures("result == 100")] fn f() { sum 0..10 } returns 45
// The verifier says VERIFIED when it should say DISPROVEN.
//
// ROOT CAUSE: Loop invariant synthesis is accepting trivially true
// invariants (like `true`) that don't actually prove the postcondition.
// The CHC solver may be returning SAT for an incorrect encoding.
//
// FIX OPTIONS:
// 1. Require explicit #[invariant] annotation for all loops
// 2. Use havoc semantics for loops without invariants (default to UNKNOWN)
// 3. Fix CHC solver to properly verify postcondition follows from invariant
//
// See: docs/design/NUCLEAR_GRADE_ROADMAP.md Phase N1.3
//
// NOTE: This test is EXPECTED to DISPROVE due to this bug being documented.
// If this test VERIFIES, the soundness bug is present and MUST be fixed.

// This MUST DISPROVE: sum of 0..10 is 45, not 100
// Currently UNSOUNDLY VERIFIES due to CHC solver bug
#[ensures("result == 100")]
fn sum_wrong() -> i32 {
    let mut sum = 0;
    for i in 0..10 {
        sum += i;
    }
    sum  // Returns 45, not 100!
}

// This MUST DISPROVE: loop result is 5, not 999
// Currently UNSOUNDLY VERIFIES due to CHC solver bug
#[ensures("result == 999")]
fn loop_wrong() -> i32 {
    let mut x = 0;
    for _ in 0..5 {
        x += 1;
    }
    x  // Returns 5, not 999!
}

// Control: this SHOULD verify (correct spec)
#[ensures("result == 42")]
fn simple_correct() -> i32 {
    42
}

fn main() {}
