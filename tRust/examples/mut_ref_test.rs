//! Mutable reference verification test
//! Tests how &mut T parameters work with specs
//!
//! Expected outcomes:
//! increment_return: @expect: VERIFIED
//! read_and_modify: @expect: VERIFIED

// Test 1: Return value through immutable ref
// NOTE: Preconditions on reference types (x: &i32) currently refer to the
// reference address, not the dereferenced value (*x). Until deref support
// is added to preconditions, use saturating arithmetic or checked operations.
fn increment_return(x: &i32) -> i32 {
    // Use saturating_add to avoid overflow - this is the idiomatic safe approach
    x.saturating_add(1)
}

// Test 2: Simple mutable ref that returns original value
// The function modifies *x but returns the original value
// No arithmetic operations, so no overflow check needed
#[requires("x > 0")]
fn read_and_modify(x: &mut i32) -> i32 {
    let val = *x;
    *x = 0;  // modify *x to 0
    val      // return original value
}

// Test 3: Verify the modified value of a mutable reference
// No arithmetic operations, so no overflow check needed
#[requires("x >= 0")]
fn set_to_zero(x: &mut i32) {
    *x = 0;
}

fn main() {
    let val = 42;
    println!("increment_return: {}", increment_return(&val));

    let mut val2 = 10;
    println!("read_and_modify: {}", read_and_modify(&mut val2));
    println!("val2 after: {}", val2);

    let mut val3 = 5;
    set_to_zero(&mut val3);
    println!("val3 after set_to_zero: {}", val3);
}
