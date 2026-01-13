// Float Encoding Test
//
// STATUS: SHOULD_VERIFY
//
// Purpose:
// - Ensure float literals in function bodies survive the MIR-to-CHC conversion layer
//   (upstream/rustc/compiler/rustc_verify/src/kani_bridge.rs const_to_smt()).
//
// This test intentionally avoids strict float equality for non-trivial arithmetic
// and instead uses a tight range around the expected value.

#[ensures("result == 0.0")]
fn return_zero() -> f64 {
    0.0
}

// If float constants are extracted incorrectly (e.g. to 0), this becomes DISPROVEN.
#[ensures("result > 0.299 && result < 0.301")]
fn add_floats() -> f64 {
    0.1 + 0.2
}

// Integer control: this should VERIFY (integers are exact)
#[ensures("result == 42")]
fn return_int() -> i32 {
    42
}

fn main() {}
