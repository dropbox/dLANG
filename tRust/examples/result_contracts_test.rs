// Test Result<T, E> modeling for contracts (Phase 10.1)
// Result is modeled as (is_ok: bool, value: T, err_value: E) where:
//   result.is_ok()      -> result_is_ok
//   result.is_err()     -> (not result_is_ok)
//   result.unwrap()     -> result_value (same as Option for consistency)
//   result.unwrap_err() -> result_err_value
//
// This tests Result constructor tracking where:
// - Ok(x) sets _is_ok = true and _value = x
// - Err(e) sets _is_ok = false and _err_value = e
//
// ALL TESTS SHOULD BE VERIFIED now that constructor tracking is implemented.

// Helper type for our tests - representing possible errors
// (In real code this would be a proper error type)
type ParseError = i32;

// Test basic Result creation and method parsing
// This function returns Ok(x) when x >= 0, Err(-1) when x < 0
// Postcondition: result.is_ok() means the value is valid
// VERIFIED: Constructor tracking and CHC solver prove the condition
#[ensures("result.is_ok() == (x >= 0)")]
fn validate_positive(x: i32) -> Result<i32, ParseError> {
    if x >= 0 {
        Ok(x)
    } else {
        Err(-1)
    }
}

// Test that unwrap() on Result gives the wrapped value
// Postcondition uses result.unwrap() which maps to result_value
// VERIFIED: Constructor tracking connects Ok(x) to _is_ok = true and _value = x
#[requires("x >= 0")]
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == x")]
fn wrap_positive(x: i32) -> Result<i32, ParseError> {
    Ok(x)
}

// Test is_err() method - modeled as (not result_is_ok)
// This function always returns Err with the error code
// VERIFIED: Constructor tracking connects Err(code) to _is_ok = false, _err_value = code
#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == code")]
fn make_error(code: ParseError) -> Result<i32, ParseError> {
    Err(code)
}

// Test Result in modular verification context
// When we call validate_positive and get Ok, we can use the value
fn use_validated(x: i32) -> i32 {
    let result = validate_positive(x);
    if result.is_ok() {
        // We know x >= 0 from the postcondition of validate_positive
        result.unwrap()
    } else {
        0
    }
}

// Test Result with both branches handled
// Demonstrates that is_ok() and is_err() are opposites
fn result_to_option(result: Result<i32, ParseError>) -> Option<i32> {
    if result.is_ok() {
        Some(result.unwrap())
    } else {
        None
    }
}

// Test using Result postcondition from another function
// This demonstrates modular verification with Result types
// VERIFIED: Uses modular verification - wrap_positive has result.is_ok() postcondition
#[requires("n >= 1")]
#[ensures("result.is_ok()")]
fn double_positive(n: i32) -> Result<i32, ParseError> {
    // n >= 1 implies 2*n >= 2, which is valid
    let validated = wrap_positive(n);
    // wrap_positive postcondition: result.is_ok() when n >= 0
    // Since n >= 1, this should always be Ok
    validated
}

// Test combined Ok value extraction
// When we know result is Ok, we can reason about the unwrapped value
// VERIFIED: CHC solver synthesizes invariant for the conditional
#[requires("a >= 0 && a <= 1000000")]
#[requires("b >= 0 && b <= 1000000")]
#[ensures("result.is_ok()")]
fn combine_results(a: i32, b: i32) -> Result<i32, ParseError> {
    let ra = wrap_positive(a);
    let rb = wrap_positive(b);

    // Both are Ok since a >= 0 and b >= 0
    // Use checked_add to avoid overflow detection
    if ra.is_ok() && rb.is_ok() {
        match ra.unwrap().checked_add(rb.unwrap()) {
            Some(sum) => Ok(sum),
            None => Err(-3), // overflow case
        }
    } else {
        Err(-2)
    }
}

// Test that Err branch gives access to error value
// Demonstrates unwrap_err() method parsing
// VERIFIED: make_error postcondition works with constructor tracking
#[ensures("result.is_err()")]
fn propagate_error(code: ParseError) -> Result<i32, ParseError> {
    let err_result = make_error(code);
    // err_result.is_err() is true from postcondition
    // We can access the error via unwrap_err()
    Err(err_result.unwrap_err())
}

fn main() {
    // Runtime tests (not verified, just sanity checks)

    // Test validate_positive
    assert!(validate_positive(5).is_ok());
    assert!(validate_positive(0).is_ok());
    assert!(validate_positive(-1).is_err());

    // Test wrap_positive
    let r = wrap_positive(10);
    assert!(r.is_ok());
    assert_eq!(r.unwrap(), 10);

    // Test make_error
    let e = make_error(42);
    assert!(e.is_err());
    assert_eq!(e.unwrap_err(), 42);

    // Test use_validated
    assert_eq!(use_validated(5), 5);
    assert_eq!(use_validated(-1), 0);

    // Test double_positive
    assert!(double_positive(1).is_ok());

    // Test combine_results
    assert!(combine_results(10, 20).is_ok());

    // Test propagate_error
    assert!(propagate_error(99).is_err());

    println!("All Result contract tests passed!");
}
