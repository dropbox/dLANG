// Test Option/Result constructor tracking (Phase 10.1)
//
// When Option or Result types are constructed, this sets the is_some/is_ok
// and value variables so postconditions can reason about them.
//
// Option<T> constructor tracking:
//   Some(x) sets: _X_is_some = true, _X_value = x
//   None sets: _X_is_some = false
//
// Result<T,E> constructor tracking:
//   Ok(x) sets: _X_is_ok = true, _X_ok_value = x
//   Err(e) sets: _X_is_ok = false, _X_err_value = e
//
// WORKING PATTERNS:
// - Direct return of Option/Result (Some(x), None, Ok(x), Err(e))
// - Postconditions using result.is_some(), result.is_none(), result.is_ok(), result.is_err()
// - Postconditions using result.unwrap() on the return value
// - Conditional Option/Result construction (if/else returning different variants)
//
// LIMITATIONS (future work):
// - Method calls like unwrap_or() don't propagate tracking to return value
// - Local variable method calls (opt.unwrap_or()) vs direct returns
//
// Conversion methods (.ok(), .err(), .ok_or()) are NOW TRACKED - see conversion_methods_test.rs

// === Option Constructor Tests (VERIFIED) ===

// Test: Some(x) sets is_some=true and value=x
// The postcondition result.is_some() should be true after Some construction
#[ensures("result.is_some()")]
fn create_some() -> Option<i32> {
    Some(42)
}

// Test: Some(x) - verify the value is captured
// The postcondition should verify the wrapped value
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 100")]
fn create_some_with_value() -> Option<i32> {
    Some(100)
}

// Test: None sets is_some=false
// The postcondition result.is_none() should be true after None construction
#[ensures("result.is_none()")]
fn create_none() -> Option<i32> {
    None
}

// Test: Conditional Option construction preserves tracking
#[requires("condition || !condition")]  // Always true, just for having a spec
#[ensures("condition ==> result.is_some()")]
#[ensures("!condition ==> result.is_none()")]
fn conditional_option(condition: bool) -> Option<i32> {
    if condition {
        Some(10)
    } else {
        None
    }
}

// Test: nested Some construction - value flows through assignment
#[ensures("result.is_some()")]
fn nested_some(x: i32) -> Option<i32> {
    let inner = Some(x);
    inner
}

// Test: Some with arithmetic expression
#[requires("x >= 0 && x <= 100")]
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == x * 2")]
fn some_with_expression(x: i32) -> Option<i32> {
    Some(x * 2)
}

// === Result Constructor Tests (VERIFIED) ===

// Test: Ok(x) sets is_ok=true and ok_value=x
#[ensures("result.is_ok()")]
fn create_ok() -> Result<i32, i32> {
    Ok(42)
}

// Test: Ok(x) - verify the value is captured
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == 200")]
fn create_ok_with_value() -> Result<i32, i32> {
    Ok(200)
}

// Test: Err(e) sets is_ok=false
#[ensures("result.is_err()")]
fn create_err() -> Result<i32, i32> {
    Err(500)
}

// Test: Err(e) - verify the error value is captured
#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == 404")]
fn create_err_with_value() -> Result<i32, i32> {
    Err(404)
}

// Test: Conditional Result construction preserves tracking
#[requires("condition || !condition")]  // Always true
#[ensures("condition ==> result.is_ok()")]
#[ensures("!condition ==> result.is_err()")]
fn conditional_result(condition: bool) -> Result<i32, i32> {
    if condition {
        Ok(10)
    } else {
        Err(-1)
    }
}

// Test: Ok with arithmetic expression
#[requires("x >= 0 && x <= 50")]
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == x + 1")]
fn ok_with_expression(x: i32) -> Result<i32, i32> {
    Ok(x + 1)
}

// === Tests showing current limitations (EXPECTED DISPROVEN) ===
// These demonstrate what's not yet working - method call return tracking

// NOTE: This is expected to be DISPROVEN because unwrap_or() as a method call
// doesn't propagate the Option tracking to the integer return value
// #[ensures("result == 42")]
// fn test_unwrap_or_limitation() -> i32 {
//     let opt = Some(42);
//     opt.unwrap_or(0)
// }

// === Helper function without specs (for runtime verification) ===

fn result_to_option() -> Option<i32> {
    let r: Result<i32, i32> = Ok(50);
    r.ok()
}

fn main() {
    // Runtime verification - Option tests
    assert!(create_some().is_some());
    assert_eq!(create_some_with_value(), Some(100));
    assert!(create_none().is_none());
    assert!(conditional_option(true).is_some());
    assert!(conditional_option(false).is_none());
    assert!(nested_some(5).is_some());
    assert_eq!(some_with_expression(10), Some(20));

    // Runtime verification - Result tests
    assert!(create_ok().is_ok());
    assert_eq!(create_ok_with_value(), Ok(200));
    assert!(create_err().is_err());
    assert_eq!(create_err_with_value(), Err(404));
    assert!(conditional_result(true).is_ok());
    assert!(conditional_result(false).is_err());
    assert_eq!(ok_with_expression(5), Ok(6));

    // Conversion test (no spec verification)
    assert!(result_to_option().is_some());

    println!("All constructor tracking tests passed!");
}
