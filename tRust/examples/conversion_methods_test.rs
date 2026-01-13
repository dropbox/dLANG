// Test Result/Option conversion methods (Phase 10.1)
//
// This test verifies that the SMT solver correctly models:
//   - Result::ok() - converts Result<T, E> to Option<T>
//   - Result::err() - converts Result<T, E> to Option<E>
//   - Option::ok_or() - converts Option<T> to Result<T, E>
//
// These methods enable seamless conversion between Option and Result types
// while preserving verification semantics.
//
// === EXPECTED RESULTS: All VERIFIED ===

// ============================================================================
// Result::ok() - Convert Result<T, E> to Option<T>
// Returns Some(value) if Ok, None if Err
// ============================================================================

// Test: Ok(x).ok() produces Some(x)
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 42")]
fn ok_to_option_some() -> Option<i32> {
    let r: Result<i32, i32> = Ok(42);
    r.ok()
}

// Test: Err(e).ok() produces None
#[ensures("result.is_none()")]
fn err_to_option_none() -> Option<i32> {
    let r: Result<i32, i32> = Err(500);
    r.ok()
}

// Test: Conditional result.ok() preserves variant tracking
#[requires("condition || !condition")]
#[ensures("condition ==> result.is_some()")]
#[ensures("!condition ==> result.is_none()")]
fn conditional_ok_conversion(condition: bool) -> Option<i32> {
    let r: Result<i32, i32> = if condition { Ok(10) } else { Err(-1) };
    r.ok()
}

// Test: Ok value flows through to Option value
#[requires("x >= 0 && x <= 100")]
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == x")]
fn ok_value_to_option(x: i32) -> Option<i32> {
    let r: Result<i32, i32> = Ok(x);
    r.ok()
}

// ============================================================================
// Result::err() - Convert Result<T, E> to Option<E>
// Returns Some(err_value) if Err, None if Ok
// ============================================================================

// Test: Err(e).err() produces Some(e)
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 404")]
fn err_to_option_some() -> Option<i32> {
    let r: Result<i32, i32> = Err(404);
    r.err()
}

// Test: Ok(x).err() produces None
#[ensures("result.is_none()")]
fn ok_to_option_none() -> Option<i32> {
    let r: Result<i32, i32> = Ok(42);
    r.err()
}

// Test: Conditional result.err() preserves variant tracking
#[requires("condition || !condition")]
#[ensures("condition ==> result.is_none()")]  // Ok -> err() gives None
#[ensures("!condition ==> result.is_some()")]  // Err -> err() gives Some
fn conditional_err_conversion(condition: bool) -> Option<i32> {
    let r: Result<i32, i32> = if condition { Ok(10) } else { Err(-1) };
    r.err()
}

// Test: Err value flows through to Option value
#[requires("e >= 400 && e <= 599")]
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == e")]
fn err_value_to_option(e: i32) -> Option<i32> {
    let r: Result<i32, i32> = Err(e);
    r.err()
}

// ============================================================================
// Option::ok_or() - Convert Option<T> to Result<T, E>
// Returns Ok(value) if Some, Err(err) if None
// ============================================================================

// Test: Some(x).ok_or(err) produces Ok(x)
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == 42")]
fn some_to_result_ok() -> Result<i32, i32> {
    let opt: Option<i32> = Some(42);
    opt.ok_or(0)
}

// Test: None.ok_or(err) produces Err(err)
#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == 999")]
fn none_to_result_err() -> Result<i32, i32> {
    let opt: Option<i32> = None;
    opt.ok_or(999)
}

// Test: Conditional option.ok_or() preserves variant tracking
#[requires("condition || !condition")]
#[ensures("condition ==> result.is_ok()")]
#[ensures("!condition ==> result.is_err()")]
fn conditional_ok_or_conversion(condition: bool) -> Result<i32, i32> {
    let opt: Option<i32> = if condition { Some(10) } else { None };
    opt.ok_or(-1)
}

// Test: Some value flows through to Result value
#[requires("x >= 0 && x <= 100")]
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == x")]
fn some_value_to_result(x: i32) -> Result<i32, i32> {
    let opt: Option<i32> = Some(x);
    opt.ok_or(0)
}

// Test: Error value flows through when None
#[requires("err_code >= 400 && err_code <= 599")]
#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == err_code")]
fn none_value_to_result(err_code: i32) -> Result<i32, i32> {
    let opt: Option<i32> = None;
    opt.ok_or(err_code)
}

// ============================================================================
// Chained conversions
// ============================================================================

// Test: Ok -> ok() -> ok_or() round trip preserves value
#[requires("x >= 0 && x <= 50")]
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == x")]
fn ok_to_option_to_result(x: i32) -> Result<i32, i32> {
    let r: Result<i32, i32> = Ok(x);
    let opt = r.ok();
    opt.ok_or(0)
}

// Test: Some -> ok_or() -> ok() round trip preserves value
#[requires("x >= 0 && x <= 50")]
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == x")]
fn some_to_result_to_option(x: i32) -> Option<i32> {
    let opt: Option<i32> = Some(x);
    let r = opt.ok_or(0);
    r.ok()
}

fn main() {
    // Runtime verification - Result::ok()
    assert_eq!(ok_to_option_some(), Some(42));
    assert_eq!(err_to_option_none(), None);
    assert!(conditional_ok_conversion(true).is_some());
    assert!(conditional_ok_conversion(false).is_none());
    assert_eq!(ok_value_to_option(50), Some(50));

    // Runtime verification - Result::err()
    assert_eq!(err_to_option_some(), Some(404));
    assert_eq!(ok_to_option_none(), None);
    assert!(conditional_err_conversion(true).is_none());
    assert!(conditional_err_conversion(false).is_some());
    assert_eq!(err_value_to_option(500), Some(500));

    // Runtime verification - Option::ok_or()
    assert_eq!(some_to_result_ok(), Ok(42));
    assert_eq!(none_to_result_err(), Err(999));
    assert!(conditional_ok_or_conversion(true).is_ok());
    assert!(conditional_ok_or_conversion(false).is_err());
    assert_eq!(some_value_to_result(50), Ok(50));
    assert_eq!(none_value_to_result(404), Err(404));

    // Runtime verification - Chained conversions
    assert_eq!(ok_to_option_to_result(25), Ok(25));
    assert_eq!(some_to_result_to_option(25), Some(25));

    println!("All conversion methods tests passed!");
}
