// Test additional Option/Result methods (Phase 10.1)
//
// This test verifies the additional methods added:
//   - Option: unwrap_or_else, unwrap_or_default, xor, expect, zip
//   - Result: unwrap_or_else, unwrap_or_default, expect, expect_err
//
// === EXPECTED RESULTS: All VERIFIED ===

// ============================================================================
// Option::unwrap_or_else - returns value if Some, calls closure if None
// ============================================================================

// Test: Some(x).unwrap_or_else(f) returns x
#[requires("x >= 0 && x <= 100")]
#[ensures("result == x")]
fn option_unwrap_or_else_some(x: i32) -> i32 {
    let opt: Option<i32> = Some(x);
    opt.unwrap_or_else(|| 999)
}

// ============================================================================
// Option::unwrap_or_default - returns value if Some, default if None
// ============================================================================

// Test: Some(x).unwrap_or_default() returns x
#[requires("x >= 0 && x <= 100")]
#[ensures("result == x")]
fn option_unwrap_or_default_some(x: i32) -> i32 {
    let opt: Option<i32> = Some(x);
    opt.unwrap_or_default()
}

// ============================================================================
// Option::xor - returns Some if exactly one is Some
// ============================================================================

// Test: Some(x).xor(None) returns Some(x)
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 42")]
fn option_xor_first_some() -> Option<i32> {
    let opt1: Option<i32> = Some(42);
    let opt2: Option<i32> = None;
    opt1.xor(opt2)
}

// Test: None.xor(Some(y)) returns Some(y)
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 100")]
fn option_xor_second_some() -> Option<i32> {
    let opt1: Option<i32> = None;
    let opt2: Option<i32> = Some(100);
    opt1.xor(opt2)
}

// Test: Some(x).xor(Some(y)) returns None
#[ensures("result.is_none()")]
fn option_xor_both_some() -> Option<i32> {
    let opt1: Option<i32> = Some(42);
    let opt2: Option<i32> = Some(100);
    opt1.xor(opt2)
}

// Test: None.xor(None) returns None
#[ensures("result.is_none()")]
fn option_xor_both_none() -> Option<i32> {
    let opt1: Option<i32> = None;
    let opt2: Option<i32> = None;
    opt1.xor(opt2)
}

// ============================================================================
// Option::expect - returns value if Some (panics with message if None)
// ============================================================================

// Test: Some(x).expect(msg) returns x
#[requires("x >= 0 && x <= 100")]
#[ensures("result == x")]
fn option_expect_some(x: i32) -> i32 {
    let opt: Option<i32> = Some(x);
    opt.expect("value should be Some")
}

// ============================================================================
// Option::zip - combines two Options into Option<(T, U)>
// ============================================================================

// Test: Some(x).zip(Some(y)) is Some
#[ensures("result.is_some()")]
fn option_zip_both_some() -> Option<(i32, i32)> {
    let opt1: Option<i32> = Some(42);
    let opt2: Option<i32> = Some(100);
    opt1.zip(opt2)
}

// Test: Some(x).zip(None) is None
#[ensures("result.is_none()")]
fn option_zip_second_none() -> Option<(i32, i32)> {
    let opt1: Option<i32> = Some(42);
    let opt2: Option<i32> = None;
    opt1.zip(opt2)
}

// Test: None.zip(Some(y)) is None
#[ensures("result.is_none()")]
fn option_zip_first_none() -> Option<(i32, i32)> {
    let opt1: Option<i32> = None;
    let opt2: Option<i32> = Some(100);
    opt1.zip(opt2)
}

// Test: None.zip(None) is None
#[ensures("result.is_none()")]
fn option_zip_both_none() -> Option<(i32, i32)> {
    let opt1: Option<i32> = None;
    let opt2: Option<i32> = None;
    opt1.zip(opt2)
}

// ============================================================================
// Result::unwrap_or_else - returns Ok value if Ok, calls closure if Err
// ============================================================================

// Test: Ok(x).unwrap_or_else(f) returns x
#[requires("x >= 0 && x <= 100")]
#[ensures("result == x")]
fn result_unwrap_or_else_ok(x: i32) -> i32 {
    let res: Result<i32, i32> = Ok(x);
    res.unwrap_or_else(|_e| 999)
}

// ============================================================================
// Result::unwrap_or_default - returns Ok value if Ok, default if Err
// ============================================================================

// Test: Ok(x).unwrap_or_default() returns x
#[requires("x >= 0 && x <= 100")]
#[ensures("result == x")]
fn result_unwrap_or_default_ok(x: i32) -> i32 {
    let res: Result<i32, i32> = Ok(x);
    res.unwrap_or_default()
}

// ============================================================================
// Result::expect - returns Ok value if Ok (panics with message if Err)
// ============================================================================

// Test: Ok(x).expect(msg) returns x
#[requires("x >= 0 && x <= 100")]
#[ensures("result == x")]
fn result_expect_ok(x: i32) -> i32 {
    let res: Result<i32, i32> = Ok(x);
    res.expect("result should be Ok")
}

// ============================================================================
// Result::expect_err - returns Err value if Err (panics with message if Ok)
// ============================================================================

// Test: Err(e).expect_err(msg) returns e
#[requires("e >= 400 && e <= 599")]
#[ensures("result == e")]
fn result_expect_err_err(e: i32) -> i32 {
    let res: Result<i32, i32> = Err(e);
    res.expect_err("result should be Err")
}

fn main() {
    // Runtime verification - Option::unwrap_or_else
    assert_eq!(option_unwrap_or_else_some(42), 42);

    // Runtime verification - Option::unwrap_or_default
    assert_eq!(option_unwrap_or_default_some(42), 42);

    // Runtime verification - Option::xor
    assert_eq!(option_xor_first_some(), Some(42));
    assert_eq!(option_xor_second_some(), Some(100));
    assert_eq!(option_xor_both_some(), None);
    assert_eq!(option_xor_both_none(), None);

    // Runtime verification - Option::expect
    assert_eq!(option_expect_some(42), 42);

    // Runtime verification - Option::zip
    assert_eq!(option_zip_both_some(), Some((42, 100)));
    assert_eq!(option_zip_second_none(), None);
    assert_eq!(option_zip_first_none(), None);
    assert_eq!(option_zip_both_none(), None);

    // Runtime verification - Result::unwrap_or_else
    assert_eq!(result_unwrap_or_else_ok(42), 42);

    // Runtime verification - Result::unwrap_or_default
    assert_eq!(result_unwrap_or_default_ok(42), 42);

    // Runtime verification - Result::expect
    assert_eq!(result_expect_ok(42), 42);

    // Runtime verification - Result::expect_err
    assert_eq!(result_expect_err_err(404), 404);

    println!("All additional Option/Result methods tests passed!");
}
