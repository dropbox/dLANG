// Test Option/Result combinator methods (Phase 10.1)
//
// This test verifies structural properties of combinator methods:
//   - map() preserves Some/Ok status
//   - and_then() propagates None/Err
//   - or_else() preserves Some/Ok with value
//   - or() combines two Options/Results
//   - filter() preserves None and value
//   - map_err() preserves Ok with value
//
// Note: Closures are not analyzed statically. These tests verify the
// structural postconditions that hold regardless of closure behavior.
//
// === EXPECTED RESULTS: All VERIFIED ===

// ============================================================================
// Option::map - preserves is_some status
// ============================================================================

// Test: Some(x).map(f) is Some (value depends on closure)
#[ensures("result.is_some()")]
fn option_map_some_preserves() -> Option<i32> {
    let opt: Option<i32> = Some(42);
    opt.map(|x| x * 2)
}

// Test: None.map(f) is None
#[ensures("result.is_none()")]
fn option_map_none_stays_none() -> Option<i32> {
    let opt: Option<i32> = None;
    opt.map(|x| x * 2)
}

// Test: Conditional - map preserves Some/None status
#[requires("condition || !condition")]
#[ensures("condition ==> result.is_some()")]
#[ensures("!condition ==> result.is_none()")]
fn option_map_conditional(condition: bool) -> Option<i32> {
    let opt: Option<i32> = if condition { Some(10) } else { None };
    opt.map(|x| x + 1)
}

// ============================================================================
// Option::and_then - None propagates, Some depends on closure
// ============================================================================

// Test: None.and_then(f) is None regardless of closure
#[ensures("result.is_none()")]
fn option_and_then_none_propagates() -> Option<i32> {
    let opt: Option<i32> = None;
    opt.and_then(|x| Some(x * 2))
}

// Test: Conditional - and_then propagates None
#[requires("!condition")]
#[ensures("result.is_none()")]
fn option_and_then_none_conditional(condition: bool) -> Option<i32> {
    let opt: Option<i32> = if condition { Some(10) } else { None };
    opt.and_then(|x| Some(x + 1))
}

// ============================================================================
// Option::or_else - Some preserves value, None depends on closure
// ============================================================================

// Test: Some(x).or_else(f) is Some(x) regardless of closure
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 42")]
fn option_or_else_some_preserves() -> Option<i32> {
    let opt: Option<i32> = Some(42);
    opt.or_else(|| Some(100))
}

// Test: Conditional - or_else preserves Some with value
#[requires("condition")]
#[requires("x >= 0 && x <= 100")]
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == x")]
fn option_or_else_some_conditional(condition: bool, x: i32) -> Option<i32> {
    let opt: Option<i32> = if condition { Some(x) } else { None };
    opt.or_else(|| Some(999))
}

// ============================================================================
// Option::or - combines two Options
// ============================================================================

// Test: Some(x).or(other) returns Some(x)
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 42")]
fn option_or_some_first() -> Option<i32> {
    let opt1: Option<i32> = Some(42);
    let opt2: Option<i32> = Some(100);
    opt1.or(opt2)
}

// Test: None.or(Some(y)) returns Some(y)
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 100")]
fn option_or_none_first() -> Option<i32> {
    let opt1: Option<i32> = None;
    let opt2: Option<i32> = Some(100);
    opt1.or(opt2)
}

// Test: None.or(None) returns None
#[ensures("result.is_none()")]
fn option_or_both_none() -> Option<i32> {
    let opt1: Option<i32> = None;
    let opt2: Option<i32> = None;
    opt1.or(opt2)
}

// ============================================================================
// Option::filter - preserves None, filters Some
// ============================================================================

// Test: None.filter(p) is None
#[ensures("result.is_none()")]
fn option_filter_none_stays_none() -> Option<i32> {
    let opt: Option<i32> = None;
    opt.filter(|&x| x > 0)
}

// Test: filter preserves value when keeping Some
#[ensures("result.is_none() || result.unwrap() == 42")]
fn option_filter_preserves_value() -> Option<i32> {
    let opt: Option<i32> = Some(42);
    opt.filter(|&x| x > 0)
}

// ============================================================================
// Result::map - preserves is_ok status, error unchanged
// ============================================================================

// Test: Ok(x).map(f) is Ok (value depends on closure)
#[ensures("result.is_ok()")]
fn result_map_ok_preserves() -> Result<i32, i32> {
    let res: Result<i32, i32> = Ok(42);
    res.map(|x| x * 2)
}

// Test: Err(e).map(f) is Err with same error
#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == 500")]
fn result_map_err_unchanged() -> Result<i32, i32> {
    let res: Result<i32, i32> = Err(500);
    res.map(|x| x * 2)
}

// Test: Conditional - map preserves Ok/Err status
#[requires("condition || !condition")]
#[ensures("condition ==> result.is_ok()")]
#[ensures("!condition ==> result.is_err()")]
fn result_map_conditional(condition: bool) -> Result<i32, i32> {
    let res: Result<i32, i32> = if condition { Ok(10) } else { Err(500) };
    res.map(|x| x + 1)
}

// ============================================================================
// Result::map_err - preserves is_ok status, ok value unchanged
// ============================================================================

// Test: Ok(x).map_err(f) is Ok with same value
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == 42")]
fn result_map_err_ok_unchanged() -> Result<i32, i32> {
    let res: Result<i32, i32> = Ok(42);
    res.map_err(|e| e * 2)
}

// Test: Err(e).map_err(f) is Err (value depends on closure)
#[ensures("result.is_err()")]
fn result_map_err_err_preserves() -> Result<i32, i32> {
    let res: Result<i32, i32> = Err(500);
    res.map_err(|e| e + 1)
}

// ============================================================================
// Result::and_then - Err propagates with same error
// ============================================================================

// Test: Err(e).and_then(f) is Err(e) regardless of closure
#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == 500")]
fn result_and_then_err_propagates() -> Result<i32, i32> {
    let res: Result<i32, i32> = Err(500);
    res.and_then(|x| Ok(x * 2))
}

// Test: Conditional - and_then propagates Err with value
#[requires("!condition")]
#[requires("err_code >= 400 && err_code <= 599")]
#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == err_code")]
fn result_and_then_err_conditional(condition: bool, err_code: i32) -> Result<i32, i32> {
    let res: Result<i32, i32> = if condition { Ok(10) } else { Err(err_code) };
    res.and_then(|x| Ok(x + 1))
}

// ============================================================================
// Result::or_else - Ok preserves value
// ============================================================================

// Test: Ok(x).or_else(f) is Ok(x) regardless of closure
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == 42")]
fn result_or_else_ok_preserves() -> Result<i32, i32> {
    let res: Result<i32, i32> = Ok(42);
    res.or_else(|_e| Ok(100))
}

// Test: Conditional - or_else preserves Ok with value
#[requires("condition")]
#[requires("x >= 0 && x <= 100")]
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == x")]
fn result_or_else_ok_conditional(condition: bool, x: i32) -> Result<i32, i32> {
    let res: Result<i32, i32> = if condition { Ok(x) } else { Err(500) };
    res.or_else(|_e| Ok(999))
}

// ============================================================================
// Result::or - combines two Results
// ============================================================================

// Test: Ok(x).or(other) returns Ok(x)
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == 42")]
fn result_or_ok_first() -> Result<i32, i32> {
    let res1: Result<i32, i32> = Ok(42);
    let res2: Result<i32, i32> = Ok(100);
    res1.or(res2)
}

// Test: Err(e).or(Ok(y)) returns Ok(y)
#[ensures("result.is_ok()")]
#[ensures("result.unwrap() == 100")]
fn result_or_err_first() -> Result<i32, i32> {
    let res1: Result<i32, i32> = Err(500);
    let res2: Result<i32, i32> = Ok(100);
    res1.or(res2)
}

fn main() {
    // Runtime verification - Option::map
    assert_eq!(option_map_some_preserves(), Some(84));
    assert_eq!(option_map_none_stays_none(), None);
    assert!(option_map_conditional(true).is_some());
    assert!(option_map_conditional(false).is_none());

    // Runtime verification - Option::and_then
    assert_eq!(option_and_then_none_propagates(), None);
    assert!(option_and_then_none_conditional(false).is_none());

    // Runtime verification - Option::or_else
    assert_eq!(option_or_else_some_preserves(), Some(42));
    assert_eq!(option_or_else_some_conditional(true, 50), Some(50));

    // Runtime verification - Option::or
    assert_eq!(option_or_some_first(), Some(42));
    assert_eq!(option_or_none_first(), Some(100));
    assert_eq!(option_or_both_none(), None);

    // Runtime verification - Option::filter
    assert_eq!(option_filter_none_stays_none(), None);
    assert_eq!(option_filter_preserves_value(), Some(42));

    // Runtime verification - Result::map
    assert_eq!(result_map_ok_preserves(), Ok(84));
    assert_eq!(result_map_err_unchanged(), Err(500));
    assert!(result_map_conditional(true).is_ok());
    assert!(result_map_conditional(false).is_err());

    // Runtime verification - Result::map_err
    assert_eq!(result_map_err_ok_unchanged(), Ok(42));
    assert_eq!(result_map_err_err_preserves(), Err(501));

    // Runtime verification - Result::and_then
    assert_eq!(result_and_then_err_propagates(), Err(500));
    assert_eq!(result_and_then_err_conditional(false, 404), Err(404));

    // Runtime verification - Result::or_else
    assert_eq!(result_or_else_ok_preserves(), Ok(42));
    assert_eq!(result_or_else_ok_conditional(true, 50), Ok(50));

    // Runtime verification - Result::or
    assert_eq!(result_or_ok_first(), Ok(42));
    assert_eq!(result_or_err_first(), Ok(100));

    println!("All combinator methods tests passed!");
}
