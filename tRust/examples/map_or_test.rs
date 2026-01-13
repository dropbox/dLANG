// Test Option::map_or and Result::map_or method postconditions (Phase 10.1)
//
// map_or(default, f) - applies f to value if Some/Ok, returns default otherwise
//
// Postconditions:
// - Option::map_or: option.is_none() ==> result == default
// - Result::map_or: result.is_err() ==> result == default
//
// Note: map_or_else uses closures for both branches so no postcondition is generated.

// ===========================================
// Option::map_or tests
// ===========================================

// Test Option::map_or with None - should return default
// VERIFIED - None returns default value
#[ensures("result == 99")]
fn option_map_or_none() -> i32 {
    let opt: Option<i32> = None;
    opt.map_or(99, |x| x * 2)
}

// Test Option::map_or with Some - closure applies
// This verifies parsing works; result depends on closure
fn option_map_or_some() -> i32 {
    let opt = Some(10);
    opt.map_or(0, |x| x * 2)  // Returns 20
}

// Test Option::map_or with computed default
// VERIFIED - if None, returns computed default value
#[ensures("result == 100")]
fn option_map_or_computed_default() -> i32 {
    let opt: Option<i32> = None;
    let default = 50 + 50;
    opt.map_or(default, |x| x)
}

// Test Option::map_or in a function with requires
// Demonstrates integration with preconditions
#[requires("default >= 0")]
fn option_map_or_with_requires(opt: Option<i32>, default: i32) -> i32 {
    opt.map_or(default, |x| x.abs())
}

// Test Option::map_or_else - both branches use closures
// Just verify it parses (no postcondition generated)
fn option_map_or_else_parses() -> i32 {
    let opt: Option<i32> = None;
    opt.map_or_else(|| 42, |x| x * 2)
}

// ===========================================
// Result::map_or tests
// ===========================================

// Test Result::map_or with Err - should return default
// VERIFIED - Err returns default value
#[ensures("result == -1")]
fn result_map_or_err() -> i32 {
    let res: Result<i32, &str> = Err("error");
    res.map_or(-1, |x| x * 2)
}

// Test Result::map_or with Ok - closure applies
// This verifies parsing works; result depends on closure
fn result_map_or_ok() -> i32 {
    let res: Result<i32, &str> = Ok(10);
    res.map_or(0, |x| x * 2)  // Returns 20
}

// Test Result::map_or with computed default
// VERIFIED - if Err, returns computed default value
#[ensures("result == 200")]
fn result_map_or_computed_default() -> i32 {
    let res: Result<i32, &str> = Err("fail");
    let default = 100 + 100;
    res.map_or(default, |x| x)
}

// Test Result::map_or in a function with requires
// Demonstrates integration with preconditions
#[requires("default >= 0")]
fn result_map_or_with_requires(res: Result<i32, &str>, default: i32) -> i32 {
    res.map_or(default, |x| x.abs())
}

// Test Result::map_or_else - both branches use closures
// Just verify it parses (no postcondition generated)
fn result_map_or_else_parses() -> i32 {
    let res: Result<i32, &str> = Err("error");
    res.map_or_else(|_e| 42, |x| x * 2)
}

// ===========================================
// Combined tests
// ===========================================

// Test chaining map_or with other Option methods
fn option_chain_map_or() -> i32 {
    let opt: Option<Option<i32>> = Some(None);
    opt.flatten().map_or(5, |x| x + 1)  // flatten gives None, map_or returns 5
}

// Test chaining map_or with Result conversion
fn result_from_option_map_or() -> i32 {
    let opt: Option<i32> = None;
    let res = opt.ok_or("was none");
    res.map_or(-1, |x| x)  // Err, returns -1
}

fn main() {
    // Runtime tests for Option::map_or
    assert_eq!(option_map_or_none(), 99);
    assert_eq!(option_map_or_some(), 20);
    assert_eq!(option_map_or_computed_default(), 100);
    assert_eq!(option_map_or_with_requires(Some(-5), 0), 5);
    assert_eq!(option_map_or_with_requires(None, 10), 10);
    assert_eq!(option_map_or_else_parses(), 42);

    // Runtime tests for Result::map_or
    assert_eq!(result_map_or_err(), -1);
    assert_eq!(result_map_or_ok(), 20);
    assert_eq!(result_map_or_computed_default(), 200);
    assert_eq!(result_map_or_with_requires(Ok(-5), 0), 5);
    assert_eq!(result_map_or_with_requires(Err("fail"), 10), 10);
    assert_eq!(result_map_or_else_parses(), 42);

    // Combined tests
    assert_eq!(option_chain_map_or(), 5);
    assert_eq!(result_from_option_map_or(), -1);

    println!("All map_or tests passed!");
}
