// Integration test for Option::inspect() method
// inspect() calls a closure on the value if Some, returns self unchanged

#![allow(unused_variables)]
#![allow(dead_code)]

// Test: inspect preserves is_some status
#[requires("opt.is_some()")]
#[ensures("result.is_some()")]
fn test_inspect_preserves_some(opt: Option<i32>) -> Option<i32> {
    opt.inspect(|v| {
        // Closure called for side effects
        let _ = v;
    })
}
// EXPECT: VERIFIED

// Test: inspect preserves is_none status
#[requires("opt.is_none()")]
#[ensures("result.is_none()")]
fn test_inspect_preserves_none(opt: Option<i32>) -> Option<i32> {
    opt.inspect(|v| {
        // Closure not called for None
        let _ = v;
    })
}
// EXPECT: VERIFIED

// Test: inspect preserves the value
#[requires("opt.is_some()")]
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == opt.unwrap()")]
fn test_inspect_preserves_value(opt: Option<i32>) -> Option<i32> {
    opt.inspect(|v| {
        // Value unchanged by inspect
        let _ = v;
    })
}
// EXPECT: VERIFIED

// Test: inspect is identity for Some
#[requires("x > 0")]
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == x")]
fn test_inspect_some_identity(x: i32) -> Option<i32> {
    let opt = Some(x);
    opt.inspect(|_v| {})
}
// EXPECT: VERIFIED

// Test: inspect is identity for None
#[ensures("result.is_none()")]
fn test_inspect_none_identity() -> Option<i32> {
    let opt: Option<i32> = None;
    opt.inspect(|_v| {})
}
// EXPECT: VERIFIED

// Test: chained inspect calls
#[requires("opt.is_some()")]
#[ensures("result.is_some()")]
fn test_inspect_chained(opt: Option<i32>) -> Option<i32> {
    opt.inspect(|_| {}).inspect(|_| {}).inspect(|_| {})
}
// EXPECT: VERIFIED

fn main() {
    // Test at runtime
    let some_val = Some(42);
    let result = test_inspect_preserves_some(some_val);
    assert!(result.is_some());

    let none_val: Option<i32> = None;
    let result = test_inspect_preserves_none(none_val);
    assert!(result.is_none());

    println!("All Option::inspect tests passed!");
}
