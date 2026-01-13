// Test Option.unwrap_or() method parsing (Phase 10.1)
//
// Option.unwrap_or(default) is modeled as:
//   (ite option_is_some option_value default)
//
// This tests the SMT translation of unwrap_or() - a conditional expression
// that returns the Option's value if Some, or the default if None.
//
// Constructor tracking (Phase 10.1):
// - Some(x) sets _is_some = true, _value = x
// - None sets _is_some = false
//
// Most tests are VERIFIED with constructor tracking. The safe_add_with_default
// test remains DISPROVEN because it uses checked_add, where the is_some condition
// depends on overflow analysis which is not yet modeled.

// Test basic unwrap_or usage - returns value if Some, else default
fn unwrap_with_default(opt: Option<i32>, default: i32) -> i32 {
    opt.unwrap_or(default)
}

// Test unwrap_or with Some value
// VERIFIED - Some(42) sets is_some=true, value=42 via constructor tracking
#[ensures("result == 42")]
fn test_unwrap_or_some() -> i32 {
    let opt = Some(42);
    opt.unwrap_or(0)
}

// Test unwrap_or with None value
// VERIFIED - None sets is_some=false via constructor tracking
#[ensures("result == 99")]
fn test_unwrap_or_none() -> i32 {
    let opt: Option<i32> = None;
    opt.unwrap_or(99)
}

// Test unwrap_or with checked_add - using the builtin postcondition
// checked_add returns Option where: result.is_some() ==> result.unwrap() == a + b
// DISPROVEN - is_some condition for no-overflow not yet modeled (future work)
#[requires("a <= 100")]
#[requires("b <= 100")]
#[ensures("result == a + b")]
fn safe_add_with_default(a: u32, b: u32) -> u32 {
    a.checked_add(b).unwrap_or(0)
}

// Test unwrap_or with computed default - ensures parsing handles expressions
// VERIFIED - the #[requires] prevents overflow, and the verifier checks the precondition
#[requires("fallback >= -1073741823 && fallback <= 1073741823")]  // prevent overflow
fn unwrap_or_computed(opt: Option<i32>, fallback: i32) -> i32 {
    // This demonstrates unwrap_or parsing handles complex default expressions
    opt.unwrap_or(fallback * 2)
}

// Test unwrap_or_default alternative pattern
// This is functionally equivalent to unwrap_or(0) for i32
fn unwrap_with_default_zero(opt: Option<i32>) -> i32 {
    opt.unwrap_or(0)
}

fn main() {
    // Runtime tests (not verified, just sanity checks)
    assert_eq!(unwrap_with_default(Some(10), 0), 10);
    assert_eq!(unwrap_with_default(None, 99), 99);

    assert_eq!(test_unwrap_or_some(), 42);
    assert_eq!(test_unwrap_or_none(), 99);

    assert_eq!(safe_add_with_default(50, 30), 80);

    assert_eq!(unwrap_or_computed(Some(10), 5), 10);
    assert_eq!(unwrap_or_computed(None, 5), 10);

    assert_eq!(unwrap_with_default_zero(Some(42)), 42);
    assert_eq!(unwrap_with_default_zero(None), 0);

    println!("All unwrap_or tests passed!");
}
