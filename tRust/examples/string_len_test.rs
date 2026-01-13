// Test String and &str length/is_empty modeling (Phase 10.1)
//
// Current builtin modeling:
// - String::new / String::with_capacity: len(result) == 0
// - String::len: result == len(self)
// - String::is_empty: result == (len(self) == 0)
// - String::capacity: result >= len(self)
// - str::len: result == len(self)
// - str::is_empty: result == (len(self) == 0)
//
// Note: This only models length; character contents are not modeled.

// =================================================================
// String::new() tests
// =================================================================

// String::new().len() == 0
// VERIFIED
#[ensures("result == 0")]
fn string_new_len_zero() -> usize {
    let s: String = String::new();
    s.len()
}

// String::new().is_empty() == true
// VERIFIED
#[ensures("result")]
fn string_new_is_empty_true() -> bool {
    let s: String = String::new();
    s.is_empty()
}

// =================================================================
// String::with_capacity() tests
// =================================================================

// String::with_capacity(n).len() == 0
// VERIFIED
#[ensures("result == 0")]
fn string_with_capacity_len_zero() -> usize {
    let s: String = String::with_capacity(100);
    s.len()
}

// String::with_capacity(n).is_empty() == true
// VERIFIED
#[ensures("result")]
fn string_with_capacity_is_empty_true() -> bool {
    let s: String = String::with_capacity(100);
    s.is_empty()
}

// =================================================================
// String::capacity() tests
// =================================================================

// String::capacity() >= String::len()
// VERIFIED
#[ensures("result >= 0")]
fn string_capacity_nonneg() -> usize {
    let s: String = String::new();
    s.capacity()
}

// =================================================================
// Local postcondition tests
// =================================================================

// Local postconditions: s.len() == 0 and s.is_empty()
// VERIFIED
#[ensures("s.len() == 0")]
#[ensures("s.is_empty()")]
fn string_new_local_postconditions() {
    let s: String = String::new();
    let _n = s.len();
}

// =================================================================
// &str tests
// Note: String literals do not have their length modeled in the
// current architecture (literal "" doesn't establish len == 0)
// The str methods themselves work via (len ...) UF for parameters.
// =================================================================

// =================================================================
// Parameter tests with requires/ensures
// =================================================================

// Parameter with precondition on length
// VERIFIED: len returns the preconditioned length value
#[requires("s.len() > 0")]
#[ensures("result > 0")]
fn string_param_len_positive(s: &String) -> usize {
    s.len()
}

// Parameter with precondition using len > 0 (equivalent to !is_empty)
// Note: Negation `!s.is_empty()` has parsing issues, use len > 0 instead
// VERIFIED: non-empty means len > 0
#[requires("s.len() > 0")]
#[ensures("result > 0")]
fn string_param_not_empty_len_positive(s: &String) -> usize {
    s.len()
}

// str parameter with precondition
// VERIFIED
#[requires("s.len() > 0")]
#[ensures("result > 0")]
fn str_param_len_positive(s: &str) -> usize {
    s.len()
}

fn main() {
    // String::new() tests
    assert_eq!(string_new_len_zero(), 0);
    assert!(string_new_is_empty_true());

    // String::with_capacity() tests
    assert_eq!(string_with_capacity_len_zero(), 0);
    assert!(string_with_capacity_is_empty_true());

    // String::capacity() test
    let _ = string_capacity_nonneg();

    // Local postcondition test
    string_new_local_postconditions();

    // Parameter tests
    let s = String::from("hello");
    assert_eq!(string_param_len_positive(&s), 5);
    assert_eq!(string_param_not_empty_len_positive(&s), 5);
    assert_eq!(str_param_len_positive("world"), 5);
}
