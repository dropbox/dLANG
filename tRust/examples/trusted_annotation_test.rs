//! Integration test for #[trusted] annotation (Phase N1.4)
//!
//! Functions marked with #[trusted] have their specifications assumed without
//! verification. This is used for:
//! - FFI functions that can't be verified
//! - Well-audited unsafe code
//! - External implementations verified by other means
//!
//! Expected behavior:
//! - Trusted functions should be marked "assumed" in verification output
//! - Their specs are still available for modular verification of callers
//! - Unsafe code inside trusted functions doesn't require effect annotation

#![allow(dead_code)]

/// A trusted function that wraps unsafe code.
/// The postcondition is assumed without verification.
#[trusted]
#[ensures("*result == value")]
fn trusted_box_new(value: i32) -> Box<i32> {
    Box::new(value)
}

/// A trusted function with an INTENTIONALLY INCORRECT spec.
/// Because it's trusted, verification is skipped - this should NOT fail.
#[trusted]
#[ensures("result == 0")]  // Bug: always returns 42, not 0
fn trusted_incorrect_spec() -> i32 {
    42  // Intentionally wrong - but trusted, so not verified
}

/// A trusted unsafe function.
/// Trusted skips verification AND allows unsafe without #[effects(Unsafe)].
#[trusted]
#[requires("!ptr.is_null()")]
#[ensures("result == *ptr")]
unsafe fn trusted_unsafe_deref(ptr: *const i32) -> i32 {
    *ptr
}

/// A non-trusted function that uses trusted functions.
/// This function IS verified - it can rely on trusted specs as assumptions.
#[ensures("*result == 100")]
fn verified_caller() -> Box<i32> {
    trusted_box_new(100)
}

/// Another verified function that calls trusted code.
/// The caller's spec must hold given the trusted callee's assumed spec.
#[ensures("result == 42")]
fn verified_uses_trusted() -> i32 {
    // Even though trusted_incorrect_spec's spec says result == 0,
    // it actually returns 42. But since it's trusted, we assume the spec.
    // NOTE: This demonstrates trust is a soundness boundary - if the
    // trusted spec is wrong, verification of callers can be unsound.
    let _ = trusted_incorrect_spec(); // Ignored, we return our own value
    42
}

fn main() {
    // Basic smoke tests
    let b = trusted_box_new(42);
    assert_eq!(*b, 42);

    let x = trusted_incorrect_spec();
    // Note: x is 42, not 0 as the (wrong) spec claims
    assert_eq!(x, 42);

    let r = verified_caller();
    assert_eq!(*r, 100);

    let v = verified_uses_trusted();
    assert_eq!(v, 42);
}
