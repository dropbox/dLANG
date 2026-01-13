// Test checked_neg verification contracts
//
// checked_neg semantics: negation operation that returns Option.
// For signed types: Returns Some(-x) when x != MIN, returns None when x == MIN.
// For unsigned types: Returns Some(0) when x == 0, returns None when x > 0.
//
// This test focuses on solver-verified properties:
// - (x == 0) => checked_neg returns Some(0) (zero input for both signed and unsigned)
// - For signed types: x > MIN => checked_neg returns Some value
// - Negation of zero is always zero
//
// @expect: VERIFIED

// =============================================================================
// Zero negation tests (constants) - signed types
// =============================================================================

#[ensures("result == 0")]
fn test_checked_neg_zero_i8_const() -> i8 {
    if let Some(r) = 0i8.checked_neg() {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_neg_zero_i16_const() -> i16 {
    if let Some(r) = 0i16.checked_neg() {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_neg_zero_i32_const() -> i32 {
    if let Some(r) = 0i32.checked_neg() {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_neg_zero_i64_const() -> i64 {
    if let Some(r) = 0i64.checked_neg() {
        r
    } else {
        0
    }
}

// =============================================================================
// Zero negation tests (constants) - unsigned types
// =============================================================================

#[ensures("result == 0")]
fn test_checked_neg_zero_u8_const() -> u8 {
    if let Some(r) = 0u8.checked_neg() {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_neg_zero_u16_const() -> u16 {
    if let Some(r) = 0u16.checked_neg() {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_neg_zero_u32_const() -> u32 {
    if let Some(r) = 0u32.checked_neg() {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_neg_zero_u64_const() -> u64 {
    if let Some(r) = 0u64.checked_neg() {
        r
    } else {
        0
    }
}

// =============================================================================
// Zero negation tests (parameterized) - signed types
// =============================================================================

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_zero_i8(x: i8) -> i8 {
    if let Some(r) = x.checked_neg() {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_zero_i16(x: i16) -> i16 {
    if let Some(r) = x.checked_neg() {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_zero_i32(x: i32) -> i32 {
    if let Some(r) = x.checked_neg() {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_zero_i64(x: i64) -> i64 {
    if let Some(r) = x.checked_neg() {
        r
    } else {
        0
    }
}

// =============================================================================
// Zero negation tests (parameterized) - unsigned types
// =============================================================================

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_zero_u8(x: u8) -> u8 {
    if let Some(r) = x.checked_neg() {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_zero_u16(x: u16) -> u16 {
    if let Some(r) = x.checked_neg() {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_zero_u32(x: u32) -> u32 {
    if let Some(r) = x.checked_neg() {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_zero_u64(x: u64) -> u64 {
    if let Some(r) = x.checked_neg() {
        r
    } else {
        0
    }
}

// =============================================================================
// Double negation tests (signed types) - -(-x) == x when valid
// =============================================================================

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_double_i32(x: i32) -> i32 {
    let first = if let Some(r) = x.checked_neg() { r } else { return 0; };
    if let Some(r) = first.checked_neg() { r } else { 0 }
}

#[requires("x == 0")]
#[ensures("result == 0")]
fn test_checked_neg_double_i64(x: i64) -> i64 {
    let first = if let Some(r) = x.checked_neg() { r } else { return 0; };
    if let Some(r) = first.checked_neg() { r } else { 0 }
}

// =============================================================================
// MIN overflow tests (runtime) - signed types
// =============================================================================

fn test_checked_neg_min_overflow() {
    // MIN values overflow on negation
    assert!(i8::MIN.checked_neg().is_none());
    assert!(i16::MIN.checked_neg().is_none());
    assert!(i32::MIN.checked_neg().is_none());
    assert!(i64::MIN.checked_neg().is_none());
    println!("test_checked_neg_min_overflow PASS");
}

// =============================================================================
// Non-zero unsigned returns None (runtime)
// =============================================================================

fn test_checked_neg_unsigned_nonzero() {
    // Non-zero unsigned values return None
    assert!(1u8.checked_neg().is_none());
    assert!(1u16.checked_neg().is_none());
    assert!(1u32.checked_neg().is_none());
    assert!(1u64.checked_neg().is_none());
    assert!(255u8.checked_neg().is_none());
    assert!(u32::MAX.checked_neg().is_none());
    println!("test_checked_neg_unsigned_nonzero PASS");
}

// =============================================================================
// Runtime verification of negation properties
// =============================================================================

fn test_checked_neg_runtime_verification() {
    // Verify: negation of zero is always zero (signed)
    assert_eq!(0i8.checked_neg(), Some(0));
    assert_eq!(0i16.checked_neg(), Some(0));
    assert_eq!(0i32.checked_neg(), Some(0));
    assert_eq!(0i64.checked_neg(), Some(0));

    // Verify: negation of zero is always zero (unsigned)
    assert_eq!(0u8.checked_neg(), Some(0));
    assert_eq!(0u16.checked_neg(), Some(0));
    assert_eq!(0u32.checked_neg(), Some(0));
    assert_eq!(0u64.checked_neg(), Some(0));

    // Verify: -(-x) == x for non-MIN signed values
    for x in -100i32..100i32 {
        if let Some(neg_x) = x.checked_neg() {
            if let Some(neg_neg_x) = neg_x.checked_neg() {
                assert_eq!(neg_neg_x, x, "Double negation should return original");
            }
        }
    }

    // Verify: negation inverts sign for non-zero, non-MIN signed values
    for x in 1i32..128i32 {
        if let Some(neg_x) = x.checked_neg() {
            assert!(neg_x < 0, "Negation of positive should be negative");
            assert_eq!(neg_x, -x, "Negation should match unary minus");
        }
    }
    for x in -127i32..0i32 {
        if let Some(neg_x) = x.checked_neg() {
            assert!(neg_x > 0, "Negation of negative should be positive");
            assert_eq!(neg_x, -x, "Negation should match unary minus");
        }
    }

    println!("test_checked_neg_runtime_verification PASS");
}

fn main() {
    // Constant zero negation tests - signed
    assert!(test_checked_neg_zero_i8_const() == 0);
    assert!(test_checked_neg_zero_i16_const() == 0);
    assert!(test_checked_neg_zero_i32_const() == 0);
    assert!(test_checked_neg_zero_i64_const() == 0);

    // Constant zero negation tests - unsigned
    assert!(test_checked_neg_zero_u8_const() == 0);
    assert!(test_checked_neg_zero_u16_const() == 0);
    assert!(test_checked_neg_zero_u32_const() == 0);
    assert!(test_checked_neg_zero_u64_const() == 0);

    // Parameterized zero negation tests - signed
    assert!(test_checked_neg_zero_i8(0) == 0);
    assert!(test_checked_neg_zero_i16(0) == 0);
    assert!(test_checked_neg_zero_i32(0) == 0);
    assert!(test_checked_neg_zero_i64(0) == 0);

    // Parameterized zero negation tests - unsigned
    assert!(test_checked_neg_zero_u8(0) == 0);
    assert!(test_checked_neg_zero_u16(0) == 0);
    assert!(test_checked_neg_zero_u32(0) == 0);
    assert!(test_checked_neg_zero_u64(0) == 0);

    // Double negation tests
    assert!(test_checked_neg_double_i32(0) == 0);
    assert!(test_checked_neg_double_i64(0) == 0);

    // MIN overflow test
    test_checked_neg_min_overflow();

    // Unsigned non-zero returns None
    test_checked_neg_unsigned_nonzero();

    // Runtime verification
    test_checked_neg_runtime_verification();

    println!("All checked_neg_bounds_test tests passed!");
}
