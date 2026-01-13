// Test overflowing_mul semantics and behavior
// x.overflowing_mul(y) returns (result, overflowed) where:
// - result is always x * y (wrapping on overflow)
// - overflowed is true if overflow occurred, false otherwise
//
// Note: Unlike checked_mul, overflowing_mul always returns the wrapped result.
// The boolean overflow flag allows callers to detect and handle overflow cases.
//
// This test validates:
// - Correct wrapping arithmetic
// - Overflow detection accuracy
// - Consistency with checked_mul semantics

/// Test that overflowing_mul correctly detects overflow
pub fn test_overflowing_mul_overflow_detection() {
    let mut overflow_count = 0u32;
    let mut success_count = 0u32;

    for a in 10u8..=20u8 {
        for b in 10u8..=20u8 {
            let (_result, overflowed) = a.overflowing_mul(b);
            if overflowed {
                overflow_count += 1;
            } else {
                success_count += 1;
            }
        }
    }

    assert!(success_count > 0, "Should have some non-overflow cases");
    assert!(overflow_count > 0, "Should have some overflow cases");
    println!("test_overflowing_mul_overflow_detection PASS (success: {}, overflow: {})",
             success_count, overflow_count);
}

/// Test that overflowing_mul wrapping behavior is correct
pub fn test_overflowing_mul_wrapping() {
    // Test wrapping: 16u8 * 17u8 = 272 should wrap to 16 with overflow = true
    let (result, overflowed) = 16u8.overflowing_mul(17);
    assert!(overflowed, "Should have overflowed");
    assert_eq!(result, 16, "Should wrap to 16 (16 * 17 = 272 = 256 + 16)");

    // Test non-overflow case
    let (result2, overflowed2) = 10u8.overflowing_mul(5);
    assert!(!overflowed2, "Should not overflow");
    assert_eq!(result2, 50, "Should equal 50");

    // Test edge case: max value * 2
    let (result3, overflowed3) = 255u8.overflowing_mul(2);
    assert!(overflowed3, "255 * 2 should overflow");
    assert_eq!(result3, 254, "Should wrap to 254 (510 - 256 = 254)");

    // Test edge case: multiplying by 0 never overflows
    let (result4, overflowed4) = 255u8.overflowing_mul(0);
    assert!(!overflowed4, "Multiplying by 0 should not overflow");
    assert_eq!(result4, 0, "Should equal 0");

    // Test edge case: multiplying by 1 never overflows
    let (result5, overflowed5) = 255u8.overflowing_mul(1);
    assert!(!overflowed5, "Multiplying by 1 should not overflow");
    assert_eq!(result5, 255, "Should equal 255");

    println!("test_overflowing_mul_wrapping PASS");
}

/// Test that upper bound from min() is preserved through overflowing_mul (when no overflow)
pub fn test_overflowing_mul_preserves_upper_bound() {
    for x in 0..50u8 {
        // min(x, 15) <= 15 (MinUpper gives upper bound 15)
        let upper_bounded = std::cmp::min(x, 15);
        // overflowing_mul result without overflow <= 15 * 15 = 225 <= 255
        let (result, overflowed) = upper_bounded.overflowing_mul(15);
        if !overflowed {
            assert!(result <= 225, "Upper bound not preserved: {} > 225", result);
        }
    }
    println!("test_overflowing_mul_preserves_upper_bound PASS");
}

/// Compare overflowing_mul with checked_mul behavior
pub fn test_overflowing_mul_vs_checked() {
    for a in 0u8..=50u8 {
        for b in 0u8..=10u8 {
            let checked = a.checked_mul(b);
            let (result, overflowed) = a.overflowing_mul(b);

            match checked {
                Some(val) => {
                    assert!(!overflowed, "checked Some implies no overflow for {} * {}", a, b);
                    assert_eq!(val, result, "Results should match for {} * {}", a, b);
                }
                None => {
                    assert!(overflowed, "checked None implies overflow for {} * {}", a, b);
                }
            }
        }
    }
    println!("test_overflowing_mul_vs_checked PASS");
}

/// Test overflowing_mul with signed integers
pub fn test_overflowing_mul_signed() {
    // Positive overflow: large positive * positive
    let (result, overflowed) = 64i8.overflowing_mul(2);
    assert!(overflowed, "64 * 2 = 128 should overflow for i8");
    assert_eq!(result, -128, "Should wrap to -128");

    // Negative overflow: large positive * negative
    let (result2, overflowed2) = 64i8.overflowing_mul(-2);
    assert!(!overflowed2, "64 * -2 = -128 should not overflow for i8");
    assert_eq!(result2, -128, "Should equal -128");

    // Negative overflow: negative * negative giving positive overflow
    let (result3, overflowed3) = (-128i8).overflowing_mul(-1);
    assert!(overflowed3, "-128 * -1 should overflow for i8");
    assert_eq!(result3, -128, "Should wrap to -128");

    // No overflow case
    let (result4, overflowed4) = 10i8.overflowing_mul(5);
    assert!(!overflowed4, "10 * 5 should not overflow for i8");
    assert_eq!(result4, 50, "Should equal 50");

    // Negative result without overflow
    let (result5, overflowed5) = (-10i8).overflowing_mul(5);
    assert!(!overflowed5, "-10 * 5 should not overflow for i8");
    assert_eq!(result5, -50, "Should equal -50");

    println!("test_overflowing_mul_signed PASS");
}

/// Test overflowing_mul with larger integer types
pub fn test_overflowing_mul_u32() {
    // Test wrapping at u32 boundary
    let (result, overflowed) = (u32::MAX / 2 + 1).overflowing_mul(2);
    assert!(!overflowed, "Should not overflow exactly at MAX");
    assert_eq!(result, 0, "Should equal 0 (edge case)");
    // Actually: (2^31) * 2 = 2^32 = 0 with overflow
    let (result_actual, overflowed_actual) = 2147483648u32.overflowing_mul(2);
    assert!(overflowed_actual, "2^31 * 2 should overflow for u32");
    assert_eq!(result_actual, 0, "Should wrap to 0");

    // Test non-overflow case
    let (result2, overflowed2) = 1000u32.overflowing_mul(2000);
    assert!(!overflowed2, "Should not overflow");
    assert_eq!(result2, 2_000_000, "Should equal 2_000_000");

    println!("test_overflowing_mul_u32 PASS");
}

/// Test safe array access using .get() pattern
pub fn test_overflowing_mul_safe_array_get() {
    let arr: [u8; 256] = [42u8; 256];
    let mut access_count = 0;

    // Pattern: use overflowing_mul and .get() for safe access
    for x in 0..50usize {
        let (idx, overflowed) = x.overflowing_mul(5);
        // Use .get() for safe access when overflow didn't occur
        if !overflowed {
            if let Some(&val) = arr.get(idx) {
                assert_eq!(val, 42);
                access_count += 1;
            }
        }
    }

    // 0*5=0, 1*5=5, ..., 51*5=255 (51 values fit in 256)
    // But we only go up to 49*5=245, so 50 accesses
    assert_eq!(access_count, 50, "Should have accessed 50 times");
    println!("test_overflowing_mul_safe_array_get PASS");
}

/// Test overflowing_mul matches wrapping_mul when overflow occurs
pub fn test_overflowing_mul_matches_wrapping() {
    for a in 0u8..=50u8 {
        for b in 0u8..=10u8 {
            let (overflowing_result, _) = a.overflowing_mul(b);
            let wrapping_result = a.wrapping_mul(b);
            assert_eq!(
                overflowing_result, wrapping_result,
                "overflowing_mul and wrapping_mul should produce same result for {} * {}",
                a, b
            );
        }
    }
    println!("test_overflowing_mul_matches_wrapping PASS");
}

/// Test overflowing_mul tuple destructuring pattern
pub fn test_overflowing_mul_tuple_pattern() {
    // Test various tuple destructuring patterns
    let a: u8 = 10;
    let b: u8 = 5;

    // Pattern 1: Direct destructuring
    let (product, overflow) = a.overflowing_mul(b);
    assert_eq!(product, 50);
    assert!(!overflow);

    // Pattern 2: Named tuple fields
    let result = a.overflowing_mul(b);
    assert_eq!(result.0, 50);
    assert!(!result.1);

    // Pattern 3: Ignoring overflow flag
    let (product2, _) = a.overflowing_mul(b);
    assert_eq!(product2, 50);

    println!("test_overflowing_mul_tuple_pattern PASS");
}

/// Test overflowing_mul with usize
pub fn test_overflowing_mul_usize() {
    // These tests are platform-independent behavior
    let (result, overflowed) = 100usize.overflowing_mul(200);
    assert_eq!(result, 20000);
    assert!(!overflowed);

    // Test with moderate values
    let (result2, overflowed2) = 1000usize.overflowing_mul(1000);
    assert_eq!(result2, 1_000_000);
    assert!(!overflowed2);

    // Test multiplying by 0
    let (result3, overflowed3) = usize::MAX.overflowing_mul(0);
    assert_eq!(result3, 0);
    assert!(!overflowed3);

    println!("test_overflowing_mul_usize PASS");
}

/// Test squares with overflow detection
pub fn test_overflowing_mul_squares() {
    // Computing squares of small values
    let values: [u8; 5] = [3, 8, 15, 16, 17];

    for i in 0..values.len() {
        // Use .get() for safe access (bounds propagation not tracked through for loops)
        if let Some(&a) = values.get(i) {
            let (square, overflowed) = a.overflowing_mul(a);

            // 3*3=9, 8*8=64, 15*15=225, 16*16=256->0 (overflow), 17*17=289->33 (overflow)
            if a <= 15 {
                assert!(!overflowed, "{} squared should not overflow", a);
            } else {
                assert!(overflowed, "{} squared should overflow", a);
            }

            // Verify wrapping behavior
            let expected = (a as u16).wrapping_mul(a as u16) as u8;
            assert_eq!(square, expected, "Square of {} should wrap correctly", a);
        }
    }

    println!("test_overflowing_mul_squares PASS");
}

/// Test powers of 2 multiplication
pub fn test_overflowing_mul_powers_of_two() {
    // Multiplying by powers of 2 is equivalent to left shift
    let base: u8 = 5;

    // 5 * 1 = 5
    let (r1, o1) = base.overflowing_mul(1);
    assert_eq!(r1, 5);
    assert!(!o1);

    // 5 * 2 = 10
    let (r2, o2) = base.overflowing_mul(2);
    assert_eq!(r2, 10);
    assert!(!o2);

    // 5 * 4 = 20
    let (r3, o3) = base.overflowing_mul(4);
    assert_eq!(r3, 20);
    assert!(!o3);

    // 5 * 8 = 40
    let (r4, o4) = base.overflowing_mul(8);
    assert_eq!(r4, 40);
    assert!(!o4);

    // 5 * 16 = 80
    let (r5, o5) = base.overflowing_mul(16);
    assert_eq!(r5, 80);
    assert!(!o5);

    // 5 * 32 = 160
    let (r6, o6) = base.overflowing_mul(32);
    assert_eq!(r6, 160);
    assert!(!o6);

    // 5 * 64 = 320 -> wraps to 64
    let (r7, o7) = base.overflowing_mul(64);
    assert_eq!(r7, 64);
    assert!(o7);

    println!("test_overflowing_mul_powers_of_two PASS");
}

pub fn main() {
    // Test overflow detection
    test_overflowing_mul_overflow_detection();

    // Test wrapping behavior
    test_overflowing_mul_wrapping();

    // Test upper bound preservation
    test_overflowing_mul_preserves_upper_bound();

    // Compare with checked_mul
    test_overflowing_mul_vs_checked();

    // Test signed integers
    test_overflowing_mul_signed();

    // Test u32
    test_overflowing_mul_u32();

    // Test safe array access with .get()
    test_overflowing_mul_safe_array_get();

    // Test matches wrapping_mul
    test_overflowing_mul_matches_wrapping();

    // Test tuple patterns
    test_overflowing_mul_tuple_pattern();

    // Test usize
    test_overflowing_mul_usize();

    // Test squares
    test_overflowing_mul_squares();

    // Test powers of two
    test_overflowing_mul_powers_of_two();

    println!("\nAll overflowing_mul bounds tests passed!");
}
