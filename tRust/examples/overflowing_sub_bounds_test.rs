// Test overflowing_sub semantics and behavior
// x.overflowing_sub(y) returns (result, overflowed) where:
// - result is always x - y (wrapping on underflow)
// - overflowed is true if underflow occurred, false otherwise
//
// Note: Unlike checked_sub, overflowing_sub always returns the wrapped result.
// The boolean overflow flag allows callers to detect and handle underflow cases.
//
// This test validates:
// - Correct wrapping arithmetic
// - Underflow detection accuracy
// - Consistency with checked_sub semantics

/// Test that overflowing_sub correctly detects underflow
pub fn test_overflowing_sub_underflow_detection() {
    let mut underflow_count = 0u32;
    let mut success_count = 0u32;

    for a in 0u8..=50u8 {
        for b in 40u8..=100u8 {
            let (_result, overflowed) = a.overflowing_sub(b);
            if overflowed {
                underflow_count += 1;
            } else {
                success_count += 1;
            }
        }
    }

    assert!(success_count > 0, "Should have some non-underflow cases");
    assert!(underflow_count > 0, "Should have some underflow cases");
    println!("test_overflowing_sub_underflow_detection PASS (success: {}, underflow: {})",
             success_count, underflow_count);
}

/// Test that overflowing_sub wrapping behavior is correct
pub fn test_overflowing_sub_wrapping() {
    // Test wrapping: 5u8 - 10u8 should wrap to 251 with overflow = true
    let (result, overflowed) = 5u8.overflowing_sub(10);
    assert!(overflowed, "Should have underflowed");
    assert_eq!(result, 251, "Should wrap to 251 (5 - 10 + 256 = 251)");

    // Test non-underflow case
    let (result2, overflowed2) = 100u8.overflowing_sub(50);
    assert!(!overflowed2, "Should not underflow");
    assert_eq!(result2, 50, "Should equal 50");

    // Test edge case: 0 - 1
    let (result3, overflowed3) = 0u8.overflowing_sub(1);
    assert!(overflowed3, "0 - 1 should underflow");
    assert_eq!(result3, 255, "Should wrap to 255");

    // Test edge case: subtracting 0 never underflows
    let (result4, overflowed4) = 0u8.overflowing_sub(0);
    assert!(!overflowed4, "Subtracting 0 should not underflow");
    assert_eq!(result4, 0, "Should equal 0");

    println!("test_overflowing_sub_wrapping PASS");
}

/// Test that upper bound from min() is preserved through overflowing_sub
pub fn test_overflowing_sub_preserves_upper_bound() {
    for x in 200..=255u8 {
        // min(x, 250) <= 250 (MinUpper gives upper bound 250)
        let upper_bounded = std::cmp::min(x, 250);
        // overflowing_sub result = upper_bounded - 5 <= 250
        let (result, overflowed) = upper_bounded.overflowing_sub(5);
        if !overflowed {
            assert!(result <= 250, "Upper bound not preserved: {} > 250", result);
        }
    }
    println!("test_overflowing_sub_preserves_upper_bound PASS");
}

/// Compare overflowing_sub with checked_sub behavior
pub fn test_overflowing_sub_vs_checked() {
    for a in 0u8..=255u8 {
        for b in 0u8..=10u8 {
            let checked = a.checked_sub(b);
            let (result, overflowed) = a.overflowing_sub(b);

            match checked {
                Some(val) => {
                    assert!(!overflowed, "checked Some implies no underflow for {} - {}", a, b);
                    assert_eq!(val, result, "Results should match for {} - {}", a, b);
                }
                None => {
                    assert!(overflowed, "checked None implies underflow for {} - {}", a, b);
                }
            }
        }
    }
    println!("test_overflowing_sub_vs_checked PASS");
}

/// Test overflowing_sub with signed integers
pub fn test_overflowing_sub_signed() {
    // Negative overflow: i8::MIN - 1
    let (result, overflowed) = (-128i8).overflowing_sub(1);
    assert!(overflowed, "-128 - 1 should overflow for i8");
    assert_eq!(result, 127, "Should wrap to 127");

    // Positive overflow: i8::MAX - (-1) = i8::MAX + 1
    let (result2, overflowed2) = 127i8.overflowing_sub(-1);
    assert!(overflowed2, "127 - (-1) should overflow for i8");
    assert_eq!(result2, -128, "Should wrap to -128");

    // No overflow case
    let (result3, overflowed3) = 50i8.overflowing_sub(25);
    assert!(!overflowed3, "50 - 25 should not overflow for i8");
    assert_eq!(result3, 25, "Should equal 25");

    // Negative result without overflow
    let (result4, overflowed4) = (-50i8).overflowing_sub(25);
    assert!(!overflowed4, "-50 - 25 should not overflow for i8");
    assert_eq!(result4, -75, "Should equal -75");

    println!("test_overflowing_sub_signed PASS");
}

/// Test overflowing_sub with larger integer types
pub fn test_overflowing_sub_u32() {
    // Test wrapping at u32 boundary
    let (result, overflowed) = 0u32.overflowing_sub(1);
    assert!(overflowed, "0 - 1 should underflow for u32");
    assert_eq!(result, u32::MAX, "Should wrap to u32::MAX");

    // Test non-underflow case
    let (result2, overflowed2) = 3_000_000u32.overflowing_sub(2_000_000);
    assert!(!overflowed2, "Should not underflow");
    assert_eq!(result2, 1_000_000, "Should equal 1_000_000");

    println!("test_overflowing_sub_u32 PASS");
}

/// Test safe array access using .get() pattern
pub fn test_overflowing_sub_safe_array_get() {
    let arr: [u8; 256] = [42u8; 256];
    let mut access_count = 0;

    // Pattern: use overflowing_sub and .get() for safe access
    for x in 5..255usize {
        let (idx, overflowed) = x.overflowing_sub(5);
        // Use .get() for safe access when underflow didn't occur
        if !overflowed {
            if let Some(&val) = arr.get(idx) {
                assert_eq!(val, 42);
                access_count += 1;
            }
        }
    }

    assert_eq!(access_count, 250, "Should have accessed 250 times");
    println!("test_overflowing_sub_safe_array_get PASS");
}

/// Test overflowing_sub matches wrapping_sub when underflow occurs
pub fn test_overflowing_sub_matches_wrapping() {
    for a in 0u8..=255u8 {
        for b in 0u8..=10u8 {
            let (overflowing_result, _) = a.overflowing_sub(b);
            let wrapping_result = a.wrapping_sub(b);
            assert_eq!(
                overflowing_result, wrapping_result,
                "overflowing_sub and wrapping_sub should produce same result for {} - {}",
                a, b
            );
        }
    }
    println!("test_overflowing_sub_matches_wrapping PASS");
}

/// Test overflowing_sub tuple destructuring pattern
pub fn test_overflowing_sub_tuple_pattern() {
    // Test various tuple destructuring patterns
    let a: u8 = 100;
    let b: u8 = 50;

    // Pattern 1: Direct destructuring
    let (diff, overflow) = a.overflowing_sub(b);
    assert_eq!(diff, 50);
    assert!(!overflow);

    // Pattern 2: Named tuple fields
    let result = a.overflowing_sub(b);
    assert_eq!(result.0, 50);
    assert!(!result.1);

    // Pattern 3: Ignoring overflow flag
    let (diff2, _) = a.overflowing_sub(b);
    assert_eq!(diff2, 50);

    println!("test_overflowing_sub_tuple_pattern PASS");
}

/// Test overflowing_sub with usize
pub fn test_overflowing_sub_usize() {
    // These tests are platform-independent behavior
    let (result, overflowed) = 300usize.overflowing_sub(200);
    assert_eq!(result, 100);
    assert!(!overflowed);

    // Test with values near zero
    let (result2, overflowed2) = 10usize.overflowing_sub(5);
    assert_eq!(result2, 5);
    assert!(!overflowed2);

    // Test underflow
    let (result3, overflowed3) = 0usize.overflowing_sub(1);
    assert_eq!(result3, usize::MAX);
    assert!(overflowed3);

    println!("test_overflowing_sub_usize PASS");
}

/// Test difference between two values with overflow detection
pub fn test_overflowing_sub_difference() {
    // Computing difference between two values
    let values: [u8; 5] = [10, 50, 100, 150, 200];

    for i in 0..values.len() {
        for j in 0..values.len() {
            // Use .get() for safe access (bounds propagation not tracked through for loops)
            if let (Some(&a), Some(&b)) = (values.get(i), values.get(j)) {
                let (diff, _) = a.overflowing_sub(b);
                let (reverse_diff, _) = b.overflowing_sub(a);

                // The sum of forward and reverse differences wraps to 0
                let (sum, _) = diff.overflowing_add(reverse_diff);
                assert_eq!(sum, 0, "Forward + reverse difference should wrap to 0");
            }
        }
    }

    println!("test_overflowing_sub_difference PASS");
}

pub fn main() {
    // Test underflow detection
    test_overflowing_sub_underflow_detection();

    // Test wrapping behavior
    test_overflowing_sub_wrapping();

    // Test upper bound preservation
    test_overflowing_sub_preserves_upper_bound();

    // Compare with checked_sub
    test_overflowing_sub_vs_checked();

    // Test signed integers
    test_overflowing_sub_signed();

    // Test u32
    test_overflowing_sub_u32();

    // Test safe array access with .get()
    test_overflowing_sub_safe_array_get();

    // Test matches wrapping_sub
    test_overflowing_sub_matches_wrapping();

    // Test tuple patterns
    test_overflowing_sub_tuple_pattern();

    // Test usize
    test_overflowing_sub_usize();

    // Test difference computation
    test_overflowing_sub_difference();

    println!("\nAll overflowing_sub bounds tests passed!");
}
