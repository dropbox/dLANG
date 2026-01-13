// Test overflowing_add semantics and behavior
// x.overflowing_add(y) returns (result, overflowed) where:
// - result is always x + y (wrapping on overflow)
// - overflowed is true if overflow occurred, false otherwise
//
// Note: Unlike checked_add, overflowing_add always returns the wrapped result.
// The boolean overflow flag allows callers to detect and handle overflow cases.
//
// This test validates:
// - Correct wrapping arithmetic
// - Overflow detection accuracy
// - Consistency with checked_add semantics

/// Test that overflowing_add correctly detects overflow
pub fn test_overflowing_add_overflow_detection() {
    let mut overflow_count = 0u32;
    let mut success_count = 0u32;

    for a in 200u8..=255u8 {
        for b in 50u8..=100u8 {
            let (_result, overflowed) = a.overflowing_add(b);
            if overflowed {
                overflow_count += 1;
            } else {
                success_count += 1;
            }
        }
    }

    assert!(success_count > 0, "Should have some non-overflow cases");
    assert!(overflow_count > 0, "Should have some overflow cases");
    println!("test_overflowing_add_overflow_detection PASS (success: {}, overflow: {})",
             success_count, overflow_count);
}

/// Test that overflowing_add wrapping behavior is correct
pub fn test_overflowing_add_wrapping() {
    // Test wrapping: 250u8 + 10u8 should wrap to 4 with overflow = true
    let (result, overflowed) = 250u8.overflowing_add(10);
    assert!(overflowed, "Should have overflowed");
    assert_eq!(result, 4, "Should wrap to 4 (250 + 10 - 256 = 4)");

    // Test non-overflow case
    let (result2, overflowed2) = 100u8.overflowing_add(50);
    assert!(!overflowed2, "Should not overflow");
    assert_eq!(result2, 150, "Should equal 150");

    // Test edge case: max value
    let (result3, overflowed3) = 255u8.overflowing_add(1);
    assert!(overflowed3, "255 + 1 should overflow");
    assert_eq!(result3, 0, "Should wrap to 0");

    // Test edge case: adding 0 never overflows
    let (result4, overflowed4) = 255u8.overflowing_add(0);
    assert!(!overflowed4, "Adding 0 should not overflow");
    assert_eq!(result4, 255, "Should equal 255");

    println!("test_overflowing_add_wrapping PASS");
}

/// Test that lower bound from max() is preserved through overflowing_add
pub fn test_overflowing_add_preserves_lower_bound() {
    for x in 0..50u8 {
        // max(x, 10) >= 10 (MaxLower gives lower bound 10)
        let lower_bounded = std::cmp::max(x, 10);
        // overflowing_add result = lower_bounded + 5 >= 10
        let (result, overflowed) = lower_bounded.overflowing_add(5);
        if !overflowed {
            assert!(result >= 10, "Lower bound not preserved: {} < 10", result);
        }
    }
    println!("test_overflowing_add_preserves_lower_bound PASS");
}

/// Compare overflowing_add with checked_add behavior
pub fn test_overflowing_add_vs_checked() {
    for a in 0u8..=255u8 {
        for b in 0u8..=10u8 {
            let checked = a.checked_add(b);
            let (result, overflowed) = a.overflowing_add(b);

            match checked {
                Some(val) => {
                    assert!(!overflowed, "checked Some implies no overflow for {} + {}", a, b);
                    assert_eq!(val, result, "Results should match for {} + {}", a, b);
                }
                None => {
                    assert!(overflowed, "checked None implies overflow for {} + {}", a, b);
                }
            }
        }
    }
    println!("test_overflowing_add_vs_checked PASS");
}

/// Test overflowing_add with signed integers
pub fn test_overflowing_add_signed() {
    // Positive overflow: i8::MAX + 1
    let (result, overflowed) = 127i8.overflowing_add(1);
    assert!(overflowed, "127 + 1 should overflow for i8");
    assert_eq!(result, -128, "Should wrap to -128");

    // Negative overflow: i8::MIN + (-1)
    let (result2, overflowed2) = (-128i8).overflowing_add(-1);
    assert!(overflowed2, "-128 + (-1) should overflow for i8");
    assert_eq!(result2, 127, "Should wrap to 127");

    // No overflow case
    let (result3, overflowed3) = 50i8.overflowing_add(25);
    assert!(!overflowed3, "50 + 25 should not overflow for i8");
    assert_eq!(result3, 75, "Should equal 75");

    println!("test_overflowing_add_signed PASS");
}

/// Test overflowing_add with larger integer types
pub fn test_overflowing_add_u32() {
    // Test wrapping at u32 boundary
    let (result, overflowed) = u32::MAX.overflowing_add(1);
    assert!(overflowed, "u32::MAX + 1 should overflow");
    assert_eq!(result, 0, "Should wrap to 0");

    // Test non-overflow case
    let (result2, overflowed2) = 1_000_000u32.overflowing_add(2_000_000);
    assert!(!overflowed2, "Should not overflow");
    assert_eq!(result2, 3_000_000, "Should equal 3_000_000");

    println!("test_overflowing_add_u32 PASS");
}

/// Test safe array access using .get() pattern
pub fn test_overflowing_add_safe_array_get() {
    let arr: [u8; 256] = [42u8; 256];
    let mut access_count = 0;

    // Pattern: use overflowing_add and .get() for safe access
    for x in 0..250usize {
        let (idx, overflowed) = x.overflowing_add(5);
        // Use .get() for safe access when overflow didn't occur
        if !overflowed {
            if let Some(&val) = arr.get(idx) {
                assert_eq!(val, 42);
                access_count += 1;
            }
        }
    }

    assert_eq!(access_count, 250, "Should have accessed 250 times");
    println!("test_overflowing_add_safe_array_get PASS");
}

/// Test overflowing_add matches wrapping_add when overflow occurs
pub fn test_overflowing_add_matches_wrapping() {
    for a in 0u8..=255u8 {
        for b in 0u8..=10u8 {
            let (overflowing_result, _) = a.overflowing_add(b);
            let wrapping_result = a.wrapping_add(b);
            assert_eq!(
                overflowing_result, wrapping_result,
                "overflowing_add and wrapping_add should produce same result for {} + {}",
                a, b
            );
        }
    }
    println!("test_overflowing_add_matches_wrapping PASS");
}

/// Test overflowing_add tuple destructuring pattern
pub fn test_overflowing_add_tuple_pattern() {
    // Test various tuple destructuring patterns
    let a: u8 = 100;
    let b: u8 = 50;

    // Pattern 1: Direct destructuring
    let (sum, overflow) = a.overflowing_add(b);
    assert_eq!(sum, 150);
    assert!(!overflow);

    // Pattern 2: Named tuple fields
    let result = a.overflowing_add(b);
    assert_eq!(result.0, 150);
    assert!(!result.1);

    // Pattern 3: Ignoring overflow flag
    let (sum2, _) = a.overflowing_add(b);
    assert_eq!(sum2, 150);

    println!("test_overflowing_add_tuple_pattern PASS");
}

/// Test overflowing_add with usize
pub fn test_overflowing_add_usize() {
    // These tests are platform-independent behavior
    let (result, overflowed) = 100usize.overflowing_add(200);
    assert_eq!(result, 300);
    assert!(!overflowed);

    // Test with large values that don't overflow on 64-bit
    let (result2, overflowed2) = (usize::MAX - 10).overflowing_add(5);
    assert_eq!(result2, usize::MAX - 5);
    assert!(!overflowed2);

    // Test overflow
    let (result3, overflowed3) = usize::MAX.overflowing_add(1);
    assert_eq!(result3, 0);
    assert!(overflowed3);

    println!("test_overflowing_add_usize PASS");
}

pub fn main() {
    // Test overflow detection
    test_overflowing_add_overflow_detection();

    // Test wrapping behavior
    test_overflowing_add_wrapping();

    // Test lower bound preservation
    test_overflowing_add_preserves_lower_bound();

    // Compare with checked_add
    test_overflowing_add_vs_checked();

    // Test signed integers
    test_overflowing_add_signed();

    // Test u32
    test_overflowing_add_u32();

    // Test safe array access with .get()
    test_overflowing_add_safe_array_get();

    // Test matches wrapping_add
    test_overflowing_add_matches_wrapping();

    // Test tuple patterns
    test_overflowing_add_tuple_pattern();

    // Test usize
    test_overflowing_add_usize();

    println!("\nAll overflowing_add bounds tests passed!");
}
