// Test wrapping_add bounds propagation
// x.wrapping_add(y) provides bounds ONLY when no overflow is guaranteed:
// - operand must have known lower and upper bounds
// - addend must be a constant
// - operand_upper + addend <= type_max (no overflow)
// - Then result has lower bound = operand_lower, upper bound = operand_upper + addend
//
// This is useful for safe array indexing when adding known constants
// to bounded values, where we can prove the addition won't wrap.

fn test_wrapping_add_after_clamp() {
    // ClampBounds provides both lower (5) and upper (20) bounds
    let arr: [u8; 64] = [0; 64];

    for x in 0..100u8 {
        // x.clamp(5, 20) gives 5 <= result <= 20 (ClampBounds)
        let clamped = x.clamp(5, 20);
        // wrapping_add with constant 10:
        // upper (20) + 10 = 30 <= 255, so no overflow
        // Result has lower = 5, upper = 30
        let result = clamped.wrapping_add(10);
        // result <= 30 < 64, safe for array access
        let _ = arr[result as usize];
    }
    println!("test_wrapping_add_after_clamp PASS");
}

fn test_wrapping_add_after_max() {
    // max(x & mask, const) provides both bounds
    let arr: [u8; 64] = [0; 64];

    for x in 0..200u8 {
        // x & 0x1F <= 31 (BitAndMask gives upper bound 31)
        let masked = x & 0x1F;
        // max(masked, 10) >= 10, and inherits upper bound 31
        let bounded = std::cmp::max(masked, 10);
        // wrapping_add with constant 15:
        // upper (31) + 15 = 46 <= 255, so no overflow
        // Result has lower = 10, upper = 46
        let result = bounded.wrapping_add(15);
        // result <= 46 < 64, safe for array access
        let _ = arr[result as usize];
    }
    println!("test_wrapping_add_after_max PASS");
}

fn test_wrapping_add_with_min_and_max() {
    // Combine min and max for precise bounds
    let arr: [u8; 100] = [0; 100];

    for x in 0..100u8 {
        // min(x, 50) <= 50 (upper bound from MinUpper)
        let upper_bounded = std::cmp::min(x, 50);
        // max(upper_bounded, 20) >= 20, inherits upper = 50
        let bounded = std::cmp::max(upper_bounded, 20);
        // wrapping_add with constant 30:
        // upper (50) + 30 = 80 <= 255, so no overflow
        // Result has lower = 20, upper = 80
        let result = bounded.wrapping_add(30);
        // result <= 80 < 100, safe
        let _ = arr[result as usize];
    }
    println!("test_wrapping_add_with_min_and_max PASS");
}

fn test_wrapping_add_exact_max() {
    // Test when upper + addend exactly equals type_max
    let arr: [u8; 256] = [0; 256];

    for x in 0..100u8 {
        // x.clamp(100, 200) gives 100 <= result <= 200
        let clamped = x.clamp(100, 200);
        // wrapping_add with constant 55:
        // upper (200) + 55 = 255 = type_max, so still no overflow
        // Result has lower = 100, upper = 255
        let result = clamped.wrapping_add(55);
        // result <= 255 < 256, safe
        let _ = arr[result as usize];
    }
    println!("test_wrapping_add_exact_max PASS");
}

fn test_wrapping_add_vs_checked_add() {
    // Compare wrapping_add and checked_add behavior
    // When no overflow: both produce same result

    for x in 0..=200u8 {
        let base = x.clamp(10, 50);  // 10 <= base <= 50
        // Adding 100: 50 + 100 = 150 <= 255, no overflow
        let wrapping_result = base.wrapping_add(100);
        let checked_result = base.checked_add(100);
        assert_eq!(Some(wrapping_result), checked_result,
            "When no overflow, results should match");
    }
    println!("test_wrapping_add_vs_checked_add PASS");
}

fn test_wrapping_add_vs_saturating_add() {
    // Compare wrapping_add and saturating_add behavior
    // When no overflow: both produce same result

    for x in 0..=100u8 {
        let base = x.clamp(5, 30);  // 5 <= base <= 30
        // Adding 50: 30 + 50 = 80 <= 255, no overflow
        let wrapping_result = base.wrapping_add(50);
        let saturating_result = base.saturating_add(50);
        assert_eq!(wrapping_result, saturating_result,
            "When no overflow, results should match");
    }
    println!("test_wrapping_add_vs_saturating_add PASS");
}

fn test_wrapping_add_runtime_verification() {
    // Runtime verification that wrapping_add behaves correctly
    // when we prove no overflow occurs

    for base in 0..=100u8 {
        for add in 0..=50u8 {
            // When base + add <= 255, wrapping_add equals checked_add.unwrap()
            if let Some(checked_result) = base.checked_add(add) {
                let wrapping_result = base.wrapping_add(add);
                assert_eq!(wrapping_result, checked_result,
                    "base={}, add={}: wrapping and checked should match", base, add);
            }
        }
    }
    println!("test_wrapping_add_runtime_verification PASS");
}

fn main() {
    test_wrapping_add_after_clamp();
    test_wrapping_add_after_max();
    test_wrapping_add_with_min_and_max();
    test_wrapping_add_exact_max();
    test_wrapping_add_vs_checked_add();
    test_wrapping_add_vs_saturating_add();
    test_wrapping_add_runtime_verification();
    println!("\nAll wrapping_add bounds tests passed!");
}
