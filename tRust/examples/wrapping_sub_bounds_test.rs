// Test wrapping_sub bounds propagation
// x.wrapping_sub(y) provides bounds ONLY when no underflow is guaranteed:
// - operand must have lower bound >= subtrahend (constant)
// - operand must have upper bound U
// - Then result has upper bound U (subtraction can only decrease the value)
//
// This is useful for safe array indexing when subtracting known constants
// from bounded values, where we can prove the subtraction won't wrap.

fn test_wrapping_sub_after_clamp() {
    // ClampBounds provides both lower (10) and upper (20) bounds
    let arr: [u8; 32] = [0; 32];

    for x in 0..100u8 {
        // x.clamp(10, 20) gives 10 <= result <= 20 (ClampBounds)
        let clamped = x.clamp(10, 20);
        // wrapping_sub with constant 5: since lower_bound (10) >= 5, no underflow
        // Result has upper bound 20 (inherited from clamped)
        let result = clamped.wrapping_sub(5);
        // result <= 20 < 32, safe for array access
        let _ = arr[result as usize];
    }
    println!("test_wrapping_sub_after_clamp PASS");
}

fn test_wrapping_sub_after_max() {
    // max(x, const) provides lower bound = const
    // Combined with mask for upper bound
    let arr: [u8; 32] = [0; 32];

    for x in 0..200u8 {
        // x & 0x1F <= 31 (BitAndMask gives upper bound 31)
        let masked = x & 0x1F;
        // max(masked, 10) >= 10, and inherits upper bound 31
        let bounded = std::cmp::max(masked, 10);
        // wrapping_sub with constant 8: since lower_bound (10) >= 8, no underflow
        // Result has upper bound 31 (inherited)
        let result = bounded.wrapping_sub(8);
        // result <= 31 < 32, safe for array access
        let _ = arr[result as usize];
    }
    println!("test_wrapping_sub_after_max PASS");
}

fn test_wrapping_sub_chain() {
    // Test chained wrapping_sub operations
    let arr: [u8; 32] = [0; 32];

    for x in 0..200u8 {
        // x.clamp(15, 25) gives 15 <= result <= 25
        let clamped = x.clamp(15, 25);
        // First wrapping_sub: lower (15) >= 3, so no underflow, upper = 25
        let r1 = clamped.wrapping_sub(3);
        // Second wrapping_sub would need r1's bounds:
        // r1 inherits upper = 25 and has lower = 0 (from WrappingSubUpper)
        // Since we can't prove r1 >= 5 (lower is 0), no bounds propagation
        // This test validates the first subtraction works
        let _ = arr[r1 as usize];
    }
    println!("test_wrapping_sub_chain PASS");
}

fn test_wrapping_sub_with_min_upper() {
    // min(x, const) provides upper bound
    // Combined with max for lower bound
    let arr: [u8; 64] = [0; 64];

    for x in 0..100u8 {
        // min(x, 50) <= 50 (upper bound from MinUpper)
        let upper_bounded = std::cmp::min(x, 50);
        // max(upper_bounded, 20) >= 20, inherits upper = 50
        let bounded = std::cmp::max(upper_bounded, 20);
        // wrapping_sub with constant 15: since lower (20) >= 15, no underflow
        // Result has upper bound 50
        let result = bounded.wrapping_sub(15);
        // result <= 50 < 64, safe
        let _ = arr[result as usize];
    }
    println!("test_wrapping_sub_with_min_upper PASS");
}

fn test_wrapping_sub_vs_saturating_sub() {
    // Compare wrapping_sub and saturating_sub behavior
    // When no underflow: both produce same result
    // When underflow: wrapping wraps, saturating clamps to 0

    for x in 0..=50u8 {
        let base = x.max(30);  // >= 30
        // Both should give same result when subtracting 20 (30 >= 20)
        let wrapping_result = base.wrapping_sub(20);
        let saturating_result = base.saturating_sub(20);
        assert_eq!(wrapping_result, saturating_result,
            "When no underflow, results should match");
    }
    println!("test_wrapping_sub_vs_saturating_sub PASS");
}

fn test_wrapping_sub_exact_lower_bound() {
    // Test when lower bound exactly equals subtrahend
    let arr: [u8; 32] = [0; 32];

    for x in 0..100u8 {
        // x.clamp(5, 20) gives 5 <= result <= 20
        let clamped = x.clamp(5, 20);
        // wrapping_sub with constant 5: since lower_bound (5) >= 5, no underflow
        // Result is 0 to 15 (upper bound 20)
        let result = clamped.wrapping_sub(5);
        // result <= 20 < 32, safe
        let _ = arr[result as usize];
    }
    println!("test_wrapping_sub_exact_lower_bound PASS");
}

fn test_wrapping_sub_runtime_verification() {
    // Runtime verification that wrapping_sub behaves correctly
    // when we prove no underflow occurs

    for base in 10..=100u8 {
        for sub in 0..=10u8 {
            // When base >= sub, wrapping_sub equals checked_sub.unwrap()
            if let Some(checked_result) = base.checked_sub(sub) {
                let wrapping_result = base.wrapping_sub(sub);
                assert_eq!(wrapping_result, checked_result,
                    "base={}, sub={}: wrapping and checked should match", base, sub);
            }
        }
    }
    println!("test_wrapping_sub_runtime_verification PASS");
}

fn main() {
    test_wrapping_sub_after_clamp();
    test_wrapping_sub_after_max();
    test_wrapping_sub_chain();
    test_wrapping_sub_with_min_upper();
    test_wrapping_sub_vs_saturating_sub();
    test_wrapping_sub_exact_lower_bound();
    test_wrapping_sub_runtime_verification();
    println!("\nAll wrapping_sub bounds tests passed!");
}
