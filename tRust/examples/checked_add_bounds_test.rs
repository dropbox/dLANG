// Test checked_add bounds propagation via path conditions
// x.checked_add(y) returns Some(x + y) when no overflow occurs
//
// CheckedAddRelation provides:
// - result >= 0 (for unsigned types)
// - result = operand + addend (exact SMT relation)
//
// This allows the SMT solver to derive bounds from path conditions:
// - If path condition constrains operand (e.g., operand < 250)
// - And addend is a constant literal (e.g., 5)
// - Then result < 255 (safe for array[256])
//
// Limitations:
// - Addend must be a constant literal, not a local variable
// - Operand path conditions must come directly from control flow

/// Test that checked_add bounds are propagated through path conditions
/// When x < 250 and checked_add returns Some:
/// - result = x + 5
/// - From path condition: x < 250
/// - Therefore: result < 255
pub fn test_checked_add_array_access(data: &[u8; 256], x: usize) -> u8 {
    // Path condition: x < 250
    // If checked_add(x, 5) returns Some:
    //   result = x + 5 < 250 + 5 = 255 < 256
    // So array access is safe
    if x < 250 {
        if let Some(idx) = x.checked_add(5) {
            return data[idx];
        }
    }
    0
}

/// Test with explicit path condition constraint
pub fn test_checked_add_explicit(data: &[u8; 100], x: usize) -> u8 {
    // Path condition: x < 95
    // result = x + 4 < 95 + 4 = 99 < 100
    if x < 95 {
        if let Some(idx) = x.checked_add(4) {
            return data[idx];
        }
    }
    0
}

/// Test tighter constraint for smaller array
pub fn test_checked_add_small_array(data: &[u8; 50], x: usize) -> u8 {
    // Path condition: x < 40
    // result = x + 9 < 40 + 9 = 49 < 50
    if x < 40 {
        if let Some(idx) = x.checked_add(9) {
            return data[idx];
        }
    }
    0
}

/// Test edge case: addend of 0
pub fn test_checked_add_zero(data: &[u8; 256], x: usize) -> u8 {
    // Path condition: x < 256
    // result = x + 0 < 256 + 0 = 256
    // Actually, result = x < 256 (safe)
    if x < 256 {
        if let Some(idx) = x.checked_add(0) {
            return data[idx];
        }
    }
    0
}

/// Test checked_add with clamp (provides both bounds directly)
pub fn test_checked_add_with_clamp(data: &[u8; 256], x: usize) -> u8 {
    // clamp(x, 5, 200) gives 5 <= result <= 200
    // checked_add(result, 50): 5 + 50 <= idx <= 200 + 50
    // So idx <= 250 < 256
    let clamped = x.clamp(5, 200);
    if let Some(idx) = clamped.checked_add(50) {
        return data[idx];
    }
    0
}

/// Test that lower bound from max() is preserved through checked_add
pub fn test_checked_add_preserves_lower_bound() {
    for x in 0..50u8 {
        // max(x, 10) >= 10 (MaxLower gives lower bound 10)
        let lower_bounded = std::cmp::max(x, 10);
        // checked_add result = lower_bounded + 5 >= 10
        if let Some(result) = lower_bounded.checked_add(5) {
            assert!(result >= 10, "Lower bound not preserved");
        }
    }
    println!("test_checked_add_preserves_lower_bound PASS");
}

/// Demonstrate overflow detection with checked_add
pub fn test_checked_add_overflow_detection() {
    let mut overflow_count = 0u32;
    let mut success_count = 0u32;

    for a in 200u8..=255u8 {
        for b in 50u8..=100u8 {
            match a.checked_add(b) {
                Some(_sum) => success_count += 1,
                None => overflow_count += 1,
            }
        }
    }

    assert!(success_count > 0);
    assert!(overflow_count > 0);
    println!("test_checked_add_overflow_detection PASS (success: {}, overflow: {})",
             success_count, overflow_count);
}

/// Runtime verification that the bounds logic is correct
pub fn test_checked_add_runtime_verification() {
    let arr: [u8; 256] = [42u8; 256];

    // Verify path condition logic
    for x in 0..250usize {
        if let Some(idx) = x.checked_add(5) {
            assert!(idx < 256, "Index {} should be < 256", idx);
            let _ = arr[idx]; // This access is always safe
        }
    }
    println!("test_checked_add_runtime_verification PASS");
}

pub fn main() {
    let arr256 = [0u8; 256];
    let arr100 = [0u8; 100];
    let arr50 = [0u8; 50];

    // Test path-condition-based array access (these should verify)
    let _ = test_checked_add_array_access(&arr256, 200);
    let _ = test_checked_add_explicit(&arr100, 50);
    let _ = test_checked_add_small_array(&arr50, 30);
    let _ = test_checked_add_zero(&arr256, 100);
    let _ = test_checked_add_with_clamp(&arr256, 175);

    // Test lower bound preservation
    test_checked_add_preserves_lower_bound();

    // Test overflow detection
    test_checked_add_overflow_detection();

    // Runtime verification
    test_checked_add_runtime_verification();

    println!("\nAll checked_add bounds tests passed!");
}
