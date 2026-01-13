// Test checked_mul bounds propagation via path conditions
// x.checked_mul(y) returns Some(x * y) when no overflow occurs
//
// CheckedMulRelation provides:
// - result >= 0 (for unsigned types)
// - result = operand * multiplier (exact SMT relation)
//
// This allows the SMT solver to derive bounds from path conditions:
// - If path condition constrains operand (e.g., operand < 32)
// - And multiplier is a constant literal (e.g., 2)
// - Then result < 64 (safe for array[64])
//
// Limitations:
// - Multiplier must be a constant literal, not a local variable
// - Operand path conditions must come directly from control flow

/// Test that checked_mul bounds are propagated through path conditions
/// When x < 32 and checked_mul returns Some:
/// - result = x * 2
/// - From path condition: x < 32
/// - Therefore: result < 64
pub fn test_checked_mul_array_access(data: &[u8; 64], x: usize) -> u8 {
    // Path condition: x < 32
    // If checked_mul(x, 2) returns Some:
    //   result = x * 2 < 32 * 2 = 64
    // So array access is safe
    if x < 32 {
        if let Some(idx) = x.checked_mul(2) {
            return data[idx];
        }
    }
    0
}

/// Test with larger multiplier
pub fn test_checked_mul_by_4(data: &[u8; 256], x: usize) -> u8 {
    // Path condition: x < 64
    // result = x * 4 < 64 * 4 = 256
    if x < 64 {
        if let Some(idx) = x.checked_mul(4) {
            return data[idx];
        }
    }
    0
}

/// Test with smaller array
pub fn test_checked_mul_small_array(data: &[u8; 100], x: usize) -> u8 {
    // Path condition: x < 25
    // result = x * 4 < 25 * 4 = 100
    if x < 25 {
        if let Some(idx) = x.checked_mul(4) {
            return data[idx];
        }
    }
    0
}

/// Test edge case: multiplier of 1
pub fn test_checked_mul_one(data: &[u8; 256], x: usize) -> u8 {
    // Path condition: x < 256
    // result = x * 1 < 256
    if x < 256 {
        if let Some(idx) = x.checked_mul(1) {
            return data[idx];
        }
    }
    0
}

/// Test checked_mul with clamp (provides both bounds directly)
pub fn test_checked_mul_with_clamp(data: &[u8; 256], x: usize) -> u8 {
    // clamp(x, 1, 50) gives 1 <= result <= 50
    // checked_mul(result, 5): 1 * 5 <= idx <= 50 * 5
    // So idx <= 250 < 256
    let clamped = x.clamp(1, 50);
    if let Some(idx) = clamped.checked_mul(5) {
        return data[idx];
    }
    0
}

/// Test multiplication by 8 (common for struct indexing)
pub fn test_checked_mul_struct_offset(data: &[u8; 256], x: usize) -> u8 {
    // Path condition: x < 32
    // result = x * 8 < 32 * 8 = 256
    // Common pattern: array of 8-byte structs
    if x < 32 {
        if let Some(idx) = x.checked_mul(8) {
            return data[idx];
        }
    }
    0
}

/// Demonstrate overflow detection with checked_mul
pub fn test_checked_mul_overflow_detection() {
    let mut overflow_count = 0u32;
    let mut success_count = 0u32;

    // Use range that produces both successes and overflows
    // 100*2=200 (ok), 100*3=300 (overflow for u8 max 255)
    for a in 100u8..=127u8 {
        for b in 2u8..=5u8 {
            match a.checked_mul(b) {
                Some(_product) => success_count += 1,
                None => overflow_count += 1,
            }
        }
    }

    assert!(success_count > 0);
    assert!(overflow_count > 0);
    println!("test_checked_mul_overflow_detection PASS (success: {}, overflow: {})",
             success_count, overflow_count);
}

/// Runtime verification that the bounds logic is correct
pub fn test_checked_mul_runtime_verification() {
    let arr: [u8; 64] = [42u8; 64];

    // Verify path condition logic
    for x in 0..32usize {
        if let Some(idx) = x.checked_mul(2) {
            assert!(idx < 64, "Index {} should be < 64", idx);
            let _ = arr[idx]; // This access is always safe
        }
    }
    println!("test_checked_mul_runtime_verification PASS");
}

/// Test combined with checked_add for complex indexing
pub fn test_checked_mul_then_add(data: &[u8; 256], x: usize) -> u8 {
    // Path condition: x < 30
    // mul_result = x * 8 < 30 * 8 = 240
    // add_result = mul_result + 10 < 240 + 10 = 250 < 256
    if x < 30 {
        if let Some(offset) = x.checked_mul(8) {
            if let Some(idx) = offset.checked_add(10) {
                return data[idx];
            }
        }
    }
    0
}

pub fn main() {
    let arr64 = [0u8; 64];
    let arr100 = [0u8; 100];
    let arr256 = [0u8; 256];

    // Test path-condition-based array access (these should verify)
    let _ = test_checked_mul_array_access(&arr64, 20);
    let _ = test_checked_mul_by_4(&arr256, 50);
    let _ = test_checked_mul_small_array(&arr100, 20);
    let _ = test_checked_mul_one(&arr256, 100);
    let _ = test_checked_mul_with_clamp(&arr256, 45);
    let _ = test_checked_mul_struct_offset(&arr256, 25);
    let _ = test_checked_mul_then_add(&arr256, 25);

    // Test overflow detection
    test_checked_mul_overflow_detection();

    // Runtime verification
    test_checked_mul_runtime_verification();

    println!("\nAll checked_mul bounds tests passed!");
}
