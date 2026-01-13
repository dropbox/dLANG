// Test: checked_sub bounds propagation
// When checked_sub returns Some, we know no underflow occurred
// and result <= operand (subtraction decreases value)

/// Test that checked_sub bounds are propagated through path conditions
pub fn test_checked_sub_array_access(data: &[u8; 256], x: usize, y: usize) -> u8 {
    // When x < 256 and checked_sub returns Some:
    // - x >= y (no underflow)
    // - result = x - y <= x < 256
    // So the array access is safe
    if x < 256 {
        if let Some(idx) = x.checked_sub(y) {
            return data[idx];
        }
    }
    0
}

/// Test with explicit bounds
pub fn test_checked_sub_explicit(data: &[u8; 100], x: usize, y: usize) -> u8 {
    if x < 100 {
        if let Some(idx) = x.checked_sub(y) {
            // idx = x - y where x < 100, so idx < 100
            return data[idx];
        }
    }
    0
}

pub fn main() {
    let arr256 = [0u8; 256];
    let arr100 = [0u8; 100];
    let _ = test_checked_sub_array_access(&arr256, 200, 50);
    let _ = test_checked_sub_explicit(&arr100, 50, 10);
}
