// Test max bounds propagation for std::cmp::max
// max(x, const) should have lower bound = const

fn main() {
    test_max_bounds();
    test_max_bounds_chained();
    test_max_inherits_upper();
    println!("All max bounds tests passed!");
}

fn test_max_bounds() {
    // max(x, 5) guarantees result >= 5
    for x in 0u32..100 {
        let result = std::cmp::max(x, 5);
        // SHOULD BE VERIFIED: result >= 5
        assert!(result >= 5);
    }
    println!("test_max_bounds: PASS");
}

fn test_max_bounds_chained() {
    // Chaining max with min to clamp to a range
    // clamp(x, 5, 10) = max(min(x, 10), 5)
    // Result should be in range [5, 10]
    let arr = [0u8; 16];

    for x in 0u32..100 {
        // First min(x, 10) gives upper = 10
        let clamped_upper = std::cmp::min(x, 10);
        // Then max(_, 5) gives lower = 5, inherits upper = 10
        let clamped = std::cmp::max(clamped_upper, 5);
        // Result is in [5, 10], safe for arr[16]
        let idx = clamped as usize;
        // SHOULD BE VERIFIED SAFE: 5 <= idx <= 10 < 16
        let _ = arr[idx];
    }
    println!("test_max_bounds_chained: PASS");
}

fn test_max_inherits_upper() {
    // When operand has upper bound, max inherits it
    let arr = [0u8; 32];

    for x in 0u32..256 {
        // x & 0x1F gives upper = 31
        let masked = x & 0x1F;
        // max(masked, 5) should inherit upper = 31
        let result = std::cmp::max(masked, 5);
        let idx = result as usize;
        // SHOULD BE VERIFIED SAFE: result <= 31 < 32
        let _ = arr[idx];
    }
    println!("test_max_inherits_upper: PASS");
}
