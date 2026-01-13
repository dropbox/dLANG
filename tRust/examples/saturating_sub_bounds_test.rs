// Test saturating_sub bounds propagation
// x.saturating_sub(y) provides:
// - result >= 0 (saturates at 0)
// - result <= x (subtraction can only decrease)
//
// If x has upper bound M, then x.saturating_sub(y) also has upper bound M.

fn test_basic_saturating_sub() {
    let arr: [u8; 16] = [0; 16];

    for i in 0..20u8 {
        // i & 0x0F <= 15
        let bounded = i & 0x0F;
        // saturating_sub preserves upper bound: bounded.saturating_sub(5) <= 15
        // Even though we subtract 5, the upper bound is still 15 (worst case: 15 - 0 = 15)
        let result = bounded.saturating_sub(5);
        // Safe: result <= 15 < 16
        let _ = arr[result as usize];
    }
    println!("test_basic_saturating_sub PASS");
}

fn test_saturating_sub_chained() {
    let arr: [u8; 8] = [0; 8];

    for x in 0..100u8 {
        // x & 0x07 <= 7
        let masked = x & 0x07;
        // masked.saturating_sub(any) <= 7
        let result = masked.saturating_sub(2);
        // Safe: result <= 7 < 8
        let _ = arr[result as usize];
    }
    println!("test_saturating_sub_chained PASS");
}

fn test_saturating_sub_with_max() {
    let arr: [u8; 16] = [0; 16];

    for i in 0..50u8 {
        // max(i, 3) >= 3
        let lower_bounded = std::cmp::max(i, 3);
        // min(lower_bounded, 15) has both: >= 3, <= 15
        let bounded = std::cmp::min(lower_bounded, 15);
        // bounded.saturating_sub(any) <= 15
        let result = bounded.saturating_sub(10);
        // Safe: result <= 15 < 16
        let _ = arr[result as usize];
    }
    println!("test_saturating_sub_with_max PASS");
}

fn test_saturating_sub_multiple() {
    let arr: [u8; 32] = [0; 32];

    for x in 0..200u8 {
        // x & 0x1F <= 31
        let masked = x & 0x1F;
        // Multiple saturating_sub calls preserve upper bound
        let result1 = masked.saturating_sub(5);
        let result2 = result1.saturating_sub(3);
        let result3 = result2.saturating_sub(1);
        // Safe: result3 <= 31 < 32
        let _ = arr[result3 as usize];
    }
    println!("test_saturating_sub_multiple PASS");
}

fn test_saturating_sub_vs_regular_sub() {
    // This test demonstrates why saturating_sub is useful:
    // Regular subtraction can underflow, but saturating_sub saturates at 0
    let arr: [u8; 10] = [0; 10];

    for i in 0..20u8 {
        let bounded = i % 10;  // 0 <= bounded <= 9
        // saturating_sub(5) gives 0..=9 (saturates at 0)
        // whereas bounded - 5 could underflow for bounded < 5
        let result = bounded.saturating_sub(5);
        // Safe: 0 <= result <= 9 < 10
        let _ = arr[result as usize];
    }
    println!("test_saturating_sub_vs_regular_sub PASS");
}

fn test_saturating_sub_with_clamp() {
    let arr: [u8; 20] = [0; 20];

    for x in 0..100u8 {
        // x.clamp(5, 19) gives 5 <= result <= 19
        let clamped = x.clamp(5, 19);
        // saturating_sub preserves upper: result <= 19
        let result = clamped.saturating_sub(7);
        // Safe: result <= 19 < 20
        let _ = arr[result as usize];
    }
    println!("test_saturating_sub_with_clamp PASS");
}

fn main() {
    test_basic_saturating_sub();
    test_saturating_sub_chained();
    test_saturating_sub_with_max();
    test_saturating_sub_multiple();
    test_saturating_sub_vs_regular_sub();
    test_saturating_sub_with_clamp();
    println!("\nAll saturating_sub bounds tests passed!");
}
