// Test min bounds propagation for std::cmp::min
// min(x, const) should have upper bound = const

fn main() {
    test_min_bounds();
    test_min_bounds_var();
    println!("All min bounds tests passed!");
}

fn test_min_bounds() {
    let arr = [0u8; 32];

    for x in 0u32..1000 {
        // min(x, 31) should have upper bound = 31
        let idx = std::cmp::min(x, 31) as usize;
        // SHOULD BE VERIFIED SAFE: idx <= 31 < 32
        let _ = arr[idx];
    }
    println!("test_min_bounds: PASS");
}

fn test_min_bounds_var() {
    let arr = [0u8; 16];

    for x in 0u32..1000 {
        // min(x, 15) should have upper bound = 15
        let idx = std::cmp::min(x, 15) as usize;
        // SHOULD BE VERIFIED SAFE: idx <= 15 < 16
        let _ = arr[idx];
    }
    println!("test_min_bounds_var: PASS");
}
