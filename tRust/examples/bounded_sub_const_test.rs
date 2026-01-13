// SubtractionUpper bounds propagation test
//
// This test verifies that tRust's -Zverify can track upper bounds
// through subtraction where: bounded_x - constant
//
// Pattern: (x & mask) - constant => upper bound = mask - constant (when constant <= mask)
//
// Uses std::cmp::max() to establish lower bounds that the verifier tracks via MaxLower.
// The if-guard pattern (if masked >= 5) isn't tracked by the verifier.

fn main() {
    // === Test 1: BitAnd - constant ===
    // x & 0x1F has upper bound 31
    // max(masked, 5) has lower bound 5, upper bound 31
    // max(masked, 5) - 5 has upper bound 26
    let table1: [u8; 32] = [0; 32];
    for x in 0u32..1000 {
        let masked = x & 0x1F;                    // upper bound = 31
        let lower_bounded = std::cmp::max(masked, 5);  // lower = 5, upper = 31
        let offset = lower_bounded - 5;           // upper bound = 26
        let idx = offset as usize;
        // VERIFIED SAFE: 26 < 32
        let _ = table1[idx];
    }

    // === Test 2: Modulo - constant ===
    // x % 32 has upper bound 31
    // max(modded, 10) - 10 has upper bound 21
    let table2: [u8; 24] = [0; 24];
    for x in 0u32..500 {
        let modded = x % 32;                      // upper bound = 31
        let lower_bounded = std::cmp::max(modded, 10);  // lower = 10, upper = 31
        let offset = lower_bounded - 10;          // upper bound = 21
        let idx = offset as usize;
        // VERIFIED SAFE: 21 < 24
        let _ = table2[idx];
    }

    // === Test 3: Chained: (x & mask) + constant - constant2 ===
    // (x & 0xF) + 10 has upper bound 25
    // max(added, 3) - 3 has upper bound 22
    let table3: [u8; 24] = [0; 24];
    for x in 0u32..100 {
        let masked = x & 0xF;                     // upper bound = 15
        let added = masked.saturating_add(10);    // upper bound = 25 (saturating preserves u32 range)
        let lower_bounded = std::cmp::max(added, 3);  // lower = 3, upper = 25
        let offset = lower_bounded - 3;           // upper bound = 22
        let idx = offset as usize;
        // VERIFIED SAFE: 22 < 24
        let _ = table3[idx];
    }

    println!("All bounded_sub_const tests passed!");
}
