// ConstSubtractionUpper bounds propagation test
//
// This test verifies that tRust's -Zverify can track upper bounds
// through subtraction where: constant - bounded_x
//
// Pattern: const - (x & mask) => upper bound = const (when mask <= const)
// The result of (const - x) where x has upper bound <= const is bounded by [0, const]

fn main() {
    // === Test 1: const - (x & mask) ===
    // x & 0x1F has upper bound 31
    // 31 - (x & 0x1F) has upper bound 31 (ConstSubtractionUpper)
    let table1: [u8; 32] = [0; 32];
    for x in 0u32..1000 {
        let masked = x & 0x1F;        // upper bound = 31
        let inverted = 31 - masked;   // upper bound = 31 (const - bounded)
        let idx = inverted as usize;
        // VERIFIED SAFE: 31 < 32
        let _ = table1[idx];
    }

    // === Test 2: const - (x % divisor) ===
    // x % 16 has upper bound 15
    // 20 - (x % 16) has upper bound 20
    let table2: [u8; 24] = [0; 24];
    for x in 0u32..500 {
        let modded = x % 16;          // upper bound = 15
        let subtracted = 20 - modded; // upper bound = 20 (const - bounded)
        let idx = subtracted as usize;
        // VERIFIED SAFE: 20 < 24
        let _ = table2[idx];
    }

    // === Test 3: const - (chained bounded) ===
    // (x & 0x7) has upper bound 7
    // ((x & 0x7) * 2) has upper bound 14
    // 15 - ((x & 0x7) * 2) has upper bound 15
    let table3: [u8; 16] = [0; 16];
    for x in 0u32..100 {
        let masked = x & 0x7;         // upper bound = 7
        let doubled = masked * 2;     // upper bound = 14
        let result = 15 - doubled;    // upper bound = 15 (const - bounded)
        let idx = result as usize;
        // VERIFIED SAFE: 15 < 16
        let _ = table3[idx];
    }

    println!("All const_sub_bounded tests passed!");
}
