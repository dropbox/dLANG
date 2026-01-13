// Addition bounds propagation test
//
// This test verifies that tRust's -Zverify can track upper bounds
// through addition operations where one operand has known bounds
// and the other is a constant.
//
// Pattern: (x & mask) + constant => upper bound = mask + constant
// Pattern: (x % modulo) + constant => upper bound = (modulo - 1) + constant

fn main() {
    // === Test 1: BitAnd + constant addition ===
    // x & 0xF has upper bound 15
    // (x & 0xF) + 10 has upper bound 25
    let table1: [u8; 32] = [0; 32];
    for x in 0u32..1000 {
        let masked = x & 0xF;       // upper bound = 15
        let offset = masked + 10;   // upper bound = 25 (AddWithOverflow in debug)
        let idx = offset as usize;
        // VERIFIED SAFE: 25 < 32
        let _ = table1[idx];
    }

    // === Test 2: Modulo + constant addition ===
    // x % 16 has upper bound 15
    // (x % 16) + 5 has upper bound 20
    let table2: [u8; 24] = [0; 24];
    for x in 0u32..500 {
        let modded = x % 16;        // upper bound = 15
        let offset = modded + 5;    // upper bound = 20
        let idx = offset as usize;
        // VERIFIED SAFE: 20 < 24
        let _ = table2[idx];
    }

    // === Test 3: RightShift + constant addition ===
    // For u32, x >> 30 has upper bound 3
    // (x >> 30) + 4 has upper bound 7
    let table3: [u8; 8] = [0; 8];
    for x in 0u32..100 {
        let shifted = x >> 30;      // upper bound = 3
        let offset = shifted + 4;   // upper bound = 7
        let idx = offset as usize;
        // VERIFIED SAFE: 7 < 8
        let _ = table3[idx];
    }

    // === Test 4: Chained operations ===
    // (x & 0x7) * 2 has upper bound 14
    // ((x & 0x7) * 2) + 1 has upper bound 15
    let table4: [u8; 16] = [0; 16];
    for x in 0u32..200 {
        let masked = x & 0x7;       // upper bound = 7
        let doubled = masked * 2;   // upper bound = 14
        let offset = doubled + 1;   // upper bound = 15
        let idx = offset as usize;
        // VERIFIED SAFE: 15 < 16
        let _ = table4[idx];
    }

    // === Test 5: Commutative addition (constant + bounded) ===
    // constant + (x & mask)
    let table5: [u8; 26] = [0; 26];
    for x in 0u32..300 {
        let masked = x & 0xF;       // upper bound = 15
        let offset = 10 + masked;   // upper bound = 25 (commutative)
        let idx = offset as usize;
        // VERIFIED SAFE: 25 < 26
        let _ = table5[idx];
    }

    // === Test 6: Direct constant addition (usize type) ===
    // For usize addition bounds propagation
    let table6: [u8; 32] = [0; 32];
    for x in 0usize..100 {
        let masked = x & 0xF;       // upper bound = 15
        let offset = masked + 10;   // upper bound = 25
        // VERIFIED SAFE: 25 < 32
        let _ = table6[offset];
    }

    // === Test 7: Multiple additions ===
    // ((x & 0x3) + 5) + 3 => upper bound = 3 + 5 + 3 = 11
    let table7: [u8; 16] = [0; 16];
    for x in 0u32..100 {
        let masked = x & 0x3;       // upper bound = 3
        let step1 = masked + 5;     // upper bound = 8
        let step2 = step1 + 3;      // upper bound = 11
        let idx = step2 as usize;
        // VERIFIED SAFE: 11 < 16
        let _ = table7[idx];
    }

    // === Test 8: Division + addition ===
    // For u32 / 1000000000, upper bound is ~4
    // (x / 1000000000) + 2 has upper bound = 4 + 2 = 6
    let table8: [u8; 8] = [0; 8];
    for x in 0u32..100 {
        let divided = x / 1000000000; // upper bound = 4 (u32::MAX / 1000000000)
        let offset = divided + 2;     // upper bound = 6
        let idx = offset as usize;
        // VERIFIED SAFE: 6 < 8
        let _ = table8[idx];
    }

    println!("All addition bounds tests passed!");
}
