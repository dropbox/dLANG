//! Multiplication Bounds Test
//!
//! This example demonstrates how tRust propagates upper bounds through multiplication operations.
//! When an operand with a known upper bound is multiplied by a constant,
//! the result inherits a product upper bound (if it doesn't overflow).
//!
//! Test with:
//!   ./build/host/stage1/bin/rustc examples/multiplication_bounds_test.rs -Zverify
//!
//! Expected: No verification errors for safe array accesses.

fn main() {
    let table = [0u8; 256];

    // Test case 1: Mask then multiply
    // (x & 0xF) gives upper bound of 15
    // (x & 0xF) * 16 gives upper bound of 15 * 16 = 240
    // 240 < 256, so this is safe
    for x in 0u32..1000 {
        let masked = x & 0xF;       // upper bound = 15
        let product = masked * 16;  // upper bound = 15 * 16 = 240
        let idx = product as usize;
        let _ = table[idx];         // SAFE: 240 < 256
    }

    // Test case 2: Modulo then multiply
    // x % 16 gives upper bound of 15
    // (x % 16) * 10 gives upper bound of 150
    // 150 < 256, so this is safe
    for x in 0u32..1000 {
        let remainder = x % 16;       // upper bound = 15
        let product = remainder * 10; // upper bound = 150
        let idx = product as usize;
        let _ = table[idx];           // SAFE: 150 < 256
    }

    // Test case 3: Right shift then multiply
    // For u8: x >> 6 gives upper bound of 3 (255 >> 6 = 3)
    // (x >> 6) * 50 gives upper bound of 3 * 50 = 150
    for x in 0u8..=255 {
        let shifted = x >> 6;         // upper bound = 3
        let product = shifted * 50;   // upper bound = 150
        let idx = product as usize;
        let _ = table[idx];           // SAFE: 150 < 256
    }

    // Test case 4: Chained operations - mask then multiply then add
    // (x & 0x7) has upper bound 7
    // (x & 0x7) * 32 has upper bound 224
    for x in 0u32..1000 {
        let masked = x & 0x7;           // upper bound = 7
        let product = masked * 32;      // upper bound = 224
        let idx = product as usize;
        let _ = table[idx];             // SAFE: 224 < 256
    }

    // Test case 5: Small multiplier with tight bounds
    let small_table = [0u8; 64];
    for x in 0u32..1000 {
        let masked = x & 0xF;         // upper bound = 15
        let product = masked * 4;     // upper bound = 15 * 4 = 60
        let idx = product as usize;
        let _ = small_table[idx];     // SAFE: 60 < 64
    }

    // Test case 6: Division then multiply (common scaling pattern)
    // For u32: x / 1000 gives upper bound of 4_294_967
    // But if x is itself bounded (e.g., x < 10000), (x / 100) * 2 is bounded
    // Using modulo to create initial bound: x % 100 <= 99
    // (x % 100) * 2 <= 198
    for x in 0u32..1000 {
        let remainder = x % 100;      // upper bound = 99
        let product = remainder * 2;  // upper bound = 198
        let idx = product as usize;
        let _ = table[idx];           // SAFE: 198 < 256
    }

    // Test case 7: Commutative multiplication - constant on left
    // 10 * (x & 0x1F) = 10 * value where value <= 31
    // Upper bound = 10 * 31 = 310 > 256, but we'll use a smaller constant
    let medium_table = [0u8; 200];
    for x in 0u32..1000 {
        let masked = x & 0xF;         // upper bound = 15
        let product = 12 * masked;    // upper bound = 12 * 15 = 180
        let idx = product as usize;
        let _ = medium_table[idx];    // SAFE: 180 < 200
    }

    // Test case 8: Mask with multiply producing exact bound
    // (x & 0x3) has upper bound 3
    // (x & 0x3) * 63 has upper bound 189
    for x in 0u32..1000 {
        let masked = x & 0x3;         // upper bound = 3
        let product = masked * 63;    // upper bound = 189
        let idx = product as usize;
        let _ = medium_table[idx];    // SAFE: 189 < 200
    }

    // Test case 9: Combined mask + multiply for stride patterns
    // This is a common pattern for row-major array indexing
    let row_data = [0u8; 128]; // 8 rows * 16 columns
    for row in 0u32..100 {
        let row_idx = row & 0x7;        // upper bound = 7
        let offset = row_idx * 16;      // upper bound = 7 * 16 = 112
        let idx = offset as usize;
        let _ = row_data[idx];          // SAFE: 112 < 128
    }

    // Test case 10: Multiple chained operations
    // (x >> 4) & 0xF has upper bound 15 (mask dominates)
    // ((x >> 4) & 0xF) * 16 has upper bound 240
    for x in 0u32..65536 {
        let shifted = x >> 4;            // For u32: upper bound = 268_435_455 (too large)
        let masked = shifted & 0xF;      // upper bound = 15 (mask provides bound)
        let product = masked * 16;       // upper bound = 240
        let idx = product as usize;
        let _ = table[idx];              // SAFE: 240 < 256
    }

    println!("All multiplication bounds tests passed!");
}
