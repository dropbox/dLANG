//! Left Shift Bounds Test
//!
//! This example demonstrates how tRust propagates upper bounds through left shift operations.
//! When an operand with a known upper bound is left-shifted by a constant amount,
//! the result inherits a shifted upper bound (if it doesn't overflow).
//!
//! Test with:
//!   ./build/host/stage1/bin/rustc examples/left_shift_bounds_test.rs -Zverify
//!
//! Expected: No verification errors for safe array accesses.

fn main() {
    let table = [0u8; 256];

    // Test case 1: Mask then shift
    // (x & 0xF) gives upper bound of 15
    // (x & 0xF) << 4 gives upper bound of 15 << 4 = 240
    // 240 < 256, so this is safe
    for x in 0u32..1000 {
        let masked = x & 0xF;       // upper bound = 15
        let shifted = masked << 4;  // upper bound = 15 << 4 = 240
        let idx = shifted as usize;
        let _ = table[idx];         // SAFE: 240 < 256
    }

    // Test case 2: Modulo then shift
    // x % 16 gives upper bound of 15
    // (x % 16) << 4 gives upper bound of 240
    for x in 0u32..1000 {
        let remainder = x % 16;     // upper bound = 15
        let shifted = remainder << 4; // upper bound = 240
        let idx = shifted as usize;
        let _ = table[idx];         // SAFE: 240 < 256
    }

    // Test case 3: Right shift then left shift
    // For u8: x >> 5 gives upper bound of 7 (255 >> 5 = 7)
    // (x >> 5) << 2 gives upper bound of 7 << 2 = 28
    let small_table = [0u8; 32];
    for x in 0u8..=255 {
        let right_shifted = x >> 5;   // upper bound = 7
        let left_shifted = right_shifted << 2; // upper bound = 28
        let idx = left_shifted as usize;
        let _ = small_table[idx];     // SAFE: 28 < 32
    }

    // Test case 4: Chained operations with mask at end
    // Even if shift could overflow, final mask makes it safe
    for x in 0u32..1000 {
        let shifted = (x & 0xFF) << 2; // (x & 255) << 2 gives max 1020
        let final_idx = (shifted & 0xFF) as usize; // mask brings it down to 255
        let _ = table[final_idx];      // SAFE: mask ensures < 256
    }

    // Test case 5: Small shift amounts on masked values
    let tiny_table = [0u8; 64];
    for x in 0u32..1000 {
        let masked = x & 0xF;         // upper bound = 15
        let shifted = masked << 2;    // upper bound = 15 << 2 = 60
        let idx = shifted as usize;
        let _ = tiny_table[idx];      // SAFE: 60 < 64
    }

    // Test case 6: Shift then mask (alternative safe pattern)
    // Even if shifted value is large, final mask makes it safe
    let lookup_table = [0u8; 128];
    for x in 0u32..1000 {
        let shifted = (x & 0xFF) << 3;    // Could be up to 2040
        let final_idx = (shifted & 0x7F) as usize; // Mask brings to 0..127
        let _ = lookup_table[final_idx];  // SAFE: mask ensures < 128
    }

    // Test case 7: Multiple shifts with mask
    // (x & 0x3) has upper bound 3
    // (x & 0x3) << 3 has upper bound 24
    // ((x & 0x3) << 3) as usize indexes into table of 32
    let tiny_lookup = [0u8; 32];
    for x in 0u32..100 {
        let masked = x & 0x3;            // upper bound = 3
        let shifted = masked << 3;       // upper bound = 24
        let idx = shifted as usize;
        let _ = tiny_lookup[idx];        // SAFE: 24 < 32
    }

    println!("All left shift bounds tests passed!");
}
