//! Test Ord::clamp bounds propagation for array index verification
//!
//! This demonstrates that tRust's bounds propagation system can:
//! - Track both lower and upper bounds from x.clamp(min, max)
//! - Verify array index safety when clamp guarantees min <= result <= max
//!
//! Compile with: rustc -Zverify examples/clamp_bounds_test.rs

/// Test 1: Basic clamp for array indexing
/// x.clamp(2, 10) guarantees 2 <= result <= 10
fn test_basic_clamp() {
    let table: [u8; 16] = [0; 16];

    for x in 0u32..100 {
        // clamp guarantees: 2 <= clamped <= 10
        let clamped = x.clamp(2, 10);
        let idx = clamped as usize;
        // VERIFIED SAFE: idx in [2, 10] and 10 < 16
        let _ = table[idx];
    }
}

/// Test 2: Clamp as a replacement for min(max(x, low), high)
/// This is the common pattern that clamp simplifies
fn test_clamp_replaces_min_max() {
    let data: [u8; 32] = [0; 32];

    for i in 0u32..256 {
        // i.clamp(5, 20) is equivalent to max(min(i, 20), 5)
        let bounded = i.clamp(5, 20);
        let idx = bounded as usize;
        // VERIFIED SAFE: idx in [5, 20] and 20 < 32
        let _ = data[idx];
    }
}

/// Test 3: Clamp with u8 type for byte-level bounds
fn test_clamp_u8() {
    let lut: [u8; 64] = [0; 64];

    for byte in 0u8..=255 {
        // clamp to [0, 63] for lookup table indexing
        let idx = byte.clamp(0, 63) as usize;
        // VERIFIED SAFE: idx in [0, 63] and 63 < 64
        let _ = lut[idx];
    }
}

/// Test 4: Clamp with wider range to demonstrate bounds tracking
fn test_clamp_wider_range() {
    let buffer: [u8; 128] = [0; 128];

    for x in 0u64..10000 {
        // clamp to [10, 100]
        let pos = x.clamp(10, 100);
        let idx = pos as usize;
        // VERIFIED SAFE: idx in [10, 100] and 100 < 128
        let _ = buffer[idx];
    }
}

/// Test 5: Clamp with tight bounds (single value)
fn test_clamp_tight_bounds() {
    let single: [u8; 8] = [0; 8];

    for x in 0u32..50 {
        // x.clamp(5, 5) always returns 5
        let idx = x.clamp(5, 5) as usize;
        // VERIFIED SAFE: idx == 5 and 5 < 8
        let _ = single[idx];
    }
}

/// Test 6: Chained operations - clamp then arithmetic
fn test_clamp_then_add() {
    let array: [u8; 32] = [0; 32];

    for x in 0u32..100 {
        // clamp to [0, 15], then add 5
        // Result: [5, 20]
        let clamped = x.clamp(0, 15);
        let idx = (clamped + 5) as usize;
        // VERIFIED SAFE: idx in [5, 20] and 20 < 32
        let _ = array[idx];
    }
}

fn main() {
    test_basic_clamp();
    test_clamp_replaces_min_max();
    test_clamp_u8();
    test_clamp_wider_range();
    test_clamp_tight_bounds();
    test_clamp_then_add();
    println!("All clamp bounds tests passed!");
}
