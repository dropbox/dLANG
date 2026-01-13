// BitOr Lower Bound Propagation Test
//
// This test validates that the verifier correctly propagates lower bounds
// through bitwise OR operations: x | mask >= mask
//
// The key insight: OR can only set bits, never clear them.
// So if we OR any value with a constant mask, the result is at least as large as the mask.

fn main() {
    test_basic_bitor_lower_bound();
    test_bitor_with_flag_setting();
    test_bitor_commutative();
    test_bitor_floor_guarantee();
}

/// Basic test: x | mask >= mask
/// For any u8 value x, x | 0x80 >= 128 (bit 7 always set)
fn test_basic_bitor_lower_bound() {
    let x: u8 = get_arbitrary_u8();
    let result = x | 0x80; // Set high bit

    // The verifier should know: result >= 128
    // This can be useful for ensuring a value is in a certain range
    assert!(result >= 128);
}

/// Test: Setting flags ensures minimum value
/// Common pattern: setting bits to ensure alignment or flags
fn test_bitor_with_flag_setting() {
    let x: u32 = get_arbitrary_u32();
    let with_flags = x | 0x0F00_0000; // Set upper nibble of third byte

    // The verifier should know: with_flags >= 0x0F00_0000 (251658240)
    assert!(with_flags >= 0x0F00_0000);
}

/// Test: BitOr is commutative, bounds should work either way
fn test_bitor_commutative() {
    let x: u16 = get_arbitrary_u16();
    let result1 = x | 0x00F0;    // mask on right
    let result2 = 0x00F0 | x;    // mask on left (same thing)

    // Both should give lower bound of 240
    assert!(result1 >= 0x00F0);
    assert!(result2 >= 0x00F0);
}

/// Test: BitOr provides a floor guarantee
/// Useful for ensuring minimum values in protocols
fn test_bitor_floor_guarantee() {
    let protocol_version: u8 = get_arbitrary_u8();
    // Ensure version is at least 1 by setting bit 0
    let safe_version = protocol_version | 0x01;

    // The verifier should know: safe_version >= 1
    assert!(safe_version >= 1);

    // This is useful for avoiding division by zero, etc.
}

// External functions to prevent constant folding
#[inline(never)]
fn get_arbitrary_u8() -> u8 {
    0
}

#[inline(never)]
fn get_arbitrary_u16() -> u16 {
    0
}

#[inline(never)]
fn get_arbitrary_u32() -> u32 {
    0
}
