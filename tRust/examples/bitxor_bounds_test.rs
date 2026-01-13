//! Bitwise XOR bounds propagation test for tRust `-Zverify`.
//!
//! Run with:
//! `upstream/rustc/build/host/stage1/bin/rustc -Zverify examples/bitxor_bounds_test.rs -o /tmp/bitxor_bounds_test`
//!
//! XOR key properties for verification:
//!   - x ^ 0 == x (identity)
//!   - x ^ x == 0 (self-cancellation)
//!   - (x ^ y) ^ y == x (toggle/restore property)
//!   - For bounded x: x ^ mask <= max(x_max, mask) + min(x_max, mask) (loose bound)

fn main() {
    test_xor_identity();
    test_xor_self_cancel();
    test_xor_toggle_restore();
    test_xor_mask_bounds();
    test_xor_swap_pattern();
    test_xor_checksum_pattern();
}

/// Test: x ^ 0 == x (XOR identity property)
fn test_xor_identity() {
    let x: u8 = get_arbitrary_u8();
    let result = x ^ 0;
    assert!(result == x);
}

/// Test: x ^ x == 0 (XOR self-cancellation)
fn test_xor_self_cancel() {
    let x: u32 = get_arbitrary_u32();
    let result = x ^ x;
    assert!(result == 0);
}

/// Test: (x ^ y) ^ y == x (XOR toggle/restore property)
/// This is fundamental for encryption and checksum patterns
fn test_xor_toggle_restore() {
    let x: u16 = get_arbitrary_u16();
    let key: u16 = 0xABCD;
    let encrypted = x ^ key;
    let decrypted = encrypted ^ key;
    assert!(decrypted == x);
}

/// Test: XOR with small mask has bounded upper bits
/// When XORing a bounded value with a mask, we can reason about the result
fn test_xor_mask_bounds() {
    let x: u8 = get_arbitrary_u8();
    // Mask off low 4 bits first with AND
    let masked = x & 0xF0; // masked is in [0, 240] with low nibble = 0
    // XOR with 0x0F toggles exactly the low 4 bits
    let result = masked ^ 0x0F;
    // Result is in [0x0F, 0xFF] - low nibble is always 0x0F
    // Since masked had low nibble 0, XOR 0x0F gives low nibble 0x0F
    // So result >= 0x0F
    assert!(result >= 0x0F);
}

/// Test: XOR swap pattern (classic swap without temp variable)
/// a' = a ^ b, b' = a' ^ b = a, a'' = a' ^ b' = b
fn test_xor_swap_pattern() {
    let mut a: u8 = 5;
    let mut b: u8 = 10;
    let orig_a = a;
    let orig_b = b;

    a = a ^ b;    // a = 5 ^ 10 = 15
    b = a ^ b;    // b = 15 ^ 10 = 5 (original a)
    a = a ^ b;    // a = 15 ^ 5 = 10 (original b)

    assert!(a == orig_b);
    assert!(b == orig_a);
}

/// Test: XOR used in checksum/parity calculation
/// The verifier should understand that XOR accumulates parity
fn test_xor_checksum_pattern() {
    let bytes: [u8; 4] = [0xAB, 0xCD, 0xEF, 0x12];
    let checksum = bytes[0] ^ bytes[1] ^ bytes[2] ^ bytes[3];
    // Checksum is bounded by u8 type (0-255)
    // We can't predict the exact value without the inputs, but we can verify
    // that XOR operations preserve the bit width
    assert!(checksum <= 255);
}

/// Test: XOR with constant mask preserves some bits
/// If we know bits are set in the mask and the input, we know bits in output
fn test_xor_bit_preservation() {
    let x: u8 = get_arbitrary_u8();
    // Force high bit to be set via OR
    let high_set = x | 0x80;  // high_set >= 128
    // XOR with 0x0F only affects low nibble, preserves high bit
    let result = high_set ^ 0x0F;
    // High bit (0x80) is preserved since 0x0F doesn't touch it
    // If high_set had high bit set (guaranteed by OR), result still has it set
    // Actually, we can verify result is in [0x80 ^ 0x0F, 0xFF ^ 0x0F] = [0x8F, 0xF0] ...
    // Better: The high nibble is unchanged, so result >= 0x80 still holds
    assert!(result >= 0x80);
}

/// Test: XOR double application restores original (cryptographic property)
fn test_xor_round_trip() {
    let data: u32 = get_arbitrary_u32();
    let key: u32 = 0xDEADBEEF;

    let step1 = data ^ key;
    let step2 = step1 ^ key;

    assert!(step2 == data);
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
