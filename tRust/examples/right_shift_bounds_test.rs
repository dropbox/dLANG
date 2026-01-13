//! Right shift bound propagation test
//!
//! This file is meant to be verified with `rustc -Zverify`.
//!
//! The key property:
//! - For unsigned types: `x >> n` is always in `[0, type_max >> n]`.
//!
//! tRust uses this to avoid false positives in:
//! - Byte extraction from larger integers
//! - Converting larger types to smaller ones after shifting
//! - Division by powers of two

// Right shift with constant shrinks the range.
// u32::MAX >> 24 = 255, so result fits in u8.
fn extract_high_byte(x: u32) -> u8 {
    let shifted = x >> 24;
    shifted as u8  // Safe: shifted is always <= 255
}

// Right shift by 16 on u32 gives 16-bit value.
fn extract_high_word(x: u32) -> u16 {
    let shifted = x >> 16;
    shifted as u16  // Safe: shifted is always <= 65535
}

// Shift amount larger than type's value range.
fn large_shift(x: u64) -> u8 {
    let shifted = x >> 56;  // Result is always <= 255 (u64::MAX >> 56)
    shifted as u8
}

// Array index after right shift with cast aliasing.
// CastAlias propagates bounds through cast operations, so `(x >> 24) as usize`
// inherits the bounds [0, 255] from the shift operation.
fn array_index_from_shift(arr: &[u8; 256], x: u32) -> u8 {
    let shifted = x >> 24;  // 0..255
    let idx = shifted as usize;  // CastAlias propagates bounds: 0..255
    arr[idx]  // Safe: idx <= 255 < 256
}

// Right shift combined with addition.
fn shift_then_add(a: u32, b: u32) -> u16 {
    let shifted_a = a >> 24;  // 0..255
    let shifted_b = b >> 24;  // 0..255
    // 255 + 255 = 510 <= 65535, so result fits in u16
    (shifted_a + shifted_b) as u16
}

// Multiple shifts to extract nibbles.
fn extract_nibble(x: u8) -> u8 {
    let high = x >> 4;  // 0..15
    high + high  // 15 + 15 = 30, no overflow in u8
}

// Division emulated by right shift (shift by log2 of divisor).
fn divide_by_power_of_two(x: u64) -> u32 {
    let divided = x >> 32;  // Same as x / 2^32, result <= u32::MAX
    divided as u32
}

// Chained shifts.
fn chained_shifts(x: u64) -> u8 {
    let step1 = x >> 32;  // 0..u32::MAX
    let step2 = step1 >> 24;  // 0..255
    step2 as u8
}

// Shift then mask - both provide bounds.
fn shift_and_mask(x: u32) -> u8 {
    let shifted = x >> 16;  // 0..65535
    let masked = shifted & 0xFF;  // 0..255
    masked as u8
}

fn main() {
    println!("extract_high_byte(0xDEADBEEF) = {:#04x}", extract_high_byte(0xDEADBEEF));
    println!("extract_high_word(0xDEADBEEF) = {:#06x}", extract_high_word(0xDEADBEEF));
    println!("large_shift(0xDEADBEEFCAFEBABE) = {:#04x}", large_shift(0xDEADBEEFCAFEBABE));

    let arr = [0u8; 256];
    println!("array_index_from_shift([0; 256], 0xDEADBEEF) = {}",
             array_index_from_shift(&arr, 0xDEADBEEF));

    println!("shift_then_add(0xFF000000, 0xFF000000) = {}", shift_then_add(0xFF000000, 0xFF000000));
    println!("extract_nibble(0xAB) = {}", extract_nibble(0xAB));
    println!("divide_by_power_of_two(0xFFFFFFFF00000000) = {:#010x}",
             divide_by_power_of_two(0xFFFFFFFF00000000));
    println!("chained_shifts(0xDEADBEEFCAFEBABE) = {:#04x}", chained_shifts(0xDEADBEEFCAFEBABE));
    println!("shift_and_mask(0xDEADBEEF) = {:#04x}", shift_and_mask(0xDEADBEEF));
}
