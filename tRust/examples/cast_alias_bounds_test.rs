//! Cast aliasing bounds propagation test
//!
//! This file tests that bounds flow through integer cast operations.
//! For example, `(x >> 24) as usize` should inherit the bounds from `x >> 24`.
//!
//! Run with: ./build/host/stage1/bin/rustc -Zverify examples/cast_alias_bounds_test.rs

// Right shift then cast to usize for array indexing.
// x >> 24 on u32 gives 0..255, which should flow through the cast.
fn array_index_from_shift(arr: &[u8; 256], x: u32) -> u8 {
    let shifted = x >> 24;  // 0..255
    let idx = shifted as usize;  // CastAlias should propagate bounds
    arr[idx]  // Should verify: idx <= 255 < 256
}

// Multiple shifts with cast chain.
fn chained_shift_cast(arr: &[u8; 16], x: u64) -> u8 {
    let step1 = x >> 60;  // 0..15 (u64::MAX >> 60 = 15)
    let step2 = step1 as u32;  // CastAlias: 0..15
    let idx = step2 as usize;  // CastAlias: 0..15
    arr[idx]  // Should verify: idx <= 15 < 16
}

// BitAnd mask then cast.
fn bitand_cast_index(arr: &[u8; 128], x: u32) -> u8 {
    let masked = x & 0x7F;  // 0..127
    let idx = masked as usize;  // CastAlias should propagate bounds
    arr[idx]  // Should verify: idx <= 127 < 128
}

// Modulo then cast.
fn modulo_cast_index(arr: &[u8; 64], x: u32) -> u8 {
    let remainder = x % 64;  // 0..63
    let idx = remainder as usize;  // CastAlias should propagate bounds
    arr[idx]  // Should verify: idx <= 63 < 64
}

// Combination: shift, mask, then cast.
fn shift_mask_cast_index(arr: &[u8; 16], x: u32) -> u8 {
    let shifted = x >> 28;  // 0..15 (u32::MAX >> 28 = 15)
    let masked = shifted & 0x0F;  // 0..15 (redundant but tests double bounds)
    let idx = masked as usize;  // CastAlias from BitAndMask
    arr[idx]  // Should verify: idx <= 15 < 16
}

// Cast from u64 to smaller type then to usize.
fn u64_to_u8_to_usize(arr: &[u8; 256], x: u64) -> u8 {
    let shifted = x >> 56;  // 0..255 (u64::MAX >> 56 = 255)
    let byte = shifted as u8;  // CastAlias: 0..255
    let idx = byte as usize;  // CastAlias: 0..255
    arr[idx]  // Should verify: idx <= 255 < 256
}

// Signed to unsigned cast after ensuring positive bounds.
// Note: This only works if we recognize the bounds from the mask.
fn signed_mask_cast(arr: &[u8; 64], x: i32) -> u8 {
    // x & 0x3F on signed i32: result is 0..63 because mask clears sign bit
    let masked = x & 0x3F;  // 0..63 (BitAndMask for signed with positive mask)
    let idx = masked as usize;  // CastAlias from BitAndMask
    arr[idx]  // Should verify: idx <= 63 < 64
}

// Division by power of two (equivalent to right shift) then cast.
fn div_power_of_two_cast(arr: &[u8; 16], x: u32) -> u8 {
    // x / 268435456 is equivalent to x >> 28, giving 0..15
    let divided = x / 268435456;  // 0..15
    let idx = divided as usize;
    // Note: Division bounds are not yet tracked, so this may fail.
    // This is here to document the limitation.
    arr[idx % 16]  // Use modulo as fallback
}

fn main() {
    let arr256 = [0u8; 256];
    let arr128 = [0u8; 128];
    let arr64 = [0u8; 64];
    let arr16 = [0u8; 16];

    println!("array_index_from_shift: {}", array_index_from_shift(&arr256, 0xDEADBEEF));
    println!("chained_shift_cast: {}", chained_shift_cast(&arr16, 0xDEADBEEFCAFEBABE));
    println!("bitand_cast_index: {}", bitand_cast_index(&arr128, 0xDEADBEEF));
    println!("modulo_cast_index: {}", modulo_cast_index(&arr64, 0xDEADBEEF));
    println!("shift_mask_cast_index: {}", shift_mask_cast_index(&arr16, 0xDEADBEEF));
    println!("u64_to_u8_to_usize: {}", u64_to_u8_to_usize(&arr256, 0xDEADBEEFCAFEBABE));
    println!("signed_mask_cast: {}", signed_mask_cast(&arr64, -12345));
    println!("div_power_of_two_cast: {}", div_power_of_two_cast(&arr16, 0xDEADBEEF));
}
