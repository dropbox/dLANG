//! Bitwise AND mask bound propagation test
//!
//! This file is meant to be verified with `rustc -Zverify`.
//!
//! The key property:
//! - For a non-negative constant mask, `x & mask` is always in `[0, mask]`.
//!
//! tRust uses this to avoid false positives in:
//! - Array bounds checks (e.g., `arr[idx & 0xFF]` for `[T; 256]`)
//! - Overflow checks when subsequent arithmetic is guarded by the mask

// BitAnd with mask 0xFF bounds result to 0-255.
fn masked_index(x: u32) -> u8 {
    let masked = x & 0xFF;
    masked as u8
}

// Array index with mask ensures bounds.
// Uses a `mask` local to exercise constant propagation through MIR locals.
fn safe_array_access(arr: &[u8; 256], idx: usize) -> u8 {
    let mask = 0xFFusize;
    let safe_idx = idx & mask;
    arr[safe_idx]
}

// Addition after masking cannot overflow u8 when the mask is small enough.
fn add_masked_values(a: u8, b: u8) -> u8 {
    let mask = 0x7Fu8; // 0..127
    let masked_a = a & mask;
    let masked_b = b & mask;
    masked_a + masked_b // 127 + 127 = 254 <= 255
}

// Nested masking keeps shrinking the upper bound.
fn nested_mask(x: u64) -> u8 {
    let first = x & 0xFFFF; // 0..65535
    let second = first & 0x0F; // 0..15
    second as u8
}

// Hash table index pattern with a constant mask.
fn hash_table_index(hash: u64) -> usize {
    let mask = 0xFFusize;
    (hash as usize) & mask
}

fn main() {
    println!("masked_index(1000) = {}", masked_index(1000));

    let arr = [0u8; 256];
    println!("safe_array_access([0; 256], 999) = {}", safe_array_access(&arr, 999));

    println!("add_masked_values(200, 200) = {}", add_masked_values(200, 200));

    println!("nested_mask(0xABCD) = {}", nested_mask(0xABCD));

    println!("hash_table_index(12345) = {}", hash_table_index(12345));
}
