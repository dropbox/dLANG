//! Modulo bound propagation test
//!
//! This file is meant to be verified with `rustc -Zverify`.
//!
//! The key property:
//! - For unsigned types and positive divisor m: `x % m` is always in `[0, m-1]`.
//!
//! tRust uses this to avoid false positives in:
//! - Array bounds checks (e.g., `arr[idx % len]` for `[T; len]`)
//! - Ring buffer indexing
//! - Circular queue implementations

// Modulo with constant divisor bounds result to 0..255 (256-1).
fn modulo_index(x: u32) -> u8 {
    let idx = x % 256;
    idx as u8  // Safe: idx is always < 256, so fits in u8
}

// Array index with modulo ensures bounds.
fn safe_array_access(arr: &[u8; 256], idx: usize) -> u8 {
    let safe_idx = idx % 256;
    arr[safe_idx]  // Always in bounds: safe_idx < 256
}

// Ring buffer pattern: circular index
// Note: Using wrapping_add to avoid overflow check since modulo handles wraparound.
fn ring_buffer_index(base: usize, offset: usize) -> usize {
    let capacity = 128usize;
    base.wrapping_add(offset) % capacity  // Result is always < capacity
}

// Addition after modulo cannot overflow when the divisor is small enough.
fn add_modulo_values(a: u8, b: u8) -> u8 {
    let div = 128u8;
    let mod_a = a % div;  // 0..127
    let mod_b = b % div;  // 0..127
    mod_a + mod_b  // 127 + 127 = 254 <= 255, no overflow
}

// Small array access with constant modulo.
fn small_array_access(arr: &[i32; 16], idx: usize) -> i32 {
    let safe_idx = idx % 16;
    arr[safe_idx]
}

// Combined: modulo followed by bitand (both provide bounds).
fn combined_bounds(x: u32) -> u8 {
    let step1 = x % 1000;  // 0..999
    let step2 = step1 & 0xFF;  // 0..255
    step2 as u8
}

// Variable capacity pattern (constant must be known at compile time for bounds).
fn hash_slot(hash: u64) -> usize {
    let table_size = 64usize;
    (hash as usize) % table_size  // Result is always < 64
}

fn main() {
    println!("modulo_index(1000) = {}", modulo_index(1000));

    let arr = [0u8; 256];
    println!("safe_array_access([0; 256], 999) = {}", safe_array_access(&arr, 999));

    println!("ring_buffer_index(100, 50) = {}", ring_buffer_index(100, 50));

    println!("add_modulo_values(200, 200) = {}", add_modulo_values(200, 200));

    let arr16 = [0i32; 16];
    println!("small_array_access([0; 16], 100) = {}", small_array_access(&arr16, 100));

    println!("combined_bounds(12345) = {}", combined_bounds(12345));

    println!("hash_slot(12345) = {}", hash_slot(12345));
}
