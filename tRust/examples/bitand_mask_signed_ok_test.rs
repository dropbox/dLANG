//! Signed BitAnd mask bound propagation (positive mask) test
//!
//! This file is meant to be verified with `rustc -Zverify`.
//!
//! Goal:
//! - For signed integers, `x & 0x7F` clears the sign bit, so the result is in [0, 127].
//! - That bound should flow through `as usize` casts and prove array indexing safe.

fn safe_signed_index(arr: &[u8; 128], x: i8) -> u8 {
    let masked = x & 0x7F;
    let idx = masked as usize;
    arr[idx]
}

fn main() {
    let arr = [0u8; 128];
    let _ = safe_signed_index(&arr, -1);
}

