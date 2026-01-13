//! Signed BitAnd mask soundness regression test
//!
//! This file is meant to be verified with `rustc -Zverify`.
//!
//! Goal:
//! - Ensure the verifier does NOT emit `0 <= (x & mask)` bounds for signed masks that
//!   do not clear the sign bit (e.g., `-1` / `0xFF` for `i8`).
//! - Without an incorrect non-negativity bound, indexing with `(x & -1) as usize` must
//!   be flagged as potentially out-of-bounds.

fn unsafe_signed_index(arr: &[u8; 128], x: i8) -> u8 {
    let masked = x & -1;
    let idx = masked as usize;
    arr[idx]
}

fn main() {
    let arr = [0u8; 128];
    let _ = unsafe_signed_index(&arr, -1);
}

