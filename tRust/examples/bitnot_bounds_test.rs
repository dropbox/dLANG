//! Bitwise NOT bounds propagation test for tRust `-Zverify`.
//!
//! Run with:
//! `upstream/rustc/build/host/stage1/bin/rustc -Zverify examples/bitnot_bounds_test.rs -o /tmp/bitnot_bounds_test`
//!
//! This test exercises the pattern:
//!   y = x | 0xF0        ==> y >= 0xF0
//!   idx = !y            ==> idx <= 0x0F
//!   table[idx as usize] ==> VERIFIED SAFE (idx < 16)

fn bitnot_after_or_bounds(x: u8) -> u8 {
    let table: [u8; 16] = [0; 16];
    let y = x | 0xF0;
    let idx = !y;
    table[idx as usize]
}

fn bitnot_after_or_bounds_commuted(x: u8) -> u8 {
    let table: [u8; 16] = [0; 16];
    let y = 0xF0 | x;
    let idx = !y;
    table[idx as usize]
}

fn main() {
    let _ = bitnot_after_or_bounds(0);
    let _ = bitnot_after_or_bounds_commuted(0);
}

