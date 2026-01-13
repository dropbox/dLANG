//! Shift overflow checking test
//!
//! This file demonstrates automatic verification of shift operations.
//! Shift overflow occurs when the shift amount >= bit_width.
//!
//! For u32: bit_width = 32, so shift amount must be 0..31
//! For u64: bit_width = 64, so shift amount must be 0..63
//!
//! Phase 4.7: Automatic Shift Overflow Checking
//!
//! NOTE: This test has intentionally unsafe functions to verify that
//! the automatic shift overflow checker detects them.

// This function should PASS - constant shift amount < bit_width
fn safe_constant_shift(x: u32) -> u32 {
    x << 16  // OK: 16 < 32 (bit_width of u32)
}

// This function should PASS - constant shift amount at edge
fn safe_edge_shift(x: u32) -> u32 {
    x << 31  // OK: 31 < 32 (bit_width of u32)
}

// This function should PASS - right shift with constant
fn safe_right_shift(x: u64) -> u64 {
    x >> 32  // OK: 32 < 64 (bit_width of u64)
}

// This function should PASS - shift with precondition constraining amount
#[requires("amount < 32")]
fn safe_dynamic_shift(x: u32, amount: u32) -> u32 {
    x << amount  // OK: precondition ensures amount < 32
}

// This function should PASS - shift with combined preconditions
#[requires("amount < 64")]
fn safe_dynamic_right_shift(x: u64, amount: u32) -> u64 {
    x >> amount  // OK: precondition ensures amount < 64
}

// This function should FAIL - dynamic shift without constraint
fn unsafe_dynamic_shift(x: u32, amount: u32) -> u32 {
    x << amount  // ERROR: amount could be >= 32
}

// This function should FAIL - dynamic right shift without constraint
fn unsafe_dynamic_right_shift(x: u64, amount: u32) -> u64 {
    x >> amount  // ERROR: amount could be >= 64
}

// This function should PASS - shift amount constrained by control flow
fn guarded_shift(x: u32, amount: u32) -> u32 {
    if amount < 32 {
        x << amount  // OK: path condition proves amount < 32
    } else {
        0
    }
}

// This function should PASS - shift amount bounded by mask
fn masked_shift(x: u32, amount: u32) -> u32 {
    let safe_amount = amount & 0x1F;  // 0..31 after mask
    x << safe_amount  // OK: mask ensures safe_amount < 32
}

fn main() {
    println!("safe_constant_shift(0x12345678) = {:#010x}", safe_constant_shift(0x12345678));
    println!("safe_edge_shift(1) = {}", safe_edge_shift(1));
    println!("safe_right_shift(0xDEADBEEFCAFEBABE) = {:#018x}", safe_right_shift(0xDEADBEEFCAFEBABE));
    println!("safe_dynamic_shift(1, 16) = {}", safe_dynamic_shift(1, 16));
    println!("safe_dynamic_right_shift(0xFFFFFFFFFFFFFFFF, 32) = {:#018x}", safe_dynamic_right_shift(0xFFFFFFFFFFFFFFFF, 32));
    println!("guarded_shift(1, 16) = {}", guarded_shift(1, 16));
    println!("masked_shift(1, 100) = {}", masked_shift(1, 100));
}
