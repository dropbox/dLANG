// Integration test for leading_zeros/trailing_zeros/leading_ones/trailing_ones builtin contracts
// Phase 2.5.5: Builtin contracts for std library functions

// Test leading_zeros contracts
// Contract: result >= 0 && result <= bit_width && (x == 0 => result == bit_width)
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_leading_zeros_bounds(x: u32) -> u32 {
    x.leading_zeros()
}

#[requires("x == 0")]
#[ensures("result == 32")]
fn test_leading_zeros_zero() -> u32 {
    let x: u32 = 0;
    x.leading_zeros()
}

// Test trailing_zeros contracts
// Contract: result >= 0 && result <= bit_width && (x == 0 => result == bit_width)
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_trailing_zeros_bounds(x: u32) -> u32 {
    x.trailing_zeros()
}

#[requires("x == 0")]
#[ensures("result == 32")]
fn test_trailing_zeros_zero() -> u32 {
    let x: u32 = 0;
    x.trailing_zeros()
}

// Test leading_ones contracts
// Contract: result >= 0 && result <= bit_width
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_leading_ones_bounds(x: u32) -> u32 {
    x.leading_ones()
}

// Test trailing_ones contracts
// Contract: result >= 0 && result <= bit_width
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_trailing_ones_bounds(x: u32) -> u32 {
    x.trailing_ones()
}

// Test with different integer types
#[ensures("result >= 0")]
#[ensures("result <= 8")]
fn test_leading_zeros_u8(x: u8) -> u32 {
    x.leading_zeros()
}

#[ensures("result >= 0")]
#[ensures("result <= 16")]
fn test_leading_zeros_u16(x: u16) -> u32 {
    x.leading_zeros()
}

#[ensures("result >= 0")]
#[ensures("result <= 64")]
fn test_leading_zeros_u64(x: u64) -> u32 {
    x.leading_zeros()
}

// Test signed integer types
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_leading_zeros_i32(x: i32) -> u32 {
    x.leading_zeros()
}

#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_trailing_zeros_i32(x: i32) -> u32 {
    x.trailing_zeros()
}

// Test composition: using leading_zeros result in further computation
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_leading_zeros_composition(x: u32) -> u32 {
    let lz = x.leading_zeros();
    // lz is in [0, 32], so returning it directly is safe
    lz
}

// Test that leading_zeros(0) gives max bits for various types
#[ensures("result == 8")]
fn test_leading_zeros_zero_u8() -> u32 {
    0u8.leading_zeros()
}

#[ensures("result == 16")]
fn test_leading_zeros_zero_u16() -> u32 {
    0u16.leading_zeros()
}

#[ensures("result == 64")]
fn test_leading_zeros_zero_u64() -> u32 {
    0u64.leading_zeros()
}

fn main() {
    // All functions should verify with PROVEN
    println!("Leading/trailing zeros/ones contracts test");
}
