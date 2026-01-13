// Level 3 Test: Arithmetic operations
// Tests: integer ops, float ops, overflow behavior

fn main() {
    // Integer arithmetic
    let a: i32 = 42;
    let b: i32 = 17;
    println!("i32 add: {} + {} = {}", a, b, a + b);
    println!("i32 sub: {} - {} = {}", a, b, a - b);
    println!("i32 mul: {} * {} = {}", a, b, a * b);
    println!("i32 div: {} / {} = {}", a, b, a / b);
    println!("i32 rem: {} % {} = {}", a, b, a % b);

    // Unsigned arithmetic
    let c: u64 = 1000000000000u64;
    let d: u64 = 999999999u64;
    println!("u64 mul: {} * {} = {}", c, d, c.saturating_mul(d));
    println!("u64 div: {} / {} = {}", c, d, c / d);

    // Float arithmetic
    let x: f64 = 3.14159265358979;
    let y: f64 = 2.71828182845904;
    println!("f64 add: {:.10}", x + y);
    println!("f64 sub: {:.10}", x - y);
    println!("f64 mul: {:.10}", x * y);
    println!("f64 div: {:.10}", x / y);
    println!("f64 sqrt: {:.10}", x.sqrt());
    println!("f64 sin: {:.10}", x.sin());
    println!("f64 cos: {:.10}", x.cos());

    // Edge cases
    println!("i32::MAX: {}", i32::MAX);
    println!("i32::MIN: {}", i32::MIN);
    println!("u64::MAX: {}", u64::MAX);

    // Wrapping operations
    let max = i32::MAX;
    println!("wrapping_add: {}", max.wrapping_add(1));
    println!("wrapping_mul: {}", max.wrapping_mul(2));

    // Saturating operations
    println!("saturating_add: {}", max.saturating_add(100));
    println!("saturating_sub: {}", 0i32.saturating_sub(100));

    // Bitwise
    let bits: u32 = 0b10101010;
    println!("and: {:08b}", bits & 0xFF);
    println!("or: {:08b}", bits | 0x0F);
    println!("xor: {:08b}", bits ^ 0xFF);
    println!("shl: {:08b}", bits << 2);
    println!("shr: {:08b}", bits >> 2);
    println!("not: {:08b}", !bits & 0xFF);
    println!("count_ones: {}", bits.count_ones());
    println!("leading_zeros: {}", bits.leading_zeros());
    println!("trailing_zeros: {}", bits.trailing_zeros());
}
