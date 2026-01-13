// Test file for automatic overflow checking
// This file demonstrates what tRust should detect automatically

// This function should FAIL verification - overflow is possible
fn add(a: u8, b: u8) -> u8 {
    a + b  // ERROR: overflow possible when a=200, b=100
}

// This function should PASS - uses checked arithmetic
fn safe_add(a: u8, b: u8) -> Option<u8> {
    a.checked_add(b)  // OK: returns None on overflow
}

// This function should FAIL - subtraction underflow possible
fn subtract(a: u8, b: u8) -> u8 {
    a - b  // ERROR: underflow possible when b > a
}

// This function should FAIL - multiplication overflow possible
fn multiply(a: u8, b: u8) -> u8 {
    a * b  // ERROR: overflow possible
}

// This function should FAIL - division by zero possible
fn divide(a: u32, b: u32) -> u32 {
    a / b  // ERROR: division by zero possible
}

// This function PASSES with path-sensitive analysis
// The if-guard provides a path condition: when a + b executes, a < 100 && b < 100 holds
fn add_constrained(a: u8, b: u8) -> u8 {
    if a < 100 && b < 100 {
        a + b  // OK: path condition proves 99 + 99 = 198 <= 255
    } else {
        0
    }
}

fn main() {
    println!("add(1, 2) = {}", add(1, 2));
    println!("safe_add(200, 100) = {:?}", safe_add(200, 100));
    println!("subtract(5, 3) = {}", subtract(5, 3));
    println!("multiply(10, 20) = {}", multiply(10, 20));
    println!("divide(10, 2) = {}", divide(10, 2));
}
