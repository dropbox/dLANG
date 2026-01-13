// Test file for path-sensitive verification
//
// This file demonstrates that tRust's auto-verification uses path conditions
// from control flow guards to prove operations safe within branches.
//
// KEY INSIGHT: Operations guarded by if-conditions inherit those conditions
// as proof obligations. For example:
//
//   if a < 100 && b < 100 {
//       a + b  // Path condition: a < 100 AND b < 100, so max is 198 < 255
//   }
//
// FEATURES DEMONSTRATED:
// - Path conditions from if-guards are tracked and used in verification
// - Intermediate value definitions (e.g., _7 = _1 + _2) propagate bounds through chained operations
// - Division by zero checks with != 0 guards (even when MIR optimizes to direct switchInt)

// SHOULD PASS - if-guard constrains inputs for addition
fn guarded_add(a: u8, b: u8) -> u8 {
    if a < 100 && b < 100 {
        a + b  // OK: 99 + 99 = 198 <= 255
    } else {
        0
    }
}

// SHOULD PASS - if-guard constrains inputs for subtraction
fn guarded_sub(a: u8, b: u8) -> u8 {
    if a >= b {
        a - b  // OK: a >= b means no underflow
    } else {
        0
    }
}

// SHOULD PASS - if-guard constrains divisor for division by zero check
// (Fixed in #98: direct switchInt on parameter now infers != 0 path condition)
fn guarded_div(a: u32, b: u32) -> u32 {
    if b != 0 {
        a / b  // OK: b != 0, path condition from direct switchInt inferred
    } else {
        0
    }
}

// SHOULD PASS - chained operations with nested guards
// Intermediate value tracking: x+y creates _7, defined as _7 = _1 + _2
// SMT solver derives _7 < 100 from _1 < 50 && _2 < 50, then _7 + _3 < 150 < 255
fn nested_guards(x: u8, y: u8, z: u8) -> u8 {
    if x < 50 {
        if y < 50 {
            if z < 50 {
                x + y + z  // OK: x+y < 100, x+y+z < 150 <= 255
            } else {
                0
            }
        } else {
            0
        }
    } else {
        0
    }
}

// SHOULD FAIL - guard is insufficient for multiplication
fn weak_guard_mul(a: u8, b: u8) -> u8 {
    if a < 100 && b < 100 {
        a * b  // ERROR: 99 * 99 = 9801 > 255
    } else {
        0
    }
}

// SHOULD FAIL - no guard at all
fn no_guard(a: u8, b: u8) -> u8 {
    a + b  // ERROR: could overflow
}

fn main() {
    println!("guarded_add(50, 50) = {}", guarded_add(50, 50));
    println!("guarded_sub(100, 50) = {}", guarded_sub(100, 50));
    println!("guarded_div(10, 2) = {}", guarded_div(10, 2));
    println!("nested_guards(10, 20, 30) = {}", nested_guards(10, 20, 30));
    // These should fail verification:
    println!("weak_guard_mul(10, 10) = {}", weak_guard_mul(10, 10));
    println!("no_guard(10, 10) = {}", no_guard(10, 10));
}
