// Benchmark: Multiple functions with specifications
// Tests verification scaling with function count

#[requires("x > 0")]
#[requires("x <= 46340")]  // sqrt(i32::MAX) to avoid overflow
#[ensures("result > 0")]
fn square(x: i32) -> i32 {
    x * x
}

#[requires("a >= 0")]
#[requires("b >= 0")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn max_of(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

#[requires("a >= 0")]
#[requires("b >= 0")]
#[ensures("result <= a")]
#[ensures("result <= b")]
fn min_of(a: i32, b: i32) -> i32 {
    if a < b { a } else { b }
}

#[requires("x != 0")]
#[ensures("result + x == 0")]
fn negate(x: i32) -> i32 {
    -x
}

#[requires("x >= 0")]
#[requires("x <= 100")]
#[ensures("result >= 0")]
fn clamp_percentage(x: i32) -> i32 {
    if x < 0 { 0 }
    else if x > 100 { 100 }
    else { x }
}

fn main() {
    let _ = square(5);
    let _ = max_of(10, 20);
    let _ = min_of(10, 20);
    let _ = negate(5);
    let _ = clamp_percentage(50);
}
