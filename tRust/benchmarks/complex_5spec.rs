// Benchmark: Function with 5 specifications
// Tests verification scaling with spec count

#[requires("a >= 0")]
#[requires("b >= 0")]
#[requires("a <= 1000")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn max_value(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

fn main() {
    let _ = max_value(50, 75);
}
