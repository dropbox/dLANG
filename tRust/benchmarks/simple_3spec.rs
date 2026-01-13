// Benchmark: Function with 3 specifications
// Matches hello_verified.rs complexity

#[requires("n > 0")]
#[ensures("result >= 1")]
#[ensures("result <= n")]
fn clamp_positive(n: i32, val: i32) -> i32 {
    if val < 1 { 1 }
    else if val > n { n }
    else { val }
}

fn main() {
    let _ = clamp_positive(10, 5);
}
