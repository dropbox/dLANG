// Benchmark: Simple function with 1 specification
// Measures baseline verification overhead

#[requires("x > 0")]
fn positive_identity(x: i32) -> i32 {
    x
}

fn main() {
    let _ = positive_identity(42);
}
