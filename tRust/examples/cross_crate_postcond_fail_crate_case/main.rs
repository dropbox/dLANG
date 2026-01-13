extern crate dep;

#[requires("x >= 0")]
#[ensures("result > 0")]
fn call_id_strict(x: i32) -> i32 {
    dep::id_nonneg(x)
}

fn main() {}

