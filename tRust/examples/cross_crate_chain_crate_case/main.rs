extern crate dep;

// This function relies on dep::double_plus_one's postcondition
// to prove its own postcondition.
//
// Chain: use_chain -> double_plus_one -> double_positive
//
// Known from dep::double_plus_one: result > x (when x > 0)
// Our precondition gives us: n >= 1
// So: dep::double_plus_one(n) > n >= 1, thus result >= 2
#[requires("n >= 1")]
#[ensures("result >= 2")]
fn use_chain(n: i32) -> i32 {
    dep::double_plus_one(n)
}

fn main() {}

