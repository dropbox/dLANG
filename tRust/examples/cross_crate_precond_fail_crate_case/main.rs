extern crate dep;

#[ensures("result == 0")]
fn bad_call() -> i32 {
    let _ = dep::id_nonneg(-1);
    0
}

fn main() {
    let _ = bad_call();
}

