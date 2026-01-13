//! Expected outcomes:
//! array_len_eq_three: @expect: VERIFIED
//! array_len_gt_zero: @expect: VERIFIED

// Fixed-size arrays have a type-level length. Specs using `arr.len()` should be provable.

// #[ensures(arr.len() == 3)]
fn array_len_eq_three(arr: &[i32; 3]) -> i32 {
    arr[0]
}

// #[ensures(arr.len() > 0)]
fn array_len_gt_zero(arr: &[i32; 3]) -> i32 {
    arr[0]
}

fn main() {
    let a = [1, 2, 3];
    println!("{}", array_len_eq_three(&a));
    println!("{}", array_len_gt_zero(&a));
}

