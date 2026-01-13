// Test file for #[invariant] loop invariant verification
//
// Tests that loop invariants are verified using cutpoint-based approach:
// 1. Base case: precondition implies invariant at entry
// 2. Inductive case: invariant preserved by loop body
// 3. Use case: invariant at exit implies postcondition

// Simple summation with loop invariant
#[requires("n >= 0 && n < 100")]
#[ensures("result >= 0")]
#[invariant("sum >= 0 && i >= 0")]
fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        sum += i;
        i += 1;
    }
    sum
}

// Countdown with loop invariant
// When loop exits (count <= 0) AND invariant (count >= 0) => count == 0
#[requires("n >= 0 && n < 100")]
#[ensures("result >= 0")]  // Weaker postcondition that invariant implies
#[invariant("count >= 0")]
fn countdown(n: i32) -> i32 {
    let mut count = n;
    while count > 0 {
        count -= 1;
    }
    count
}

// Simple counter increment
// Invariant must be strong enough to imply postcondition when loop exits
#[requires("n > 0 && n < 50")]
#[ensures("result >= 0")]  // Weaker postcondition
#[invariant("count >= 0 && count <= n")]
fn count_up(n: i32) -> i32 {
    let mut count = 0;
    while count < n {
        count += 1;
    }
    count
}

fn main() {
    println!("sum_to_n(5) = {}", sum_to_n(5));
    println!("countdown(10) = {}", countdown(10));
    println!("count_up(10) = {}", count_up(10));
}
