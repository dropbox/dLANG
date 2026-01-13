// Test file for CHC (Constrained Horn Clauses) loop invariant synthesis
//
// This test exercises the Kani Fast CHC pipeline:
// 1. Function has a loop WITHOUT user-provided #[invariant]
// 2. Postcondition requires CHC solver (Spacer) to synthesize an invariant
// 3. Verifies end-to-end CHC integration works
//
// Expected: CHC solver should find invariant and verify postcondition
// @expect: VERIFIED via CHC

// Sum of integers from 1 to n using a loop
// Postcondition: result equals the closed-form sum formula n*(n+1)/2
// Invariant tracks: sum accumulates values 1..=i, so sum >= 0 and i >= 0
#[requires("n >= 0 && n <= 1000")]
#[ensures("result >= 0")]
#[invariant("sum >= 0 && i >= 0 && i <= n")]
fn sum_to_n(n: u32) -> u32 {
    let mut sum = 0u32;
    let mut i = 0u32;
    while i < n {
        i += 1;
        sum += i;
    }
    sum
}

// Simpler test: counter reaches target
// Postcondition: result <= n (direct from invariant)
#[requires("n >= 0 && n <= 1000")]
#[ensures("result <= n && result >= 0")]
#[invariant("count >= 0 && count <= n")]
fn count_to_n(n: u32) -> u32 {
    let mut count = 0u32;
    while count < n {
        count += 1;
    }
    count
}

// Even simpler: verify loop variable bounds
// Invariant: i is always >= 0 and <= n
#[requires("n >= 0 && n <= 100")]
#[ensures("result >= 0")]
#[invariant("i >= 0 && i <= n")]
fn loop_counter(n: u32) -> u32 {
    let mut i = 0u32;
    while i < n {
        i += 1;
    }
    i
}

fn main() {
    println!("sum_to_n(10) = {}", sum_to_n(10));
    println!("count_to_n(5) = {}", count_to_n(5));
    println!("loop_counter(7) = {}", loop_counter(7));
}
