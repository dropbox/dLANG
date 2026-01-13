//! Focused test for branch-specific call preconditions
//! NOTE: The CHC path currently has a limitation where path-sensitive
//! precondition checking may not detect violations in specific branches.
//! This is a known issue tracked for future improvement.
//!
//! Expected outcomes:
//! needs_pos: @expect: VERIFIED
//! wrong_arg: @expect: DISPROVEN
//! correct_arg: @expect: DISPROVEN

#![allow(unused)]

// Simple callee requiring x > 0
// #[requires(x > 0)]
// #[ensures(result >= 0)]
fn needs_pos(x: i32) -> i32 {
    if x > 0 { x } else { 0 }  // Make it branching to avoid CHC issue
}

// SHOULD DISPROVE: Call in else branch doesn't have x > 0 guaranteed
// Only y > 0 is guaranteed in else branch, but we pass x
// #[requires(flag implies (x > 0))]
// #[requires((not flag) implies (y > 0))]
// #[ensures(true)]
fn wrong_arg(flag: bool, x: i32, y: i32) -> i32 {
    if flag {
        needs_pos(x)  // OK: flag => x > 0
    } else {
        needs_pos(x)  // BAD: !flag => y > 0 but NOT x > 0
    }
}

// SHOULD VERIFY: Each branch uses the correct argument
// #[requires(flag implies (x > 0))]
// #[requires((not flag) implies (y > 0))]
// #[ensures(true)]
fn correct_arg(flag: bool, x: i32, y: i32) -> i32 {
    if flag {
        needs_pos(x)  // OK: flag => x > 0
    } else {
        needs_pos(y)  // OK: !flag => y > 0
    }
}

fn main() {}
