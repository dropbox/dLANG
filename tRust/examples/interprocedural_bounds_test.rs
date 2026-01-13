//! Interprocedural bounds propagation test
//!
//! Tests for postcondition-based bounds checking across function calls.
//! CURRENT STATUS: Postconditions ARE verified at function boundaries, but
//! bounds checking does NOT yet integrate with postcondition propagation.
//!
//! Expected outcomes:
//! idx_from_bool: @expect: VERIFIED (postcondition proven)
//! idx_from_direction: @expect: VERIFIED (postcondition proven)
//! use_postcond_in_ensures: @expect: VERIFIED (postcondition chains to caller's ensures)
//!
//! Known limitation: Automatic bounds checking doesn't consume postconditions.
//! The array indexing `table[idx_from_bool(flag)]` triggers bounds warnings
//! even though `idx_from_bool` guarantees `result < 2`.
//!
//! FUTURE WORK: Integrate postcondition facts into bounds checker.

#![allow(unused)]

/// Returns 0 or 1 based on boolean input
#[ensures("result < 2")]
fn idx_from_bool(b: bool) -> usize {
    if b { 0 } else { 1 }
}

#[derive(Copy, Clone)]
enum Direction {
    North,
    East,
    South,
    West,
}

/// Maps a 4-variant enum to indices 0..4
#[ensures("result < 4")]
fn idx_from_direction(d: Direction) -> usize {
    match d {
        Direction::North => 0,
        Direction::East => 1,
        Direction::South => 2,
        Direction::West => 3,
    }
}

/// Demonstrates postcondition chaining to caller's ensures clause
/// This WORKS because ensures verification integrates with postconditions
#[ensures("result < 2")]
fn use_postcond_in_ensures(flag: bool) -> usize {
    idx_from_bool(flag)  // Postcondition (result < 2) flows to our ensures
}

/// Same pattern with enum - postcondition chains correctly
#[ensures("result < 4")]
fn use_enum_postcond_in_ensures(dir: Direction) -> usize {
    idx_from_direction(dir)  // Postcondition (result < 4) flows to our ensures
}

/// Chained postcondition - multiple levels
#[ensures("result < 2")]
fn chain_postconds(a: bool) -> usize {
    use_postcond_in_ensures(a)  // Transitive: uses callee's ensures
}

fn main() {
    // These demonstrate postcondition chaining works for ensures verification
    let _ = use_postcond_in_ensures(true);
    let _ = use_enum_postcond_in_ensures(Direction::North);
    let _ = chain_postconds(false);

    println!("Interprocedural postcondition tests passed!");
}
