// Range and iterator adapter contracts test (Phase 10.1)
// Tests builtin contracts for Range and iterator adapters

// ========================================
// Range contracts
// ========================================

// Range::len() returns >= 0
#[ensures("result >= 0")]
fn range_len(start: usize, end: usize) -> usize {
    // Only valid when end >= start
    if end >= start {
        (start..end).len()
    } else {
        0
    }
}

// ========================================
// Iterator adapter contracts (len >= 0)
// ========================================

// Take adapter len >= 0
#[ensures("result >= 0")]
fn take_len(n: usize) -> usize {
    (0..100).take(n).len()
}

// Skip adapter len >= 0
#[ensures("result >= 0")]
fn skip_len(n: usize) -> usize {
    (0..100).skip(n).len()
}

// Zip adapter len >= 0
#[ensures("result >= 0")]
fn zip_len() -> usize {
    (0..5).zip(0..10).len()
}

// Enumerate adapter len >= 0
#[ensures("result >= 0")]
fn enumerate_len() -> usize {
    (0..10).enumerate().len()
}

// Map adapter len >= 0
#[ensures("result >= 0")]
fn map_len() -> usize {
    (0..10).map(|x| x * 2).len()
}

// Rev adapter len >= 0
#[ensures("result >= 0")]
fn rev_len() -> usize {
    (0..10).rev().len()
}

// Fuse adapter len >= 0
#[ensures("result >= 0")]
fn fuse_len() -> usize {
    (0..10).fuse().len()
}

// StepBy adapter len >= 0
#[ensures("result >= 0")]
fn step_by_len() -> usize {
    (0..10).step_by(2).len()
}

// Peekable adapter len >= 0
#[ensures("result >= 0")]
fn peekable_len() -> usize {
    (0..10).peekable().len()
}

// ========================================
// Combined operations
// ========================================

// Chained adapters maintain len >= 0
#[ensures("result >= 0")]
fn chained_adapters_len() -> usize {
    (0..100)
        .take(50)
        .skip(10)
        .map(|x| x * 2)
        .len()
}

// Range with take
#[ensures("result >= 0")]
fn range_take_len(n: usize) -> usize {
    (0..1000).take(n).len()
}

// Enumerate preserves length property
#[ensures("result >= 0")]
fn enumerate_with_map() -> usize {
    (0..10)
        .enumerate()
        .map(|(i, x)| i + x)
        .len()
}

fn main() {
    // Range tests
    println!("range_len(0, 10) = {}", range_len(0, 10));
    println!("range_len(5, 5) = {}", range_len(5, 5));

    // Adapter tests
    println!("take_len(5) = {}", take_len(5));
    println!("skip_len(3) = {}", skip_len(3));
    println!("zip_len() = {}", zip_len());
    println!("enumerate_len() = {}", enumerate_len());
    println!("map_len() = {}", map_len());
    println!("rev_len() = {}", rev_len());
    println!("fuse_len() = {}", fuse_len());
    println!("step_by_len() = {}", step_by_len());
    println!("peekable_len() = {}", peekable_len());

    // Combined tests
    println!("chained_adapters_len() = {}", chained_adapters_len());
    println!("range_take_len(25) = {}", range_take_len(25));
    println!("enumerate_with_map() = {}", enumerate_with_map());
}
