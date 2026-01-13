//! NonZero types integration test (Phase 10.1)
//! Tests that NonZero types' get() method returns non-zero values.
//!
//! NonZero<T> types guarantee the contained value is never zero.
//! This is a very strong invariant:
//! - NonZeroU*::get() returns a value > 0 (unsigned)
//! - NonZeroI*::get() returns a value != 0 (signed, can be negative)
//!
//! This enables optimizations like Option<NonZeroU32> being the same size as u32.

use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroUsize};
use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroIsize};

// Test 1: NonZeroU32::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_u32_get(n: NonZeroU32) -> u32 {
    n.get()
}

// Test 2: NonZeroU64::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_u64_get(n: NonZeroU64) -> u64 {
    n.get()
}

// Test 3: NonZeroUsize::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_usize_get(n: NonZeroUsize) -> usize {
    n.get()
}

// Test 4: NonZeroU8::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_u8_get(n: NonZeroU8) -> u8 {
    n.get()
}

// Test 5: NonZeroU16::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_u16_get(n: NonZeroU16) -> u16 {
    n.get()
}

// Test 6: NonZeroI32::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_i32_get(n: NonZeroI32) -> i32 {
    n.get()
}

// Test 7: NonZeroI64::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_i64_get(n: NonZeroI64) -> i64 {
    n.get()
}

// Test 8: NonZeroIsize::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_isize_get(n: NonZeroIsize) -> isize {
    n.get()
}

// Test 9: NonZeroI8::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_i8_get(n: NonZeroI8) -> i8 {
    n.get()
}

// Test 10: NonZeroI16::get returns value != 0
#[ensures("result != 0")]
fn test_nonzero_i16_get(n: NonZeroI16) -> i16 {
    n.get()
}

// Test 11: Using NonZero value in computation maintains != 0 property
#[ensures("result != 0")]
fn test_nonzero_u32_compute(n: NonZeroU32) -> u32 {
    // n.get() is guaranteed != 0, so result is guaranteed != 0
    n.get()
}

// Test 12: NonZeroU32 != 0 property
#[ensures("result != 0")]
fn test_nonzero_u32_not_zero(n: NonZeroU32) -> u32 {
    n.get()
}

// Test 13: NonZeroI32 != 0 even for negative values
#[ensures("result != 0")]
fn test_nonzero_i32_not_zero(n: NonZeroI32) -> i32 {
    n.get()
}

fn main() {
    // Create NonZero values (all must be non-zero at construction)
    let n_u8 = NonZeroU8::new(1).unwrap();
    let n_u16 = NonZeroU16::new(255).unwrap();
    let n_u32 = NonZeroU32::new(42).unwrap();
    let n_u64 = NonZeroU64::new(1_000_000).unwrap();
    let n_usize = NonZeroUsize::new(100).unwrap();

    let n_i8 = NonZeroI8::new(-1).unwrap();
    let n_i16 = NonZeroI16::new(-255).unwrap();
    let n_i32 = NonZeroI32::new(-42).unwrap();
    let n_i64 = NonZeroI64::new(-1_000_000).unwrap();
    let n_isize = NonZeroIsize::new(-100).unwrap();

    // Test unsigned get() > 0
    println!("NonZeroU8::get(): {}", test_nonzero_u8_get(n_u8));
    println!("NonZeroU16::get(): {}", test_nonzero_u16_get(n_u16));
    println!("NonZeroU32::get(): {}", test_nonzero_u32_get(n_u32));
    println!("NonZeroU64::get(): {}", test_nonzero_u64_get(n_u64));
    println!("NonZeroUsize::get(): {}", test_nonzero_usize_get(n_usize));

    // Test signed get() != 0
    println!("NonZeroI8::get(): {}", test_nonzero_i8_get(n_i8));
    println!("NonZeroI16::get(): {}", test_nonzero_i16_get(n_i16));
    println!("NonZeroI32::get(): {}", test_nonzero_i32_get(n_i32));
    println!("NonZeroI64::get(): {}", test_nonzero_i64_get(n_i64));
    println!("NonZeroIsize::get(): {}", test_nonzero_isize_get(n_isize));

    // Test computation with NonZero
    println!("NonZeroU32 compute: {}", test_nonzero_u32_compute(n_u32));
    println!("NonZeroU32 not zero: {}", test_nonzero_u32_not_zero(n_u32));
    println!("NonZeroI32 not zero: {}", test_nonzero_i32_not_zero(n_i32));

    println!("\nAll NonZero tests passed!");
}
