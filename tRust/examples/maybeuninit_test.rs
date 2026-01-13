//! MaybeUninit integration test (Phase 10.1)
//! Tests that MaybeUninit type has documented contracts.
//!
//! MaybeUninit<T> allows working with uninitialized memory safely.
//! Key methods:
//! - uninit() -> MaybeUninit<T>: creates uninitialized value
//! - new(val) -> MaybeUninit<T>: creates initialized MaybeUninit
//! - zeroed() -> MaybeUninit<T>: creates zero-initialized value
//! - assume_init(self) -> T: converts to T (unsafe)
//! - write(&mut self, val) -> &mut T: writes value
//!
//! Note: Most MaybeUninit operations are unsafe; this test uses safe patterns.

use std::mem::MaybeUninit;

// Test 1: MaybeUninit::new creates initialized value
fn test_new() -> i32 {
    let mu = MaybeUninit::new(42);
    // SAFETY: We just initialized it with 42
    unsafe { mu.assume_init() }
}

// Test 2: MaybeUninit::zeroed creates zeroed memory
fn test_zeroed() -> i32 {
    let mu: MaybeUninit<i32> = MaybeUninit::zeroed();
    // SAFETY: i32 is valid when zeroed
    unsafe { mu.assume_init() }
}

// Test 3: MaybeUninit::write initializes and returns reference
fn test_write() -> i32 {
    let mut mu = MaybeUninit::uninit();
    let r = mu.write(100);
    *r
}

// Test 4: MaybeUninit::as_ptr returns pointer
fn test_as_ptr() -> bool {
    let mu = MaybeUninit::new(42i32);
    let ptr = mu.as_ptr();
    !ptr.is_null()
}

// Test 5: MaybeUninit::as_mut_ptr returns mutable pointer
fn test_as_mut_ptr() -> bool {
    let mut mu = MaybeUninit::new(42i32);
    let ptr = mu.as_mut_ptr();
    !ptr.is_null()
}

// Test 6: Initialize values individually (no loop to avoid overflow)
fn test_values_init() -> i32 {
    let v1 = MaybeUninit::new(10i32);
    let v2 = MaybeUninit::new(20i32);
    let v3 = MaybeUninit::new(30i32);
    // SAFETY: All values are initialized
    let a: i32 = unsafe { v1.assume_init() };
    let b: i32 = unsafe { v2.assume_init() };
    let c: i32 = unsafe { v3.assume_init() };
    a.saturating_add(b).saturating_add(c)
}

// Test 7: MaybeUninit with struct
struct Point { x: i32, y: i32 }

fn test_struct_init() -> i32 {
    let mu = MaybeUninit::new(Point { x: 10, y: 20 });
    // SAFETY: Fully initialized
    let p = unsafe { mu.assume_init() };
    p.x.saturating_add(p.y)
}

// Test 8: MaybeUninit zeroed for struct
fn test_struct_zeroed() -> i32 {
    let mu: MaybeUninit<Point> = MaybeUninit::zeroed();
    // SAFETY: Point with zeroed fields is valid
    let p = unsafe { mu.assume_init() };
    p.x.saturating_add(p.y) // Should be 0
}

// Test 9: MaybeUninit::assume_init_ref (unsafe)
fn test_assume_init_ref() -> i32 {
    let mu = MaybeUninit::new(42);
    // SAFETY: Value is initialized
    let r = unsafe { mu.assume_init_ref() };
    *r
}

// Test 10: MaybeUninit::assume_init_mut (unsafe)
fn test_assume_init_mut() -> i32 {
    let mut mu = MaybeUninit::new(42);
    // SAFETY: Value is initialized
    let r = unsafe { mu.assume_init_mut() };
    *r = 50;
    *r
}

// Test 11: Pattern - conditional initialization
fn test_conditional_init(condition: bool) -> i32 {
    let mu = if condition {
        MaybeUninit::new(100)
    } else {
        MaybeUninit::new(200)
    };
    // SAFETY: Initialized in both branches
    unsafe { mu.assume_init() }
}

// Test 12: MaybeUninit for larger type
fn test_larger_type() -> i64 {
    let mu = MaybeUninit::new(1_000_000_000_000i64);
    unsafe { mu.assume_init() }
}

// Test 13: Zeroed u8 is valid
fn test_zeroed_u8() -> u8 {
    let mu: MaybeUninit<u8> = MaybeUninit::zeroed();
    unsafe { mu.assume_init() }
}

fn main() {
    println!("Test 1 - new: {}", test_new());
    println!("Test 2 - zeroed: {}", test_zeroed());
    println!("Test 3 - write: {}", test_write());
    println!("Test 4 - as_ptr: {}", test_as_ptr());
    println!("Test 5 - as_mut_ptr: {}", test_as_mut_ptr());
    println!("Test 6 - values init sum: {}", test_values_init());
    println!("Test 7 - struct init sum: {}", test_struct_init());
    println!("Test 8 - struct zeroed sum: {}", test_struct_zeroed());
    println!("Test 9 - assume_init_ref: {}", test_assume_init_ref());
    println!("Test 10 - assume_init_mut: {}", test_assume_init_mut());
    println!("Test 11 - conditional init true: {}", test_conditional_init(true));
    println!("Test 11 - conditional init false: {}", test_conditional_init(false));
    println!("Test 12 - larger type: {}", test_larger_type());
    println!("Test 13 - zeroed u8: {}", test_zeroed_u8());

    println!("\nAll MaybeUninit tests passed!");
}
