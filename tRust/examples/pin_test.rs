//! Pin integration test (Phase 10.1)
//! Tests that Pin type has documented contracts.
//!
//! Pin<P> guarantees the pointed-to value won't move in memory.
//! Used for self-referential types and async/await.
//!
//! Key methods:
//! - Pin::new(pointer) -> Pin<P>: creates Pin (requires Unpin)
//! - Pin::into_inner(self) -> P: extracts inner pointer (requires Unpin)
//! - Pin::as_ref(&self) -> Pin<&T>: converts to shared pin
//! - Pin::as_mut(&mut self) -> Pin<&mut T>: reborrows pinned reference
//! - Pin::get_mut(self) -> &mut T: gets mutable ref (requires Unpin)

use std::pin::Pin;
use std::marker::PhantomPinned;
use std::ops::Deref;

// Test 1: Pin::new with Unpin type (i32)
fn test_pin_new_unpin() -> i32 {
    let mut x = 42i32;
    let pinned = Pin::new(&mut x);
    // Deref to get value
    *pinned
}

// Test 2: Pin::into_inner extracts pointer for Unpin types
fn test_into_inner() -> i32 {
    let mut x = 100i32;
    let pinned = Pin::new(&mut x);
    let inner = Pin::into_inner(pinned);
    *inner
}

// Test 3: Pin::as_ref creates shared pin
fn test_as_ref() -> i32 {
    let mut x = 50i32;
    let mut pinned = Pin::new(&mut x);
    let shared: Pin<&i32> = pinned.as_ref();
    *shared
}

// Test 4: Pin::as_mut reborrows
fn test_as_mut() -> i32 {
    let mut x = 75i32;
    let mut pinned = Pin::new(&mut x);
    {
        let reborrowed: Pin<&mut i32> = pinned.as_mut();
        *reborrowed.get_mut() = 80;
    }
    *pinned
}

// Test 5: Deref on Pin gives shared reference
fn test_deref() -> i32 {
    let mut x = 123i32;
    let pinned = Pin::new(&mut x);
    let r: &i32 = pinned.deref();
    *r
}

// Test 6: Pin::get_mut for Unpin types (consumes Pin)
fn test_get_mut() -> i32 {
    let mut x = 200i32;
    let pinned = Pin::new(&mut x);
    *pinned.get_mut() = 250;
    x
}

// Test 7: Pin with struct containing Unpin fields
struct UnpinStruct {
    value: i32,
}

fn test_pin_struct() -> i32 {
    let mut s = UnpinStruct { value: 42 };
    let pinned = Pin::new(&mut s);
    pinned.value
}

// Test 8: Pin::set replaces value
fn test_set() -> i32 {
    let mut x = 10i32;
    let mut pinned = Pin::new(&mut x);
    pinned.set(20);
    *pinned
}

// Test 9: Multiple as_mut reborrows
fn test_multiple_ops() -> i32 {
    let mut x = 0i32;
    let mut pinned = Pin::new(&mut x);

    *pinned.as_mut().get_mut() = 1;
    *pinned.as_mut().get_mut() = 2;
    *pinned.as_mut().get_mut() = 3;

    *pinned
}

// Test 10: Pin with Box (heap-allocated)
fn test_pin_box() -> i32 {
    let boxed = Box::new(42i32);
    let pinned: Pin<Box<i32>> = Pin::new(boxed);
    *pinned
}

// Test 11: Box::pin creates pinned Box
fn test_box_pin() -> i32 {
    let pinned: Pin<Box<i32>> = Box::pin(99);
    *pinned
}

// Test 12: PhantomPinned marker type (not Unpin)
struct Pinned {
    value: i32,
    _marker: PhantomPinned,
}

fn test_phantom_pinned() -> i32 {
    let p = Pinned { value: 77, _marker: PhantomPinned };
    let pinned: Pin<Box<Pinned>> = Box::pin(p);
    // Can only use deref for !Unpin types
    pinned.value
}

// Test 13: Pin with tuple
fn test_pin_tuple() -> i32 {
    let mut t = (10i32, 20i32);
    let pinned = Pin::new(&mut t);
    pinned.0.saturating_add(pinned.1)
}

fn main() {
    println!("Test 1 - pin new unpin: {}", test_pin_new_unpin());
    println!("Test 2 - into_inner: {}", test_into_inner());
    println!("Test 3 - as_ref: {}", test_as_ref());
    println!("Test 4 - as_mut: {}", test_as_mut());
    println!("Test 5 - deref: {}", test_deref());
    println!("Test 6 - get_mut: {}", test_get_mut());
    println!("Test 7 - pin struct: {}", test_pin_struct());
    println!("Test 8 - set: {}", test_set());
    println!("Test 9 - multiple ops: {}", test_multiple_ops());
    println!("Test 10 - pin box: {}", test_pin_box());
    println!("Test 11 - box pin: {}", test_box_pin());
    println!("Test 12 - phantom pinned: {}", test_phantom_pinned());
    println!("Test 13 - pin tuple: {}", test_pin_tuple());

    println!("\nAll Pin tests passed!");
}
