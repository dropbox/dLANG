//! Cow (Clone-on-Write) integration test (Phase 10.1)
//! Tests that Cow type has documented contracts.
//!
//! Cow<'a, B> is either Borrowed(&'a B) or Owned(<B as ToOwned>::Owned).
//! Key methods:
//! - into_owned() -> Owned: converts to owned (clones if borrowed)
//! - to_mut() -> &mut Owned: gets mutable reference (clones if borrowed)
//!
//! Note: is_borrowed/is_owned are unstable in Rust 1.83, so we use pattern matching

use std::borrow::Cow;

// Test 1: Cow::Borrowed pattern matching
fn test_borrowed_pattern() -> bool {
    let s: &str = "hello";
    let cow: Cow<str> = Cow::Borrowed(s);
    matches!(cow, Cow::Borrowed(_))
}

// Test 2: Cow::Owned pattern matching
fn test_owned_pattern() -> bool {
    let cow: Cow<str> = Cow::Owned(String::from("hello"));
    matches!(cow, Cow::Owned(_))
}

// Test 3: into_owned converts borrowed to owned
fn test_into_owned_from_borrowed() -> String {
    let s: &str = "world";
    let cow: Cow<str> = Cow::Borrowed(s);
    let owned: String = cow.into_owned();
    owned
}

// Test 4: into_owned keeps owned as owned
fn test_into_owned_from_owned() -> String {
    let cow: Cow<str> = Cow::Owned(String::from("owned"));
    let owned: String = cow.into_owned();
    owned
}

// Test 5: to_mut on borrowed clones
fn test_to_mut_borrowed() -> String {
    let s: &str = "mutable";
    let mut cow: Cow<str> = Cow::Borrowed(s);
    let mref = cow.to_mut();
    mref.push_str("!");
    cow.into_owned()
}

// Test 6: to_mut on owned doesn't clone
fn test_to_mut_owned() -> String {
    let mut cow: Cow<str> = Cow::Owned(String::from("already owned"));
    let mref = cow.to_mut();
    mref.push_str("!");
    cow.into_owned()
}

// Test 7: Cow with slice borrowed
fn test_cow_slice_borrowed() -> bool {
    let arr = [1, 2, 3];
    let cow: Cow<[i32]> = Cow::Borrowed(&arr);
    matches!(cow, Cow::Borrowed(_))
}

// Test 8: Cow preserves borrowed state in clone
fn test_cow_clone_state() -> bool {
    let s: &str = "test";
    let cow1: Cow<str> = Cow::Borrowed(s);
    let cow2 = cow1.clone();
    matches!(cow2, Cow::Borrowed(_))
}

// Test 9: as_ref returns correct length
fn test_as_ref_len() -> usize {
    let cow: Cow<str> = Cow::Borrowed("test");
    let r: &str = cow.as_ref();
    r.len()
}

// Test 10: Cow from slice literal is borrowed
fn test_from_slice() -> bool {
    let cow: Cow<str> = Cow::from("literal");
    matches!(cow, Cow::Borrowed(_))
}

// Test 11: Cow from String is owned
fn test_from_string() -> bool {
    let s = String::from("string");
    let cow: Cow<str> = Cow::from(s);
    matches!(cow, Cow::Owned(_))
}

// Test 12: Clone cow keeps state
fn test_clone_borrowed() -> bool {
    let s: &str = "borrowed";
    let cow: Cow<str> = Cow::Borrowed(s);
    let cloned = cow.clone();
    matches!(cloned, Cow::Borrowed(_))
}

// Test 13: Clone owned cow clones
fn test_clone_owned() -> bool {
    let cow: Cow<str> = Cow::Owned(String::from("owned"));
    let cloned = cow.clone();
    matches!(cloned, Cow::Owned(_))
}

fn main() {
    println!("Test 1 - borrowed pattern: {}", test_borrowed_pattern());
    println!("Test 2 - owned pattern: {}", test_owned_pattern());
    println!("Test 3 - into_owned from borrowed: {}", test_into_owned_from_borrowed());
    println!("Test 4 - into_owned from owned: {}", test_into_owned_from_owned());
    println!("Test 5 - to_mut borrowed: {}", test_to_mut_borrowed());
    println!("Test 6 - to_mut owned: {}", test_to_mut_owned());
    println!("Test 7 - cow slice borrowed: {}", test_cow_slice_borrowed());
    println!("Test 8 - cow clone state: {}", test_cow_clone_state());
    println!("Test 9 - as_ref len: {}", test_as_ref_len());
    println!("Test 10 - from slice: {}", test_from_slice());
    println!("Test 11 - from string: {}", test_from_string());
    println!("Test 12 - clone borrowed: {}", test_clone_borrowed());
    println!("Test 13 - clone owned: {}", test_clone_owned());

    println!("\nAll Cow tests passed!");
}
