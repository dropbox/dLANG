//! Cell<T> and RefCell<T> interior mutability integration test (Phase 10.1)
//! Tests that Cell and RefCell methods are recognized by the verifier.
//!
//! Cell<T> provides single-threaded interior mutability for Copy types.
//! RefCell<T> provides single-threaded interior mutability with runtime borrow checking.
//!
//! These types have documented contracts but no strong postconditions since
//! their values depend on runtime state.

use std::cell::{Cell, RefCell};

// Test 1: Cell::new creates a Cell
fn test_cell_new() -> Cell<i32> {
    Cell::new(42)
}

// Test 2: Cell::get returns the contained value (Copy types only)
fn test_cell_get(c: &Cell<i32>) -> i32 {
    c.get()
}

// Test 3: Cell::set sets the value
fn test_cell_set(c: &Cell<i32>, value: i32) {
    c.set(value);
}

// Test 4: Cell::replace returns the old value and sets new
fn test_cell_replace(c: &Cell<i32>, value: i32) -> i32 {
    c.replace(value)
}

// Test 5: Cell::into_inner consumes Cell and returns value
fn test_cell_into_inner(c: Cell<i32>) -> i32 {
    c.into_inner()
}

// Test 6: Cell::take takes value and replaces with default
fn test_cell_take(c: &Cell<i32>) -> i32 {
    c.take()
}

// Test 7: RefCell::new creates a RefCell
fn test_refcell_new() -> RefCell<i32> {
    RefCell::new(100)
}

// Test 8: RefCell::borrow returns immutable reference
fn test_refcell_borrow(rc: &RefCell<i32>) -> i32 {
    *rc.borrow()
}

// Test 9: RefCell::borrow_mut returns mutable reference
fn test_refcell_borrow_mut(rc: &RefCell<i32>) {
    *rc.borrow_mut() = 200;
}

// Test 10: RefCell::try_borrow returns Result with Ref
fn test_refcell_try_borrow(rc: &RefCell<i32>) -> Option<i32> {
    rc.try_borrow().ok().map(|r| *r)
}

// Test 11: RefCell::try_borrow_mut returns Result with RefMut
fn test_refcell_try_borrow_mut(rc: &RefCell<i32>) -> bool {
    rc.try_borrow_mut().is_ok()
}

// Test 12: RefCell::replace returns old value
fn test_refcell_replace(rc: &RefCell<i32>, value: i32) -> i32 {
    rc.replace(value)
}

// Test 13: RefCell::take takes value and replaces with default
fn test_refcell_take(rc: &RefCell<i32>) -> i32 {
    rc.take()
}

// Test 14: Combined Cell usage - get after set
fn test_cell_combined(c: &Cell<i32>, new_val: i32) -> i32 {
    c.set(new_val);
    c.get()
}

// Test 15: Combined RefCell usage - borrow after borrow_mut
fn test_refcell_combined(rc: &RefCell<i32>, new_val: i32) -> i32 {
    {
        *rc.borrow_mut() = new_val;
    }
    *rc.borrow()
}

fn main() {
    // Test Cell operations
    let c = test_cell_new();
    println!("Cell::new(): {:?}", c.get());
    println!("Cell::get(): {}", test_cell_get(&c));

    test_cell_set(&c, 100);
    println!("After Cell::set(100): {}", c.get());

    let old = test_cell_replace(&c, 200);
    println!("Cell::replace(200) returned: {}, now: {}", old, c.get());

    let taken = test_cell_take(&c);
    println!("Cell::take() returned: {}, now: {}", taken, c.get());

    let c2 = Cell::new(999);
    println!("Cell::into_inner(): {}", test_cell_into_inner(c2));

    println!("Cell combined: {}", test_cell_combined(&c, 42));

    // Test RefCell operations
    let rc = test_refcell_new();
    println!("\nRefCell::new(): {:?}", *rc.borrow());
    println!("RefCell::borrow(): {}", test_refcell_borrow(&rc));

    test_refcell_borrow_mut(&rc);
    println!("After RefCell::borrow_mut(): {}", *rc.borrow());

    if let Some(val) = test_refcell_try_borrow(&rc) {
        println!("RefCell::try_borrow(): Some({})", val);
    }

    println!("RefCell::try_borrow_mut() ok: {}", test_refcell_try_borrow_mut(&rc));

    let old = test_refcell_replace(&rc, 300);
    println!("RefCell::replace(300) returned: {}, now: {}", old, *rc.borrow());

    let taken = test_refcell_take(&rc);
    println!("RefCell::take() returned: {}, now: {}", taken, *rc.borrow());

    println!("RefCell combined: {}", test_refcell_combined(&rc, 500));

    println!("\nAll Cell/RefCell tests passed!");
}
