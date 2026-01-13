// Level 3 Test: Memory allocation patterns
// Tests: Box, Rc, Arc, RefCell, lifetimes, drop

use std::rc::Rc;
use std::sync::Arc;
use std::cell::{Cell, RefCell};

fn main() {
    // Box (heap allocation)
    println!("=== Box ===");
    let boxed: Box<i32> = Box::new(42);
    println!("boxed value: {}", *boxed);

    let boxed_array: Box<[i32; 5]> = Box::new([1, 2, 3, 4, 5]);
    println!("boxed array: {:?}", *boxed_array);

    // Recursive type with Box
    #[derive(Debug)]
    enum List {
        Cons(i32, Box<List>),
        Nil,
    }
    let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
    println!("recursive list: {:?}", list);

    // Rc (reference counting)
    println!("\n=== Rc ===");
    let rc1 = Rc::new(42);
    println!("rc1: {}, count: {}", *rc1, Rc::strong_count(&rc1));

    let rc2 = Rc::clone(&rc1);
    println!("after clone: count={}", Rc::strong_count(&rc1));

    let rc3 = Rc::clone(&rc1);
    println!("after another clone: count={}", Rc::strong_count(&rc1));

    drop(rc2);
    println!("after drop(rc2): count={}", Rc::strong_count(&rc1));

    drop(rc3);
    println!("after drop(rc3): count={}", Rc::strong_count(&rc1));

    // Arc (thread-safe reference counting)
    println!("\n=== Arc ===");
    let arc1 = Arc::new(42);
    println!("arc1: {}, count: {}", *arc1, Arc::strong_count(&arc1));

    let arc2 = Arc::clone(&arc1);
    println!("after clone: count={}", Arc::strong_count(&arc1));

    // Cell (interior mutability for Copy types)
    println!("\n=== Cell ===");
    let cell = Cell::new(10);
    println!("initial: {}", cell.get());
    cell.set(20);
    println!("after set(20): {}", cell.get());

    let old = cell.replace(30);
    println!("replace(30) returned: {}, new: {}", old, cell.get());

    // RefCell (interior mutability with runtime borrow checking)
    println!("\n=== RefCell ===");
    let refcell = RefCell::new(vec![1, 2, 3]);
    println!("initial: {:?}", refcell.borrow());

    refcell.borrow_mut().push(4);
    println!("after push: {:?}", refcell.borrow());

    {
        let mut borrowed = refcell.borrow_mut();
        borrowed.push(5);
        borrowed[0] = 10;
    } // borrow dropped here
    println!("after modifications: {:?}", refcell.borrow());

    // Rc<RefCell<T>> pattern (shared mutable state)
    println!("\n=== Rc<RefCell<T>> ===");
    let shared = Rc::new(RefCell::new(0));

    let a = Rc::clone(&shared);
    let b = Rc::clone(&shared);

    *a.borrow_mut() += 10;
    *b.borrow_mut() += 5;
    println!("shared value: {}", shared.borrow());

    // Drop order
    println!("\n=== Drop Order ===");
    struct Droppable(&'static str);
    impl Drop for Droppable {
        fn drop(&mut self) {
            println!("Dropping: {}", self.0);
        }
    }

    {
        let _first = Droppable("first");
        let _second = Droppable("second");
        let _third = Droppable("third");
        println!("Inside scope");
    }
    println!("After scope");

    // Manual drop
    println!("\n=== Manual Drop ===");
    let manual = Droppable("manual");
    println!("Before explicit drop");
    drop(manual);
    println!("After explicit drop");

    // Vec memory behavior
    println!("\n=== Vec Memory ===");
    let mut v: Vec<i32> = Vec::new();
    println!("empty: len={}, cap={}", v.len(), v.capacity());

    v.push(1);
    println!("after push: len={}, cap={}", v.len(), v.capacity());

    v.reserve(100);
    println!("after reserve(100): len={}, cap>={}", v.len(), v.capacity());

    v.shrink_to_fit();
    println!("after shrink_to_fit: len={}, cap={}", v.len(), v.capacity());
}
