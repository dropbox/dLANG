// Level 3 Test: Threading
// Tests: thread spawning, joining, channels, mutexes, atomics

use std::sync::{Arc, Mutex, mpsc};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

fn main() {
    // Basic thread spawn and join
    println!("=== Basic Threading ===");
    let handle = thread::spawn(|| {
        println!("Hello from spawned thread");
        42
    });
    let result = handle.join().unwrap();
    println!("Thread returned: {}", result);

    // Multiple threads
    println!("\n=== Multiple Threads ===");
    let mut handles = vec![];
    for i in 0..5 {
        let handle = thread::spawn(move || {
            i * i
        });
        handles.push(handle);
    }

    let mut results: Vec<i32> = handles
        .into_iter()
        .map(|h| h.join().unwrap())
        .collect();
    results.sort();
    println!("Results: {:?}", results);

    // Shared state with Mutex
    println!("\n=== Mutex ===");
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final counter: {}", *counter.lock().unwrap());

    // Channels
    println!("\n=== Channels ===");
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let messages = vec!["hello", "from", "channel"];
        for msg in messages {
            tx.send(msg).unwrap();
        }
    });

    print!("Received: ");
    for received in rx {
        print!("{} ", received);
    }
    println!();

    // Multiple producers
    println!("\n=== Multiple Producers ===");
    let (tx, rx) = mpsc::channel();
    let mut handles = vec![];

    for i in 0..3 {
        let tx_clone = tx.clone();
        let handle = thread::spawn(move || {
            tx_clone.send(i).unwrap();
        });
        handles.push(handle);
    }
    drop(tx); // Close original sender

    for handle in handles {
        handle.join().unwrap();
    }

    let mut received: Vec<_> = rx.iter().collect();
    received.sort();
    println!("Received from multiple: {:?}", received);

    // Atomics
    println!("\n=== Atomics ===");
    let atomic_counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&atomic_counter);
        let handle = thread::spawn(move || {
            counter.fetch_add(1, Ordering::SeqCst);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Atomic counter: {}", atomic_counter.load(Ordering::SeqCst));

    // Thread local storage
    println!("\n=== Thread Local ===");
    thread_local! {
        static LOCAL_VALUE: std::cell::RefCell<u32> = std::cell::RefCell::new(0);
    }

    LOCAL_VALUE.with(|v| {
        *v.borrow_mut() = 42;
    });

    let handle = thread::spawn(|| {
        LOCAL_VALUE.with(|v| {
            println!("Spawned thread sees: {}", *v.borrow()); // Should be 0
        });
    });
    handle.join().unwrap();

    LOCAL_VALUE.with(|v| {
        println!("Main thread sees: {}", *v.borrow()); // Should be 42
    });
}
