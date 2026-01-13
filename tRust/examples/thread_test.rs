//! Thread module integration test (Phase 10.1)
//! Tests thread spawning and management contracts.
//!
//! Most thread operations are runtime-dependent and concurrent,
//! so they are documented contracts without strong postconditions.
//!
//! Note: ThreadId::as_u64() is unstable and not tested here.

#![allow(unused_variables)]

use std::thread;
use std::time::Duration;

// Test 1: thread::spawn creates new thread
fn test_thread_spawn() -> thread::JoinHandle<i32> {
    thread::spawn(|| {
        42
    })
}

// Test 2: JoinHandle::join waits for thread completion
fn test_join_handle_join(handle: thread::JoinHandle<i32>) -> i32 {
    handle.join().expect("Thread panicked")
}

// Test 3: thread::current returns current thread
fn test_thread_current() -> thread::Thread {
    thread::current()
}

// Test 4: Thread::id returns thread ID
fn test_thread_id(t: &thread::Thread) -> thread::ThreadId {
    t.id()
}

// Test 5: Thread::name returns optional name
fn test_thread_name<'a>(t: &'a thread::Thread) -> Option<&'a str> {
    t.name()
}

// Test 6: thread::sleep pauses execution
fn test_thread_sleep(duration: Duration) {
    thread::sleep(duration);
}

// Test 7: thread::yield_now yields to scheduler
fn test_thread_yield_now() {
    thread::yield_now();
}

// Test 8: thread::panicking checks panic state
fn test_thread_panicking() -> bool {
    thread::panicking()
}

// Test 9: thread::available_parallelism returns CPU count
fn test_available_parallelism() -> usize {
    thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

// Test 10: thread::Builder creates thread with custom settings
fn test_thread_builder() -> thread::JoinHandle<String> {
    thread::Builder::new()
        .name("test-thread".to_string())
        .stack_size(1024 * 1024)
        .spawn(|| {
            thread::current().name().unwrap_or("unnamed").to_string()
        })
        .expect("Failed to spawn thread")
}

// Test 11: thread::scope for scoped threads
fn test_thread_scope(data: &[i32]) -> i32 {
    thread::scope(|s| {
        let handle = s.spawn(|| {
            data.iter().sum::<i32>()
        });
        handle.join().expect("Scoped thread panicked")
    })
}

// Test 12: JoinHandle::is_finished checks completion
fn test_is_finished() -> bool {
    let handle = thread::spawn(|| {
        thread::sleep(Duration::from_millis(1));
    });
    // Check immediately - likely not finished
    let result = handle.is_finished();
    let _ = handle.join();
    result
}

fn main() {
    // Test thread spawning and joining
    println!("Spawning thread...");
    let handle = test_thread_spawn();
    let result = test_join_handle_join(handle);
    println!("Thread returned: {}", result);

    // Test current thread info
    let current = test_thread_current();
    println!("Current thread name: {:?}", test_thread_name(&current));

    // Test thread ID
    let id = test_thread_id(&current);
    println!("Thread ID obtained (value is implementation-defined)");

    // Test thread utilities
    println!("Yielding...");
    test_thread_yield_now();

    println!("Panicking status: {}", test_thread_panicking());

    // Test available parallelism
    let parallelism = test_available_parallelism();
    println!("Available parallelism: {}", parallelism);

    // Test thread builder
    println!("Testing thread builder...");
    let named_handle = test_thread_builder();
    let thread_name = named_handle.join().expect("Named thread panicked");
    println!("Named thread reported: {}", thread_name);

    // Test scoped threads with static array to avoid vec! overflow check
    let data: [i32; 5] = [1, 2, 3, 4, 5];
    let sum = test_thread_scope(&data);
    println!("Scoped thread sum: {}", sum);

    // Test is_finished
    let was_finished = test_is_finished();
    println!("Thread was finished immediately: {}", was_finished);

    // Test sleep (short)
    println!("Sleeping for 10ms...");
    test_thread_sleep(Duration::from_millis(10));
    println!("Awake!");

    println!("All thread tests completed!");
}
