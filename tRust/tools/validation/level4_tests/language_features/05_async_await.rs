// Level 4.1: Async/Await
// Tests async functions and .await syntax
// Note: Uses simple manual executor, no runtime dependency

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

// Simple waker that does nothing
fn dummy_raw_waker() -> RawWaker {
    fn no_op(_: *const ()) {}
    fn clone(_: *const ()) -> RawWaker { dummy_raw_waker() }
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
    RawWaker::new(std::ptr::null(), &VTABLE)
}

fn dummy_waker() -> Waker {
    unsafe { Waker::from_raw(dummy_raw_waker()) }
}

// Simple block_on for testing
fn block_on<F: Future>(mut future: F) -> F::Output {
    let waker = dummy_waker();
    let mut cx = Context::from_waker(&waker);
    let mut future = unsafe { Pin::new_unchecked(&mut future) };
    loop {
        match future.as_mut().poll(&mut cx) {
            Poll::Ready(val) => return val,
            Poll::Pending => {} // In real code, we'd wait; here we just retry
        }
    }
}

// Simple async function
async fn add(a: i32, b: i32) -> i32 {
    a + b
}

// Async function calling another async function
async fn compute() -> i32 {
    let x = add(10, 20).await;
    let y = add(5, 5).await;
    x + y
}

// Async with references
async fn concat<'a>(a: &'a str, b: &'a str) -> String {
    format!("{}{}", a, b)
}

// Async returning Result
async fn fallible(succeed: bool) -> Result<i32, &'static str> {
    if succeed {
        Ok(42)
    } else {
        Err("failed")
    }
}

// Async with control flow
async fn conditional(cond: bool) -> &'static str {
    if cond {
        "yes"
    } else {
        "no"
    }
}

// Async with loop
async fn sum_to(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 1;
    while i <= n {
        sum += i;
        i += 1;
    }
    sum
}

// Ready future using std::future::ready
async fn use_ready() -> i32 {
    let x = std::future::ready(10).await;
    let y = std::future::ready(20).await;
    x + y
}

fn main() {
    // Basic async/await
    let result = block_on(add(5, 3));
    println!("5 + 3 = {}", result);

    // Chained async calls
    let result = block_on(compute());
    println!("Compute: {}", result);

    // Async with references
    let s1 = "Hello, ";
    let s2 = "World!";
    let result = block_on(concat(s1, s2));
    println!("Concat: {}", result);

    // Async with Result
    let ok = block_on(fallible(true));
    println!("Ok: {:?}", ok);
    let err = block_on(fallible(false));
    println!("Err: {:?}", err);

    // Async with control flow
    println!("Cond true: {}", block_on(conditional(true)));
    println!("Cond false: {}", block_on(conditional(false)));

    // Async with loop
    println!("Sum 1..10: {}", block_on(sum_to(10)));

    // Custom future
    println!("Ready future: {}", block_on(use_ready()));

    println!("All async tests passed!");
}
