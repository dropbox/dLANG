//! Integration test for tokio sync primitive contracts (Phase 10.2)
//!
//! This test uses a local `tokio` module to exercise name-based builtin preconditions:
//! - tokio::sync::Barrier::new(n) requires n > 0
//! - tokio::sync::Semaphore::available_permits() returns >= 0
//!
//! @expect: ERROR

#![allow(dead_code)]
#![allow(unused)]

mod tokio {
    pub mod sync {
        use std::marker::PhantomData;

        pub struct Barrier(usize);

        impl Barrier {
            #[inline(never)]
            pub fn new(n: usize) -> Self {
                Barrier(n)
            }

            pub fn wait(&self) {}
        }

        pub struct Semaphore(usize);

        impl Semaphore {
            #[inline(never)]
            pub fn new(permits: usize) -> Self {
                Semaphore(permits)
            }

            #[inline(never)]
            pub fn available_permits(&self) -> usize {
                self.0
            }
        }

        pub struct Mutex<T>(PhantomData<T>);

        impl<T> Mutex<T> {
            #[inline(never)]
            pub fn new(_t: T) -> Self {
                Mutex(PhantomData)
            }
        }

        pub struct RwLock<T>(PhantomData<T>);

        impl<T> RwLock<T> {
            #[inline(never)]
            pub fn new(_t: T) -> Self {
                RwLock(PhantomData)
            }
        }

        pub struct Notify;

        impl Notify {
            #[inline(never)]
            pub fn new() -> Self {
                Notify
            }
        }

        pub mod oneshot {
            use std::marker::PhantomData;

            pub struct Sender<T>(PhantomData<T>);
            pub struct Receiver<T>(PhantomData<T>);

            #[inline(never)]
            pub fn channel<T>() -> (Sender<T>, Receiver<T>) {
                (Sender(PhantomData), Receiver(PhantomData))
            }
        }

        pub mod watch {
            use std::marker::PhantomData;

            pub struct Sender<T>(PhantomData<T>);
            pub struct Receiver<T>(PhantomData<T>);

            #[inline(never)]
            pub fn channel<T>(_init: T) -> (Sender<T>, Receiver<T>) {
                (Sender(PhantomData), Receiver(PhantomData))
            }
        }
    }
}

// Test: Barrier::new(0) should fail precondition (n > 0)
#[ensures("result == 0")]
fn barrier_with_zero_parties() -> i32 {
    let _b = tokio::sync::Barrier::new(0);  // ERROR: requires n > 0
    0
}

// Test: Semaphore::new(0) is valid (no precondition)
#[ensures("result == 0")]
fn semaphore_with_zero_permits() -> i32 {
    let _s = tokio::sync::Semaphore::new(0);  // OK: permits can be 0
    0
}

// Test: Mutex, RwLock, Notify constructors (no preconditions)
#[ensures("result == 0")]
fn sync_constructors_valid() -> i32 {
    let _m = tokio::sync::Mutex::new(42);
    let _rw = tokio::sync::RwLock::new("test");
    let _n = tokio::sync::Notify::new();
    0
}

// Test: oneshot and watch channels (no preconditions)
#[ensures("result == 0")]
fn channel_constructors_valid() -> i32 {
    let (_tx1, _rx1) = tokio::sync::oneshot::channel::<i32>();
    let (_tx2, _rx2) = tokio::sync::watch::channel(42);
    0
}

fn main() {}
