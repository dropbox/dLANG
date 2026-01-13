//! Integration test for builtin callee preconditions for tokio channel constructors (Phase 10.2)
//!
//! This test uses a local `tokio` module to exercise name-based builtin preconditions:
//! - tokio::sync::mpsc::channel(buffer) requires buffer > 0
//! - tokio::sync::broadcast::channel(capacity) requires capacity > 0
//!
//! @expect: ERROR

#![allow(dead_code)]
#![allow(unused)]

mod tokio {
    pub mod sync {
        pub mod mpsc {
            use std::marker::PhantomData;

            pub struct Sender<T>(pub PhantomData<T>);
            pub struct Receiver<T>(pub PhantomData<T>);

            #[inline(never)]
            pub fn channel<T>(_buffer: usize) -> (Sender<T>, Receiver<T>) {
                (Sender(PhantomData), Receiver(PhantomData))
            }
        }

        pub mod broadcast {
            use std::marker::PhantomData;

            pub struct Sender<T>(pub PhantomData<T>);
            pub struct Receiver<T>(pub PhantomData<T>);

            #[inline(never)]
            pub fn channel<T>(_capacity: usize) -> (Sender<T>, Receiver<T>) {
                (Sender(PhantomData), Receiver(PhantomData))
            }
        }
    }
}

#[ensures("result == 0")]
fn mpsc_channel_without_requires() -> i32 {
    let _ch = tokio::sync::mpsc::channel::<i32>(0);
    0
}

#[ensures("result == 0")]
fn broadcast_channel_without_requires() -> i32 {
    let _ch = tokio::sync::broadcast::channel::<i32>(0);
    0
}

fn main() {}
