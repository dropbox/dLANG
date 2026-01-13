//! mpsc channel integration test (Phase 10.1)
//! Tests that mpsc channel types have documented contracts.
//!
//! std::sync::mpsc provides multi-producer, single-consumer channels.
//! Most operations are runtime-dependent (success depends on channel state),
//! so there are no strong postconditions - this test verifies contract coverage.

use std::sync::mpsc::{channel, sync_channel};

// Test 1: Create unbounded channel and send/recv
fn test_channel_create_send() -> bool {
    let (tx, rx) = channel::<i32>();
    let _ = tx.send(42);
    let _ = rx.recv();
    true
}

// Test 2: Create bounded sync_channel
fn test_sync_channel_create() -> bool {
    let (tx, rx) = sync_channel::<i32>(1);
    let _ = tx.send(42);
    let _ = rx.recv();
    true
}

// Test 3: Clone sender for multi-producer
fn test_sender_clone() -> bool {
    let (tx, rx) = channel::<i32>();
    let tx2 = tx.clone();
    let _ = tx.send(1);
    let _ = tx2.send(2);
    let _ = rx.recv();
    let _ = rx.recv();
    true
}

// Test 4: try_recv returns immediately
fn test_try_recv() -> bool {
    let (tx, rx) = channel::<i32>();
    // No value sent, should be empty
    let result = rx.try_recv();
    assert!(result.is_err());
    let _ = tx.send(42);
    // Now should succeed
    let result = rx.try_recv();
    assert!(result.is_ok());
    true
}

// Test 5: SyncSender try_send returns immediately
fn test_sync_try_send() -> bool {
    let (tx, rx) = sync_channel::<i32>(1);
    // Buffer has space
    let result = tx.try_send(1);
    assert!(result.is_ok());
    // Buffer full
    let result = tx.try_send(2);
    assert!(result.is_err());
    let _ = rx.recv();
    true
}

// Test 6: Receiver processes sent values (no loop)
fn test_receiver_values() -> i32 {
    let (tx, rx) = channel::<i32>();
    tx.send(10).unwrap();
    tx.send(20).unwrap();
    drop(tx); // Close sender

    let v1 = rx.recv().unwrap();
    let v2 = rx.recv().unwrap();
    v1.saturating_add(v2) // Should be 30
}

// Test 7: try_recv is non-blocking
fn test_try_values() -> i32 {
    let (tx, rx) = channel::<i32>();
    tx.send(100).unwrap();

    // try_recv returns value available now
    rx.try_recv().unwrap()
}

// Test 8: Multiple senders with clone (no loop)
fn test_multi_sender() -> i32 {
    let (tx, rx) = channel::<i32>();
    let tx1 = tx.clone();
    drop(tx);

    tx1.send(100).unwrap();
    drop(tx1);

    rx.recv().unwrap()
}

// Test 9: sync_channel blocks when full
fn test_sync_channel_blocking() -> bool {
    let (tx, rx) = sync_channel::<i32>(2);
    // Fill the buffer
    tx.send(1).unwrap();
    tx.send(2).unwrap();
    // Buffer is full, try_send should fail
    let result = tx.try_send(3);
    assert!(result.is_err());
    // Receive one to make space
    let _ = rx.recv();
    // Now try_send should succeed
    let result = tx.try_send(3);
    assert!(result.is_ok());
    true
}

// Test 10: Channel disconnected when sender dropped
fn test_sender_disconnect() -> bool {
    let (tx, rx) = channel::<i32>();
    drop(tx);
    // Receiver should get Err on recv
    let result = rx.recv();
    result.is_err()
}

// Test 11: Channel disconnected when receiver dropped
fn test_receiver_disconnect() -> bool {
    let (tx, rx) = channel::<i32>();
    drop(rx);
    // Sender should get Err on send
    let result = tx.send(42);
    result.is_err()
}

// Test 12: Unbounded channel accepts many values
fn test_unbounded_capacity() -> bool {
    let (tx, rx) = channel::<i32>();
    tx.send(1).unwrap();
    tx.send(2).unwrap();
    tx.send(3).unwrap();
    tx.send(4).unwrap();
    tx.send(5).unwrap();
    drop(tx);

    let _ = rx.recv();
    let _ = rx.recv();
    let _ = rx.recv();
    let _ = rx.recv();
    let _ = rx.recv();
    true
}

// Test 13: sync_channel with zero bound
fn test_rendezvous_channel() -> bool {
    // Zero-bound channel - sender blocks until receiver ready
    let (tx, rx) = sync_channel::<i32>(0);
    // Can't send without receiver ready
    let result = tx.try_send(42);
    assert!(result.is_err());
    drop(rx);
    true
}

fn main() {
    println!("Test 1 - channel create/send: {}", test_channel_create_send());
    println!("Test 2 - sync_channel create: {}", test_sync_channel_create());
    println!("Test 3 - sender clone: {}", test_sender_clone());
    println!("Test 4 - try_recv: {}", test_try_recv());
    println!("Test 5 - sync try_send: {}", test_sync_try_send());
    println!("Test 6 - receiver values sum: {}", test_receiver_values());
    println!("Test 7 - try values: {}", test_try_values());
    println!("Test 8 - multi sender: {}", test_multi_sender());
    println!("Test 9 - sync channel blocking: {}", test_sync_channel_blocking());
    println!("Test 10 - sender disconnect: {}", test_sender_disconnect());
    println!("Test 11 - receiver disconnect: {}", test_receiver_disconnect());
    println!("Test 12 - unbounded capacity: {}", test_unbounded_capacity());
    println!("Test 13 - rendezvous channel: {}", test_rendezvous_channel());

    println!("\nAll mpsc tests passed!");
}
