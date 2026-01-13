//! Time types integration test (Phase 10.1)
//! Tests Duration, Instant, and SystemTime contracts.
//!
//! Duration represents a span of time (always non-negative).
//! Key provable properties:
//! - as_secs(), as_millis(), as_micros(), as_nanos() return >= 0
//! - subsec_millis() returns in [0, 999]
//! - subsec_micros() returns in [0, 999_999]
//! - subsec_nanos() returns in [0, 999_999_999]
//!
//! Instant and SystemTime are opaque runtime-dependent types.

use std::time::{Duration, Instant, SystemTime};

// Test 1: Duration::as_secs returns non-negative value
#[ensures("result >= 0")]
fn test_duration_as_secs(d: Duration) -> u64 {
    d.as_secs()
}

// Test 2: Duration::as_millis returns non-negative value
#[ensures("result >= 0")]
fn test_duration_as_millis(d: Duration) -> u128 {
    d.as_millis()
}

// Test 3: Duration::as_micros returns non-negative value
#[ensures("result >= 0")]
fn test_duration_as_micros(d: Duration) -> u128 {
    d.as_micros()
}

// Test 4: Duration::as_nanos returns non-negative value
#[ensures("result >= 0")]
fn test_duration_as_nanos(d: Duration) -> u128 {
    d.as_nanos()
}

// Test 5: Duration::subsec_millis returns value in [0, 1000)
#[ensures("result >= 0")]
#[ensures("result < 1000")]
fn test_duration_subsec_millis(d: Duration) -> u32 {
    d.subsec_millis()
}

// Test 6: Duration::subsec_micros returns value in [0, 1_000_000)
#[ensures("result >= 0")]
#[ensures("result < 1000000")]
fn test_duration_subsec_micros(d: Duration) -> u32 {
    d.subsec_micros()
}

// Test 7: Duration::subsec_nanos returns value in [0, 1_000_000_000)
#[ensures("result >= 0")]
#[ensures("result < 1000000000")]
fn test_duration_subsec_nanos(d: Duration) -> u32 {
    d.subsec_nanos()
}

// Test 8: Duration::from_secs creates Duration (no strong postcondition)
fn test_duration_from_secs(secs: u64) -> Duration {
    Duration::from_secs(secs)
}

// Test 9: Duration::from_millis creates Duration
fn test_duration_from_millis(millis: u64) -> Duration {
    Duration::from_millis(millis)
}

// Test 10: Duration::new creates Duration from secs and nanos
fn test_duration_new(secs: u64, nanos: u32) -> Duration {
    Duration::new(secs, nanos)
}

// Test 11: Duration::is_zero check (no postcondition - runtime dependent)
fn test_duration_is_zero(d: Duration) -> bool {
    d.is_zero()
}

// Test 12: Instant::now creates current time (runtime dependent)
fn test_instant_now() -> Instant {
    Instant::now()
}

// Test 13: SystemTime::now creates current system time (runtime dependent)
fn test_systemtime_now() -> SystemTime {
    SystemTime::now()
}

fn main() {
    // Create test durations
    let d1 = Duration::from_secs(5);
    let d2 = Duration::from_millis(5500);
    let d3 = Duration::new(3, 500_000_000); // 3.5 seconds

    // Test as_secs
    println!("Duration from_secs(5) as_secs: {}", test_duration_as_secs(d1));

    // Test as_millis
    println!("Duration from_millis(5500) as_millis: {}", test_duration_as_millis(d2));

    // Test as_micros
    println!("Duration new(3, 500M) as_micros: {}", test_duration_as_micros(d3));

    // Test as_nanos
    println!("Duration from_secs(5) as_nanos: {}", test_duration_as_nanos(d1));

    // Test subsec_millis
    println!("Duration from_millis(5500) subsec_millis: {}", test_duration_subsec_millis(d2));

    // Test subsec_micros
    println!("Duration new(3, 500M) subsec_micros: {}", test_duration_subsec_micros(d3));

    // Test subsec_nanos
    println!("Duration new(3, 500M) subsec_nanos: {}", test_duration_subsec_nanos(d3));

    // Test constructors
    let _ = test_duration_from_secs(10);
    let _ = test_duration_from_millis(10000);
    let _ = test_duration_new(1, 500_000_000);

    // Test is_zero
    println!("Duration::ZERO is_zero: {}", test_duration_is_zero(Duration::ZERO));
    println!("Duration from_secs(5) is_zero: {}", test_duration_is_zero(d1));

    // Test Instant and SystemTime
    let _ = test_instant_now();
    let _ = test_systemtime_now();

    println!("All time tests completed!");
}
