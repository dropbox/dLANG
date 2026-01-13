//! Test file for anomaly detection (Phase 6.5.4)
//! This file contains intentional anomalies to test detection.

// Test 1: Unhandled Result - NOT using _ prefix
fn unhandled_result() {
    let x = std::fs::read_to_string("test.txt");
    // Result is assigned to x (not _x) but not handled - should be flagged
    println!("done");
}

// Test 2: Function with dead code (unreachable block via optimization)
fn with_dead_code(x: i32) -> i32 {
    if true {
        return x + 1;
    } else {
        // This branch should be optimized away
        return x - 1;
    }
}

// Test 3: Unused assigned value
fn unused_value() {
    let x = 42;  // Assigned but never used
    let _y = 10; // Prefixed with _ so not flagged
}

// Test 4: Normal function (no anomalies expected)
fn normal_function(a: i32, b: i32) -> i32 {
    a + b
}

// Test 5: Function that properly handles Result
fn proper_result_handling() -> Result<String, std::io::Error> {
    let content = std::fs::read_to_string("test.txt")?;
    Ok(content)
}

fn main() {
    let _ = unhandled_result();
    let _ = with_dead_code(5);
    unused_value();
    let _ = normal_function(1, 2);
    let _ = proper_result_handling();
}
