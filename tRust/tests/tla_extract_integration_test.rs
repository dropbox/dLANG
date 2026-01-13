// Integration test for async state machine extraction (Phase 3 of DIRECTIVE_TLA_EXTRACT)
//
// This test verifies that:
// 1. trustc --extract-state-machines detects async functions
// 2. Extracted state machines are valid TLA2 JSON format
// 3. Output can be written to file
//
// Run with: ./tests/run_tla_extract_test.sh

async fn simple_async() {
    // A simple async function with no awaits
    println!("hello");
}

async fn with_await() {
    // An async function that awaits another
    simple_async().await;
}

async fn two_awaits() {
    // Two sequential awaits
    simple_async().await;
    simple_async().await;
}

fn main() {
    // Entry point for compilation
    println!("TLA extract integration test");
}
