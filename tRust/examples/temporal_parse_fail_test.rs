//! Temporal Formula Parse Failure Test - Phase 6.2
//!
//! Ensures malformed #[temporal("...")] formulas are rejected early with a
//! compiler error (before model checking is implemented).

#![feature(rustc_attrs)]

// Missing closing ')'
#[temporal("always(count >= 0")]
fn bad_missing_paren(count: i32) -> i32 {
    count
}

fn main() {
    let _ = bad_missing_paren(0);
}
