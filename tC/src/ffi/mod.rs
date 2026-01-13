//! FFI Boundary Verification
//!
//! Verifies that contracts match at language boundaries:
//! - Swift ↔ C (bridging headers)
//! - Rust ↔ C (extern "C")

mod rust;
mod swift;

pub use rust::verify_rust_boundary;
pub use swift::verify_swift_boundary;
