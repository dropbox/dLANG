// Suppress collapsible warnings - nested if/match structure is often clearer than let-chains
#![allow(clippy::collapsible_if)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::collapsible_match)]
// Allow similar names - caller/callee, param/params are intentional domain terms
#![allow(clippy::similar_names)]
// The Rust test harness can allocate a very large static test array as this crate
// grows; allow clippy warnings that are outside our direct control.
#![cfg_attr(test, allow(clippy::large_stack_arrays, clippy::large_stack_frames))]

//! JSON bridge from tSwift verification conditions to Z4 SMT solver.
//!
//! This crate provides:
//! 1. JSON schema types that mirror tSwift's `ConditionExpr` AST
//! 2. Conversion functions to translate JSON → VC IR
//! 3. Z4 SMT backend for verification
//! 4. C-compatible FFI for calling from Swift compiler (C++)
//!
//! # Architecture
//!
//! ```text
//! tSwift (C++)                    vc-ir-swift (Rust)
//! ┌──────────────┐               ┌──────────────────┐
//! │ConditionExpr │  JSON string  │ SwiftVcBundle    │
//! │ SmtLib2Gen   │ ──────────────│ → VC IR convert  │
//! │ SilTranslator│               │ → Z4 verify()    │
//! └──────────────┘               └──────────────────┘
//!                                         │
//!                                         ▼
//!                                ┌──────────────────┐
//!                                │    Z4 SMT        │
//!                                │  (Pure Rust)     │
//!                                └──────────────────┘
//! ```
//!
//! # JSON Schema
//!
//! The JSON format closely mirrors tSwift's `ConditionExpr`:
//!
//! ```json
//! {
//!   "function_name": "increment",
//!   "source_file": "test.swift",
//!   "source_line": 42,
//!   "parameters": [
//!     {"name": "x", "type": "Int"},
//!     {"name": "flag", "type": "Bool"}
//!   ],
//!   "return_type": "Int",
//!   "requires": [
//!     {"kind": "Gt", "lhs": {"kind": "ParamRef", "name": "x"}, "rhs": {"kind": "IntLit", "value": 0}}
//!   ],
//!   "ensures": [
//!     {"kind": "Ge", "lhs": {"kind": "ResultRef"}, "rhs": {"kind": "ParamRef", "name": "x"}}
//!   ],
//!   "auto_vcs": [
//!     {"kind": "Overflow", "operation": "add", "operands": [...], "description": "x + 1 may overflow"}
//!   ]
//! }
//! ```

pub mod cache;
pub mod condition_parser;
mod convert;
mod error;
mod ffi;
mod json_types;
pub mod kani_backend;
pub mod kani_runner;
pub mod sil_parser;
pub mod sil_to_vcir;
pub mod swift_demangle;
mod types;
mod z3_backend;
mod z4_backend;

pub use convert::*;
pub use error::*;
pub use ffi::*;
pub use json_types::*;
pub use types::*;

#[cfg(test)]
mod tests;
