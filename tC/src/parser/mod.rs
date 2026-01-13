//! C and ACSL parsing
//!
//! This module handles:
//! - Parsing C files using libclang
//! - Extracting ACSL specifications from comments

pub mod clang;
pub mod acsl;

pub use clang::parse_file;
pub use acsl::{extract_specs, FunctionSpec};
