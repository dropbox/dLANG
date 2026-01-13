//! Verification Condition Generation
//!
//! Translates C code + ACSL specs into VC IR (shared with tRust).

mod c_to_vcir;

pub use c_to_vcir::generate_vcs;
