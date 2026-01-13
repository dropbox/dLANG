//! trust-upstream library
//!
//! Provides components for tracking and syncing with upstream Rust releases.

pub mod analyzer;
pub mod db;
pub mod monitor;
pub mod sync;

pub use analyzer::ImpactAnalyzer;
pub use db::SyncDatabase;
pub use monitor::ReleaseMonitor;
pub use sync::SyncPipeline;
