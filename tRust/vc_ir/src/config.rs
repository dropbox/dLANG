//! Trust configuration reading from Cargo.toml
//!
//! This module provides utilities to read trust configuration from
//! `[package.metadata.trust]` in Cargo.toml files.
//!
//! # Cargo.toml Format
//!
//! ```toml
//! [package.metadata.trust]
//! level = "verified"     # Trust level for the crate
//! verify_tests = true    # Also verify test code (default: false)
//! timeout = 30           # Verification timeout in seconds (default: 60)
//! ```
//!
//! # Build Script Usage
//!
//! ```ignore
//! // In build.rs
//! use vc_ir::config::TrustConfig;
//!
//! fn main() {
//!     let config = TrustConfig::from_cargo_toml().unwrap_or_default();
//!
//!     // Set cfg flags based on trust level
//!     if config.level.requires_verification() {
//!         println!("cargo:rustc-cfg=trust_verify");
//!     }
//!
//!     // Set the trust level as cfg value
//!     println!("cargo:rustc-cfg=trust_level=\"{}\"", config.level.as_str());
//! }
//! ```

use crate::TrustLevel;
use serde::{Deserialize, Serialize};
use std::path::Path;

/// Trust configuration for a crate
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustConfig {
    /// Trust level for the crate
    #[serde(default)]
    pub level: TrustLevel,

    /// Whether to verify test code
    #[serde(default)]
    pub verify_tests: bool,

    /// Verification timeout in seconds
    #[serde(default = "default_timeout")]
    pub timeout: u32,

    /// Preferred backend hint
    #[serde(default)]
    pub backend: Option<String>,
}

const fn default_timeout() -> u32 {
    60
}

impl Default for TrustConfig {
    fn default() -> Self {
        Self {
            level: TrustLevel::default(),
            verify_tests: false,
            timeout: default_timeout(),
            backend: None,
        }
    }
}

impl TrustConfig {
    /// Read trust configuration from Cargo.toml in the current directory
    ///
    /// Returns `None` if Cargo.toml doesn't exist or has no trust metadata.
    #[must_use]
    pub fn from_cargo_toml() -> Option<Self> {
        Self::from_cargo_toml_path(Path::new("Cargo.toml"))
    }

    /// Read trust configuration from a specific Cargo.toml path
    #[must_use]
    pub fn from_cargo_toml_path(path: &Path) -> Option<Self> {
        let content = std::fs::read_to_string(path).ok()?;
        Self::from_cargo_toml_str(&content)
    }

    /// Parse trust configuration from Cargo.toml content string
    pub fn from_cargo_toml_str(content: &str) -> Option<Self> {
        // Parse using toml crate-like structure
        // We manually extract the metadata.trust section
        let doc: toml::Table = content.parse().ok()?;

        let package = doc.get("package")?.as_table()?;
        let metadata = package.get("metadata")?.as_table()?;
        let trust = metadata.get("trust")?.as_table()?;

        let level = trust
            .get("level")
            .and_then(|v| v.as_str())
            .and_then(TrustLevel::from_str)
            .unwrap_or_default();

        let verify_tests = trust
            .get("verify_tests")
            .and_then(toml::Value::as_bool)
            .unwrap_or(false);

        let timeout = trust
            .get("timeout")
            .and_then(toml::Value::as_integer)
            .map_or(default_timeout(), |v| {
                u32::try_from(v).unwrap_or_else(|_| default_timeout())
            });

        let backend = trust
            .get("backend")
            .and_then(|v| v.as_str())
            .map(String::from);

        Some(Self {
            level,
            verify_tests,
            timeout,
            backend,
        })
    }

    /// Generate cargo build script output for this configuration
    ///
    /// Returns lines to be printed in build.rs
    #[must_use]
    pub fn cargo_build_output(&self) -> Vec<String> {
        let mut lines = Vec::new();

        // Set trust_verify cfg if verification is required
        if self.level.requires_verification() {
            lines.push("cargo:rustc-cfg=trust_verify".to_string());
        }

        // Set the trust level
        lines.push(format!(
            "cargo:rustc-cfg=trust_level=\"{}\"",
            self.level.as_str()
        ));

        // Set verification mode
        if self.level.failures_are_errors() {
            lines.push("cargo:rustc-cfg=trust_errors".to_string());
        }

        lines
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trust_config_default() {
        let config = TrustConfig::default();
        assert_eq!(config.level, TrustLevel::Assumed);
        assert!(!config.verify_tests);
        assert_eq!(config.timeout, 60);
        assert!(config.backend.is_none());
    }

    #[test]
    fn test_trust_config_from_toml_verified() {
        let toml = r#"
[package]
name = "test"
version = "0.1.0"

[package.metadata.trust]
level = "verified"
verify_tests = true
timeout = 120
backend = "z3"
"#;
        let config = TrustConfig::from_cargo_toml_str(toml).unwrap();
        assert_eq!(config.level, TrustLevel::Verified);
        assert!(config.verify_tests);
        assert_eq!(config.timeout, 120);
        assert_eq!(config.backend, Some("z3".to_string()));
    }

    #[test]
    fn test_trust_config_from_toml_assumed() {
        let toml = r#"
[package]
name = "test"
version = "0.1.0"

[package.metadata.trust]
level = "assumed"
"#;
        let config = TrustConfig::from_cargo_toml_str(toml).unwrap();
        assert_eq!(config.level, TrustLevel::Assumed);
        assert!(!config.verify_tests);
        assert_eq!(config.timeout, 60); // default
    }

    #[test]
    fn test_trust_config_from_toml_audited() {
        let toml = r#"
[package]
name = "test"

[package.metadata.trust]
level = "audited"
"#;
        let config = TrustConfig::from_cargo_toml_str(toml).unwrap();
        assert_eq!(config.level, TrustLevel::Audited);
    }

    #[test]
    fn test_trust_config_from_toml_verified_warn() {
        let toml = r#"
[package]
name = "test"

[package.metadata.trust]
level = "verified_warn"
"#;
        let config = TrustConfig::from_cargo_toml_str(toml).unwrap();
        assert_eq!(config.level, TrustLevel::VerifiedWarn);
    }

    #[test]
    fn test_trust_config_from_toml_no_metadata() {
        let toml = r#"
[package]
name = "test"
version = "0.1.0"
"#;
        let config = TrustConfig::from_cargo_toml_str(toml);
        assert!(config.is_none());
    }

    #[test]
    fn test_trust_config_from_toml_empty_trust() {
        let toml = r#"
[package]
name = "test"

[package.metadata.trust]
"#;
        let config = TrustConfig::from_cargo_toml_str(toml).unwrap();
        assert_eq!(config.level, TrustLevel::Assumed); // default
    }

    #[test]
    fn test_trust_config_cargo_build_output_verified() {
        let config = TrustConfig {
            level: TrustLevel::Verified,
            ..Default::default()
        };
        let output = config.cargo_build_output();
        assert!(output.contains(&"cargo:rustc-cfg=trust_verify".to_string()));
        assert!(output.contains(&"cargo:rustc-cfg=trust_level=\"verified\"".to_string()));
        assert!(output.contains(&"cargo:rustc-cfg=trust_errors".to_string()));
    }

    #[test]
    fn test_trust_config_cargo_build_output_assumed() {
        let config = TrustConfig {
            level: TrustLevel::Assumed,
            ..Default::default()
        };
        let output = config.cargo_build_output();
        assert!(!output.contains(&"cargo:rustc-cfg=trust_verify".to_string()));
        assert!(output.contains(&"cargo:rustc-cfg=trust_level=\"assumed\"".to_string()));
        assert!(!output.contains(&"cargo:rustc-cfg=trust_errors".to_string()));
    }

    #[test]
    fn test_trust_config_cargo_build_output_verified_warn() {
        let config = TrustConfig {
            level: TrustLevel::VerifiedWarn,
            ..Default::default()
        };
        let output = config.cargo_build_output();
        assert!(output.contains(&"cargo:rustc-cfg=trust_verify".to_string()));
        assert!(output.contains(&"cargo:rustc-cfg=trust_level=\"verified_warn\"".to_string()));
        assert!(!output.contains(&"cargo:rustc-cfg=trust_errors".to_string()));
    }

    #[test]
    fn test_trust_config_serialization() {
        let config = TrustConfig {
            level: TrustLevel::Verified,
            verify_tests: true,
            timeout: 90,
            backend: Some("z3".to_string()),
        };

        let json = serde_json::to_string(&config).expect("serialize");
        let parsed: TrustConfig = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(parsed.level, TrustLevel::Verified);
        assert!(parsed.verify_tests);
        assert_eq!(parsed.timeout, 90);
        assert_eq!(parsed.backend, Some("z3".to_string()));
    }
}
