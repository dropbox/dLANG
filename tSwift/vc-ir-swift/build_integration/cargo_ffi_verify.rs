//! Cargo build.rs template for automatic FFI verification
//!
//! Copy this file to your project's `build.rs` (or merge with existing build.rs)
//! to automatically verify FFI compatibility between Swift and Rust sources
//! during `cargo build`.
//!
//! # Configuration
//!
//! Set these environment variables or modify the constants below:
//!
//! - `FFI_VERIFY_SWIFT_FILES`: Comma-separated list of Swift source files
//! - `FFI_VERIFY_RUST_FILES`: Comma-separated list of Rust source files
//! - `FFI_VERIFY_GENERATED_FILES`: Comma-separated list of swift-bridge generated files
//! - `FFI_VERIFY_ENABLE`: Set to "0" to disable verification (default: enabled)
//! - `FFI_VERIFY_Z4`: Set to "1" to enable Z4 semantic proofs (default: structural only)
//! - `FFI_VERIFY_STRICT`: Set to "1" to fail build on verification failure (default: warn only)
//!
//! # Usage
//!
//! 1. Install tswift-ffi-verify:
//!    ```bash
//!    cargo install --git https://github.com/dropbox/dLANG/tSwift --bin tswift-ffi-verify
//!    ```
//!
//! 2. Add to your Cargo.toml:
//!    ```toml
//!    [package]
//!    build = "build.rs"
//!    ```
//!
//! 3. Create build.rs with your file paths configured below.
//!
//! # Example
//!
//! ```rust
//! // build.rs
//! const SWIFT_FILES: &[&str] = &["../ios/Sources/FFI.swift"];
//! const RUST_FILES: &[&str] = &["src/ffi.rs"];
//! const GENERATED_FILES: &[&str] = &["../ios/Generated/FFI.swift"];
//! ```

use std::env;
use std::path::PathBuf;
use std::process::Command;

// ============================================================================
// Configuration: Modify these paths for your project
// ============================================================================

/// Swift source files with @_ffi_* annotations
const SWIFT_FILES: &[&str] = &[
    // "../swift/Sources/FFI.swift",
];

/// Rust source files with #[ffi_export] functions
const RUST_FILES: &[&str] = &[
    // "src/ffi.rs",
];

/// swift-bridge generated Swift files
const GENERATED_FILES: &[&str] = &[
    // "../swift/Generated/BridgeFFI.swift",
];

// ============================================================================
// Build script implementation
// ============================================================================

fn main() {
    // Check if FFI verification is enabled
    if env::var("FFI_VERIFY_ENABLE").is_ok_and(|v| v == "0") {
        println!("cargo:warning=FFI verification disabled (FFI_VERIFY_ENABLE=0)");
        return;
    }

    // Collect files from configuration or environment
    let swift_files = collect_files(SWIFT_FILES, "FFI_VERIFY_SWIFT_FILES");
    let rust_files = collect_files(RUST_FILES, "FFI_VERIFY_RUST_FILES");
    let generated_files = collect_files(GENERATED_FILES, "FFI_VERIFY_GENERATED_FILES");

    // Skip if no files configured
    if swift_files.is_empty() && generated_files.is_empty() && rust_files.is_empty() {
        return;
    }

    // Get project root (parent of target dir)
    let out_dir = env::var("OUT_DIR").expect("OUT_DIR not set");
    let project_root = PathBuf::from(&out_dir)
        .ancestors()
        .nth(4) // OUT_DIR -> target/debug/build/<pkg>/out -> project root
        .expect("Could not find project root")
        .to_path_buf();

    // Find tswift-ffi-verify binary
    let verify_bin = find_ffi_verify_binary();

    // Build command
    let mut cmd = Command::new(&verify_bin);

    // Add Swift files
    if !swift_files.is_empty() {
        cmd.arg("--swift");
        for f in &swift_files {
            let path = resolve_path(&project_root, f);
            println!("cargo:rerun-if-changed={}", path.display());
            cmd.arg(&path);
        }
    }

    // Add generated files
    if !generated_files.is_empty() {
        cmd.arg("--generated");
        for f in &generated_files {
            let path = resolve_path(&project_root, f);
            println!("cargo:rerun-if-changed={}", path.display());
            cmd.arg(&path);
        }
    }

    // Add Rust files
    if !rust_files.is_empty() {
        cmd.arg("--rust");
        for f in &rust_files {
            let path = resolve_path(&project_root, f);
            println!("cargo:rerun-if-changed={}", path.display());
            cmd.arg(&path);
        }
    }

    // Add Z4 flag if requested
    if env::var("FFI_VERIFY_Z4").is_ok_and(|v| v == "1") {
        cmd.arg("--z4");
    }

    // Run verification
    println!("cargo:warning=Running FFI verification...");

    let output = cmd.output();

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            // Print output as cargo warnings
            for line in stdout.lines().chain(stderr.lines()) {
                if !line.is_empty() {
                    println!("cargo:warning=FFI: {}", line);
                }
            }

            if !output.status.success() {
                let strict = env::var("FFI_VERIFY_STRICT").is_ok_and(|v| v == "1");
                if strict {
                    panic!("FFI verification failed (FFI_VERIFY_STRICT=1)");
                } else {
                    println!("cargo:warning=FFI verification failed (set FFI_VERIFY_STRICT=1 to fail build)");
                }
            } else {
                println!("cargo:warning=FFI verification passed");
            }
        }
        Err(e) => {
            println!("cargo:warning=Could not run tswift-ffi-verify: {}", e);
            println!("cargo:warning=Install with: cargo install --git https://github.com/dropbox/dLANG/tSwift --bin tswift-ffi-verify");
        }
    }
}

fn collect_files(defaults: &[&str], env_var: &str) -> Vec<String> {
    if let Ok(files) = env::var(env_var) {
        files.split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect()
    } else {
        defaults.iter().map(|s| s.to_string()).collect()
    }
}

fn resolve_path(root: &PathBuf, path: &str) -> PathBuf {
    let p = PathBuf::from(path);
    if p.is_absolute() {
        p
    } else {
        root.join(p)
    }
}

fn find_ffi_verify_binary() -> PathBuf {
    // Check TSWIFT_FFI_VERIFY_BIN environment variable
    if let Ok(bin) = env::var("TSWIFT_FFI_VERIFY_BIN") {
        return PathBuf::from(bin);
    }

    // Check common locations
    let candidates = [
        // Cargo-installed binary
        home::home_dir().map(|h| h.join(".cargo/bin/tswift-ffi-verify")),
        // In PATH
        which::which("tswift-ffi-verify").ok(),
        // Local development build
        Some(PathBuf::from("../tSwift/vc-ir-swift/target/release/tswift-ffi-verify")),
    ];

    for candidate in candidates.into_iter().flatten() {
        if candidate.exists() {
            return candidate;
        }
    }

    // Default to hoping it's in PATH
    PathBuf::from("tswift-ffi-verify")
}
