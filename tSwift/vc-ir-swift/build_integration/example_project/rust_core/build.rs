//! Build script with FFI verification integration.
//!
//! This demonstrates automatic FFI verification during `cargo build`.

use std::env;
use std::path::PathBuf;
use std::process::Command;

// Configuration: Swift/Rust files for FFI verification
const SWIFT_FILES: &[&str] = &[
    "../swift_app/Sources/FFI.swift",
];

const RUST_FILES: &[&str] = &[
    "src/lib.rs",
];

const GENERATED_FILES: &[&str] = &[];

fn main() {
    // Tell cargo to re-run if these environment variables change
    println!("cargo:rerun-if-env-changed=FFI_VERIFY_ENABLE");
    println!("cargo:rerun-if-env-changed=FFI_VERIFY_Z4");
    println!("cargo:rerun-if-env-changed=FFI_VERIFY_STRICT");
    println!("cargo:rerun-if-env-changed=TSWIFT_FFI_VERIFY_BIN");
    println!("cargo:rerun-if-env-changed=FFI_VERIFY_SWIFT_FILES");
    println!("cargo:rerun-if-env-changed=FFI_VERIFY_RUST_FILES");
    println!("cargo:rerun-if-env-changed=FFI_VERIFY_GENERATED_FILES");

    // Check if FFI verification is enabled
    if env::var("FFI_VERIFY_ENABLE").is_ok_and(|v| v == "0") {
        println!("cargo:warning=FFI verification disabled");
        return;
    }

    // Collect files
    let swift_files = collect_files(SWIFT_FILES, "FFI_VERIFY_SWIFT_FILES");
    let rust_files = collect_files(RUST_FILES, "FFI_VERIFY_RUST_FILES");
    let generated_files = collect_files(GENERATED_FILES, "FFI_VERIFY_GENERATED_FILES");

    if swift_files.is_empty() && generated_files.is_empty() && rust_files.is_empty() {
        return;
    }

    // Get project root
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
    let project_root = PathBuf::from(&manifest_dir);

    // Find tswift-ffi-verify
    let verify_bin = find_ffi_verify_binary();

    // Build command
    let mut cmd = Command::new(&verify_bin);

    if !swift_files.is_empty() {
        cmd.arg("--swift");
        for f in &swift_files {
            let path = resolve_path(&project_root, f);
            println!("cargo:rerun-if-changed={}", path.display());
            cmd.arg(&path);
        }
    }

    if !generated_files.is_empty() {
        cmd.arg("--generated");
        for f in &generated_files {
            let path = resolve_path(&project_root, f);
            println!("cargo:rerun-if-changed={}", path.display());
            cmd.arg(&path);
        }
    }

    if !rust_files.is_empty() {
        cmd.arg("--rust");
        for f in &rust_files {
            let path = resolve_path(&project_root, f);
            println!("cargo:rerun-if-changed={}", path.display());
            cmd.arg(&path);
        }
    }

    if env::var("FFI_VERIFY_Z4").is_ok_and(|v| v == "1") {
        cmd.arg("--z4");
    }

    println!("cargo:warning=Running FFI verification...");

    match cmd.output() {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            for line in stdout.lines().chain(stderr.lines()) {
                if !line.is_empty() {
                    println!("cargo:warning=FFI: {}", line);
                }
            }

            if !output.status.success() {
                let strict = env::var("FFI_VERIFY_STRICT").is_ok_and(|v| v == "1");
                if strict {
                    panic!("FFI verification failed");
                } else {
                    println!("cargo:warning=FFI verification failed (use FFI_VERIFY_STRICT=1 to fail)");
                }
            } else {
                println!("cargo:warning=FFI verification passed");
            }
        }
        Err(e) => {
            println!("cargo:warning=Could not run tswift-ffi-verify: {}", e);
        }
    }
}

fn collect_files(defaults: &[&str], env_var: &str) -> Vec<String> {
    if let Ok(files) = env::var(env_var) {
        files.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect()
    } else {
        defaults.iter().map(|s| s.to_string()).collect()
    }
}

fn resolve_path(root: &PathBuf, path: &str) -> PathBuf {
    let p = PathBuf::from(path);
    if p.is_absolute() { p } else { root.join(p) }
}

fn find_ffi_verify_binary() -> PathBuf {
    if let Ok(bin) = env::var("TSWIFT_FFI_VERIFY_BIN") {
        return PathBuf::from(bin);
    }

    let candidates = [
        home::home_dir().map(|h| h.join(".cargo/bin/tswift-ffi-verify")),
        which::which("tswift-ffi-verify").ok(),
    ];

    for candidate in candidates.into_iter().flatten() {
        if candidate.exists() {
            return candidate;
        }
    }

    PathBuf::from("tswift-ffi-verify")
}
