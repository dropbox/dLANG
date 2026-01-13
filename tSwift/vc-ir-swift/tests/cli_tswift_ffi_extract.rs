//! Functional CLI tests for tswift-ffi-extract

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

fn unique_temp_swift_path(suffix: &str) -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let pid = std::process::id();
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("tswift_extract_{pid}_{now}_{n}_{suffix}.swift"))
}

#[test]
fn cli_extract_basic_ffi_annotations() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("tests/ffi_examples/math_import.swift")
        .output()
        .expect("failed to run tswift-ffi-extract");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Should output JSON Lines (one per declaration)
    let lines: Vec<&str> = stdout.lines().collect();
    assert!(
        lines.len() >= 3,
        "expected at least 3 declarations, got {}: {:?}",
        lines.len(),
        lines
    );

    // Verify JSON is parseable and contains expected fields
    for line in &lines {
        let json: serde_json::Value = serde_json::from_str(line)
            .unwrap_or_else(|e| panic!("invalid JSON line: {e}\nline: {line}"));
        assert!(json.get("swift_name").is_some(), "missing swift_name");
        assert!(json.get("attributes").is_some(), "missing attributes");
        assert!(json.get("source_file").is_some(), "missing source_file");
    }

    // Check first declaration is increment
    let first: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert_eq!(first["swift_name"], "increment");
}

#[test]
fn cli_extract_pretty_flag() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Without --pretty: compact JSON
    let compact = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("tests/ffi_examples/math_import.swift")
        .output()
        .expect("failed to run tswift-ffi-extract");

    // With --pretty: indented JSON
    let pretty = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--pretty")
        .arg("tests/ffi_examples/math_import.swift")
        .output()
        .expect("failed to run tswift-ffi-extract --pretty");

    assert!(compact.status.success());
    assert!(pretty.status.success());

    let compact_out = String::from_utf8_lossy(&compact.stdout);
    let pretty_out = String::from_utf8_lossy(&pretty.stdout);

    // Pretty output should have more lines due to indentation
    assert!(
        pretty_out.lines().count() > compact_out.lines().count(),
        "pretty output should have more lines"
    );

    // Pretty output should have indentation (leading spaces)
    assert!(
        pretty_out.contains("  \""),
        "pretty output should be indented"
    );
}

#[test]
fn cli_extract_no_ffi_annotations() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");
    let temp_file = unique_temp_swift_path("no_ffi");

    // Create a Swift file without FFI annotations
    fs::write(
        &temp_file,
        r"// A Swift file with no FFI annotations
func normalFunction(_ x: Int) -> Int {
    return x + 1
}

class SomeClass {
    var value: Int = 0
}
",
    )
    .expect("failed to write temp file");

    let output = Command::new(bin)
        .arg(&temp_file)
        .output()
        .expect("failed to run tswift-ffi-extract");

    assert!(output.status.success());

    // Should produce no output
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.trim().is_empty(),
        "expected empty output for file without FFI annotations, got: {stdout}"
    );

    let _ = fs::remove_file(&temp_file);
}

#[test]
fn cli_extract_nonexistent_file() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");

    let output = Command::new(bin)
        .arg("/nonexistent/path/to/file.swift")
        .output()
        .expect("failed to run tswift-ffi-extract");

    assert!(
        !output.status.success(),
        "expected failure for nonexistent file"
    );
    assert_eq!(output.status.code(), Some(2));

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("error reading"),
        "expected error message, got: {stderr}"
    );
}

#[test]
fn cli_extract_multiple_files() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("tests/ffi_examples/math_import.swift")
        .arg("tests/ffi_examples/buffer_import.swift")
        .output()
        .expect("failed to run tswift-ffi-extract");

    assert!(output.status.success());

    let stdout = String::from_utf8_lossy(&output.stdout);
    let lines: Vec<&str> = stdout.lines().collect();

    // math_import has 4 declarations, buffer_import has 1
    assert!(
        lines.len() >= 4,
        "expected declarations from multiple files"
    );

    // Verify we have declarations from both files
    let has_math = lines.iter().any(|line| line.contains("math_import.swift"));
    let has_buffer = lines
        .iter()
        .any(|line| line.contains("buffer_import.swift"));

    assert!(has_math, "expected declarations from math_import.swift");
    assert!(has_buffer, "expected declarations from buffer_import.swift");
}

#[test]
fn cli_extract_only_flags_no_files() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");

    let output = Command::new(bin)
        .arg("--pretty")
        .output()
        .expect("failed to run tswift-ffi-extract");

    assert!(
        !output.status.success(),
        "expected failure when only flags provided"
    );
    assert_eq!(output.status.code(), Some(2));

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("no input files"),
        "expected 'no input files' error, got: {stderr}"
    );
}

#[test]
fn cli_extract_unknown_flag_ignored_needs_files() {
    // tswift-ffi-extract silently ignores unknown flags (filters them out)
    // but still requires input files
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");

    let output = Command::new(bin)
        .arg("--unknown-flag")
        .output()
        .expect("failed to run tswift-ffi-extract");

    assert!(
        !output.status.success(),
        "expected failure when only unknown flag provided (no files)"
    );
    assert_eq!(output.status.code(), Some(2));

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("no input files"),
        "expected 'no input files' error (unknown flags are ignored), got: {stderr}"
    );
}

#[test]
fn cli_extract_unknown_flag_with_valid_file() {
    // tswift-ffi-extract silently ignores unknown flags and processes the file
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--unknown-flag-xyz")
        .arg("tests/ffi_examples/math_import.swift")
        .output()
        .expect("failed to run tswift-ffi-extract");

    assert!(
        output.status.success(),
        "expected success (unknown flag should be ignored), got {:?}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr),
    );

    // Should still produce output
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.is_empty(), "expected output even with unknown flag");
}
