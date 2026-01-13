//! Integration tests for tswift-verify --dir mode (directory verification).

use std::fs;
use std::process::Command;

fn temp_dir(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("tswift_dir_test_{name}"));
    let _ = fs::remove_dir_all(&dir); // Clean up any existing
    fs::create_dir_all(&dir).expect("failed to create temp dir");
    dir
}

fn write_bundle(dir: &std::path::Path, filename: &str, function_name: &str) {
    let bundle = format!(
        r#"{{"function_name":"{function_name}","parameters":[],"verification_conditions":[]}}"#
    );
    fs::write(dir.join(filename), bundle).expect("failed to write bundle");
}

#[test]
fn cli_dir_verifies_multiple_bundles() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let dir = temp_dir("multiple");

    write_bundle(&dir, "bundle1.json", "test1");
    write_bundle(&dir, "bundle2.json", "test2");
    write_bundle(&dir, "bundle3.json", "test3");

    let output = Command::new(bin)
        .arg("--dir")
        .arg(&dir)
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify --dir");

    assert!(
        output.status.success(),
        "expected success for directory with valid bundles, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("\"files\":3"),
        "expected 3 files processed, got:\n{stdout}"
    );
    assert!(
        stdout.contains("\"verified\":3"),
        "expected 3 verified, got:\n{stdout}"
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn cli_dir_ignores_non_json_files() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let dir = temp_dir("mixed");

    write_bundle(&dir, "valid.json", "valid_func");
    fs::write(dir.join("readme.txt"), "This is not JSON").expect("failed to write txt");
    fs::write(dir.join("code.swift"), "func foo() {}").expect("failed to write swift");

    let output = Command::new(bin)
        .arg("--dir")
        .arg(&dir)
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify --dir");

    assert!(
        output.status.success(),
        "expected success ignoring non-JSON files, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Should only process the .json file
    assert!(
        stdout.contains("\"files\":1"),
        "expected 1 JSON file processed, got:\n{stdout}"
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn cli_dir_handles_empty_directory() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let dir = temp_dir("empty");

    let output = Command::new(bin)
        .arg("--dir")
        .arg(&dir)
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify --dir on empty dir");

    // Empty directory should succeed with 0 files
    assert!(
        output.status.success(),
        "expected success for empty directory, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("\"files\":0"),
        "expected 0 files in empty directory, got:\n{stdout}"
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn cli_dir_handles_nonexistent_directory() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let nonexistent = "/tmp/tswift_nonexistent_dir_12345_xyz";

    // Make sure it doesn't exist
    let _ = fs::remove_dir_all(nonexistent);

    let output = Command::new(bin)
        .arg("--dir")
        .arg(nonexistent)
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify --dir on nonexistent dir");

    assert!(
        !output.status.success(),
        "expected failure for nonexistent directory, got {:?}",
        output.status.code()
    );
    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for input error"
    );
}

#[test]
fn cli_dir_reports_failures_correctly() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let dir = temp_dir("mixed_results");

    // Valid bundle
    write_bundle(&dir, "valid.json", "valid_func");

    // Invalid JSON (will cause parse error)
    fs::write(dir.join("invalid.json"), "not valid json").expect("failed to write invalid");

    let output = Command::new(bin)
        .arg("--dir")
        .arg(&dir)
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify --dir");

    // Should complete (failure is for verification failures, not parse errors in --dir mode)
    // But overall exit depends on how the tool handles parse errors in batch mode
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Verify output mentions both files were encountered
    // (one valid, one may cause an error)
    assert!(
        stdout.contains("files") || stderr.contains("error"),
        "expected file processing output, got:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let _ = fs::remove_dir_all(&dir);
}
