//! Integration tests for the top-level `bin/tswiftv` wrapper script.
//!
//! These tests only exercise `--sil` mode so they don't depend on a Swift toolchain.

use std::path::PathBuf;
use std::process::Command;

fn get_repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("expected vc-ir-swift/.. to exist")
        .to_path_buf()
}

#[test]
fn cli_tswift_wrapper_sil_mode_json() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");
    let sil = repo_root.join("vc-ir-swift/tests/sil_examples/checked_cast_branch_safe.sil");

    let output = Command::new(tswiftv)
        .current_dir(&repo_root)
        .arg("verify")
        .arg("--sil")
        .arg("--json")
        .arg(sil)
        .output()
        .expect("failed to run bin/tswiftv");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Stable-ish assertion: either a single response or a multi-bundle payload.
    assert!(
        json.get("bundles").is_some() || json.get("function_name").is_some(),
        "unexpected JSON shape: {stdout}"
    );
}

#[test]
fn cli_tswift_wrapper_nonexistent_file_exits_2() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("verify")
        .arg("--sil")
        .arg("nonexistent_file_that_does_not_exist.sil")
        .output()
        .expect("failed to run bin/tswiftv");

    assert!(
        !output.status.success(),
        "expected failure for nonexistent file"
    );
    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for input error, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("not found") || stderr.contains("No such file"),
        "expected error message about missing file, got:\n{stderr}"
    );
}

#[test]
fn cli_tswift_wrapper_verify_help() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("verify")
        .arg("--help")
        .output()
        .expect("failed to run bin/tswiftv verify --help");

    assert!(
        output.status.success(),
        "expected success for verify --help, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    // Wrapper help goes to stdout (like main tswiftv help)
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("tswift") || stdout.contains("USAGE:"),
        "expected help output for verify subcommand, got:\n{stdout}"
    );
}

#[test]
fn cli_tswift_wrapper_sil_mode_human() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");
    let sil = repo_root.join("vc-ir-swift/tests/sil_examples/checked_cast_branch_safe.sil");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("verify")
        .arg("--sil")
        .arg("--human")
        .arg(&sil)
        .output()
        .expect("failed to run bin/tswiftv verify --sil --human");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Human output should mention verification summary or function name
    assert!(
        stdout.contains("verified") || stdout.contains("Verification"),
        "expected human-readable output mentioning verification, got:\n{stdout}"
    );
}

#[test]
fn cli_tswift_wrapper_sil_mode_quiet() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");
    let sil = repo_root.join("vc-ir-swift/tests/sil_examples/checked_cast_branch_safe.sil");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("verify")
        .arg("--sil")
        .arg("--quiet")
        .arg(&sil)
        .output()
        .expect("failed to run bin/tswiftv verify --sil --quiet");

    assert!(
        output.status.success(),
        "expected success with --quiet, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    // Quiet mode should produce minimal or no output for success
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Just verify it doesn't crash and exits 0 for valid input
    assert!(
        stdout.is_empty() || !stdout.contains("error"),
        "unexpected error in quiet output:\n{stdout}"
    );
}

#[test]
fn cli_tswift_wrapper_sil_mode_empty_file() {
    use std::fs;

    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    // Create a temporary empty SIL file
    let temp_dir = std::env::temp_dir();
    let empty_sil = temp_dir.join("tswift_test_empty.sil");
    fs::write(&empty_sil, "").expect("failed to create empty file");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("verify")
        .arg("--sil")
        .arg(&empty_sil)
        .output()
        .expect("failed to run bin/tswiftv verify --sil on empty file");

    // Empty SIL file should succeed (no functions to verify = vacuous success)
    assert!(
        output.status.success(),
        "expected success for empty SIL file, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let _ = fs::remove_file(&empty_sil);
}

#[test]
fn cli_tswift_wrapper_sil_mode_malformed_file() {
    use std::fs;

    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    // Create a temporary malformed SIL file
    let temp_dir = std::env::temp_dir();
    let malformed_sil = temp_dir.join("tswift_test_malformed.sil");
    fs::write(&malformed_sil, "this is not valid SIL at all { } } {")
        .expect("failed to create malformed file");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("verify")
        .arg("--sil")
        .arg(&malformed_sil)
        .output()
        .expect("failed to run bin/tswiftv verify --sil on malformed file");

    // Malformed SIL should succeed but with 0 functions found (parser is lenient)
    // or fail gracefully with parse error - either is acceptable
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Tool should not crash - it should either succeed (0 functions)
    // or fail with exit code 2 (parse error)
    assert!(
        output.status.success() || output.status.code() == Some(2),
        "expected success or exit code 2 for malformed SIL, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    let _ = fs::remove_file(&malformed_sil);
}

#[test]
fn cli_tswift_wrapper_sil_mode_diagnostic_output() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");
    let sil = repo_root.join("vc-ir-swift/tests/sil_examples/checked_cast_branch_safe.sil");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("verify")
        .arg("--sil")
        .arg("--diagnostic")
        .arg(&sil)
        .output()
        .expect("failed to run bin/tswiftv verify --sil --diagnostic");

    assert!(
        output.status.success(),
        "expected success with --diagnostic, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    // Diagnostic output format is compiler-style: file:line:col: message
    // For this test, just verify the output format is reasonable
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Diagnostic mode should produce some output (warnings, info, etc.)
    // but may be empty if all VCs pass silently
    assert!(
        stdout.is_empty() || stdout.contains(':') || stdout.contains("verified"),
        "unexpected diagnostic output format:\n{stdout}"
    );
}
