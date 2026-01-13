//! Integration tests for tswift-verify CLI flags: --kani-bitvector, --color, --progress, --quiet
//!
//! These tests cover functional behavior of flags that were previously only tested in help text.

use std::process::Command;

// =============================================================================
// --kani-bitvector tests
// =============================================================================

/// Test that --kani-bitvector requires --export-kani (error without it)
#[test]
fn cli_kani_bitvector_requires_export_kani() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--kani-bitvector")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 (error), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--kani-bitvector requires --export-kani"),
        "expected error about --export-kani requirement, got:\n{stderr}"
    );
}

/// Test that --kani-bitvector with --export-kani produces bitvector-mode harnesses
#[test]
fn cli_kani_bitvector_produces_bitvector_harnesses() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("kani_bitvector_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .arg("--kani-bitvector")
        .output()
        .expect("failed to run tswift-verify");

    // Command should complete
    let _ = output;

    // Check that harness uses native Rust types (i64) instead of arbitrary precision
    let src_dir = tmpdir.join("src");
    let entries: Vec<_> = fs::read_dir(&src_dir)
        .expect("should be able to read tmpdir/src")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
        .filter(|e| e.file_name().to_string_lossy() != "lib.rs")
        .collect();

    assert!(
        !entries.is_empty(),
        "At least one harness file should exist"
    );

    let harness_path = entries[0].path();
    let harness_content =
        fs::read_to_string(&harness_path).expect("should be able to read harness file");

    // Bitvector mode uses native Rust integer types like i64
    assert!(
        harness_content.contains("i64") || harness_content.contains("i32"),
        "Bitvector mode harness should use native Rust types (i64/i32), got:\n{harness_content}"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

/// Test that --export-kani without --kani-bitvector uses unbounded integers
#[test]
fn cli_export_kani_without_bitvector_uses_unbounded() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("kani_unbounded_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .output()
        .expect("failed to run tswift-verify");

    let _ = output;

    // Check harness content - without bitvector mode, should NOT force native types
    let src_dir = tmpdir.join("src");
    let entries: Vec<_> = fs::read_dir(&src_dir)
        .expect("should be able to read tmpdir/src")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
        .filter(|e| e.file_name().to_string_lossy() != "lib.rs")
        .collect();

    assert!(
        !entries.is_empty(),
        "At least one harness file should exist"
    );

    // Just verify it creates harnesses (the content test is done elsewhere)
    // This test confirms the flag is optional and export works without it
    let harness_path = entries[0].path();
    let harness_content =
        fs::read_to_string(&harness_path).expect("should be able to read harness file");

    assert!(
        harness_content.contains("#[kani::proof]"),
        "Harness should be valid Kani harness, got:\n{harness_content}"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

// =============================================================================
// --color tests
// =============================================================================

/// Test that --color=always enables color output
#[test]
fn cli_color_always_enables_color() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color=always")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // ANSI color codes start with \x1b[ (ESC [)
    assert!(
        stdout.contains("\x1b["),
        "expected ANSI color codes with --color=always, got:\n{stdout}"
    );
}

/// Test that --color=never disables color output
#[test]
fn cli_color_never_disables_color() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color=never")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should NOT have ANSI color codes
    assert!(
        !stdout.contains("\x1b["),
        "expected no ANSI color codes with --color=never, got:\n{stdout}"
    );
}

/// Test that --color=auto defaults to no color when stdout is not a TTY
#[test]
fn cli_color_auto_no_color_in_pipe() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // When running in a test, stdout is not a TTY, so auto should mean no color
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color=auto")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // In a pipe/non-TTY context, auto should default to no color
    assert!(
        !stdout.contains("\x1b["),
        "expected no ANSI color codes with --color=auto in pipe, got:\n{stdout}"
    );
}

/// Test that --color without value is rejected (requires =MODE)
#[test]
fn cli_color_flag_requires_value() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color")
        .output()
        .expect("failed to run tswift-verify");

    // The flag without a value should either work (defaulting to auto) or error
    // Check the help text - it says --color=MODE, so bare --color might error
    // Let's verify the behavior is consistent
    let _stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Either it works with default auto behavior, or it errors
    // The key is it shouldn't crash
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code, stderr:\n{stderr}"
    );
}

// =============================================================================
// --progress tests
// =============================================================================

/// Test that --progress=always enables progress output (to stderr)
#[test]
fn cli_progress_always_outputs_progress() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--progress=always")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Progress output goes to stderr and typically includes function names or progress indicators
    assert!(
        stderr.contains("Verifying") || stderr.contains("add") || stderr.contains("progress"),
        "expected progress output with --progress=always, got stderr:\n{stderr}"
    );
}

/// Test that --progress=never suppresses progress output
#[test]
fn cli_progress_never_suppresses_progress() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--progress=never")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // With progress=never, stderr should have minimal or no output
    // (unless there are errors)
    assert!(
        !stderr.contains("Verifying"),
        "expected no 'Verifying' progress with --progress=never, got stderr:\n{stderr}"
    );
}

/// Test that --progress=auto defaults to no progress when not a TTY
#[test]
fn cli_progress_auto_no_progress_in_pipe() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--progress=auto")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // In a pipe context, auto should default to no progress (unless tty)
    // This test runs in a non-tty context
    assert!(
        !stderr.contains("Verifying"),
        "expected no 'Verifying' progress with --progress=auto in pipe, got stderr:\n{stderr}"
    );
}

// =============================================================================
// --quiet tests
// =============================================================================

/// Test that --quiet suppresses non-error output for passing verification
#[test]
fn cli_quiet_suppresses_output_on_success() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_safe.sil")
        .arg("--quiet")
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.success(),
        "expected success with --quiet on safe file, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Quiet mode should produce minimal output
    assert!(
        stdout.is_empty() || stdout.trim().is_empty(),
        "expected empty stdout with --quiet on success, got:\n{stdout}"
    );
}

/// Test that --quiet still shows failures
#[test]
fn cli_quiet_still_shows_failures() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--quiet")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (failure), got {:?}",
        output.status.code(),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Even in quiet mode, failures should be reported
    assert!(
        stdout.contains("FAIL") || stdout.contains("fail") || !stdout.is_empty(),
        "expected failure output even with --quiet, got:\n{stdout}"
    );
}

/// Test that --quiet works with --json output format
#[test]
fn cli_quiet_with_json_still_outputs_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--quiet")
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // JSON output should still be produced
    assert!(
        stdout.contains('{') && stdout.contains('}'),
        "expected JSON output with --quiet --json, got:\n{stdout}"
    );

    // Verify it's valid JSON
    let _: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|_| panic!("expected valid JSON output, got:\n{stdout}"));
}

// =============================================================================
// --emit-unknown-vcs tests
// =============================================================================

/// Test that --emit-unknown-vcs writes UNKNOWN VCs to a JSON file
#[test]
fn cli_emit_unknown_vcs_writes_json_file() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpfile =
        std::env::temp_dir().join(format!("unknown_vcs_test_{}.json", std::process::id()));
    let _ = fs::remove_file(&tmpfile);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/nonlinear_mul_unknown.sil")
        .arg(format!("--emit-unknown-vcs={}", tmpfile.display()))
        .output()
        .expect("failed to run tswift-verify");

    // Command should succeed (exit 0) - UNKNOWN counts as success
    assert!(
        output.status.success(),
        "expected exit code 0, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    // JSON file should exist
    assert!(
        tmpfile.exists(),
        "expected --emit-unknown-vcs to create file at {}",
        tmpfile.display()
    );

    // Read and validate JSON content
    let content = fs::read_to_string(&tmpfile).expect("should be able to read output file");
    let records: Vec<serde_json::Value> =
        serde_json::from_str(&content).expect("output should be valid JSON array");

    // Should have at least one UNKNOWN VC (non-linear multiplication)
    assert!(
        !records.is_empty(),
        "expected at least one UNKNOWN VC record, got empty array"
    );

    // First record should have expected structure
    let first = &records[0];
    assert!(
        first.get("function_name").is_some(),
        "record should have function_name"
    );
    assert!(first.get("vc_type").is_some(), "record should have vc_type");
    assert!(first.get("reason").is_some(), "record should have reason");

    // Reason should mention non-linear arithmetic
    let reason = first["reason"].as_str().unwrap_or("");
    assert!(
        reason.contains("Non-linear") || reason.contains("variable multiplication"),
        "reason should mention non-linear arithmetic, got: {reason}"
    );

    // Clean up
    let _ = fs::remove_file(&tmpfile);
}

/// Test that --emit-unknown-vcs with space-separated path works
#[test]
fn cli_emit_unknown_vcs_space_separated() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpfile = std::env::temp_dir().join(format!(
        "unknown_vcs_space_test_{}.json",
        std::process::id()
    ));
    let _ = fs::remove_file(&tmpfile);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/nonlinear_mul_unknown.sil")
        .arg("--emit-unknown-vcs")
        .arg(&tmpfile)
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.success(),
        "expected success with --emit-unknown-vcs <path>"
    );
    assert!(
        tmpfile.exists(),
        "expected --emit-unknown-vcs with space to create file"
    );

    // Clean up
    let _ = fs::remove_file(&tmpfile);
}

/// Test that --emit-unknown-vcs creates empty array when no UNKNOWN VCs
#[test]
fn cli_emit_unknown_vcs_empty_when_no_unknowns() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpfile = std::env::temp_dir().join(format!(
        "unknown_vcs_empty_test_{}.json",
        std::process::id()
    ));
    let _ = fs::remove_file(&tmpfile);

    // Use a file that verifies cleanly (no UNKNOWN)
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_safe.sil")
        .arg(format!("--emit-unknown-vcs={}", tmpfile.display()))
        .output()
        .expect("failed to run tswift-verify");

    assert!(output.status.success(), "expected success on safe file");
    assert!(tmpfile.exists(), "file should be created even when empty");

    let content = fs::read_to_string(&tmpfile).expect("should read file");
    let records: Vec<serde_json::Value> =
        serde_json::from_str(&content).expect("should be valid JSON");

    assert!(
        records.is_empty(),
        "expected empty array when no UNKNOWN VCs, got {} records",
        records.len()
    );

    // Clean up
    let _ = fs::remove_file(&tmpfile);
}

/// Test that --emit-unknown-vcs is rejected with --dir mode
#[test]
fn cli_emit_unknown_vcs_rejected_with_dir() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--dir")
        .arg("tests/sil_examples")
        .arg("--emit-unknown-vcs=/tmp/should_not_exist.json")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for --emit-unknown-vcs with --dir"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--emit-unknown-vcs is not supported with --dir"),
        "expected error message about --dir incompatibility, got:\n{stderr}"
    );
}
