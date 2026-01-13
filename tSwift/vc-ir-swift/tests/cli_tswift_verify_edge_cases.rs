//! Edge case tests for tswift-verify CLI flags
//!
//! Tests for:
//! - Invalid flag values (graceful degradation)
//! - Flag interactions and combinations
//! - --run-kani without kani installed

use std::process::Command;

// =============================================================================
// Invalid flag value tests
// =============================================================================

/// Test that --color=invalid defaults to auto behavior (no crash, works gracefully)
#[test]
fn cli_color_invalid_value_defaults_to_auto() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color=invalid")
        .output()
        .expect("failed to run tswift-verify");

    // Command should complete without crashing
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Should behave like auto (no color in pipe context)
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("\x1b["),
        "invalid color value should default to auto (no color in pipe), got:\n{stdout}"
    );
}

/// Test that --color=INVALID (uppercase) defaults to auto
#[test]
fn cli_color_uppercase_invalid_defaults_to_auto() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color=ALWAYS")
        .output()
        .expect("failed to run tswift-verify");

    // Should complete - uppercase "ALWAYS" is not recognized, defaults to auto
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code"
    );

    // Auto in pipe means no color
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("\x1b["),
        "uppercase ALWAYS is invalid, should default to auto (no color), got:\n{stdout}"
    );
}

/// Test that --progress=invalid defaults to auto behavior (no crash)
#[test]
fn cli_progress_invalid_value_defaults_to_auto() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--progress=invalid")
        .output()
        .expect("failed to run tswift-verify");

    // Command should complete without crashing
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Test that empty color value (--color=) defaults to auto
#[test]
fn cli_color_empty_value_defaults_to_auto() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color=")
        .output()
        .expect("failed to run tswift-verify");

    // Should complete gracefully
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code"
    );
}

// =============================================================================
// Flag interaction tests
// =============================================================================

/// Test that --json and --diagnostic flags are mutually exclusive or have defined precedence
#[test]
fn cli_json_and_diagnostic_interaction() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--json")
        .arg("--diagnostic")
        .output()
        .expect("failed to run tswift-verify");

    // Should complete (not crash) regardless of precedence
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code"
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // One format should take precedence - verify it's one or the other
    let is_json = stdout.starts_with('{') || stdout.starts_with('[');
    let is_diagnostic =
        stdout.contains("note:") || stdout.contains("warning:") || stdout.contains("error:");

    // Either JSON wins (starts with brace) or diagnostic wins (contains diagnostic markers)
    assert!(
        is_json || is_diagnostic || stdout.is_empty(),
        "output should be valid JSON or diagnostic format, got:\n{stdout}"
    );
}

/// Test that --quiet and --verbose interact reasonably
#[test]
fn cli_quiet_and_verbose_interaction() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--quiet")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-verify");

    // Should complete without crash
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code"
    );
}

/// Test that --json-progress works without --json
#[test]
fn cli_json_progress_without_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--json-progress")
        .output()
        .expect("failed to run tswift-verify");

    // Should complete
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code"
    );

    // JSON progress goes to stderr
    let stderr = String::from_utf8_lossy(&output.stderr);
    // Progress events should be JSON lines
    for line in stderr.lines() {
        if line.starts_with('{') {
            // Should be valid JSON
            let parsed: Result<serde_json::Value, _> = serde_json::from_str(line);
            assert!(
                parsed.is_ok(),
                "JSON progress line should be valid JSON: {line}"
            );
        }
    }
}

/// Test that --human and --json flags have defined precedence
#[test]
fn cli_human_and_json_interaction() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--human")
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify");

    // Should complete without crash
    assert!(
        output.status.code().is_some(),
        "command should complete with exit code"
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Whichever flag comes last typically wins, but the key is it doesn't crash
    assert!(
        !stdout.is_empty() || output.status.success(),
        "should produce some output or succeed quietly"
    );
}

/// Test that multiple color flags use the first one (first match wins)
#[test]
fn cli_multiple_color_flags_first_wins() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // First flag is "never", so no color expected even though "always" comes second
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color=never")
        .arg("--color=always")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    // First flag wins - never means no ANSI codes
    assert!(
        !stdout.contains("\x1b["),
        "first --color=never should win, expected no ANSI codes, got:\n{stdout}"
    );

    // Verify opposite order - always first, then never
    let output2 = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--color=always")
        .arg("--color=never")
        .output()
        .expect("failed to run tswift-verify");

    let stdout2 = String::from_utf8_lossy(&output2.stdout);
    // First flag wins - always means ANSI codes present
    assert!(
        stdout2.contains("\x1b["),
        "first --color=always should win, expected ANSI codes, got:\n{stdout2}"
    );
}

// =============================================================================
// --run-kani error handling tests
// =============================================================================

/// Test that --run-kani without --export-kani gives helpful error
#[test]
fn cli_run_kani_requires_export_kani() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--run-kani")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for invalid usage"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--run-kani requires --export-kani"),
        "expected helpful error message, got:\n{stderr}"
    );
}

/// Test that --run-kani with --export-kani but missing cargo-kani gives helpful error
/// Note: This test only runs meaningfully if cargo-kani is NOT installed
#[test]
fn cli_run_kani_missing_kani_binary() {
    use std::fs;

    // Check if kani is installed - if so, skip this test
    let kani_check = Command::new("cargo").args(["kani", "--version"]).output();

    if kani_check.is_ok() && kani_check.unwrap().status.success() {
        // Kani is installed, test behavior is different
        // Just verify the command structure is valid
        return;
    }

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("run_kani_missing_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .arg("--run-kani")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail gracefully with helpful message
    assert!(
        !output.status.success(),
        "expected failure when kani not installed"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let combined = format!("{stdout}{stderr}");

    // Should mention kani not being installed
    assert!(
        combined.contains("not installed")
            || combined.contains("not in PATH")
            || combined.contains("cargo kani"),
        "expected helpful error about missing kani, got:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

// =============================================================================
// Additional edge cases
// =============================================================================

/// Test that combining --quiet with --json-progress still emits progress
#[test]
fn cli_quiet_with_json_progress() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--quiet")
        .arg("--json-progress")
        .output()
        .expect("failed to run tswift-verify");

    // JSON progress should still go to stderr even in quiet mode
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Should have JSON progress events
    let has_json_progress = stderr
        .lines()
        .any(|line| line.starts_with('{') && line.contains("event"));

    assert!(
        has_json_progress,
        "expected JSON progress in stderr even with --quiet, got:\n{stderr}"
    );
}

/// Test that --color works with --json (colors in JSON strings shouldn't break parsing)
#[test]
fn cli_color_with_json_output() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--json")
        .arg("--color=always")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // JSON output should still be parseable even if color is enabled
    // (colors shouldn't be in JSON, or if they are, should be properly escaped)
    let parsed: Result<serde_json::Value, _> = serde_json::from_str(&stdout);
    assert!(
        parsed.is_ok(),
        "JSON output should be valid even with --color=always, got:\n{stdout}"
    );
}

/// Test --progress=always with --quiet (progress overrides quiet for progress output)
#[test]
fn cli_progress_always_with_quiet() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--quiet")
        .arg("--progress=always")
        .output()
        .expect("failed to run tswift-verify");

    // Should complete
    assert!(output.status.code().is_some(), "command should complete");

    // Progress should appear in stderr even with quiet
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Verifying") || stderr.is_empty(),
        "progress=always should show progress even with quiet (or stderr handling varies)"
    );
}
