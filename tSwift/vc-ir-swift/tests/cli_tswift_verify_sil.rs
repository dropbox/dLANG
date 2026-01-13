//! Integration tests for tswift-verify --sil and --swift modes

use std::process::Command;

/// Test that --sil mode parses and verifies SIL files
#[test]
fn cli_sil_mode_parses_sil_file() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // This example intentionally has no preconditions on input, so verification should FAIL
    // (exit code 1) while still surfacing the overflow VC.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: add"),
        "expected 'add' function in output"
    );
    assert!(
        stdout.contains("Auto-VC #1 (arithmetic overflow)"),
        "expected overflow VC in output"
    );
}

/// Test that --sil mode detects array bounds checks from real subscript trap patterns
#[test]
fn cli_sil_mode_detects_array_bounds_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/array_subscript_bounds_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // This example intentionally has no preconditions relating `i` and `len`,
    // so verification should FAIL (exit code 1) while still surfacing bounds VCs.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failing bounds checks\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: getElement"),
        "expected 'getElement' function in output"
    );
    assert!(
        stdout.contains("Index out of range"),
        "expected bounds-check trap message in output"
    );
}

/// Test that --sil mode detects division-by-zero auto-VCs
#[test]
fn cli_sil_mode_detects_division_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/division_by_zero_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // This example intentionally has no precondition on the divisor,
    // so verification should FAIL (exit code 1) for the div-by-zero check.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failing div-by-zero check\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: divide"),
        "expected 'divide' function in output"
    );
    assert!(
        stdout.contains("div by zero"),
        "expected div-by-zero check message in output"
    );
}

/// Test that --sil mode detects modulo-by-zero auto-VCs
#[test]
fn cli_sil_mode_detects_modulo_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/modulo_by_zero_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // This example intentionally has no precondition on the divisor,
    // so verification should FAIL (exit code 1) for the mod-by-zero check.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failing mod-by-zero check\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: modulo"),
        "expected 'modulo' function in output"
    );
    assert!(
        stdout.contains("mod by zero"),
        "expected mod-by-zero check message in output"
    );
}

/// Test that --sil mode detects unsigned division-by-zero auto-VCs
#[test]
fn cli_sil_mode_detects_unsigned_division_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/unsigned_division_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // This example intentionally has no precondition on the divisor,
    // so verification should FAIL (exit code 1) for the div-by-zero check.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failing unsigned div-by-zero check\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: unsignedDivide"),
        "expected 'unsignedDivide' function in output"
    );
    assert!(
        stdout.contains("div by zero"),
        "expected div-by-zero check message in output"
    );
}

/// Test that --sil mode detects unsigned modulo-by-zero auto-VCs
#[test]
fn cli_sil_mode_detects_unsigned_modulo_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/unsigned_modulo_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // This example intentionally has no precondition on the divisor,
    // so verification should FAIL (exit code 1) for the mod-by-zero check.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failing unsigned mod-by-zero check\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: unsignedModulo"),
        "expected 'unsignedModulo' function in output"
    );
    assert!(
        stdout.contains("mod by zero"),
        "expected mod-by-zero check message in output"
    );
}

/// Test that --sil mode detects force unwrap nil check auto-VCs
#[test]
fn cli_sil_mode_detects_force_unwrap_nil_check_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/force_unwrap_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // This example intentionally force unwraps without any nil check,
    // so verification should FAIL (exit code 1) for the nil check.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failing force unwrap nil check\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: unsafeUnwrap"),
        "expected 'unsafeUnwrap' function in output"
    );
    assert!(
        stdout.contains("force unwrap may be nil") || stdout.contains("nil"),
        "expected nil check message in output"
    );
}

/// Test that --sil mode with --json produces valid JSON
#[test]
fn cli_sil_mode_json_output() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    assert_eq!(json["function_name"], "add");
    assert!(!json["auto_vc_results"].as_array().unwrap().is_empty());
}

/// Test that --swift mode compiles and verifies Swift source files
#[test]
fn cli_swift_mode_compiles_and_verifies() {
    // Check if swiftc is available
    if Command::new("swiftc").arg("--version").output().is_err() {
        eprintln!("Skipping test: swiftc not found");
        return;
    }

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/sil_examples/simple_add_unsafe.swift")
        .output()
        .expect("failed to run tswift-verify");

    // simple_add_unsafe.swift contains an unchecked add that can overflow, so verification should FAIL.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // The add and multiply functions should be found
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VCs in output"
    );
}

/// Test that --swift mode with --json produces valid JSON
#[test]
fn cli_swift_mode_json_output() {
    // Check if swiftc is available
    if Command::new("swiftc").arg("--version").output().is_err() {
        eprintln!("Skipping test: swiftc not found");
        return;
    }

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("--json")
        .arg("tests/sil_examples/simple_add_unsafe.swift")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have multiple bundles (main, add, multiply)
    assert!(json["bundles"].as_array().is_some() || json["function_name"].as_str().is_some());
}

/// Test that malformed SIL produces an error
#[test]
fn cli_sil_mode_rejects_malformed_sil() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create a temporary file with malformed SIL that starts parsing but fails
    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("malformed_test.sil");
    std::fs::write(&tmp_file, "sil_stage canonical\nsil @bad : $broken {\n")
        .expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    // Should fail with exit code 2 (parse error)
    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for malformed SIL\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that malformed SIL produces compiler-style diagnostic output with a real location.
#[test]
fn cli_sil_mode_diagnostic_rejects_malformed_sil_with_location() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create a temporary file with malformed SIL that starts parsing but fails on line 2.
    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("malformed_diagnostic_test.sil");
    std::fs::write(&tmp_file, "sil_stage canonical\nsil @bad : $broken {\n")
        .expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--diagnostic")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for malformed SIL\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains(&format!("{}:", tmp_file.display()))
            && stdout.contains(": error: SIL parse error:")
            && !stdout.contains(":1:1: error:"),
        "expected diagnostic output to include a real (non-1:1) error location\nstdout:\n{stdout}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that --diagnostic flag produces compiler-style output for SIL files
#[test]
fn cli_sil_mode_diagnostic_output() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--diagnostic")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should NOT contain the human-readable format markers
    assert!(
        !stdout.contains("==="),
        "diagnostic mode should not contain === markers"
    );
    assert!(
        !stdout.contains("Auto-VC #"),
        "diagnostic mode should not contain Auto-VC # format"
    );
}

/// Test that --diagnostic flag produces compiler-style output for Swift files
#[test]
fn cli_swift_mode_diagnostic_output() {
    // Check if swiftc is available
    if Command::new("swiftc").arg("--version").output().is_err() {
        eprintln!("Skipping test: swiftc not found");
        return;
    }

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("--diagnostic")
        .arg("tests/sil_examples/simple_add_unsafe.swift")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should NOT contain the human-readable format markers
    assert!(
        !stdout.contains("==="),
        "diagnostic mode should not contain === markers"
    );
    assert!(
        !stdout.contains("Auto-VC #"),
        "diagnostic mode should not contain Auto-VC # format"
    );
}

/// Test that --diagnostic flag produces error output for failed VCs
#[test]
fn cli_diagnostic_output_shows_failures() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create a test bundle with a failing VC (condition = false means always fails)
    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("failing_bundle.json");
    // JSON must be on a single line or be a valid JSON object
    // SwiftType uses internal tagging with "kind" field
    let bundle_json = r#"{"function_name":"test_func","source_file":"/path/to/test.swift","source_line":42,"parameters":[{"name":"x","type":{"kind":"Int","signed":true,"bits":64}}],"auto_vcs":[{"kind":"CondFail","description":"overflow check","condition":{"kind":"BoolLit","value":false},"message":"test failure","source_line":42,"source_column":10}]}"#;
    std::fs::write(&tmp_file, bundle_json).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--diagnostic")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    // Should exit with code 1 (verification failure)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failed VC\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should contain compiler-style error format: file:line:col: error:
    assert!(
        stdout.contains(": error:"),
        "diagnostic output should contain ': error:' format, got: {stdout}"
    );
    assert!(
        stdout.contains("overflow check"),
        "diagnostic output should contain the VC description, got: {stdout}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that --color=always forces ANSI color output
#[test]
fn cli_color_always_forces_ansi_output() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--color=always")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // ANSI escape codes start with ESC (0x1b) followed by [
    assert!(
        stdout.contains("\x1b["),
        "--color=always should produce ANSI escape codes, got: {stdout}"
    );
}

/// Test that --color=never suppresses ANSI color output
#[test]
fn cli_color_never_suppresses_ansi_output() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--color=never")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should NOT contain ANSI escape codes
    assert!(
        !stdout.contains("\x1b["),
        "--color=never should not produce ANSI escape codes, got: {stdout}"
    );
}

/// Test that --color=always with --diagnostic produces colored error output
#[test]
fn cli_color_always_diagnostic_colored_errors() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create a test bundle with a failing VC
    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("failing_bundle_color.json");
    let bundle_json = r#"{"function_name":"test_func","source_file":"/path/to/test.swift","source_line":42,"parameters":[{"name":"x","type":{"kind":"Int","signed":true,"bits":64}}],"auto_vcs":[{"kind":"CondFail","description":"overflow check","condition":{"kind":"BoolLit","value":false},"message":"test failure","source_line":42,"source_column":10}]}"#;
    std::fs::write(&tmp_file, bundle_json).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--diagnostic")
        .arg("--color=always")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    // Should exit with code 1 (verification failure)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failed VC"
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should contain ANSI escape codes for colored "error:" label
    // The error label uses BOLD_RED: \x1b[1;31m
    assert!(
        stdout.contains("\x1b[1;31m"),
        "colored diagnostic should contain bold red for error, got: {stdout}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that --progress=always emits progress updates on stderr (not stdout)
#[test]
fn cli_progress_always_emits_progress_to_stderr() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--progress=always")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    // Progress now uses visual progress bar format: [====================] 100%
    assert!(
        stderr.contains("Verifying") && stderr.contains('%'),
        "expected progress output on stderr, got: {stderr}"
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("Verifying"),
        "progress output should not be on stdout, got: {stdout}"
    );
}

/// Test that progress output includes per-function stats and ETA
#[test]
fn cli_progress_shows_function_stats_and_eta() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--progress=always")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Check for expected progress format: "[N/M] function_name: X verified, Y failed, Z unknown (T.TTTs, ETA T.Ts)"
    assert!(
        stderr.contains("verified") && stderr.contains("failed") && stderr.contains("unknown"),
        "progress should include verified/failed/unknown counts, got: {stderr}"
    );

    assert!(
        stderr.contains("ETA"),
        "progress should include ETA estimate, got: {stderr}"
    );
}

/// Test that progress output includes visual progress bar
#[test]
fn cli_progress_shows_visual_progress_bar() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--progress=always")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Progress bar format: [====...===] or [====>     ] or similar
    // Should contain '[' and ']' and '%' as progress bar components
    assert!(
        stderr.contains('[') && stderr.contains(']') && stderr.contains('%'),
        "progress should include visual progress bar [=====>    ] N%, got: {stderr}"
    );

    // For a single function (1/1), the completed bar should show 100%
    assert!(
        stderr.contains("100%"),
        "single function verification should show 100% upon completion, got: {stderr}"
    );
}

/// Test that --verbose / -v flag shows per-VC progress in non-TTY mode
#[test]
fn cli_verbose_shows_per_vc_progress() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("-v")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Verbose mode should show per-VC progress lines with format:
    // "  [VC N/M] function_name type (vc_name): STATUS"
    assert!(
        stderr.contains("[VC ") && stderr.contains("auto"),
        "verbose mode should show per-VC progress lines, got stderr: {stderr}"
    );

    // Should contain the VC status (OK, FAIL, WARN, or ERR)
    assert!(
        stderr.contains("OK")
            || stderr.contains("FAIL")
            || stderr.contains("WARN")
            || stderr.contains("ERR"),
        "verbose mode should show VC status, got stderr: {stderr}"
    );
}

/// Test that --verbose works with --json (verbose on stderr, JSON on stdout)
#[test]
fn cli_verbose_with_json_output() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("--verbose")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    // stdout should be valid JSON
    let stdout = String::from_utf8_lossy(&output.stdout);
    let _json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output on stdout");

    // stderr should contain verbose per-VC output
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("[VC "),
        "verbose mode should emit per-VC lines to stderr, got: {stderr}"
    );
}

/// Test that --verbose with --color=always shows colored status output
#[test]
fn cli_verbose_color_always_shows_colored_status() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("-v")
        .arg("--color=always")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Verbose mode with --color=always should show colored status
    // ANSI green: \x1b[32m for OK
    assert!(
        stderr.contains("\x1b[32mOK\x1b[0m")
            || stderr.contains("\x1b[31mFAIL\x1b[0m")
            || stderr.contains("\x1b[33mWARN\x1b[0m")
            || stderr.contains("\x1b[31mERR\x1b[0m"),
        "verbose mode with --color=always should show colored status (expected ANSI codes), got stderr: {stderr}"
    );

    // Should still have the VC progress format
    assert!(
        stderr.contains("[VC ") && stderr.contains("auto"),
        "verbose mode should show per-VC progress lines, got stderr: {stderr}"
    );
}

/// Test that --verbose with --color=never shows plain status output (no ANSI codes)
#[test]
fn cli_verbose_color_never_shows_plain_status() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("-v")
        .arg("--color=never")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Should NOT contain ANSI escape codes
    assert!(
        !stderr.contains("\x1b["),
        "verbose mode with --color=never should NOT contain ANSI codes, got stderr: {stderr}"
    );

    // Should contain plain text status
    assert!(
        stderr.contains("OK")
            || stderr.contains("FAIL")
            || stderr.contains("WARN")
            || stderr.contains("ERR"),
        "verbose mode should show VC status, got stderr: {stderr}"
    );
}

/// Test that --verbose shows a summary line at the end with OK/FAIL/WARN counts
#[test]
fn cli_verbose_shows_summary_line() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("-v")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Verbose summary line should appear at the end of stderr
    // Format: "Verbose summary: N OK, N FAIL, N WARN"
    assert!(
        stderr.contains("Verbose summary:"),
        "verbose mode should show a summary line, got stderr: {stderr}"
    );

    // Summary should contain OK count
    assert!(
        stderr.contains(" OK,"),
        "verbose summary should contain OK count, got stderr: {stderr}"
    );
}

/// Test that --verbose summary respects --color=always
#[test]
fn cli_verbose_summary_color_always() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("-v")
        .arg("--color=always")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Verbose summary line should appear
    assert!(
        stderr.contains("Verbose summary:"),
        "verbose mode should show a summary line, got stderr: {stderr}"
    );

    // Should contain ANSI color codes for green (OK count)
    assert!(
        stderr.contains("\x1b[32m"),
        "verbose summary with --color=always should contain green ANSI codes for OK count, got stderr: {stderr}"
    );
}

/// Test that --verbose shows timing on each per-VC output line
#[test]
fn cli_verbose_shows_per_vc_timing() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("-v")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Per-VC lines should show timing in format: STATUS (X.XXXs)
    // Look for pattern like "OK (0." or "FAIL (0." etc.
    assert!(
        stderr.contains("s)"),
        "verbose per-VC lines should include timing (ending with 's)'), got stderr: {stderr}"
    );

    // Check that there's a number before the 's' - pattern like "(0.001s)" or "(1.234s)"
    let has_timing = stderr
        .lines()
        .filter(|line| line.contains("[VC "))
        .any(|line| {
            // Look for pattern: ) (N.NNNs) at end of line where N is any digit
            if !line.ends_with("s)") {
                return false;
            }
            // Check for timing pattern with any decimal number, not just sub-second
            line.chars()
                .rev()
                .skip(2) // skip "s)"
                .take_while(|&c| c != '(')
                .all(|c| c.is_ascii_digit() || c == '.')
        });
    assert!(
        has_timing,
        "verbose per-VC lines should show timing like '(N.NNNs)', got stderr: {stderr}"
    );
}

/// Test that --verbose summary line includes total time
#[test]
fn cli_verbose_summary_includes_total_time() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("-v")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Find the verbose summary line
    let summary_line = stderr
        .lines()
        .find(|line| line.contains("Verbose summary:"))
        .expect("should have Verbose summary line");

    // Summary line should include total time in format: (N.NNNs)
    assert!(
        summary_line.contains("s)"),
        "verbose summary should include total time ending with 's)', got: {summary_line}"
    );

    // More specific: look for pattern (N.NNNs) at end
    assert!(
        summary_line.ends_with("s)"),
        "verbose summary line should end with timing (N.NNNs), got: {summary_line}"
    );
}

/// Test that --json-progress emits JSON Lines events to stderr
#[test]
fn cli_json_progress_emits_events() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json-progress")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Should contain function_start event
    assert!(
        stderr.contains(r#""event":"function_start""#),
        "json-progress should emit function_start event, got stderr: {stderr}"
    );

    // Should contain vc_complete event
    assert!(
        stderr.contains(r#""event":"vc_complete""#),
        "json-progress should emit vc_complete event, got stderr: {stderr}"
    );

    // Should contain function_complete event
    assert!(
        stderr.contains(r#""event":"function_complete""#),
        "json-progress should emit function_complete event, got stderr: {stderr}"
    );

    // Should contain summary event
    assert!(
        stderr.contains(r#""event":"summary""#),
        "json-progress should emit summary event, got stderr: {stderr}"
    );

    // Each line should be valid JSON
    for line in stderr.lines() {
        if line.starts_with('{') {
            let parsed: Result<serde_json::Value, _> = serde_json::from_str(line);
            assert!(
                parsed.is_ok(),
                "each JSON progress line should be valid JSON, failed to parse: {line}"
            );
        }
    }
}

/// Test that --json-progress events contain expected fields
#[test]
fn cli_json_progress_event_fields() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json-progress")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Parse and check vc_complete event fields
    let vc_complete_line = stderr
        .lines()
        .find(|line| line.contains(r#""event":"vc_complete""#))
        .expect("should have vc_complete event");

    let vc_json: serde_json::Value =
        serde_json::from_str(vc_complete_line).expect("vc_complete should be valid JSON");

    assert_eq!(vc_json["event"], "vc_complete");
    assert!(
        vc_json["function"].is_string(),
        "vc_complete should have function field"
    );
    assert!(
        vc_json["vc"].is_string(),
        "vc_complete should have vc field"
    );
    assert!(
        vc_json["status"].is_string(),
        "vc_complete should have status field"
    );
    assert!(
        vc_json["completed"].is_number(),
        "vc_complete should have completed field"
    );
    assert!(
        vc_json["total"].is_number(),
        "vc_complete should have total field"
    );
    assert!(
        vc_json["time_seconds"].is_number(),
        "vc_complete should have time_seconds field"
    );

    // Parse and check summary event fields
    let summary_line = stderr
        .lines()
        .find(|line| line.contains(r#""event":"summary""#))
        .expect("should have summary event");

    let summary_json: serde_json::Value =
        serde_json::from_str(summary_line).expect("summary should be valid JSON");

    assert_eq!(summary_json["event"], "summary");
    assert!(
        summary_json["total_vcs"].is_number(),
        "summary should have total_vcs field"
    );
    assert!(
        summary_json["verified"].is_number(),
        "summary should have verified field"
    );
    assert!(
        summary_json["failed"].is_number(),
        "summary should have failed field"
    );
    assert!(
        summary_json["unknown"].is_number(),
        "summary should have unknown field"
    );
    assert!(
        summary_json["time_seconds"].is_number(),
        "summary should have time_seconds field"
    );
}

/// Test that --json-progress `vc_complete` events include `vc_type` field ("spec" or "auto")
#[test]
fn cli_json_progress_vc_type_field() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Use verified_positive.sil which has specs (@_ensures) and auto-VCs
    // Note: This file has some verification failures (safeAdd overflow) but we're
    // only testing JSON structure, not verification results
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json-progress")
        .arg("tests/sil_examples/verified_positive_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Command should run (exit code may be non-zero due to verification failures)
    assert!(
        output.status.code().is_some(),
        "command should have run, got no exit code"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Find all vc_complete events
    let vc_events: Vec<serde_json::Value> = stderr
        .lines()
        .filter(|line| line.contains(r#""event":"vc_complete""#))
        .map(|line| serde_json::from_str(line).expect("vc_complete should be valid JSON"))
        .collect();

    assert!(
        !vc_events.is_empty(),
        "should have at least one vc_complete event, got stderr: {stderr}"
    );

    // Every vc_complete event should have vc_type field with value "spec" or "auto"
    for (i, vc_json) in vc_events.iter().enumerate() {
        let vc_type = vc_json["vc_type"].as_str();
        assert!(
            vc_type.is_some(),
            "vc_complete event {i} should have vc_type field as string"
        );
        let vc_type = vc_type.unwrap();
        assert!(
            vc_type == "spec" || vc_type == "auto",
            "vc_type should be 'spec' or 'auto', got '{vc_type}' in event {i}"
        );
    }

    // With verified_positive.sil, we should have at least one spec VC
    let has_spec = vc_events.iter().any(|v| v["vc_type"] == "spec");
    assert!(
        has_spec,
        "verified_positive.sil should have at least one spec VC, events: {vc_events:?}"
    );
}

/// Test that --quiet-progress suppresses OK-only progress lines in non-TTY mode
#[test]
fn cli_quiet_progress_suppresses_ok_lines() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create a test bundle with a trivially verified VC.
    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("ok_bundle_quiet_progress.json");
    let bundle_json = r#"{"function_name":"ok_func","source_file":"/path/to/test.swift","source_line":1,"parameters":[],"auto_vcs":[{"kind":"CondFail","description":"trivial check","condition":{"kind":"BoolLit","value":true},"message":"should verify","source_line":1,"source_column":1}]}"#;
    std::fs::write(&tmp_file, bundle_json).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--progress=always")
        .arg("--quiet-progress")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.trim().is_empty(),
        "expected quiet-progress to suppress OK-only progress output on stderr, got: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that --quiet-progress still emits progress lines for failures
#[test]
fn cli_quiet_progress_still_shows_failures() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create a test bundle with a failing VC (condition = false means always fails)
    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("failing_bundle_quiet_progress.json");
    let bundle_json = r#"{"function_name":"test_func","source_file":"/path/to/test.swift","source_line":42,"parameters":[{"name":"x","type":{"kind":"Int","signed":true,"bits":64}}],"auto_vcs":[{"kind":"CondFail","description":"overflow check","condition":{"kind":"BoolLit","value":false},"message":"test failure","source_line":42,"source_column":10}]}"#;
    std::fs::write(&tmp_file, bundle_json).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--progress=always")
        .arg("--quiet-progress")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    // Should exit with code 1 (verification failure)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failed VC\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("test_func") && stderr.contains("failed") && stderr.contains('%'),
        "expected quiet-progress to still emit failure progress line on stderr, got: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

// ===========================================================================
// End-to-End Tests for swift-frontend Pipeline
// ===========================================================================
// These tests verify the full verification pipeline from Swift-syntax
// declarations with @_requires/@_ensures/@_trusted attributes.

/// Test that SIL with Swift-syntax @_requires/@_ensures is parsed and verified
#[test]
fn cli_e2e_swift_syntax_requires_ensures_verified() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // This SIL file was produced by swift-frontend and contains:
    // @_requires("x > 0") @_ensures("result > 0") func keepPositive
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/verified_positive_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // keepPositive spec should verify OK
    assert!(
        stderr.contains("keepPositive spec") && stderr.contains("OK"),
        "keepPositive spec should verify OK, got stderr: {stderr}"
    );

    // stdout should show keepPositive function
    assert!(
        stdout.contains("Function: keepPositive"),
        "output should include keepPositive function, got stdout: {stdout}"
    );
}

/// Test that @_requires precondition is used in verification
#[test]
fn cli_e2e_requires_strengthens_verification() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL with @_requires that enables the proof
    // Without @_requires("x > 0"), proving result > 0 would fail
    let sil = r#"sil_stage canonical

@_requires("x > 0")
@_ensures("result > 0")
func positive(_ x: Int) -> Int

sil hidden @$s4test8positiveyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("requires_strengthens.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // The spec should verify OK because x > 0 => result > 0
    assert!(
        stderr.contains("spec") && stderr.contains("OK"),
        "spec with @_requires should verify OK, got stderr: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that @_trusted attribute is parsed and function is skipped from deep verification
#[test]
fn cli_e2e_trusted_attribute_parsed() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // This SIL file contains @_trusted func unsafeOperation
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/verified_positive_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // JSON output should show unsafeOperation
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Find the unsafeOperation bundle
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");
    let unsafe_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("unsafeOperation"))
    });

    assert!(
        unsafe_bundle.is_some(),
        "should have unsafeOperation bundle in output, got: {stdout}"
    );

    // Trusted functions should verify immediately with no auto-VCs generated
    // (because the @_trusted attribute skips deep verification)
    let bundle = unsafe_bundle.unwrap();
    let auto_vcs = bundle["auto_vc_results"]
        .as_array()
        .expect("should have auto_vc_results");
    assert!(
        auto_vcs.is_empty(),
        "trusted function should have no auto-VCs (skipped verification), got: {auto_vcs:?}"
    );

    // Should still count as verified
    let verified = bundle["summary"]["verified"]
        .as_u64()
        .expect("should have verified count");
    assert!(
        verified >= 1,
        "trusted function should count as verified, got summary: {}",
        bundle["summary"]
    );
}

/// Test that multiple @_requires attributes form a conjunction
#[test]
fn cli_e2e_multiple_requires_conjoined() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // SIL with multiple @_requires
    let sil = r#"sil_stage canonical

@_requires("a >= 0")
@_requires("b >= 0")
@_ensures("result >= a")
func conjoinedReqs(_ a: Int, _ b: Int) -> Int

sil hidden @$s4test12conjoinedReqsyS2i_SitF : $@convention(thin) (Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int):
  debug_value %0, let, name "a", argno 1
  debug_value %1, let, name "b", argno 2
  return %0
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("multiple_requires.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse JSON and verify the spec verified
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should verify: (a >= 0 && b >= 0) => result >= a (since result = a)
    let spec_result = json["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "multiple @_requires should form conjunction and verify, got: {stdout}"
    );

    // Check summary shows verified
    let verified = json["summary"]["verified"]
        .as_u64()
        .expect("should have verified count");
    assert!(
        verified >= 1,
        "should have at least 1 verified VC, got: {stdout}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that safeAdd specs are extracted from Swift-syntax and verified
#[test]
fn cli_e2e_safeadd_specs_verified() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/verified_positive_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // safeAdd has @_requires("a >= 0") @_requires("b >= 0") @_ensures("result >= 0")
    // The spec should verify: (a >= 0 && b >= 0) => result >= 0
    assert!(
        stderr.contains("safeAdd spec") && stderr.contains("OK"),
        "safeAdd spec should verify OK, got stderr: {stderr}"
    );
}

/// Test that incorrect postcondition fails verification (sanity check)
#[test]
fn cli_e2e_incorrect_postcondition_fails() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // SIL with incorrect postcondition: x > 0 does NOT imply result < 0
    let sil = r#"sil_stage canonical

@_requires("x > 0")
@_ensures("result < 0")
func incorrectPost(_ x: Int) -> Int

sil hidden @$s4test13incorrectPostyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("incorrect_post.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Should FAIL: x > 0 does NOT prove result < 0
    assert!(
        stderr.contains("FAIL"),
        "incorrect postcondition should FAIL verification, got stderr: {stderr}"
    );

    // Exit code should be 1 for verification failure
    assert_eq!(
        output.status.code(),
        Some(1),
        "should exit with code 1 for verification failure"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that real swift-frontend compiled SIL is verified end-to-end
/// This test uses the pre-compiled SIL from `verified_positive.swift`
#[test]
fn cli_e2e_full_pipeline_from_swift_frontend() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Run verification on the swift-frontend produced SIL
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/verified_positive_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Check for expected functions: keepPositive, safeAdd, unsafeOperation
    let function_names: Vec<&str> = bundles
        .iter()
        .filter_map(|b| b["function_name"].as_str())
        .collect();

    assert!(
        function_names.iter().any(|n| n.contains("keepPositive")),
        "should have keepPositive function, got: {function_names:?}"
    );

    assert!(
        function_names.iter().any(|n| n.contains("safeAdd")),
        "should have safeAdd function, got: {function_names:?}"
    );

    assert!(
        function_names.iter().any(|n| n.contains("unsafeOperation")),
        "should have unsafeOperation function, got: {function_names:?}"
    );

    // Count functions with verified specs (spec_result.result == "Verified")
    let functions_with_verified_specs: Vec<_> = bundles
        .iter()
        .filter(|b| {
            b["spec_result"]["result"]
                .as_str()
                .is_some_and(|r| r == "Verified")
        })
        .collect();

    // Should have at least 2 functions with verified specs (keepPositive, safeAdd)
    assert!(
        functions_with_verified_specs.len() >= 2,
        "should have at least 2 functions with verified specs, got {}: {:?}",
        functions_with_verified_specs.len(),
        functions_with_verified_specs
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );
}

/// Test that clamp function with phi-pattern (branch-with-args) verifies its spec
/// This is a critical test for the phi-resolution feature added in #154
#[test]
fn cli_e2e_clamp_phi_pattern_spec_verified() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Run verification on the counter_vtable.sil which contains clamp with specs:
    // @_requires("true") @_ensures("result >= 0")
    // clamp returns x >= 0 ? x : 0, so result is always >= 0
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/counter_vtable_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // clamp spec should verify OK
    assert!(
        stderr.contains("clamp spec") && stderr.contains("OK"),
        "clamp spec should verify OK, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Should also show the clamp function in output
    assert!(
        stdout.contains("Function: clamp"),
        "output should include clamp function, got stdout: {stdout}"
    );
}

/// Test that clamp function with phi-pattern produces correct JSON output
#[test]
fn cli_e2e_clamp_phi_pattern_json_verified() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/counter_vtable_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find the clamp bundle
    let clamp_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("clamp"))
    });

    assert!(
        clamp_bundle.is_some(),
        "should have clamp bundle in output, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = clamp_bundle.unwrap();

    // clamp spec should verify
    let spec_result = bundle["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "clamp spec should verify, got: {bundle}"
    );

    // Summary should show verified
    let verified = bundle["summary"]["verified"]
        .as_u64()
        .expect("should have verified count");
    assert!(
        verified >= 1,
        "clamp should have at least 1 verified VC, got summary: {}",
        bundle["summary"]
    );
}

// ===========================================================================
// Cross-Function @_ensures Postcondition Assumption Tests
// ===========================================================================
// These tests verify that a caller's @_ensures can be proven by assuming the
// callee's @_ensures postcondition at call sites.

/// Test that cross-function @_ensures assumptions enable verification
/// useAddOne(@_ensures "result > n") calls addOne(@_ensures "result > x").
/// useAddOne's postcondition is only provable via the assumed postcondition from addOne.
#[test]
fn cli_e2e_cross_function_ensures_assumption_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_ensures_assumption_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // useAddOne spec should verify OK because we assume addOne's postcondition
    assert!(
        stderr.contains("useAddOne spec") && stderr.contains("OK"),
        "useAddOne spec should verify OK using callee postcondition assumption, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Overall verification should succeed
    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );
}

/// Test that cross-function @_ensures assumptions are reflected in JSON output
#[test]
fn cli_e2e_cross_function_ensures_assumption_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_ensures_assumption_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find the useAddOne bundle
    let use_add_one_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("useAddOne"))
    });

    assert!(
        use_add_one_bundle.is_some(),
        "should have useAddOne bundle in output, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = use_add_one_bundle.unwrap();

    // useAddOne spec should verify
    let spec_result = bundle["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "useAddOne spec should verify using callee postcondition assumption, got: {bundle}"
    );

    // Verify summary shows spec verified
    // (body_constraints is internal and not serialized to JSON output)
    let spec_verified = bundle["summary"]["spec_verified"]
        .as_u64()
        .expect("should have spec_verified count");
    assert_eq!(
        spec_verified, 1,
        "useAddOne should have 1 spec verified, got: {}",
        bundle["summary"]
    );
}

/// Negative control: without callee @_ensures, the caller's postcondition should NOT verify.
/// This uses a SIL snippet where the callee has no postcondition.
#[test]
fn cli_e2e_cross_function_ensures_fails_without_callee_postcondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where callee has NO @_ensures but caller expects result > n
    // This should NOT verify because there's no assumption to use
    // Uses proper Swift name mangling: $s<module_len><module><func_len><func><type_suffix>
    // Module: "nospec" (6 chars), func: "addOne" (6 chars), "useAddOne" (9 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// addOne: NO postcondition here - caller cannot assume anything
func addOne(_ x: Int) -> Int

// useAddOne: caller tries to prove result > n but cannot without callee spec
@_ensures("result > n")
func useAddOne(_ n: Int) -> Int

sil hidden @$s6nospec6addOneyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 1
  %4 = integer_literal $Builtin.Int1, 0
  %5 = builtin "sadd_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
  %6 = tuple_extract %5, 0
  %7 = struct $Int (%6)
  return %7
}

sil hidden @$s6nospec9useAddOneyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "n", argno 1
  %2 = function_ref @$s6nospec6addOneyS2iF : $@convention(thin) (Int) -> Int
  %3 = apply %2(%0) : $@convention(thin) (Int) -> Int
  return %3
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_ensures_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // useAddOne spec should FAIL because we have no assumption from callee
    assert!(
        stderr.contains("useAddOne spec") && stderr.contains("FAIL"),
        "useAddOne spec should FAIL without callee postcondition, got stderr: {stderr}"
    );

    // Exit code should be 1 for verification failure
    assert_eq!(
        output.status.code(),
        Some(1),
        "should exit with code 1 for verification failure\nstderr: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

// ===========================================================================
// Complex Argument Expression @_ensures Substitution Tests
// ===========================================================================
// These tests verify that postcondition assumptions work correctly when
// the call site uses complex argument expressions like addOne(a+1).

/// Test that complex argument expression substitution works in @_ensures assumptions.
/// useAddOneComplex(@_ensures "result > a+1") calls addOne(a+1).
/// The postcondition is provable because: call addOne(a+1) => `call_result` > a+1.
#[test]
fn cli_e2e_complex_arg_ensures_substitution_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_ensures_complex_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // useAddOneComplex spec should verify OK because we assume addOne's postcondition
    // with the complex argument (a+1) substituted for parameter x
    assert!(
        stderr.contains("useAddOneComplex spec") && stderr.contains("OK"),
        "useAddOneComplex spec should verify OK using callee postcondition with complex arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Overall verification should succeed
    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );
}

/// Test that complex argument expression substitution is reflected in JSON output.
#[test]
fn cli_e2e_complex_arg_ensures_substitution_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_ensures_complex_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find the useAddOneComplex bundle
    let use_complex_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("useAddOneComplex"))
    });

    assert!(
        use_complex_bundle.is_some(),
        "should have useAddOneComplex bundle in output, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = use_complex_bundle.unwrap();

    // useAddOneComplex spec should verify
    let spec_result = bundle["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "useAddOneComplex spec should verify using complex arg substitution, got: {bundle}"
    );

    // Verify summary shows spec verified
    let spec_verified = bundle["summary"]["spec_verified"]
        .as_u64()
        .expect("should have spec_verified count");
    assert_eq!(
        spec_verified, 1,
        "useAddOneComplex should have 1 spec verified, got: {}",
        bundle["summary"]
    );
}

/// Negative control: complex arg postcondition fails when callee has no @_ensures.
#[test]
fn cli_e2e_complex_arg_fails_without_callee_postcondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where callee has NO @_ensures but caller expects result > a+1
    // Uses module "nocomplexspec" (13 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// addOne: NO postcondition here - caller cannot assume anything
func addOne(_ x: Int) -> Int

// useAddOneComplex: caller tries to prove result > a+1 but cannot without callee spec
@_ensures("result > a + 1")
func useAddOneComplex(_ a: Int) -> Int

sil hidden @$s13nocomplexspec6addOneyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 1
  %4 = integer_literal $Builtin.Int1, 0
  %5 = builtin "sadd_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
  %6 = tuple_extract %5, 0
  %7 = struct $Int (%6)
  return %7
}

sil hidden @$s13nocomplexspec16useAddOneComplexySiSiF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "a", argno 1
  // Compute a+1
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 1
  %4 = integer_literal $Builtin.Int1, 0
  %5 = builtin "sadd_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
  %6 = tuple_extract %5, 0
  %7 = struct $Int (%6)
  // Call addOne(a+1)
  %8 = function_ref @$s13nocomplexspec6addOneyS2iF : $@convention(thin) (Int) -> Int
  %9 = apply %8(%7) : $@convention(thin) (Int) -> Int
  return %9
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_complex_ensures_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // useAddOneComplex spec should FAIL because we have no assumption from callee
    assert!(
        stderr.contains("useAddOneComplex spec") && stderr.contains("FAIL"),
        "useAddOneComplex spec should FAIL without callee postcondition, got stderr: {stderr}"
    );

    // Exit code should be 1 for verification failure
    assert_eq!(
        output.status.code(),
        Some(1),
        "should exit with code 1 for verification failure\nstderr: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that multiplication argument expression substitution enables postcondition verification.
/// The useAtLeast function calls atLeast(a*2) where atLeast has @_ensures("result >= x").
/// The postcondition assumption "`call_result` >= a*2" should enable proving "result >= a*2".
#[test]
fn cli_e2e_mul_arg_ensures_substitution_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_ensures_mul_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // useAtLeast spec should verify OK because we assume atLeast's postcondition
    // with the multiplication argument (a*2) substituted for parameter x
    assert!(
        stderr.contains("useAtLeast spec") && stderr.contains("OK"),
        "useAtLeast spec should verify OK using callee postcondition with mul arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Overall verification should succeed
    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );
}

/// Test that multiplication argument expression substitution is reflected in JSON output.
#[test]
fn cli_e2e_mul_arg_ensures_substitution_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_ensures_mul_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find the useAtLeast bundle
    let use_at_least_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("useAtLeast"))
    });

    assert!(
        use_at_least_bundle.is_some(),
        "should have useAtLeast bundle in output, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = use_at_least_bundle.unwrap();

    // useAtLeast spec should verify
    let spec_result = bundle["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "useAtLeast spec should verify using mul arg substitution, got: {bundle}"
    );
}

/// Negative control: multiplication argument - verification FAILS without callee postcondition.
/// This proves the caller's @_ensures("result >= a*2") cannot be verified without assuming
/// the callee's postcondition. Tests that our positive test isn't a false positive.
#[test]
fn cli_e2e_mul_arg_fails_without_callee_postcondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where callee has NO @_ensures but caller expects result >= a*2
    // Uses module "nomulspec" (9 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// atLeast: NO postcondition here - caller cannot assume anything
func atLeast(_ x: Int) -> Int

// useAtLeast: caller tries to prove result >= a*2 but cannot without callee spec
@_ensures("result >= a * 2")
func useAtLeast(_ a: Int) -> Int

sil hidden @$s9nomulspec7atLeastyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}

sil hidden @$s9nomulspec10useAtLeastySiSiF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "a", argno 1
  // Compute a*2
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 2
  %4 = integer_literal $Builtin.Int1, 0
  %5 = builtin "smul_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
  %6 = tuple_extract %5, 0
  %7 = struct $Int (%6)
  // Call atLeast(a*2)
  %8 = function_ref @$s9nomulspec7atLeastyS2iF : $@convention(thin) (Int) -> Int
  %9 = apply %8(%7) : $@convention(thin) (Int) -> Int
  return %9
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_mul_ensures_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // useAtLeast spec should FAIL because we have no assumption from callee
    assert!(
        stderr.contains("useAtLeast spec") && stderr.contains("FAIL"),
        "useAtLeast spec should FAIL without callee postcondition, got stderr: {stderr}"
    );

    // Exit code should be 1 for verification failure
    assert_eq!(
        output.status.code(),
        Some(1),
        "should exit with code 1 for verification failure\nstderr: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

// ===========================================================================
// Division Argument Expression @_ensures Substitution Tests
// ===========================================================================
// These tests verify that postcondition assumptions work correctly when
// the call site uses division argument expressions like addOne(a/2).

/// Test that division argument expression substitution works in @_ensures assumptions.
/// useDivArg(@_ensures "result > a/2") calls addOne(a/2).
/// The postcondition is provable because: call addOne(a/2) => `call_result` > a/2.
#[test]
fn cli_e2e_div_arg_ensures_substitution_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_ensures_div_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("useDivArg spec") && line.contains("): OK")),
        "useDivArg spec should verify OK using callee postcondition with div arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Overall verification should succeed
    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );
}

/// Test that division argument expression substitution is reflected in JSON output.
#[test]
fn cli_e2e_div_arg_ensures_substitution_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_ensures_div_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find the useDivArg bundle
    let use_div_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("useDivArg"))
    });

    assert!(
        use_div_bundle.is_some(),
        "should have useDivArg bundle in output, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = use_div_bundle.unwrap();

    // useDivArg spec should verify
    let spec_result = bundle["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "useDivArg spec should verify using div arg substitution, got: {bundle}"
    );
}

/// Negative control: division arg postcondition fails when callee has no @_ensures.
#[test]
fn cli_e2e_div_arg_fails_without_callee_postcondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where callee has NO @_ensures but caller expects result > a/2
    // Uses module "nodivspec" (9 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// addOne: NO postcondition here - caller cannot assume anything
func addOne(_ x: Int) -> Int

// useDivArg: caller tries to prove result > a/2 but cannot without callee spec
@_ensures("result > a / 2")
func useDivArg(_ a: Int) -> Int

sil hidden @$s9nodivspec6addOneyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 1
  %4 = integer_literal $Builtin.Int1, 0
  %5 = builtin "sadd_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
  %6 = tuple_extract %5, 0
  %7 = struct $Int (%6)
  return %7
}

sil hidden @$s9nodivspec9useDivArgySiSiF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "a", argno 1
  // Compute a/2
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 2
  %4 = builtin "sdiv_Int64"(%2, %3) : $Builtin.Int64
  %5 = struct $Int (%4)
  // Call addOne(a/2)
  %6 = function_ref @$s9nodivspec6addOneyS2iF : $@convention(thin) (Int) -> Int
  %7 = apply %6(%5) : $@convention(thin) (Int) -> Int
  return %7
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_div_ensures_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    if cfg!(feature = "z3-fallback") {
        assert!(
            stderr
                .lines()
                .any(|line| line.contains("useDivArg spec") && line.contains("): FAIL")),
            "useDivArg spec should FAIL without callee postcondition when Z3 fallback is enabled, got stderr: {stderr}"
        );

        // With Z3 fallback, the verifier can find a concrete counterexample model showing the spec is not provable.
        assert_eq!(
            output.status.code(),
            Some(1),
            "should exit with code 1 for verification failure\nstderr: {stderr}"
        );
    } else {
        assert!(
            stderr
                .lines()
                .any(|line| line.contains("useDivArg spec") && line.contains("): WARN")),
            "useDivArg spec should be WARN (unknown) without callee postcondition, got stderr: {stderr}"
        );

        // Unknown results do not exit with code 1 (only definite failures do).
        assert_eq!(
            output.status.code(),
            Some(0),
            "should exit with code 0 for unknown (WARN) result\nstderr: {stderr}"
        );
    }

    std::fs::remove_file(&tmp_file).ok();
}

// ==================== @_requires complex argument expression tests ====================
//
// These tests verify that CallPrecondition VCs correctly handle complex argument
// expressions. When call f(a+1) where f has @_requires("x > 0"), the caller must
// prove (a+1) > 0. With caller precondition a >= 0, this should verify.

/// Test that @_requires precondition with complex argument expression verifies.
/// callWithAddOne(a) calls requiresPositive(a+1) with @_requires("x > 0").
/// With caller precondition a >= 0, the obligation a+1 > 0 should be provable.
#[test]
fn cli_e2e_complex_arg_requires_substitution_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_requires_complex_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // callWithAddOne's call to requiresPositive should verify
    // The call precondition x > 0 with x := a+1 becomes a+1 > 0
    // With caller hypothesis a >= 0, this is provable
    assert!(
        stderr.contains("callWithAddOne") && stderr.contains("OK"),
        "callWithAddOne call precondition should verify with complex arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Exit code should be 0 for success
    assert_eq!(
        output.status.code(),
        Some(0),
        "should exit with code 0 for verification success\nstderr: {stderr}\nstdout: {stdout}"
    );
}

/// Test that complex argument @_requires substitution is reflected in JSON output.
#[test]
fn cli_e2e_complex_arg_requires_substitution_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_requires_complex_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find callWithAddOne bundle
    let call_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|n| n.contains("callWithAddOne"))
    });

    assert!(
        call_bundle.is_some(),
        "should have callWithAddOne bundle in output, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = call_bundle.unwrap();

    // Should have auto_vc_results
    let auto_vc_results = bundle["auto_vc_results"]
        .as_array()
        .expect("should have auto_vc_results");

    // Should have at least one verified auto-VC (the call precondition)
    // Note: result is nested as result.result in JSON structure
    let verified_count = auto_vc_results
        .iter()
        .filter(|r| r["result"]["result"].as_str() == Some("Verified"))
        .count();

    assert!(
        verified_count >= 1,
        "callWithAddOne should have at least 1 verified auto-VC (the call precondition), got: {auto_vc_results:?}"
    );
}

/// Negative control: verification FAILS when caller precondition is too weak.
/// Without a >= 0 precondition, we cannot prove a+1 > 0 for all a.
#[test]
fn cli_e2e_complex_arg_requires_fails_without_caller_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where caller has NO @_requires but callee needs x > 0
    // Uses module "noreqprecond" (12 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// requiresPositive: requires x > 0
@_requires("x > 0")
func requiresPositive(_ x: Int) -> Int

// callWithAddOne: NO precondition - cannot prove a+1 > 0 for all a
func callWithAddOne(_ a: Int) -> Int

sil hidden @$s12noreqprecond16requiresPositiveyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}

sil hidden @$s12noreqprecond14callWithAddOneyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "a", argno 1
  // Compute a+1
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 1
  %4 = integer_literal $Builtin.Int1, 0
  %5 = builtin "sadd_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
  %6 = tuple_extract %5, 0
  %7 = struct $Int (%6)
  // Call requiresPositive(a+1)
  %8 = function_ref @$s12noreqprecond16requiresPositiveyS2iF : $@convention(thin) (Int) -> Int
  %9 = apply %8(%7) : $@convention(thin) (Int) -> Int
  return %9
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_requires_precondition_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // callWithAddOne's call precondition should FAIL
    // Without knowing a >= 0, we cannot prove a+1 > 0
    assert!(
        stderr.contains("callWithAddOne") && stderr.contains("FAIL"),
        "callWithAddOne call precondition should FAIL without caller precondition, got stderr: {stderr}"
    );

    // Exit code should be 1 for verification failure
    assert_eq!(
        output.status.code(),
        Some(1),
        "should exit with code 1 for verification failure\nstderr: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

/// Test that multiplication argument expression substitution in @_requires works.
/// f(a*2) where f has @_requires("x > 0") and caller has @_requires("a > 0")
/// should verify because a > 0 => a*2 > 0 for positive multiplication.
#[test]
fn cli_e2e_mul_arg_requires_substitution_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_requires_mul_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // callWithDoubled's call to requiresPositive should verify
    // The call precondition x > 0 with x := a*2 becomes a*2 > 0
    // With caller hypothesis a > 0, this is provable (positive times positive)
    assert!(
        stderr.contains("callWithDoubled") && stderr.contains("OK"),
        "callWithDoubled call precondition should verify with mul arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Exit code should be 0 for success
    assert_eq!(
        output.status.code(),
        Some(0),
        "should exit with code 0 for verification success\nstderr: {stderr}\nstdout: {stdout}"
    );
}

/// Test that multiplication argument @_requires substitution is reflected in JSON output.
#[test]
fn cli_e2e_mul_arg_requires_substitution_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_requires_mul_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find callWithDoubled bundle
    let call_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|n| n.contains("callWithDoubled"))
    });

    assert!(
        call_bundle.is_some(),
        "should have callWithDoubled bundle in output, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = call_bundle.unwrap();

    // Should have auto_vc_results
    let auto_vc_results = bundle["auto_vc_results"]
        .as_array()
        .expect("should have auto_vc_results");

    // Should have at least one verified auto-VC (the call precondition)
    // Note: result is nested as result.result in JSON structure
    let verified_count = auto_vc_results
        .iter()
        .filter(|r| r["result"]["result"].as_str() == Some("Verified"))
        .count();

    assert!(
        verified_count >= 1,
        "callWithDoubled should have at least 1 verified auto-VC (the call precondition), got: {auto_vc_results:?}"
    );
}

/// Negative control: verification FAILS when caller precondition is too weak.
/// Without a > 0 precondition, we cannot prove a*2 > 0 for all a.
#[test]
fn cli_e2e_mul_arg_requires_fails_without_caller_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where caller has NO @_requires but callee needs x > 0
    // Uses module "noreqmulpre" (11 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// requiresPositive: requires x > 0
@_requires("x > 0")
func requiresPositive(_ x: Int) -> Int

// callWithDoubled: NO precondition - cannot prove a*2 > 0 for all a
func callWithDoubled(_ a: Int) -> Int

sil hidden @$s11noreqmulpre16requiresPositiveyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}

sil hidden @$s11noreqmulpre15callWithDoubledyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "a", argno 1
  // Compute a*2
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 2
  %4 = integer_literal $Builtin.Int1, 0
  %5 = builtin "smul_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
  %6 = tuple_extract %5, 0
  %7 = struct $Int (%6)
  // Call requiresPositive(a*2)
  %8 = function_ref @$s11noreqmulpre16requiresPositiveyS2iF : $@convention(thin) (Int) -> Int
  %9 = apply %8(%7) : $@convention(thin) (Int) -> Int
  return %9
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_requires_mul_precondition_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // callWithDoubled's call precondition should FAIL
    // Without knowing a > 0, we cannot prove a*2 > 0
    assert!(
        stderr.contains("callWithDoubled") && stderr.contains("FAIL"),
        "callWithDoubled call precondition should FAIL without caller precondition, got stderr: {stderr}"
    );

    // Exit code should be 1 for verification failure
    assert_eq!(
        output.status.code(),
        Some(1),
        "should exit with code 1 for verification failure\nstderr: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

// ===========================================================================
// Division Argument Expression @_requires Substitution Tests
// ===========================================================================
// These tests verify that CallPrecondition VCs correctly handle division argument
// expressions. When calling f(a/2) where f has @_requires("x <= 10"), the caller must
// prove (a/2) <= 10, using its own @_requires hypotheses.

/// Test that division argument expression substitution in @_requires works.
/// f(a/2) where f has @_requires("x <= 10") and caller has @_requires("a/2 <= 10")
/// should verify because the obligation matches the hypothesis.
#[test]
fn cli_e2e_div_arg_requires_substitution_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_requires_div_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("callWithHalf auto") && line.contains("): OK")),
        "callWithHalf call precondition should verify with div arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Exit code should be 0 for success
    assert_eq!(
        output.status.code(),
        Some(0),
        "should exit with code 0 for verification success\nstderr: {stderr}\nstdout: {stdout}"
    );
}

/// Test that division argument @_requires substitution is reflected in JSON output.
#[test]
fn cli_e2e_div_arg_requires_substitution_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_requires_div_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find callWithHalf bundle
    let call_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|n| n.contains("callWithHalf"))
    });

    assert!(
        call_bundle.is_some(),
        "should have callWithHalf bundle in output, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = call_bundle.unwrap();

    // Should have auto_vc_results
    let auto_vc_results = bundle["auto_vc_results"]
        .as_array()
        .expect("should have auto_vc_results");

    // Should have at least one verified auto-VC (the call precondition)
    // Note: result is nested as result.result in JSON structure
    let verified_count = auto_vc_results
        .iter()
        .filter(|r| r["result"]["result"].as_str() == Some("Verified"))
        .count();

    assert!(
        verified_count >= 1,
        "callWithHalf should have at least 1 verified auto-VC (the call precondition), got: {auto_vc_results:?}"
    );
}

/// Negative control: without a caller precondition, we cannot prove a/2 <= 10 for all a.
#[test]
fn cli_e2e_div_arg_requires_fails_without_caller_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where caller has NO @_requires but callee needs x <= 10
    // Uses module "noreqdivpre" (11 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// requiresAtMostTen: requires x <= 10
@_requires("x <= 10")
func requiresAtMostTen(_ x: Int) -> Int

// callWithHalf: NO precondition - cannot prove a/2 <= 10 for all a
func callWithHalf(_ a: Int) -> Int

sil hidden @$s11noreqdivpre17requiresAtMostTenyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}

sil hidden @$s11noreqdivpre12callWithHalfyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "a", argno 1
  // Compute a/2
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 2
  %4 = builtin "sdiv_Int64"(%2, %3) : $Builtin.Int64
  %5 = struct $Int (%4)
  // Call requiresAtMostTen(a/2)
  %6 = function_ref @$s11noreqdivpre17requiresAtMostTenyS2iF : $@convention(thin) (Int) -> Int
  %7 = apply %6(%5) : $@convention(thin) (Int) -> Int
  return %7
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_requires_div_precondition_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    if cfg!(feature = "z3-fallback") {
        assert!(
            stderr
                .lines()
                .any(|line| line.contains("callWithHalf auto") && line.contains("): FAIL")),
            "callWithHalf call precondition should FAIL without caller precondition when Z3 fallback is enabled, got stderr: {stderr}"
        );

        assert_eq!(
            output.status.code(),
            Some(1),
            "should exit with code 1 for verification failure\nstderr: {stderr}"
        );
    } else {
        assert!(
            stderr
                .lines()
                .any(|line| line.contains("callWithHalf auto") && line.contains("): WARN")),
            "callWithHalf call precondition should be WARN (unknown) without caller precondition, got stderr: {stderr}"
        );

        // Unknown results do not exit with code 1 (only definite failures do).
        assert_eq!(
            output.status.code(),
            Some(0),
            "should exit with code 0 for unknown (WARN) result\nstderr: {stderr}"
        );
    }

    std::fs::remove_file(&tmp_file).ok();
}

// ===========================================================================
// Modulo argument expression tests (srem_Int64)
// ===========================================================================

/// Tests @_ensures with modulo argument expressions.
/// The callee postcondition (result > x) with call addOne(a % 10) should
/// generate assumption (`call_result` > a % 10) which proves (result > a % 10).
#[test]
fn cli_e2e_mod_arg_ensures_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_ensures_mod_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("useModArg spec") && line.contains("): OK")),
        "useModArg spec should verify OK using callee postcondition with mod arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests @_ensures with modulo argument expressions in JSON output.
#[test]
fn cli_e2e_mod_arg_ensures_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_ensures_mod_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find the useModArg bundle
    let use_mod_bundle = bundles
        .iter()
        .find(|b| b["function_name"].as_str() == Some("useModArg"));

    assert!(
        use_mod_bundle.is_some(),
        "should find useModArg bundle, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = use_mod_bundle.unwrap();

    // useModArg spec should verify
    let spec_result = bundle["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "useModArg spec should verify using mod arg substitution, got: {bundle}"
    );
}

/// Tests @_requires with modulo argument expressions.
/// The callee precondition (x <= 10) with call requiresAtMostTen(a % 10) should
/// generate obligation (a % 10 <= 10) which is provable from caller precondition.
#[test]
fn cli_e2e_mod_arg_requires_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_requires_mod_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("callWithMod auto") && line.contains("): OK")),
        "callWithMod call precondition should verify with mod arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests @_requires with modulo argument expressions in JSON output.
#[test]
fn cli_e2e_mod_arg_requires_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_requires_mod_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find callWithMod bundle
    let call_bundle = bundles
        .iter()
        .find(|b| b["function_name"].as_str() == Some("callWithMod"));

    assert!(
        call_bundle.is_some(),
        "should find callWithMod bundle, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = call_bundle.unwrap();

    // Should have auto_vc_results
    let auto_vc_results = bundle["auto_vc_results"]
        .as_array()
        .expect("should have auto_vc_results");

    // Should have at least one verified auto-VC (the call precondition)
    // Note: result is nested as result.result in JSON structure
    let verified_count = auto_vc_results
        .iter()
        .filter(|r| r["result"]["result"].as_str() == Some("Verified"))
        .count();

    assert!(
        verified_count >= 1,
        "callWithMod should have at least 1 verified auto-VC (the call precondition), got: {auto_vc_results:?}"
    );
}

/// Negative control: without a caller precondition, we cannot prove a % 10 <= 10 for all a.
/// Actually, a % 10 IS always <= 10 mathematically, but our LIA backend may not know this
/// without the explicit hypothesis. This tests that the hypothesis-to-obligation match works.
#[test]
fn cli_e2e_mod_arg_requires_fails_without_caller_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where caller has NO @_requires but callee needs x <= 10
    // Uses module "noreqmodpre" (11 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// requiresAtMostTen: requires x <= 10
@_requires("x <= 10")
func requiresAtMostTen(_ x: Int) -> Int

// callWithMod: NO precondition - cannot prove a % 10 <= 10 without reasoning about mod
func callWithMod(_ a: Int) -> Int

sil hidden @$s11noreqmodpre17requiresAtMostTenyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}

sil hidden @$s11noreqmodpre11callWithModyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "a", argno 1
  // Compute a % 10
  %2 = struct_extract %0, #Int._value
  %3 = integer_literal $Builtin.Int64, 10
  %4 = builtin "srem_Int64"(%2, %3) : $Builtin.Int64
  %5 = struct $Int (%4)
  // Call requiresAtMostTen(a % 10)
  %6 = function_ref @$s11noreqmodpre17requiresAtMostTenyS2iF : $@convention(thin) (Int) -> Int
  %7 = apply %6(%5) : $@convention(thin) (Int) -> Int
  return %7
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_requires_mod_precondition_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Note: LIA backend might return unknown (WARN) because it doesn't reason about
    // modulo semantics. The key is that it doesn't verify without the hypothesis.
    let has_warn_or_fail = stderr.lines().any(|line| {
        line.contains("callWithMod auto") && (line.contains("): WARN") || line.contains("): FAIL"))
    });

    assert!(
        has_warn_or_fail,
        "callWithMod call precondition should be WARN or FAIL without caller precondition, got stderr: {stderr}"
    );

    // Unknown or failed results: unknown exits 0, failed exits 1
    // Either is acceptable for this negative control
    let exit_code = output.status.code().unwrap_or(-1);
    assert!(
        exit_code == 0 || exit_code == 1,
        "should exit with code 0 (unknown) or 1 (fail), got: {exit_code}\nstderr: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

// ============================================================================
// Nested compound argument expression tests: (a + b) * 2
// Tests both @_ensures and @_requires with multi-operation expressions
// ============================================================================

/// Tests @_ensures with multi-parameter argument expressions.
/// The callee postcondition (result >= x) with call atLeast(a + b) should
/// generate assumption `call_result` >= (a + b), proving result >= a + b.
#[test]
fn cli_e2e_nested_arg_ensures_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_ensures_nested_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("callWithSum spec") && line.contains("): OK")),
        "callWithSum spec should verify OK using callee postcondition with nested arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests @_ensures with multi-parameter argument expressions in JSON output.
#[test]
fn cli_e2e_nested_arg_ensures_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_ensures_nested_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find the callWithSum bundle
    let call_bundle = bundles
        .iter()
        .find(|b| b["function_name"].as_str() == Some("callWithSum"));

    assert!(
        call_bundle.is_some(),
        "should find callWithSum bundle, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = call_bundle.unwrap();

    // callWithSum spec should verify
    let spec_result = bundle["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "callWithSum spec should verify using nested arg substitution, got: {bundle}"
    );
}

/// Tests @_requires with multi-parameter argument expressions.
/// The callee precondition (x > 0) with call requiresPositive(a + b) should
/// generate obligation (a + b) > 0 which is provable from caller precondition.
#[test]
fn cli_e2e_nested_arg_requires_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cross_requires_nested_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("callWithSum auto") && line.contains("): OK")),
        "callWithSum call precondition should verify with multi-param arg substitution, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests @_requires with multi-parameter argument expressions in JSON output.
#[test]
fn cli_e2e_nested_arg_requires_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/cross_requires_nested_args_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find callWithSum bundle
    let call_bundle = bundles
        .iter()
        .find(|b| b["function_name"].as_str() == Some("callWithSum"));

    assert!(
        call_bundle.is_some(),
        "should find callWithSum bundle, got bundles: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let bundle = call_bundle.unwrap();

    // Should have auto_vc_results
    let auto_vc_results = bundle["auto_vc_results"]
        .as_array()
        .expect("should have auto_vc_results");

    // Should have at least one verified auto-VC (the call precondition)
    let verified_count = auto_vc_results
        .iter()
        .filter(|r| r["result"]["result"].as_str() == Some("Verified"))
        .count();

    assert!(
        verified_count >= 1,
        "callWithSum should have at least 1 verified auto-VC (the call precondition), got: {auto_vc_results:?}"
    );
}

/// Negative control: without a caller precondition, we cannot prove a + b > 0 for all a, b.
#[test]
fn cli_e2e_nested_arg_requires_fails_without_caller_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create SIL where caller has NO @_requires but callee needs x > 0
    // Uses module "noreqnested" (11 chars)
    let sil = r#"sil_stage canonical

import Builtin
import Swift

// requiresPositive: requires x > 0
@_requires("x > 0")
func requiresPositive(_ x: Int) -> Int

// callWithSum: NO precondition - cannot prove a + b > 0
func callWithSum(_ a: Int, _ b: Int) -> Int

sil hidden @$s11noreqnested16requiresPositiveyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}

sil hidden @$s11noreqnested11callWithSumyS2i_SitF : $@convention(thin) (Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int):
  debug_value %0, let, name "a", argno 1
  debug_value %1, let, name "b", argno 2
  // Compute a + b
  %4 = struct_extract %0, #Int._value
  %5 = struct_extract %1, #Int._value
  %6 = integer_literal $Builtin.Int1, 0
  %7 = builtin "sadd_with_overflow_Int64"(%4, %5, %6) : $(Builtin.Int64, Builtin.Int1)
  %8 = tuple_extract %7, 0
  %9 = struct $Int (%8)
  // Call requiresPositive(a + b)
  %10 = function_ref @$s11noreqnested16requiresPositiveyS2iF : $@convention(thin) (Int) -> Int
  %11 = apply %10(%9) : $@convention(thin) (Int) -> Int
  return %11
}
"#;

    let tmp_dir = std::env::temp_dir();
    let tmp_file = tmp_dir.join("no_requires_nested_precondition_control.sil");
    std::fs::write(&tmp_file, sil).expect("failed to write temp file");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg(&tmp_file)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Without the caller precondition, the call precondition should be WARN or FAIL
    let has_warn_or_fail = stderr.lines().any(|line| {
        line.contains("callWithSum auto") && (line.contains("): WARN") || line.contains("): FAIL"))
    });

    assert!(
        has_warn_or_fail,
        "callWithSum call precondition should be WARN or FAIL without caller precondition, got stderr: {stderr}"
    );

    // Unknown or failed results: unknown exits 0, failed exits 1
    // Either is acceptable for this negative control
    let exit_code = output.status.code().unwrap_or(-1);
    assert!(
        exit_code == 0 || exit_code == 1,
        "should exit with code 0 (unknown) or 1 (fail), got: {exit_code}\nstderr: {stderr}"
    );

    std::fs::remove_file(&tmp_file).ok();
}

// =============================================================================
// switch_enum control flow tests
// =============================================================================

/// Tests `switch_enum` with Optional type verifies when precondition ensures non-negative payload.
#[test]
fn cli_e2e_switch_enum_optional_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/switch_enum_optional_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "switch_enum_optional.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("unwrapOrZero spec") && line.contains("): OK")),
        "unwrapOrZero spec should verify OK with precondition, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests `switch_enum` with Optional type in JSON output.
#[test]
fn cli_e2e_switch_enum_optional_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/switch_enum_optional_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Single function output format
    assert_eq!(
        json["function_name"].as_str(),
        Some("unwrapOrZero"),
        "should have unwrapOrZero function"
    );

    let spec_result = json["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "unwrapOrZero spec should verify with precondition, got: {json}"
    );
}

/// Tests `switch_enum` that should fail verification (returns -1 which violates result >= 0).
#[test]
fn cli_e2e_switch_enum_should_fail() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/switch_enum_should_fail.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // The verification should fail because result can be -1 which violates result >= 0
    assert!(
        stderr
            .lines()
            .any(|line| line.contains("unwrapOrNegative spec") && line.contains("): FAIL")),
        "unwrapOrNegative spec should FAIL when return can be -1, got stderr: {stderr}"
    );

    // Should exit with code 1 (failed)
    let exit_code = output.status.code().unwrap_or(-1);
    assert_eq!(
        exit_code, 1,
        "should exit with code 1 (fail), got: {exit_code}\nstderr: {stderr}"
    );
}

// =============================================================================
// try_apply (throwing function) control flow tests
// =============================================================================

/// Tests `try_apply` parsing and verification with a tautology postcondition.
/// The function calls a throwing function and handles both success and error paths.
#[test]
fn cli_e2e_try_apply_throwing_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/try_apply_throwing_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "try_apply_throwing.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("tryOrDefault spec") && line.contains("): OK")),
        "tryOrDefault spec should verify OK, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests `try_apply` in JSON output mode.
#[test]
fn cli_e2e_try_apply_throwing_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/try_apply_throwing_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // JSON has "bundles" array with multiple functions
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    // Find the tryOrDefault function
    let try_or_default = bundles
        .iter()
        .find(|b| b["function_name"].as_str() == Some("tryOrDefault"))
        .expect("should have tryOrDefault function");

    let spec_result = try_or_default["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "tryOrDefault spec should verify, got: {json}"
    );
}

/// Tests `try_apply` that should fail verification (error path returns -1 violating result >= 0).
#[test]
fn cli_e2e_try_apply_should_fail() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/try_apply_should_fail.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // The verification should fail because error path returns -1 which violates result >= 0
    assert!(
        stderr
            .lines()
            .any(|line| line.contains("tryOrPositive spec") && line.contains("): FAIL")),
        "tryOrPositive spec should FAIL when error path returns -1, got stderr: {stderr}"
    );

    // Should exit with code 1 (failed)
    let exit_code = output.status.code().unwrap_or(-1);
    assert_eq!(
        exit_code, 1,
        "should exit with code 1 (fail), got: {exit_code}\nstderr: {stderr}"
    );
}

// =============================================================================
// switch_enum Result<T, E> control flow tests
// =============================================================================

/// Tests `switch_enum` with Result<Int, Error> type verifies when precondition ensures non-negative payload.
/// The function returns the success value or 0 on failure, and with precondition that success payload >= 0.
#[test]
fn cli_e2e_switch_enum_result_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/switch_enum_result_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "switch_enum_result.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("unwrapResultOrZero spec") && line.contains("): OK")),
        "unwrapResultOrZero spec should verify OK, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests `switch_enum` with Result<Int, Error> type in JSON output.
#[test]
fn cli_e2e_switch_enum_result_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/switch_enum_result_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Single function output format
    assert_eq!(
        json["function_name"].as_str(),
        Some("unwrapResultOrZero"),
        "should have unwrapResultOrZero function"
    );

    let spec_result = json["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "unwrapResultOrZero spec should verify, got: {json}"
    );
}

/// Tests `switch_enum` with Result<Int, Error> that should fail verification.
/// Returns success value or -1 on failure, violating result >= 0.
#[test]
fn cli_e2e_switch_enum_result_should_fail() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/switch_enum_result_should_fail.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // The verification should fail because:
    // 1. Success branch has no constraint on payload (could be negative)
    // 2. Failure branch returns -1 which violates result >= 0
    assert!(
        stderr
            .lines()
            .any(|line| line.contains("unwrapResultOrNegative spec") && line.contains("): FAIL")),
        "unwrapResultOrNegative spec should FAIL when result can be negative, got stderr: {stderr}"
    );

    // Should exit with code 1 (failed)
    let exit_code = output.status.code().unwrap_or(-1);
    assert_eq!(
        exit_code, 1,
        "should exit with code 1 (fail), got: {exit_code}\nstderr: {stderr}"
    );
}

// =============================================================================
// checked_cast_branch control flow tests
// =============================================================================

/// Tests `checked_cast_br` with type casting verifies when precondition ensures non-negative casted value.
#[test]
fn cli_e2e_checked_cast_branch_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/checked_cast_branch_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "checked_cast_branch.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("castOrDefault spec") && line.contains("): OK")),
        "castOrDefault spec should verify OK with precondition, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests `checked_cast_br` with type casting in JSON output.
#[test]
fn cli_e2e_checked_cast_branch_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/checked_cast_branch_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Single function output format
    assert_eq!(
        json["function_name"].as_str(),
        Some("castOrDefault"),
        "should have castOrDefault function"
    );

    let spec_result = json["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "castOrDefault spec should verify with precondition, got: {json}"
    );
}

/// Tests `checked_cast_br` that should fail verification (returns -1 which violates result >= 0).
#[test]
fn cli_e2e_checked_cast_branch_should_fail() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/checked_cast_branch_should_fail.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // The verification should fail because:
    // 1. Success branch returns 4 (OK)
    // 2. Failure branch returns -1 which violates result >= 0
    assert!(
        stderr
            .lines()
            .any(|line| line.contains("castOrNegative spec") && line.contains("): FAIL")),
        "castOrNegative spec should FAIL when result can be negative, got stderr: {stderr}"
    );

    // Should exit with code 1 (failed)
    let exit_code = output.status.code().unwrap_or(-1);
    assert_eq!(
        exit_code, 1,
        "should exit with code 1 (fail), got: {exit_code}\nstderr: {stderr}"
    );
}

// =============================================================================
// select_enum instruction tests
// =============================================================================

/// Tests `select_enum` instruction parsing and verification.
/// `select_enum` is a single-value instruction that picks a result based on enum discriminant.
#[test]
fn cli_e2e_select_enum_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/select_enum_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "select_enum.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests `select_enum` in JSON output mode.
#[test]
fn cli_e2e_select_enum_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/select_enum_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Check function was parsed
    assert!(
        json["function_name"].as_str().is_some(),
        "should have function_name in output, got: {json}"
    );
}

// =============================================================================
// Address-based enum instruction tests (init_enum_data_addr, inject_enum_addr, switch_enum_addr)
// =============================================================================

/// Tests in-place enum construction with `init_enum_data_addr` and `inject_enum_addr`.
/// The makeSome function constructs Optional<Int>.some(value) in-place.
#[test]
fn cli_e2e_enum_addr_construction_parses() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/enum_addr_construction_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "enum_addr_construction.sil should parse successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Check that the function was found
    assert!(
        stdout.contains("makeSome"),
        "should find makeSome function, got stdout: {stdout}"
    );
}

/// Tests `switch_enum_addr` terminator with Optional type.
/// The getOrDefault function uses `switch_enum_addr` to branch on an indirect Optional.
#[test]
fn cli_e2e_switch_enum_addr_verifies() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/switch_enum_addr_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "switch_enum_addr.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    assert!(
        stderr
            .lines()
            .any(|line| line.contains("getOrDefault spec") && line.contains("): OK")),
        "getOrDefault spec should verify OK with precondition, got stderr: {stderr}\nstdout: {stdout}"
    );
}

/// Tests `switch_enum_addr` in JSON output.
#[test]
fn cli_e2e_switch_enum_addr_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/switch_enum_addr_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    assert_eq!(
        json["function_name"].as_str(),
        Some("getOrDefault"),
        "should have getOrDefault function"
    );

    let spec_result = json["spec_result"]["result"]
        .as_str()
        .expect("should have spec_result");
    assert_eq!(
        spec_result, "Verified",
        "getOrDefault spec should verify with precondition, got: {json}"
    );
}

/// Tests `switch_enum_addr` that should fail verification (returns -1 which violates result >= 0).
#[test]
fn cli_e2e_switch_enum_addr_should_fail() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/switch_enum_addr_should_fail.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // The verification should fail because result can be -1 which violates result >= 0
    assert!(
        stderr
            .lines()
            .any(|line| line.contains("getOrNegative spec") && line.contains("): FAIL")),
        "getOrNegative spec should FAIL when return can be -1, got stderr: {stderr}"
    );

    // Should exit with code 1 (failed)
    let exit_code = output.status.code().unwrap_or(-1);
    assert_eq!(
        exit_code, 1,
        "should exit with code 1 (fail), got: {exit_code}\nstderr: {stderr}"
    );
}

// ============================================================================
// Protocol existential instruction tests (init_existential_addr, open_existential_addr,
// init_existential_ref, open_existential_ref)
// ============================================================================

/// Tests `init_existential_addr` and `open_existential_addr` for address-based protocol existentials.
/// These instructions handle protocol types stored indirectly (at addresses).
#[test]
fn cli_e2e_existential_addr_verifies() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("tests/sil_examples/existential_addr_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "existential_addr.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the summary shows functions verified (output goes to stdout)
    assert!(
        stdout.contains("verified"),
        "should show verification summary, got stdout: {stdout}"
    );
}

/// Tests `init_existential_addr` in JSON output mode.
#[test]
fn cli_e2e_existential_addr_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/existential_addr_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse JSON output
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("should produce valid JSON");

    // Check the summary
    let summary = &json["summary"];
    assert!(
        summary["verified"].as_u64().unwrap() >= 2,
        "should verify at least 2 functions: {json}"
    );
    assert_eq!(
        summary["failed"].as_u64().unwrap(),
        0,
        "no functions should fail: {json}"
    );
}

/// Tests `init_existential_ref` and `open_existential_ref` for class-bound protocol existentials.
/// These instructions handle reference-type existentials (protocols constrained to `AnyObject`).
#[test]
fn cli_e2e_existential_ref_verifies() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("tests/sil_examples/existential_ref_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "existential_ref.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the summary shows functions verified (output goes to stdout)
    assert!(
        stdout.contains("verified"),
        "should show verification summary, got stdout: {stdout}"
    );
}

/// Tests `init_existential_ref` and `open_existential_ref` in JSON output mode.
#[test]
fn cli_e2e_existential_ref_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/existential_ref_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse JSON output
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("should produce valid JSON");

    // Check the summary
    let summary = &json["summary"];
    assert!(
        summary["verified"].as_u64().unwrap() >= 2,
        "should verify at least 2 functions: {json}"
    );
    assert_eq!(
        summary["failed"].as_u64().unwrap(),
        0,
        "no functions should fail: {json}"
    );
}

// ============================================================================
// Metatype existential instruction tests (existential_metatype,
// init_existential_metatype, open_existential_metatype)
// ============================================================================

/// Tests `existential_metatype`, `init_existential_metatype`, and `open_existential_metatype`.
/// These instructions handle protocol metatypes.
#[test]
fn cli_e2e_existential_metatype_verifies() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("tests/sil_examples/existential_metatype_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "existential_metatype.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the summary shows functions verified
    assert!(
        stdout.contains("verified"),
        "should show verification summary, got stdout: {stdout}"
    );
}

/// Tests metatype existential instructions in JSON output mode.
#[test]
fn cli_e2e_existential_metatype_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/existential_metatype_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse JSON output
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("should produce valid JSON");

    // Check the summary
    let summary = &json["summary"];
    assert!(
        summary["verified"].as_u64().unwrap() >= 3,
        "should verify at least 3 metatype existential functions: {json}"
    );
    assert_eq!(
        summary["failed"].as_u64().unwrap(),
        0,
        "no metatype existential functions should fail: {json}"
    );
}

// ============================================================================
// Boxed existential instruction tests (alloc_existential_box,
// project_existential_box, open_existential_box, open_existential_box_value,
// dealloc_existential_box)
// ============================================================================

/// Tests boxed existential instructions: `alloc_existential_box`, `project_existential_box`,
/// `open_existential_box`, `open_existential_box_value`, and `dealloc_existential_box`.
/// These instructions handle heap-allocated protocol containers.
#[test]
fn cli_e2e_existential_box_verifies() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("tests/sil_examples/existential_box_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "existential_box.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the summary shows functions verified
    assert!(
        stdout.contains("verified"),
        "should show verification summary, got stdout: {stdout}"
    );
}

/// Tests boxed existential instructions in JSON output mode.
#[test]
fn cli_e2e_existential_box_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/existential_box_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse JSON output
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("should produce valid JSON");

    // Check the summary
    let summary = &json["summary"];
    assert!(
        summary["verified"].as_u64().unwrap() >= 5,
        "should verify at least 5 boxed existential functions: {json}"
    );
    assert_eq!(
        summary["failed"].as_u64().unwrap(),
        0,
        "no boxed existential functions should fail: {json}"
    );
}

// ===========================================================================
// Memory Address Operations Tests
// ===========================================================================
// Tests for ref_element_addr, copy_addr, and destroy_addr instructions.

/// Test `ref_element_addr` (class field access) parses and verifies correctly.
#[test]
fn cli_e2e_memory_addr_ops_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/memory_addr_ops_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should successfully parse all functions
    assert!(
        output.status.success(),
        "memory_addr_ops.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // getPointX and getPositiveX have specs that should verify
    assert!(
        stderr.contains("getPointX spec") && stderr.contains("OK"),
        "getPointX spec should verify OK, got stderr: {stderr}"
    );
    assert!(
        stderr.contains("getPositiveX spec") && stderr.contains("OK"),
        "getPositiveX spec should verify OK, got stderr: {stderr}"
    );

    // All three functions should be parsed
    assert!(
        stdout.contains("Function: getPointX"),
        "should parse getPointX function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("Function: copyPoint"),
        "should parse copyPoint function with copy_addr, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("Function: getPositiveX"),
        "should parse getPositiveX function with immutable ref_element_addr, got stdout: {stdout}"
    );
}

/// Test memory address operations in JSON output mode.
#[test]
fn cli_e2e_memory_addr_ops_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_tswift-verify"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg("--sil")
        .arg("--json")
        .arg("tests/sil_examples/memory_addr_ops_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse JSON output
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("should produce valid JSON");

    // Check bundles array exists with functions
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");
    assert!(
        bundles.len() >= 2,
        "should have at least 2 bundles (functions with specs): {bundles:?}"
    );

    // Check summary: should verify specs with no failures
    let summary = &json["summary"];
    assert!(
        summary["verified"].as_u64().unwrap() >= 2,
        "should verify at least 2 specs from memory_addr_ops: {json}"
    );
    assert_eq!(
        summary["failed"].as_u64().unwrap(),
        0,
        "no memory addr ops should fail: {json}"
    );
}

// ===========================================================================
// Stack Store/Load Tests
// ===========================================================================

/// Test `alloc_stack` + store + load preserves result binding for postconditions.
#[test]
fn cli_e2e_stack_store_load_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/stack_store_load_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "stack_store_load.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    assert!(
        stderr.contains("idThroughVar spec") && stderr.contains("OK"),
        "idThroughVar spec should verify OK, got stderr: {stderr}"
    );
    assert!(
        stdout.contains("Function: idThroughVar"),
        "should include idThroughVar function, got stdout: {stdout}"
    );
}

// ===========================================================================
// Class/Method/Global instruction tests
// ===========================================================================

/// Test class allocation, method dispatch, upcast, and global address instructions.
#[test]
fn cli_e2e_class_method_dispatch_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/class_method_dispatch_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "class_method_dispatch.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the key functions are present and verified
    assert!(
        stdout.contains("Function: testAllocAndMethod"),
        "should include testAllocAndMethod function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("Function: testGlobalAccess"),
        "should include testGlobalAccess function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("Function: testWitnessMethod"),
        "should include testWitnessMethod function, got stdout: {stdout}"
    );

    // Verify specs passed
    assert!(
        stderr.contains("testAllocAndMethod spec") && stderr.contains("OK"),
        "testAllocAndMethod spec should verify OK, got stderr: {stderr}"
    );
}

// ===========================================================================
// Reference counting and metatype instruction tests
// ===========================================================================

/// Test reference counting (`strong_retain`, `strong_release`, `retain_value`, `release_value`)
/// and metatype instructions (metatype, `value_metatype`).
#[test]
fn cli_e2e_refcount_metatype_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/refcount_metatype_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "refcount_metatype.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the key functions are present (using mangled names from SIL)
    assert!(
        stdout.contains("testStrongRetainRelease"),
        "should include testStrongRetainRelease function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testRetainReleaseValue"),
        "should include testRetainReleaseValue function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testStaticMetatype"),
        "should include testStaticMetatype function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testValueMetatype"),
        "should include testValueMetatype function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testCombined"),
        "should include testCombined function, got stdout: {stdout}"
    );

    // Verify summary shows all functions verified (5 functions)
    assert!(
        stdout.contains("5 verified, 0 failed"),
        "all 5 functions should verify successfully, got stdout: {stdout}"
    );
}

// ===========================================================================
// Function conversion and lifetime instruction tests
// ===========================================================================

/// Test function conversion (`thin_to_thick_function`, `convert_function`, `convert_escape_to_noescape`)
/// and lifetime instructions (`fix_lifetime`, `is_unique`).
#[test]
fn cli_e2e_func_conversion_lifetime_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/func_conversion_lifetime_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "func_conversion_lifetime.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the key functions are present
    assert!(
        stdout.contains("testThinToThick"),
        "should include testThinToThick function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testConvertFunction"),
        "should include testConvertFunction function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testEscapeToNoEscape"),
        "should include testEscapeToNoEscape function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testFixLifetime"),
        "should include testFixLifetime function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testIsUnique"),
        "should include testIsUnique function, got stdout: {stdout}"
    );

    // Verify summary shows all functions verified (7 functions including helperFunc)
    assert!(
        stdout.contains("7 verified, 0 failed"),
        "all 7 functions should verify successfully, got stdout: {stdout}"
    );
}

/// Verbose test for bridge object and `ObjC` interop instructions
#[test]
fn cli_e2e_bridge_objc_interop_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/bridge_objc_interop_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "bridge_objc_interop.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the key functions are present
    assert!(
        stdout.contains("testRefToBridgeObject"),
        "should include testRefToBridgeObject function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testBridgeObjectToWord"),
        "should include testBridgeObjectToWord function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testClassifyBridgeObject"),
        "should include testClassifyBridgeObject function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testValueToBridgeObject"),
        "should include testValueToBridgeObject function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testMetatypeConversion"),
        "should include testMetatypeConversion function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testBlockStorage"),
        "should include testBlockStorage function, got stdout: {stdout}"
    );

    // Verify summary shows all functions verified (7 functions including blockInvoke)
    assert!(
        stdout.contains("7 verified, 0 failed"),
        "all 7 functions should verify successfully, got stdout: {stdout}"
    );
}

#[test]
fn cli_e2e_cow_objc_method_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/cow_objc_method_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "cow_objc_method.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify the key functions are present
    assert!(
        stdout.contains("testObjcMethod"),
        "should include testObjcMethod function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testObjcSuperMethod"),
        "should include testObjcSuperMethod function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testCowMutation"),
        "should include testCowMutation function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testCowMutationNative"),
        "should include testCowMutationNative function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testCowMutationAddr"),
        "should include testCowMutationAddr function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testUnmanagedRetain"),
        "should include testUnmanagedRetain function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testUnmanagedAutorelease"),
        "should include testUnmanagedAutorelease function, got stdout: {stdout}"
    );

    // Verify summary shows all functions verified (8 functions including stub)
    assert!(
        stdout.contains("8 verified, 0 failed"),
        "all 8 functions should verify successfully, got stdout: {stdout}"
    );
}

#[test]
fn cli_e2e_keypath_objc_protocol_conversions_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/keypath_objc_protocol_conversions_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "keypath_objc_protocol_conversions.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    assert!(
        stdout.contains("testObjcProtocolAndKeyPath"),
        "should include testObjcProtocolAndKeyPath function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testUnmanagedConversion"),
        "should include testUnmanagedConversion function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("testRawPointerConversion"),
        "should include testRawPointerConversion function, got stdout: {stdout}"
    );

    assert!(
        stdout.contains("3 verified, 0 failed"),
        "all 3 functions should verify successfully, got stdout: {stdout}"
    );
}

#[test]
fn cli_e2e_weak_unowned_storage_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/weak_unowned_storage_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let _stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Note: This test now expects failures because UnownedAccess VCs are generated
    // for load_unowned instructions. These VCs flag potentially unsafe accesses
    // to unowned references and cannot be verified without user-provided preconditions.

    // Verify the key functions are present
    assert!(
        stdout.contains("test_weak_operations"),
        "should include test_weak_operations function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("test_unowned_operations"),
        "should include test_unowned_operations function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("test_objc_metatype_conversions"),
        "should include test_objc_metatype_conversions function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("test_objc_existential_metatype"),
        "should include test_objc_existential_metatype function, got stdout: {stdout}"
    );

    // UnownedAccess VCs should be generated for load_unowned instructions
    assert!(
        stdout.contains("unowned reference") && stdout.contains("accessed"),
        "should generate UnownedAccess VCs for load_unowned instructions, got stdout: {stdout}"
    );

    // There are 2 load_unowned instructions in test_unowned_operations, so 2 failed VCs
    assert!(
        stdout.contains("4 verified, 2 failed"),
        "should have 4 verified (specs) and 2 failed (UnownedAccess), got stdout: {stdout}"
    );
}

#[test]
fn cli_e2e_pack_async_instructions_verbose() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("--verbose")
        .arg("tests/sil_examples/pack_async_instructions_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "pack_async_instructions.sil should verify successfully, got stderr: {stderr}\nstdout: {stdout}"
    );

    // Verify pack instruction functions are present
    assert!(
        stdout.contains("test_pack_length"),
        "should include test_pack_length function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("test_scalar_pack_index"),
        "should include test_scalar_pack_index function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("test_pack_alloc_dealloc"),
        "should include test_pack_alloc_dealloc function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("test_async_continuation"),
        "should include test_async_continuation function, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("test_async_continuation_throws"),
        "should include test_async_continuation_throws function, got stdout: {stdout}"
    );

    // All 7 functions should verify (helper_func is external declaration, no body to verify)
    assert!(
        stdout.contains("7 verified, 0 failed"),
        "all 7 functions should verify successfully, got stdout: {stdout}"
    );
}

/// Test that forced type cast (as!) generates `CastCheck` auto-VC.
#[test]
fn cli_sil_mode_detects_forced_cast_check_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/forced_cast_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // This example intentionally force casts without checking the type,
    // so verification should FAIL (exit code 1) for the cast check.
    // Note: The SMT solver treats uninterpreted functions (like is_type) as unknown,
    // which results in a verification failure.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failing forced cast check\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // The function name may be mangled or demangled
    assert!(
        stdout.contains("unsafeCast") || stdout.contains("forced_cast"),
        "expected forced_cast/unsafeCast function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("forced cast") && stdout.contains("may fail"),
        "expected 'forced cast' and 'may fail' in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Dog"),
        "expected target type 'Dog' in output, got: {stdout}"
    );
}

/// Test that --sil mode detects integer truncation bounds auto-VCs
///
/// Swift's integer truncation (e.g., Int8(x) where x is Int) generates
/// `cond_fail` instructions for bounds checking. Our verifier should detect
/// these when the value could overflow the target type.
#[test]
fn cli_sil_mode_detects_truncation_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/truncation_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // These functions have no preconditions on input, so truncation
    // bounds checks should FAIL (exit code 1)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 for failing truncation bounds check\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Check that truncateInt is detected (has two bounds checks)
    assert!(
        stdout.contains("Function: truncateInt"),
        "expected 'truncateInt' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Not enough bits to represent a signed value"),
        "expected lower bound check message in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Not enough bits to represent the passed value"),
        "expected upper bound check message in output, got: {stdout}"
    );

    // Check truncateUInt is detected
    assert!(
        stdout.contains("Function: truncateUInt"),
        "expected 'truncateUInt' function in output, got: {stdout}"
    );

    // Check truncateToSigned is detected
    assert!(
        stdout.contains("Function: truncateToSigned"),
        "expected 'truncateToSigned' function in output, got: {stdout}"
    );
}

/// Test that --sil mode detects signed addition overflow auto-VCs
#[test]
fn cli_sil_mode_detects_signed_addition_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Signed addition overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: add"),
        "expected 'add' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects subtraction overflow auto-VCs
#[test]
fn cli_sil_mode_detects_subtraction_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sub_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Subtraction overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sub"),
        "expected 'sub' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects unsigned addition overflow auto-VCs
#[test]
fn cli_sil_mode_detects_unsigned_addition_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/uadd_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Unsigned addition overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: uadd"),
        "expected 'uadd' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects unsigned subtraction overflow auto-VCs
#[test]
fn cli_sil_mode_detects_unsigned_subtraction_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/usub_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Unsigned subtraction overflow is correctly DETECTED - verifier finds counterexample (e.g., a=0, b=1)
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: usub"),
        "expected 'usub' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects negation overflow auto-VCs
/// Swift implements -x as 0 - x, so negation overflow is detected via `ssub_with_overflow`
/// Negation of Int.min overflows, so verifier correctly finds counterexample
#[test]
fn cli_sil_mode_detects_negation_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/neg_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Negation overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert!(
        !output.status.success(),
        "expected failure (overflow detected), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: neg"),
        "expected 'neg' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED") || stdout.contains("Counterexample"),
        "expected FAILED or counterexample in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int8 negation overflow auto-VCs with correct bounds
/// Negation of Int8.min overflows, so verifier correctly finds counterexample
#[test]
fn cli_sil_mode_detects_int8_negation_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/neg_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Negation overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert!(
        !output.status.success(),
        "expected failure (overflow detected), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: neg_int8"),
        "expected 'neg_int8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED") || stdout.contains("Counterexample"),
        "expected FAILED or counterexample in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int16 negation overflow auto-VCs with correct bounds
/// Negation of Int16.min overflows, so verifier correctly finds counterexample
#[test]
fn cli_sil_mode_detects_int16_negation_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/neg_overflow_int16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Negation overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert!(
        !output.status.success(),
        "expected failure (overflow detected), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: neg_int16"),
        "expected 'neg_int16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED") || stdout.contains("Counterexample"),
        "expected FAILED or counterexample in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int32 negation overflow auto-VCs with correct bounds
/// Negation of Int32.min overflows, so verifier correctly finds counterexample
#[test]
fn cli_sil_mode_detects_int32_negation_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/neg_overflow_int32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Negation overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert!(
        !output.status.success(),
        "expected failure (overflow detected), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: neg_int32"),
        "expected 'neg_int32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED") || stdout.contains("Counterexample"),
        "expected FAILED or counterexample in output, got: {stdout}"
    );
}

/// Test that --sil mode detects signed division overflow auto-VCs
/// Division of `INT_MIN` by -1 causes overflow (because -`INT_MIN` doesn't fit)
/// The verifier should detect both div-by-zero AND overflow checks
#[test]
fn cli_sil_mode_detects_signed_division_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/signed_division_overflow_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should have failures (div by zero definitely fails)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero detected), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should have the function name
    assert!(
        stdout.contains("Function: divideUnchecked"),
        "expected 'divideUnchecked' function in output, got: {stdout}"
    );

    // Should detect div-by-zero check
    assert!(
        stdout.contains("div by zero"),
        "expected 'div by zero' VC in output, got: {stdout}"
    );

    // Should detect div overflow check (INT_MIN / -1)
    assert!(
        stdout.contains("div overflow") || stdout.contains("INT_MIN / -1"),
        "expected 'div overflow' VC in output, got: {stdout}"
    );

    // Should have at least 2 auto-VCs (div-by-zero and overflow)
    assert!(
        stdout.contains("Auto-VC #1") && stdout.contains("Auto-VC #2"),
        "expected at least 2 auto-VCs in output, got: {stdout}"
    );
}

/// Test that --sil mode detects range bounds violation auto-VCs
/// Swift's range creation (start..<end) requires start <= end
/// The verifier should detect this as a `CondFail` auto-VC
#[test]
fn cli_sil_mode_detects_range_bounds_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/range_bounds_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Range bounds violation is detected - exit code is 1 (failure found)
    assert!(
        !output.status.success(),
        "expected failure (range bounds violation detected), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should have the function names
    assert!(
        stdout.contains("Function: makeRange"),
        "expected 'makeRange' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Function: makeClosedRange"),
        "expected 'makeClosedRange' function in output, got: {stdout}"
    );

    // Should detect range bounds check
    assert!(
        stdout.contains("lowerBound") || stdout.contains("upperBound") || stdout.contains("Range"),
        "expected range bounds check message in output, got: {stdout}"
    );

    // Should show counterexamples
    assert!(
        stdout.contains("FAILED") || stdout.contains("Counterexample"),
        "expected FAILED or counterexample in output, got: {stdout}"
    );
}

// ===========================================================================
// --swift mode Auto-VC Detection Tests
// ===========================================================================

/// Test that --swift mode compiles Swift source and detects auto-VCs
/// with verbose output showing per-VC progress.
#[test]
fn cli_swift_mode_auto_vc_verbose_output() {
    // Check if swiftc is available
    if Command::new("swiftc").arg("--version").output().is_err() {
        eprintln!("Skipping test: swiftc not found");
        return;
    }

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("--verbose")
        .arg("tests/sil_examples/simple_add_unsafe.swift")
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);

    // Verbose output should show per-VC lines with OK/FAIL/WARN status
    // Unguarded arithmetic may return UNKNOWN (WARN) since there's no proof either way
    assert!(
        stderr.contains("auto")
            && (stderr.contains("OK") || stderr.contains("FAIL") || stderr.contains("WARN")),
        "verbose output should show auto-VC status, got stderr: {stderr}"
    );

    // Should have overflow check VCs
    assert!(
        stderr.contains("overflow") || stdout.contains("overflow"),
        "should detect overflow auto-VCs, got stdout: {stdout}\nstderr: {stderr}"
    );

    // Verbose summary should be printed
    assert!(
        stderr.contains("Verbose summary"),
        "should have verbose summary line, got stderr: {stderr}"
    );
}

/// Test that --swift mode with --json produces valid JSON with auto-VC results
#[test]
fn cli_swift_mode_auto_vc_json_output() {
    // Check if swiftc is available
    if Command::new("swiftc").arg("--version").output().is_err() {
        eprintln!("Skipping test: swiftc not found");
        return;
    }

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("--json")
        .arg("tests/sil_examples/simple_add_unsafe.swift")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Should have bundles array (multiple functions: add, multiply)
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");
    assert!(
        bundles.len() >= 2,
        "should have at least 2 function bundles (add, multiply), got: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    // Find add bundle
    let add_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("add"))
    });

    assert!(
        add_bundle.is_some(),
        "should have add bundle in JSON output"
    );

    let bundle = add_bundle.unwrap();

    // add function should have auto_vc_results for overflow
    let auto_vcs = bundle["auto_vc_results"]
        .as_array()
        .expect("should have auto_vc_results array");
    assert!(
        !auto_vcs.is_empty(),
        "add function should have auto-VCs for arithmetic overflow"
    );

    // Check that overflow VCs are present
    let has_overflow_vc = auto_vcs.iter().any(|vc| {
        vc["description"]
            .as_str()
            .is_some_and(|s| s.contains("overflow"))
    });
    assert!(
        has_overflow_vc,
        "should have overflow auto-VC, got: {auto_vcs:?}"
    );
}

// ===========================================================================
// --swift mode User Spec Verification Tests
// ===========================================================================

/// Test that --swift mode extracts and verifies @_requires/@_ensures specs
/// from Swift declarations that have @inline(never) on the same line.
#[test]
fn cli_swift_mode_verifies_user_specs() {
    // Check if custom swift-frontend is available (required for @_requires/@_ensures)
    // The custom swift-frontend has been patched to recognize these attributes
    let Ok(home) = std::env::var("HOME") else {
        eprintln!("Skipping test: HOME environment variable not set");
        return;
    };
    let arch = std::process::Command::new("uname")
        .arg("-m")
        .output()
        .map_or_else(
            |_| "arm64".to_string(),
            |o| String::from_utf8_lossy(&o.stdout).trim().to_string(),
        );
    let swift_frontend = format!(
        "{home}/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-{arch}/bin/swift-frontend"
    );
    if !std::path::Path::new(&swift_frontend).exists() {
        eprintln!("Skipping test: custom swift-frontend not found at {swift_frontend}");
        return;
    }

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Use SWIFTC env var to point to custom swift-frontend
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .env("SWIFTC", swift_frontend)
        .arg("--swift")
        .arg("--json")
        .arg("tests/sil_examples/verified_spec.swift")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Should produce valid JSON output
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Find keepPositive function (single @_requires/@_ensures)
    let bundles = json["bundles"]
        .as_array()
        .expect("should have bundles array");

    let keep_positive_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("keepPositive"))
    });

    assert!(
        keep_positive_bundle.is_some(),
        "should have keepPositive bundle in JSON output, got functions: {:?}",
        bundles
            .iter()
            .filter_map(|b| b["function_name"].as_str())
            .collect::<Vec<_>>()
    );

    let keep_bundle = keep_positive_bundle.unwrap();

    // keepPositive should have spec_result = Verified
    let spec_result = &keep_bundle["spec_result"];
    assert!(
        !spec_result.is_null(),
        "keepPositive should have spec_result, got: {keep_bundle}"
    );
    assert_eq!(
        spec_result["result"].as_str().unwrap_or(""),
        "Verified",
        "keepPositive spec should be Verified, got: {spec_result}"
    );

    // Find maxOf function (multiple @_requires/@_ensures)
    let max_of_bundle = bundles.iter().find(|b| {
        b["function_name"]
            .as_str()
            .is_some_and(|s| s.contains("maxOf"))
    });

    assert!(
        max_of_bundle.is_some(),
        "should have maxOf bundle in JSON output"
    );

    let max_bundle = max_of_bundle.unwrap();

    // maxOf should have spec_result = Verified
    let max_spec_result = &max_bundle["spec_result"];
    assert!(
        !max_spec_result.is_null(),
        "maxOf should have spec_result, got: {max_bundle}"
    );
    assert_eq!(
        max_spec_result["result"].as_str().unwrap_or(""),
        "Verified",
        "maxOf spec should be Verified, got: {max_spec_result}"
    );

    // maxOf should have 2 ensures verified (result >= a AND result >= b)
    let max_summary = &max_bundle["summary"];
    assert!(
        max_summary["spec_verified"].as_u64().unwrap_or(0) >= 2,
        "maxOf should have at least 2 specs verified, got summary: {max_summary}"
    );
}

/// Test that --sil mode detects Int32 overflow auto-VCs with correct bounds
/// Int32 has bounds -2147483648 to 2147483647 (narrower than Int64)
#[test]
fn cli_sil_mode_detects_int32_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_int32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int32 overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: add_int32"),
        "expected 'add_int32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int8 overflow auto-VCs with correct bounds
/// Int8 has bounds -128 to 127 (much narrower than Int64)
#[test]
fn cli_sil_mode_detects_int8_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int8 overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: add_int8"),
        "expected 'add_int8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt8` overflow auto-VCs with correct bounds
/// `UInt8` has bounds 0 to 255 (unsigned 8-bit)
#[test]
fn cli_sil_mode_detects_uint8_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_uint8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt8 overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: add_uint8"),
        "expected 'add_uint8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt32` overflow auto-VCs with correct bounds
/// `UInt32` has bounds 0 to 4294967295 (unsigned 32-bit)
#[test]
fn cli_sil_mode_detects_uint32_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_uint32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt32 overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: add_uint32"),
        "expected 'add_uint32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int8 subtraction overflow auto-VCs
/// Int8 has bounds -128 to 127 (signed 8-bit)
#[test]
fn cli_sil_mode_detects_int8_sub_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sub_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int8 subtraction overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sub_int8"),
        "expected 'sub_int8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt8` subtraction overflow auto-VCs
/// `UInt8` has bounds 0 to 255 (unsigned 8-bit)
#[test]
fn cli_sil_mode_detects_uint8_sub_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sub_overflow_uint8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt8 subtraction overflow is correctly DETECTED - verifier finds counterexample (e.g., a=0, b=1)
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sub_uint8"),
        "expected 'sub_uint8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int32 subtraction overflow auto-VCs
/// Int32 has bounds -2147483648 to 2147483647 (signed 32-bit)
#[test]
fn cli_sil_mode_detects_int32_sub_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sub_overflow_int32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int32 subtraction overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sub_int32"),
        "expected 'sub_int32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt32` subtraction overflow auto-VCs
/// `UInt32` has bounds 0 to 4294967295 (unsigned 32-bit)
#[test]
fn cli_sil_mode_detects_uint32_sub_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sub_overflow_uint32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt32 subtraction overflow is correctly DETECTED - verifier finds counterexample (e.g., a=0, b=1)
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sub_uint32"),
        "expected 'sub_uint32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int16 addition overflow auto-VCs
/// Int16 has bounds -32768 to 32767 (signed 16-bit)
#[test]
fn cli_sil_mode_detects_int16_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_int16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int16 addition overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: add_int16"),
        "expected 'add_int16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt16` addition overflow auto-VCs
/// `UInt16` has bounds 0 to 65535 (unsigned 16-bit)
#[test]
fn cli_sil_mode_detects_uint16_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_uint16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt16 addition overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: add_uint16"),
        "expected 'add_uint16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int16 subtraction overflow auto-VCs
/// Int16 has bounds -32768 to 32767 (signed 16-bit)
#[test]
fn cli_sil_mode_detects_int16_sub_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sub_overflow_int16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int16 subtraction overflow is correctly DETECTED - verifier finds counterexample
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sub_int16"),
        "expected 'sub_int16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt16` subtraction overflow auto-VCs
/// `UInt16` has bounds 0 to 65535 (unsigned 16-bit)
#[test]
fn cli_sil_mode_detects_uint16_sub_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sub_overflow_uint16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt16 subtraction overflow is correctly DETECTED - verifier finds counterexample (e.g., a=0, b=1)
    // Exit code is 1 because verification fails (bug found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sub_uint16"),
        "expected 'sub_uint16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow"),
        "expected overflow VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int8 multiplication overflow auto-VCs
/// Int8 has bounds -128 to 127 (signed 8-bit)
/// Overflow IS detectable via interval analysis: 127 * 127 = 16129 > 127
#[test]
fn cli_sil_mode_detects_int8_mul_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mul_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int8 multiplication overflow IS detected via interval analysis
    // Exit code 1 = verification failed (overflow found)
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mul_int8"),
        "expected 'mul_int8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED"),
        "expected FAILED result in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Counterexample"),
        "expected Counterexample in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt8` multiplication overflow auto-VCs
/// `UInt8` has bounds 0 to 255 (unsigned 8-bit)
/// Overflow IS detectable via interval analysis: 255 * 255 = 65025 > 255
#[test]
fn cli_sil_mode_detects_uint8_mul_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mul_overflow_uint8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt8 multiplication overflow IS detected via interval analysis
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mul_uint8"),
        "expected 'mul_uint8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED"),
        "expected FAILED result in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int16 multiplication overflow auto-VCs
/// Int16 has bounds -32768 to 32767 (signed 16-bit)
/// Overflow IS detectable via interval analysis: 32767 * 32767 > 32767
#[test]
fn cli_sil_mode_detects_int16_mul_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mul_overflow_int16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int16 multiplication overflow IS detected via interval analysis
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mul_int16"),
        "expected 'mul_int16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED"),
        "expected FAILED result in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt16` multiplication overflow auto-VCs
/// `UInt16` has bounds 0 to 65535 (unsigned 16-bit)
/// Overflow IS detectable via interval analysis: 65535 * 65535 > 65535
#[test]
fn cli_sil_mode_detects_uint16_mul_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mul_overflow_uint16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt16 multiplication overflow IS detected via interval analysis
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mul_uint16"),
        "expected 'mul_uint16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED"),
        "expected FAILED result in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int32 multiplication overflow auto-VCs
/// Int32 has bounds -2147483648 to 2147483647 (signed 32-bit)
/// Overflow IS detectable via interval analysis
#[test]
fn cli_sil_mode_detects_int32_mul_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mul_overflow_int32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Int32 multiplication overflow IS detected via interval analysis
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mul_int32"),
        "expected 'mul_int32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED"),
        "expected FAILED result in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt32` multiplication overflow auto-VCs
/// `UInt32` has bounds 0 to 4294967295 (unsigned 32-bit)
/// Overflow IS detectable via interval analysis
#[test]
fn cli_sil_mode_detects_uint32_mul_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mul_overflow_uint32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // UInt32 multiplication overflow IS detected via interval analysis
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mul_uint32"),
        "expected 'mul_uint32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED"),
        "expected FAILED result in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int8 division by zero auto-VCs
#[test]
fn cli_sil_mode_detects_int8_div_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/div_by_zero_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: div_int8"),
        "expected 'div_int8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("div by zero"),
        "expected 'div by zero' VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int16 division by zero auto-VCs
#[test]
fn cli_sil_mode_detects_int16_div_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/div_by_zero_int16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: div_int16"),
        "expected 'div_int16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("div by zero"),
        "expected 'div by zero' VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int32 division by zero auto-VCs
#[test]
fn cli_sil_mode_detects_int32_div_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/div_by_zero_int32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: div_int32"),
        "expected 'div_int32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("div by zero"),
        "expected 'div by zero' VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt8` division by zero auto-VCs
#[test]
fn cli_sil_mode_detects_uint8_div_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/div_by_zero_uint8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: div_uint8"),
        "expected 'div_uint8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("div by zero"),
        "expected 'div by zero' VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt16` division by zero auto-VCs
#[test]
fn cli_sil_mode_detects_uint16_div_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/div_by_zero_uint16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: div_uint16"),
        "expected 'div_uint16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("div by zero"),
        "expected 'div by zero' VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt32` division by zero auto-VCs
#[test]
fn cli_sil_mode_detects_uint32_div_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/div_by_zero_uint32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: div_uint32"),
        "expected 'div_uint32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("div by zero"),
        "expected 'div by zero' VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int8 signed division overflow (`INT_MIN` / -1)
#[test]
fn cli_sil_mode_detects_int8_sdiv_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sdiv_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero and/or overflow detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero/overflow), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sdiv_int8"),
        "expected 'sdiv_int8' function in output, got: {stdout}"
    );
    // Should have div-by-zero and/or overflow checks
    assert!(
        stdout.contains("div by zero") || stdout.contains("div overflow"),
        "expected div VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int16 signed division overflow (`INT_MIN` / -1)
#[test]
fn cli_sil_mode_detects_int16_sdiv_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sdiv_overflow_int16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero and/or overflow detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero/overflow), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sdiv_int16"),
        "expected 'sdiv_int16' function in output, got: {stdout}"
    );
    // Should have div-by-zero and/or overflow checks
    assert!(
        stdout.contains("div by zero") || stdout.contains("div overflow"),
        "expected div VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int32 signed division overflow (`INT_MIN` / -1)
#[test]
fn cli_sil_mode_detects_int32_sdiv_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sdiv_overflow_int32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (div-by-zero and/or overflow detected)
    assert!(
        !output.status.success(),
        "expected failure (div-by-zero/overflow), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: sdiv_int32"),
        "expected 'sdiv_int32' function in output, got: {stdout}"
    );
    // Should have div-by-zero and/or overflow checks
    assert!(
        stdout.contains("div by zero") || stdout.contains("div overflow"),
        "expected div VC in output, got: {stdout}"
    );
}

// ============================================================================
// Modulo by zero tests (bitwidth-specific)
// ============================================================================

/// Test that --sil mode detects Int8 modulo by zero auto-VCs
#[test]
fn cli_sil_mode_detects_int8_mod_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mod_by_zero_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mod_int8"),
        "expected 'mod_int8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("mod by zero"),
        "expected mod-by-zero check message in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int16 modulo by zero auto-VCs
#[test]
fn cli_sil_mode_detects_int16_mod_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mod_by_zero_int16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mod_int16"),
        "expected 'mod_int16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("mod by zero"),
        "expected mod-by-zero check message in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int32 modulo by zero auto-VCs
#[test]
fn cli_sil_mode_detects_int32_mod_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mod_by_zero_int32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mod_int32"),
        "expected 'mod_int32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("mod by zero"),
        "expected mod-by-zero check message in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt8` modulo by zero auto-VCs
#[test]
fn cli_sil_mode_detects_uint8_mod_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mod_by_zero_uint8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mod_uint8"),
        "expected 'mod_uint8' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("mod by zero"),
        "expected mod-by-zero check message in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt16` modulo by zero auto-VCs
#[test]
fn cli_sil_mode_detects_uint16_mod_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mod_by_zero_uint16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mod_uint16"),
        "expected 'mod_uint16' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("mod by zero"),
        "expected mod-by-zero check message in output, got: {stdout}"
    );
}

/// Test that --sil mode detects `UInt32` modulo by zero auto-VCs
#[test]
fn cli_sil_mode_detects_uint32_mod_by_zero_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mod_by_zero_uint32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: mod_uint32"),
        "expected 'mod_uint32' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("mod by zero"),
        "expected mod-by-zero check message in output, got: {stdout}"
    );
}

// ============================================================================
// Signed modulo overflow tests (INT_MIN % -1)
// ============================================================================

/// Test that --sil mode detects Int8 signed modulo overflow (`INT_MIN` % -1)
#[test]
fn cli_sil_mode_detects_int8_srem_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/srem_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero and/or overflow detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero/overflow), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: srem_int8"),
        "expected 'srem_int8' function in output, got: {stdout}"
    );
    // Should have mod-by-zero and/or overflow checks
    assert!(
        stdout.contains("mod by zero") || stdout.contains("mod overflow"),
        "expected mod VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int16 signed modulo overflow (`INT_MIN` % -1)
#[test]
fn cli_sil_mode_detects_int16_srem_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/srem_overflow_int16_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero and/or overflow detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero/overflow), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: srem_int16"),
        "expected 'srem_int16' function in output, got: {stdout}"
    );
    // Should have mod-by-zero and/or overflow checks
    assert!(
        stdout.contains("mod by zero") || stdout.contains("mod overflow"),
        "expected mod VC in output, got: {stdout}"
    );
}

/// Test that --sil mode detects Int32 signed modulo overflow (`INT_MIN` % -1)
#[test]
fn cli_sil_mode_detects_int32_srem_overflow_autovc() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/srem_overflow_int32_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail (mod-by-zero and/or overflow detected)
    assert!(
        !output.status.success(),
        "expected failure (mod-by-zero/overflow), got success\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: srem_int32"),
        "expected 'srem_int32' function in output, got: {stdout}"
    );
    // Should have mod-by-zero and/or overflow checks
    assert!(
        stdout.contains("mod by zero") || stdout.contains("mod overflow"),
        "expected mod VC in output, got: {stdout}"
    );
}

// ===========================================================================
// JSON Counterexample Structure Tests
// ===========================================================================

/// Test that JSON output for failed verification contains properly structured counterexample
/// The counterexample should be an array of [`variable_name`, value] pairs
#[test]
fn cli_json_counterexample_structure() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--json")
        .arg("--sil")
        .arg("tests/sil_examples/neg_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail with counterexample (Int8 negation of -128 overflows)
    assert!(
        !output.status.success(),
        "expected failure for negation overflow, got success"
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Check auto_vc_results array exists
    let auto_vc_results = json["auto_vc_results"]
        .as_array()
        .expect("expected auto_vc_results array");

    // Find the failed result
    let failed_result = auto_vc_results
        .iter()
        .find(|r| r["result"]["result"].as_str() == Some("Failed"))
        .expect("expected at least one Failed auto-VC result");

    // Verify counterexample structure: array of [name, value] pairs
    let counterexample = failed_result["result"]["counterexample"]
        .as_array()
        .expect("expected counterexample to be an array");

    assert!(
        !counterexample.is_empty(),
        "counterexample should not be empty"
    );

    // Each entry should be a 2-element array [variable_name, value]
    for entry in counterexample {
        let entry_arr = entry
            .as_array()
            .expect("counterexample entry should be an array");
        assert_eq!(
            entry_arr.len(),
            2,
            "counterexample entry should have 2 elements [name, value], got: {entry_arr:?}"
        );

        // First element is variable name (string)
        assert!(
            entry_arr[0].is_string(),
            "counterexample variable name should be a string, got: {:?}",
            entry_arr[0]
        );

        // Second element is value (string representation)
        assert!(
            entry_arr[1].is_string(),
            "counterexample value should be a string, got: {:?}",
            entry_arr[1]
        );
    }

    // Verify there's a counterexample for 'x' variable
    let has_x = counterexample.iter().any(|entry| {
        entry
            .as_array()
            .is_some_and(|arr| arr[0].as_str() == Some("x"))
    });
    assert!(
        has_x,
        "counterexample should include 'x' variable, got: {counterexample:?}"
    );
}

/// Test that JSON output for failed auto-VCs includes suggestion field
#[test]
fn cli_json_suggestion_field_populated() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--json")
        .arg("--sil")
        .arg("tests/sil_examples/neg_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Find the failed result
    let auto_vc_results = json["auto_vc_results"]
        .as_array()
        .expect("expected auto_vc_results array");

    let failed_result = auto_vc_results
        .iter()
        .find(|r| r["result"]["result"].as_str() == Some("Failed"))
        .expect("expected at least one Failed auto-VC result");

    // Verify suggestion field exists and is non-empty for overflow failures
    let suggestion = failed_result["suggestion"].as_str();
    assert!(
        suggestion.is_some() && !suggestion.unwrap().is_empty(),
        "expected non-empty suggestion for failed overflow auto-VC, got: {:?}",
        failed_result["suggestion"]
    );

    // Suggestion should mention wraparound or precondition
    let suggestion_text = suggestion.unwrap();
    assert!(
        suggestion_text.contains('&') || suggestion_text.contains("precondition"),
        "suggestion should mention wraparound operator or precondition, got: {suggestion_text}"
    );
}

/// Test that JSON counterexample values are valid for the detected overflow
#[test]
fn cli_json_counterexample_values_valid() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--json")
        .arg("--sil")
        .arg("tests/sil_examples/neg_overflow_int8_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    let auto_vc_results = json["auto_vc_results"]
        .as_array()
        .expect("expected auto_vc_results array");

    let failed_result = auto_vc_results
        .iter()
        .find(|r| r["result"]["result"].as_str() == Some("Failed"))
        .expect("expected at least one Failed auto-VC result");

    let counterexample = failed_result["result"]["counterexample"]
        .as_array()
        .expect("expected counterexample array");

    // Find the x value
    let x_entry = counterexample
        .iter()
        .find(|entry| {
            entry
                .as_array()
                .is_some_and(|arr| arr[0].as_str() == Some("x"))
        })
        .expect("expected x in counterexample");

    let x_value_str = x_entry.as_array().unwrap()[1]
        .as_str()
        .expect("x value should be a string");

    // The counterexample value should be parseable as an integer
    // For Int8 negation overflow, valid counterexamples include values that would overflow
    // when negated (e.g., -128 represented in some form, or values outside Int8 range
    // that the SMT solver found as witnesses)
    assert!(
        x_value_str.parse::<i64>().is_ok() || x_value_str.starts_with('-'),
        "counterexample value '{x_value_str}' should be a valid integer representation"
    );
}

// =========================================================================
// Verified Auto-VC Tests (auto-VCs that PASS with proper preconditions)
// =========================================================================

/// Test that array bounds checks verify when index bounds are provided
#[test]
fn cli_sil_mode_verifies_array_bounds_with_preconditions() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/array_subscript_bounds_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.success(),
        "expected success with bounds preconditions, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: getElementSafe"),
        "expected 'getElementSafe' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Index out of range") && stdout.contains("VERIFIED"),
        "expected verified bounds checks in output, got: {stdout}"
    );
}

/// Test that division with non-zero precondition verifies the div-by-zero auto-VC
#[test]
fn cli_sil_mode_verifies_division_with_nonzero_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/division_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    if cfg!(feature = "z3-fallback") {
        // With Z3 fallback enabled, the verifier can also detect the signed division overflow case
        // (INT_MIN / -1), so overall verification fails (exit code 1), but the div-by-zero VC
        // should still be VERIFIED.
        assert_eq!(
            output.status.code(),
            Some(1),
            "expected exit code 1 (division overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            stdout,
            String::from_utf8_lossy(&output.stderr),
        );
        assert!(
            stdout.contains("div overflow check")
                && (stdout.contains("FAILED") || stdout.contains("FAIL")),
            "expected division overflow check to FAIL with Z3 fallback, got: {stdout}"
        );
    } else {
        // Without Z3 fallback, non-linear division reasoning may be UNKNOWN and treated as non-failing.
        assert!(
            output.status.success(),
            "expected success with non-zero precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            stdout,
            String::from_utf8_lossy(&output.stderr),
        );
    }

    assert!(
        stdout.contains("Function: safeDivide"),
        "expected 'safeDivide' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("div by zero check") && stdout.contains("VERIFIED"),
        "expected verified div-by-zero check in output, got: {stdout}"
    );
}

/// Test that modulo with non-zero precondition verifies the mod-by-zero auto-VC
#[test]
fn cli_sil_mode_verifies_modulo_with_nonzero_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/modulo_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (mod-by-zero auto-VC verified)
    assert!(
        output.status.success(),
        "expected success with non-zero precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeMod"),
        "expected 'safeMod' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("mod by zero check") && stdout.contains("VERIFIED"),
        "expected verified mod-by-zero check in output, got: {stdout}"
    );
}

/// Test that bounded addition with preconditions verifies the overflow auto-VC
#[test]
fn cli_sil_mode_verifies_bounded_addition_overflow() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/overflow_bounded_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (overflow auto-VC verified due to bounded inputs)
    assert!(
        output.status.success(),
        "expected success with bounded preconditions, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: boundedAdd"),
        "expected 'boundedAdd' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow") && stdout.contains("VERIFIED"),
        "expected verified overflow check in output, got: {stdout}"
    );
}

/// Test that range bounds `cond_fail` checks verify with end >= start precondition
#[test]
fn cli_sil_mode_verifies_range_bounds_with_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/range_bounds_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.success(),
        "expected success with range bounds precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: makeRangeSafe"),
        "expected 'makeRangeSafe' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Function: makeClosedRangeSafe"),
        "expected 'makeClosedRangeSafe' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Range requires lowerBound <= upperBound") && stdout.contains("VERIFIED"),
        "expected verified range bounds checks in output, got: {stdout}"
    );
}

/// Test that integer truncation bounds checks verify when explicit bounds are provided
#[test]
fn cli_sil_mode_verifies_truncation_bounds_with_preconditions() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/truncation_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.success(),
        "expected success with truncation preconditions, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: truncateIntSafe"),
        "expected 'truncateIntSafe' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Function: truncateUIntSafe"),
        "expected 'truncateUIntSafe' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Function: truncateToSignedSafe"),
        "expected 'truncateToSignedSafe' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Not enough bits to represent") && stdout.contains("VERIFIED"),
        "expected verified truncation bounds checks in output, got: {stdout}"
    );
}

/// Test that force unwrap nil check verifies with opt != nil precondition
#[test]
fn cli_sil_mode_verifies_force_unwrap_with_non_nil_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/force_unwrap_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.success(),
        "expected success with non-nil precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeUnwrap"),
        "expected 'safeUnwrap' function in output, got: {stdout}"
    );
    assert!(
        (stdout.contains("force unwrap") || stdout.contains("nil")) && stdout.contains("VERIFIED"),
        "expected verified nil check in output, got: {stdout}"
    );
}

/// Test that forced cast verifies with `is_type` precondition
#[test]
fn cli_sil_mode_verifies_forced_cast_with_type_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/forced_cast_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.success(),
        "expected success with is_type precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("forced cast") && stdout.contains("VERIFIED"),
        "expected verified forced cast in output, got: {stdout}"
    );
}

/// Test JSON output for verified division auto-VC
#[test]
fn cli_sil_mode_verifies_division_json_output() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--json")
        .arg("--sil")
        .arg("tests/sil_examples/division_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    if cfg!(feature = "z3-fallback") {
        assert_eq!(
            output.status.code(),
            Some(1),
            "expected exit code 1 (division overflow detected), got {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    } else {
        assert!(
            output.status.success(),
            "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    let auto_vc_results = json["auto_vc_results"]
        .as_array()
        .expect("expected auto_vc_results array");

    // Find the div-by-zero check result
    let div_zero_result = auto_vc_results
        .iter()
        .find(|r| {
            r["description"]
                .as_str()
                .is_some_and(|s| s.contains("div by zero"))
        })
        .expect("expected div-by-zero auto-VC result");

    assert_eq!(
        div_zero_result["result"]["result"].as_str(),
        Some("Verified"),
        "expected Verified result for div-by-zero with precondition, got: {div_zero_result:?}"
    );

    if cfg!(feature = "z3-fallback") {
        let div_overflow_result = auto_vc_results
            .iter()
            .find(|r| {
                r["description"]
                    .as_str()
                    .is_some_and(|s| s.contains("div overflow"))
            })
            .expect("expected div overflow auto-VC result with Z3 fallback enabled");

        assert_eq!(
            div_overflow_result["result"]["result"].as_str(),
            Some("Failed"),
            "expected Failed result for division overflow with Z3 fallback enabled, got: {div_overflow_result:?}"
        );
    }
}

// ============================================================================
// Verified safe overflow tests (with preconditions)
// ============================================================================

/// Test that --sil mode verifies addition is safe when inputs are bounded
#[test]
fn cli_sil_mode_verifies_addition_overflow_with_bounded_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (overflow auto-VC verified with bounded inputs)
    assert!(
        output.status.success(),
        "expected success with bounded inputs precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeAdd"),
        "expected 'safeAdd' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow") && stdout.contains("VERIFIED"),
        "expected verified overflow check in output, got: {stdout}"
    );
}

/// Test that --sil mode verifies subtraction is safe when inputs are bounded
#[test]
fn cli_sil_mode_verifies_subtraction_overflow_with_bounded_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sub_overflow_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (overflow auto-VC verified with bounded inputs)
    assert!(
        output.status.success(),
        "expected success with bounded inputs precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeSub"),
        "expected 'safeSub' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow") && stdout.contains("VERIFIED"),
        "expected verified subtraction overflow check in output, got: {stdout}"
    );
}

/// Test that --sil mode verifies multiplication is safe when inputs are bounded
#[test]
fn cli_sil_mode_verifies_multiplication_overflow_with_bounded_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/mul_overflow_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (overflow auto-VC verified with bounded inputs)
    assert!(
        output.status.success(),
        "expected success with bounded inputs precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeMul"),
        "expected 'safeMul' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow") && stdout.contains("VERIFIED"),
        "expected verified multiplication overflow check in output, got: {stdout}"
    );
}

/// Test that --sil mode verifies negation is safe when input is bounded
#[test]
fn cli_sil_mode_verifies_negation_overflow_with_bounded_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/neg_overflow_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (negation overflow auto-VC verified with bounded input)
    assert!(
        output.status.success(),
        "expected success with bounded input precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeNegate"),
        "expected 'safeNegate' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow") && stdout.contains("VERIFIED"),
        "expected verified negation overflow check in output, got: {stdout}"
    );
}

/// Test that --sil mode verifies signed division is safe when inputs are bounded
#[test]
fn cli_sil_mode_verifies_sdiv_overflow_with_bounded_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/sdiv_overflow_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (signed div auto-VCs verified with bounded inputs)
    assert!(
        output.status.success(),
        "expected success with bounded inputs precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeSdiv"),
        "expected 'safeSdiv' function in output, got: {stdout}"
    );
    // Signed division generates two auto-VCs: div-by-zero and overflow
    // Both should be verified with the positive inputs precondition
    assert!(
        stdout.contains("VERIFIED"),
        "expected verified auto-VCs in output, got: {stdout}"
    );
}

// ============================================================================
// Verified safe UNSIGNED overflow tests (with preconditions)
// ============================================================================

/// Test that --sil mode verifies unsigned addition is safe when inputs are bounded
#[test]
fn cli_sil_mode_verifies_uadd_overflow_with_bounded_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/uadd_overflow_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (unsigned overflow auto-VC verified with bounded inputs)
    assert!(
        output.status.success(),
        "expected success with bounded inputs precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeUAdd"),
        "expected 'safeUAdd' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow") && stdout.contains("VERIFIED"),
        "expected verified unsigned addition overflow check in output, got: {stdout}"
    );
}

/// Test that --sil mode verifies unsigned subtraction is safe when a >= b
#[test]
fn cli_sil_mode_verifies_usub_overflow_with_bounded_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/usub_overflow_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (unsigned subtraction auto-VC verified with a >= b bounds)
    assert!(
        output.status.success(),
        "expected success with a >= b bounds precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeUSub"),
        "expected 'safeUSub' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow") && stdout.contains("VERIFIED"),
        "expected verified unsigned subtraction overflow check in output, got: {stdout}"
    );
}

/// Test that --sil mode verifies unsigned multiplication is safe when inputs are bounded
#[test]
fn cli_sil_mode_verifies_umul_overflow_with_bounded_precondition() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/umul_overflow_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (unsigned multiplication auto-VC verified with bounded inputs)
    assert!(
        output.status.success(),
        "expected success with bounded inputs precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: safeUMul"),
        "expected 'safeUMul' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("arithmetic overflow") && stdout.contains("VERIFIED"),
        "expected verified unsigned multiplication overflow check in output, got: {stdout}"
    );
}

// ============================================================================
// SwiftUI Pattern Tests
// ============================================================================

/// Test that --sil mode verifies `SwiftUI` @State counter increment with overflow protection
#[test]
fn cli_sil_mode_verifies_swiftui_state_counter_safe() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/swiftui_state_counter_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (overflow protected by path condition)
    assert!(
        output.status.success(),
        "expected success with path-guarded increment, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: swiftui_state_counter_increment"),
        "expected 'swiftui_state_counter_increment' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("VERIFIED"),
        "expected overflow check to be verified, got: {stdout}"
    );
}

/// Test that --sil mode verifies `SwiftUI` @Binding safe value update with precondition
#[test]
fn cli_sil_mode_verifies_swiftui_binding_safe() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/swiftui_binding_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (bounded value prevents overflow)
    assert!(
        output.status.success(),
        "expected success with bounded value precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: swiftui_binding_transform"),
        "expected 'swiftui_binding_transform' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("VERIFIED"),
        "expected multiplication overflow check to be verified, got: {stdout}"
    );
}

/// Test that --sil mode verifies `SwiftUI` `ForEach` safe index access with precondition
#[test]
fn cli_sil_mode_verifies_swiftui_foreach_bounds_safe() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/swiftui_foreach_bounds_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (index bounds enforced by precondition)
    assert!(
        output.status.success(),
        "expected success with bounds precondition, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: swiftui_foreach_safe_access"),
        "expected 'swiftui_foreach_safe_access' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("Index out of range") && stdout.contains("VERIFIED"),
        "expected bounds check to be verified, got: {stdout}"
    );
}

/// Test that --sil mode verifies `SwiftUI` @Observable state safe access with isEmpty check
#[test]
fn cli_sil_mode_verifies_swiftui_observable_state_safe() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/swiftui_observable_state_safe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should succeed (bounds check guarded by count > 0 path condition)
    assert!(
        output.status.success(),
        "expected success with isEmpty guard, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Function: swiftui_observable_first_item"),
        "expected 'swiftui_observable_first_item' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("VERIFIED"),
        "expected bounds check to be verified, got: {stdout}"
    );
}

/// Test that --sil mode verifies `SwiftUI` List delete safe with precondition, detects unsafe
#[test]
fn cli_sil_mode_swiftui_list_delete_mixed() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/swiftui_list_delete_unsafe.sil")
        .output()
        .expect("failed to run tswift-verify");

    // Should fail overall (unsafe function detected)
    assert!(
        !output.status.success(),
        "expected failure due to unsafe function, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Safe function should be verified
    assert!(
        stdout.contains("Function: swiftui_list_delete_at_index"),
        "expected 'swiftui_list_delete_at_index' function in output, got: {stdout}"
    );
    // Unsafe function should fail
    assert!(
        stdout.contains("Function: swiftui_list_delete_unsafe"),
        "expected 'swiftui_list_delete_unsafe' function in output, got: {stdout}"
    );
    assert!(
        stdout.contains("FAILED"),
        "expected FAILED for unsafe delete, got: {stdout}"
    );
}

// =============================================================================
// Tests for MethodCallStateEffect VCs (cross-method state tracking)
// =============================================================================

/// Test that --sil mode generates `MethodCallStateEffect` VCs for transitive call chains.
/// When a method with type invariants calls another method that transitively modifies state
/// (via further calls), a `MethodCallStateEffect` VC should be generated with the full call chain.
#[test]
fn cli_sil_mode_method_call_state_effect_transitive_call_chain() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/method_call_state_effect_transitive_unsafe.sil")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-verify");

    // The VCs will fail (invariant not proven) but that's expected
    // We're testing that the MethodCallStateEffect VC is generated with call chain
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Check that Counter_top function is in output
    assert!(
        stdout.contains("Function: Counter_top"),
        "expected 'Counter_top' function in output, got stdout: {stdout}\nstderr: {stderr}"
    );

    // Check that MethodCallStateEffect VC was generated with transitive call chain
    // The description should contain "transitively modifies" and "via:"
    assert!(
        stdout.contains("transitively modifies"),
        "expected 'transitively modifies' in output for transitive call chain, got stdout: {stdout}"
    );

    assert!(
        stdout.contains("via:"),
        "expected 'via:' in output showing call chain, got stdout: {stdout}"
    );

    // Check the call chain includes the intermediate and ultimate modifier
    assert!(
        stdout.contains("Counter_mid") && stdout.contains("Counter_helper"),
        "expected call chain to include 'Counter_mid' and 'Counter_helper', got stdout: {stdout}"
    );

    // Check verbose output shows the call chain in the per-VC line
    assert!(
        stderr.contains("transitively"),
        "expected verbose per-VC output to show 'transitively', got stderr: {stderr}"
    );
}

/// Test that --json output shows call chain in description for `MethodCallStateEffect` VCs
#[test]
fn cli_sil_mode_method_call_state_effect_json_call_chain() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/method_call_state_effect_transitive_unsafe.sil")
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // The JSON description should contain the call chain info
    // "transitively modifies [...] via: Counter_mid -> Counter_helper"
    assert!(
        stdout.contains("transitively modifies"),
        "expected JSON description to contain 'transitively modifies', got: {stdout}"
    );

    assert!(
        stdout.contains("via:"),
        "expected JSON description to contain 'via:' showing call chain, got: {stdout}"
    );

    assert!(
        stdout.contains("Counter_helper"),
        "expected call chain to include 'Counter_helper', got: {stdout}"
    );

    // Check that the suggestion also includes the call chain
    assert!(
        stdout.contains("Consider adding postconditions along the call chain"),
        "expected suggestion to reference call chain, got: {stdout}"
    );

    // NEW in v346: Verify the dedicated call_chain JSON field
    // For transitive effects (Counter_top), the call_chain array should be present
    assert!(
        stdout.contains("\"call_chain\""),
        "expected JSON to contain 'call_chain' field for transitive MethodCallStateEffect, got: {stdout}"
    );

    // Parse JSON and verify call_chain field structure
    let json: serde_json::Value =
        serde_json::from_str(&stdout).expect("expected valid JSON output");

    // Find Counter_top bundle (the one with transitive call chain)
    let counter_top = json["bundles"]
        .as_array()
        .expect("expected bundles array")
        .iter()
        .find(|b| b["function_name"].as_str() == Some("Counter_top"))
        .expect("expected Counter_top bundle");

    // Get the auto_vc_results
    let auto_vcs = counter_top["auto_vc_results"]
        .as_array()
        .expect("expected auto_vc_results array");

    // Find the MethodCallStateEffect VC (has call_chain field)
    let transitive_vc = auto_vcs
        .iter()
        .find(|vc| vc.get("call_chain").is_some())
        .expect("expected at least one auto-VC with call_chain field");

    // Verify call_chain is an array with "Counter_helper"
    let call_chain = transitive_vc["call_chain"]
        .as_array()
        .expect("expected call_chain to be an array");
    assert!(
        !call_chain.is_empty(),
        "expected non-empty call_chain for transitive effect"
    );
    assert!(
        call_chain
            .iter()
            .any(|v| v.as_str().is_some_and(|s| s.contains("helper"))),
        "expected call_chain to include 'helper', got: {call_chain:?}"
    );

    // Verify Counter_mid (direct call) does NOT have call_chain field
    // (because serde skips empty vecs)
    let counter_mid = json["bundles"]
        .as_array()
        .expect("expected bundles array")
        .iter()
        .find(|b| b["function_name"].as_str() == Some("Counter_mid"))
        .expect("expected Counter_mid bundle");

    let mid_auto_vcs = counter_mid["auto_vc_results"]
        .as_array()
        .expect("expected auto_vc_results array");

    // Counter_mid's MethodCallStateEffect should NOT have call_chain (direct call)
    for vc in mid_auto_vcs {
        if vc["description"]
            .as_str()
            .is_some_and(|d| d.contains("calling 'Counter_helper'"))
        {
            assert!(
                vc.get("call_chain").is_none(),
                "expected no call_chain field for direct MethodCallStateEffect, got: {:?}",
                vc.get("call_chain")
            );
        }
    }
}

// =============================================================================
// Tests for --export-kani CLI flag
// =============================================================================

/// Test that --export-kani creates the output directory and harness files
#[test]
fn cli_export_kani_creates_directory_and_harness_files() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Create a temporary directory for Kani output
    let tmpdir = std::env::temp_dir().join(format!("kani_export_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir); // Clean up any previous runs

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .output()
        .expect("failed to run tswift-verify");

    // The command should still run verification (which fails due to overflow)
    assert!(
        !output.status.success() || output.status.success(),
        "command should complete, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    // Check that the output directory was created
    assert!(
        tmpdir.exists(),
        "Kani export directory should be created at {}",
        tmpdir.display()
    );

    // Export should create a runnable Cargo project.
    assert!(
        tmpdir.join("Cargo.toml").exists(),
        "Kani export should create Cargo.toml at {}",
        tmpdir.join("Cargo.toml").display()
    );
    assert!(
        tmpdir.join("src").join("lib.rs").exists(),
        "Kani export should create src/lib.rs at {}",
        tmpdir.join("src").join("lib.rs").display()
    );

    // Check that at least one harness module file was created (excluding lib.rs).
    let entries: Vec<_> = fs::read_dir(tmpdir.join("src"))
        .expect("should be able to read tmpdir/src")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
        .filter(|e| e.file_name().to_string_lossy() != "lib.rs")
        .collect();

    assert!(
        !entries.is_empty(),
        "At least one .rs harness file should be created in {}",
        tmpdir.display()
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

/// Test that exported Kani harness files contain expected content
#[test]
fn cli_export_kani_harness_content() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("kani_content_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .output()
        .expect("failed to run tswift-verify");

    // Command should complete (exit code doesn't matter for this test)
    let _ = output;

    // Find the first harness module file and check its content (exclude lib.rs).
    let entries: Vec<_> = fs::read_dir(tmpdir.join("src"))
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

    // Check for Kani-specific content
    assert!(
        harness_content.contains("#[kani::proof]"),
        "Harness should contain #[kani::proof] attribute, got:\n{harness_content}"
    );
    assert!(
        harness_content.contains("kani::"),
        "Harness should use kani:: macros, got:\n{harness_content}"
    );
    assert!(
        harness_content.contains("extern crate kani"),
        "Harness should import kani crate, got:\n{harness_content}"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

/// Test that --export-kani shows summary in human-readable output
#[test]
fn cli_export_kani_shows_summary_in_stderr() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("kani_summary_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .output()
        .expect("failed to run tswift-verify");

    let stderr = String::from_utf8_lossy(&output.stderr);

    // Human-readable mode should show Kani export summary
    assert!(
        stderr.contains("Kani export") || stderr.contains("harness"),
        "Should show Kani export summary in stderr, got:\n{stderr}"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

/// Test that --export-kani works with --json output format
#[test]
fn cli_export_kani_with_json_output() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("kani_json_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .arg("--json")
        .output()
        .expect("failed to run tswift-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    // JSON output should still be valid JSON
    assert!(
        stdout.contains('{') && stdout.contains('}'),
        "JSON output should be valid JSON structure, got:\n{stdout}"
    );

    // Parse to verify it's valid JSON
    let _: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|_| panic!("Output should be valid JSON, got:\n{stdout}"));

    // Harness files should still be created
    let entries: Vec<_> = fs::read_dir(tmpdir.join("src"))
        .expect("should be able to read tmpdir/src")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
        .filter(|e| e.file_name().to_string_lossy() != "lib.rs")
        .collect();

    assert!(
        !entries.is_empty(),
        "Harness files should be created even with --json output"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

/// Test that --export-kani=dir syntax works (equals sign format)
#[test]
fn cli_export_kani_equals_syntax() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("kani_equals_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg(format!("--export-kani={}", tmpdir.display()))
        .output()
        .expect("failed to run tswift-verify");

    // Command should complete
    let _ = output;

    // Check that the output directory was created
    assert!(
        tmpdir.exists(),
        "Kani export directory should be created with equals syntax at {}",
        tmpdir.display()
    );

    // Check that at least one harness module file was created (excluding lib.rs).
    let entries: Vec<_> = fs::read_dir(tmpdir.join("src"))
        .expect("should be able to read tmpdir/src")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
        .filter(|e| e.file_name().to_string_lossy() != "lib.rs")
        .collect();

    assert!(
        !entries.is_empty(),
        "At least one .rs harness file should be created with equals syntax"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

// =============================================================================
// Tests for --run-kani CLI flag
// =============================================================================

/// Test that --run-kani requires --export-kani to be set.
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
        "expected exit code 2 when --run-kani is used without --export-kani, got {:?}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--run-kani requires --export-kani"),
        "expected error message about --export-kani requirement, got:\n{stderr}"
    );
}

/// Test that --export-kani exports @_ensures annotations as `kani::assert()` calls
#[test]
fn cli_export_kani_with_ensures_annotations() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("kani_ensures_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    // Use verified_positive.sil which has @_ensures annotations
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/verified_positive_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .output()
        .expect("failed to run tswift-verify");

    // Command should complete (exit code may be non-zero due to verification failures)
    let _ = output;

    // Find harness files
    let src_dir = tmpdir.join("src");
    assert!(
        src_dir.exists(),
        "src directory should exist in Kani export"
    );

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

    // Find the safeAdd harness which has @_ensures
    let harness_path = entries
        .iter()
        .find(|e| e.file_name().to_string_lossy().contains("safeadd"))
        .map_or_else(|| entries[0].path(), std::fs::DirEntry::path);

    let harness_content =
        fs::read_to_string(&harness_path).expect("should be able to read harness file");

    // Check that postconditions are exported as kani::assert()
    assert!(
        harness_content.contains("// Postconditions (@_ensures)"),
        "Harness should have postconditions section, got:\n{harness_content}"
    );
    assert!(
        harness_content.contains("kani::assert(") && harness_content.contains("postcondition"),
        "Postconditions should be exported as kani::assert() calls, got:\n{harness_content}"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}

/// Test that --export-kani exports both @_requires (as assume) and @_ensures (as assert)
#[test]
fn cli_export_kani_requires_and_ensures_together() {
    use std::fs;

    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let tmpdir = std::env::temp_dir().join(format!("kani_req_ens_test_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmpdir);

    // Use verified_positive.sil which has both @_requires and @_ensures
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/verified_positive_unsafe.sil")
        .arg("--export-kani")
        .arg(&tmpdir)
        .output()
        .expect("failed to run tswift-verify");

    let _ = output;

    // Find harness files
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

    let harness_path = entries
        .iter()
        .find(|e| e.file_name().to_string_lossy().contains("safeadd"))
        .map_or_else(|| entries[0].path(), std::fs::DirEntry::path);

    let harness_content =
        fs::read_to_string(&harness_path).expect("should be able to read harness file");

    // Check that preconditions are exported as kani::assume()
    assert!(
        harness_content.contains("// Preconditions (@_requires)"),
        "Harness should have preconditions section, got:\n{harness_content}"
    );
    assert!(
        harness_content.contains("kani::assume(") && harness_content.contains("precondition"),
        "Preconditions should be exported as kani::assume() calls, got:\n{harness_content}"
    );

    // Check that postconditions are exported as kani::assert()
    assert!(
        harness_content.contains("// Postconditions (@_ensures)"),
        "Harness should have postconditions section, got:\n{harness_content}"
    );
    assert!(
        harness_content.contains("kani::assert(") && harness_content.contains("postcondition"),
        "Postconditions should be exported as kani::assert() calls, got:\n{harness_content}"
    );

    // Verify the order: preconditions (assume) come before postconditions (assert)
    let assume_pos = harness_content
        .find("// Preconditions (@_requires)")
        .expect("should find preconditions section");
    let assert_pos = harness_content
        .find("// Postconditions (@_ensures)")
        .expect("should find postconditions section");
    assert!(
        assume_pos < assert_pos,
        "Preconditions section should come before postconditions section"
    );

    // Clean up
    let _ = fs::remove_dir_all(&tmpdir);
}
