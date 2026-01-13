//! Integration tests for tswift-verify stdin reading functionality.

use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn cli_stdin_verifies_valid_bundle() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");

    let mut child = Command::new(bin)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn tswift-verify");

    let stdin = child.stdin.as_mut().expect("failed to open stdin");
    let input = r#"{"function_name":"test","parameters":[],"verification_conditions":[]}"#;
    stdin
        .write_all(input.as_bytes())
        .expect("failed to write to stdin");

    let output = child.wait_with_output().expect("failed to wait on child");

    assert!(
        output.status.success(),
        "expected success for valid stdin bundle, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Verified"),
        "expected 'Verified' in output, got:\n{stdout}"
    );
}

#[test]
fn cli_stdin_fails_on_invalid_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");

    let mut child = Command::new(bin)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn tswift-verify");

    let stdin = child.stdin.as_mut().expect("failed to open stdin");
    stdin
        .write_all(b"not valid json at all")
        .expect("failed to write to stdin");

    let output = child.wait_with_output().expect("failed to wait on child");

    assert!(
        !output.status.success(),
        "expected failure for invalid JSON, got {:?}",
        output.status.code()
    );
    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for parse error"
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("error") || stdout.contains("Parse error"),
        "expected error message for invalid JSON, got:\n{stdout}"
    );
}

#[test]
fn cli_stdin_fails_on_missing_required_field() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");

    let mut child = Command::new(bin)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn tswift-verify");

    let stdin = child.stdin.as_mut().expect("failed to open stdin");
    // Missing function_name field
    let input = r#"{"parameters":[],"verification_conditions":[]}"#;
    stdin
        .write_all(input.as_bytes())
        .expect("failed to write to stdin");

    let output = child.wait_with_output().expect("failed to wait on child");

    assert!(
        !output.status.success(),
        "expected failure for missing field, got {:?}",
        output.status.code()
    );
    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for parse error"
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("function_name"),
        "expected error to mention missing field, got:\n{stdout}"
    );
}

#[test]
fn cli_stdin_handles_empty_input() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");

    let mut child = Command::new(bin)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn tswift-verify");

    let stdin = child.stdin.as_mut().expect("failed to open stdin");
    stdin
        .write_all(b"")
        .expect("failed to write empty input to stdin");

    let output = child.wait_with_output().expect("failed to wait on child");

    // Empty input should either succeed (no bundles) or fail gracefully
    // Check that it doesn't crash
    let code = output.status.code().unwrap_or(-1);
    assert!(
        code == 0 || code == 2,
        "expected exit code 0 (no bundles) or 2 (parse error) for empty input, got {code}"
    );
}

#[test]
fn cli_stdin_handles_multiple_json_lines() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");

    let mut child = Command::new(bin)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn tswift-verify");

    let stdin = child.stdin.as_mut().expect("failed to open stdin");
    let input = r#"{"function_name":"test1","parameters":[],"verification_conditions":[]}
{"function_name":"test2","parameters":[],"verification_conditions":[]}"#;
    stdin
        .write_all(input.as_bytes())
        .expect("failed to write to stdin");

    let output = child.wait_with_output().expect("failed to wait on child");

    assert!(
        output.status.success(),
        "expected success for multiple bundles via stdin, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Should contain results for both functions
    assert!(
        stdout.contains("test1") && stdout.contains("test2"),
        "expected both function results in output, got:\n{stdout}"
    );
}

#[test]
fn cli_stdin_outputs_json_by_default() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");

    let mut child = Command::new(bin)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn tswift-verify");

    let stdin = child.stdin.as_mut().expect("failed to open stdin");
    let input = r#"{"function_name":"test","parameters":[],"verification_conditions":[]}"#;
    stdin
        .write_all(input.as_bytes())
        .expect("failed to write to stdin");

    let output = child.wait_with_output().expect("failed to wait on child");

    let stdout = String::from_utf8_lossy(&output.stdout);
    // Stdin mode always uses JSON output
    assert!(
        stdout.contains('{') && stdout.contains('}'),
        "expected JSON output for stdin mode, got:\n{stdout}"
    );
    // Check for valid JSON structure
    assert!(
        stdout.contains("\"function_name\"") && stdout.contains("\"summary\""),
        "expected valid JSON with function_name and summary fields, got:\n{stdout}"
    );
}
