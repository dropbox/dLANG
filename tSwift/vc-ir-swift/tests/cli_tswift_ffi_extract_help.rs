//! Integration tests for `tswift-ffi-extract` help output.

use std::process::Command;

#[test]
fn cli_tswift_ffi_extract_help_flag() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");

    let output = Command::new(bin)
        .arg("--help")
        .output()
        .expect("failed to run tswift-ffi-extract --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    assert!(
        stdout.contains("tswift-ffi-extract - Extract"),
        "expected help to contain title, got:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("USAGE:"),
        "expected help to contain USAGE section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("OPTIONS:"),
        "expected help to contain OPTIONS section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("OUTPUT:"),
        "expected help to contain OUTPUT section, got:\n{stdout}"
    );
    assert!(
        !stdout.contains('\t'),
        "expected help output to not contain tab characters, got:\n{stdout}"
    );
}

#[test]
fn cli_tswift_ffi_extract_help_short_flag() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");

    let output = Command::new(bin)
        .arg("-h")
        .output()
        .expect("failed to run tswift-ffi-extract -h");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("tswift-ffi-extract - Extract"),
        "expected -h to show help, got:\n{stdout}"
    );
}

#[test]
fn cli_tswift_ffi_extract_no_args_shows_help() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-extract");

    let output = Command::new(bin)
        .output()
        .expect("failed to run tswift-ffi-extract");

    // No args should show help and succeed
    assert!(
        output.status.success(),
        "expected success with no args, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("USAGE:"),
        "expected help output with no args, got:\n{stdout}"
    );
}
