//! Integration tests for the top-level `bin/tswift-ffi-verify` wrapper help output.

use std::path::PathBuf;
use std::process::Command;

fn get_repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("expected vc-ir-swift/.. to exist")
        .to_path_buf()
}

#[test]
fn cli_tswift_ffi_verify_help_flag() {
    let repo_root = get_repo_root();
    let wrapper = repo_root.join("bin/tswift-ffi-verify");

    // Verify the wrapper script exists
    assert!(wrapper.exists(), "wrapper script not found at {wrapper:?}");

    let output = Command::new(&wrapper)
        .arg("--help")
        .current_dir(&repo_root)
        .output()
        .expect("failed to run bin/tswift-ffi-verify --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected success, got {:?}\nwrapper: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        wrapper,
        stdout,
        stderr,
    );

    assert!(
        stdout.contains("tswift-ffi-verify - Verify FFI compatibility"),
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
        stdout.contains("EXIT CODES:"),
        "expected help to contain EXIT CODES section, got:\n{stdout}"
    );
    assert!(
        !stdout.contains('\t'),
        "expected help output to not contain tab characters, got:\n{stdout}"
    );
}

#[test]
fn cli_tswift_ffi_verify_help_short_flag() {
    let repo_root = get_repo_root();
    let wrapper = repo_root.join("bin/tswift-ffi-verify");

    let output = Command::new(&wrapper)
        .arg("-h")
        .current_dir(&repo_root)
        .output()
        .expect("failed to run bin/tswift-ffi-verify -h");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("tswift-ffi-verify - Verify FFI compatibility"),
        "expected -h to show help, got:\n{stdout}"
    );
}

#[test]
fn cli_tswift_ffi_verify_help_has_modes_section() {
    let repo_root = get_repo_root();
    let wrapper = repo_root.join("bin/tswift-ffi-verify");

    let output = Command::new(&wrapper)
        .arg("--help")
        .current_dir(&repo_root)
        .output()
        .expect("failed to run bin/tswift-ffi-verify --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("MODES:"),
        "expected help to contain MODES section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("Unified Mode:"),
        "expected help to document Unified Mode, got:\n{stdout}"
    );
    assert!(
        stdout.contains("Contract Mode:"),
        "expected help to document Contract Mode, got:\n{stdout}"
    );
    assert!(
        stdout.contains("Emit Mode:"),
        "expected help to document Emit Mode, got:\n{stdout}"
    );
}

#[test]
fn cli_tswift_ffi_verify_help_has_examples() {
    let repo_root = get_repo_root();
    let wrapper = repo_root.join("bin/tswift-ffi-verify");

    let output = Command::new(&wrapper)
        .arg("--help")
        .current_dir(&repo_root)
        .output()
        .expect("failed to run bin/tswift-ffi-verify --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("EXAMPLES:"),
        "expected help to contain EXAMPLES section, got:\n{stdout}"
    );
}
