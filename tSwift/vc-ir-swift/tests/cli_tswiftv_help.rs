//! Integration tests for the top-level `bin/tswiftv` wrapper help output.

use std::path::PathBuf;
use std::process::Command;

fn get_repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("expected vc-ir-swift/.. to exist")
        .to_path_buf()
}

#[test]
fn cli_tswiftv_help_subcommand() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("help")
        .output()
        .expect("failed to run bin/tswiftv help");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("tswift - Swift compiler with formal verification"),
        "expected help to contain title, got:\n{stdout}"
    );
    assert!(
        stdout.contains("USAGE:"),
        "expected help to contain USAGE section, got:\n{stdout}"
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
fn cli_tswiftv_help_flag() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("--help")
        .output()
        .expect("failed to run bin/tswiftv --help");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("tswift - Swift compiler with formal verification"),
        "expected --help to contain title, got:\n{stdout}"
    );
}

#[test]
fn cli_tswiftv_no_args_shows_help() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .output()
        .expect("failed to run bin/tswiftv with no args");

    assert!(
        output.status.success(),
        "expected success when no args, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("tswift - Swift compiler with formal verification"),
        "expected no-args to show help, got:\n{stdout}"
    );
}

#[test]
fn cli_tswiftv_help_short_flag() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("-h")
        .output()
        .expect("failed to run bin/tswiftv -h");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("tswift - Swift compiler with formal verification"),
        "expected -h to show help, got:\n{stdout}"
    );
}

#[test]
fn cli_tswiftv_help_has_options_section() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("--help")
        .output()
        .expect("failed to run bin/tswiftv --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("OPTIONS:"),
        "expected help to contain OPTIONS section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("--no-verify"),
        "expected OPTIONS to include --no-verify, got:\n{stdout}"
    );
    assert!(
        stdout.contains("--verify-only"),
        "expected OPTIONS to include --verify-only, got:\n{stdout}"
    );
    assert!(
        stdout.contains("--json"),
        "expected OPTIONS to include --json, got:\n{stdout}"
    );
}

#[test]
fn cli_tswiftv_help_has_kani_options() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("--help")
        .output()
        .expect("failed to run bin/tswiftv --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("KANI OPTIONS"),
        "expected help to contain KANI OPTIONS section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("--export-kani"),
        "expected KANI OPTIONS to include --export-kani, got:\n{stdout}"
    );
    assert!(
        stdout.contains("--run-kani"),
        "expected KANI OPTIONS to include --run-kani, got:\n{stdout}"
    );
    assert!(
        stdout.contains("--kani-bitvector"),
        "expected KANI OPTIONS to include --kani-bitvector, got:\n{stdout}"
    );
}

#[test]
fn cli_tswiftv_help_has_examples() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("--help")
        .output()
        .expect("failed to run bin/tswiftv --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("EXAMPLES:"),
        "expected help to contain EXAMPLES section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("tswift main.swift"),
        "expected EXAMPLES to include basic compile example, got:\n{stdout}"
    );
    assert!(
        stdout.contains("tswift verify"),
        "expected EXAMPLES to include verify example, got:\n{stdout}"
    );
}

#[test]
fn cli_tswiftv_help_has_verification_section() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("--help")
        .output()
        .expect("failed to run bin/tswiftv --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("VERIFICATION:"),
        "expected help to contain VERIFICATION section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("Arithmetic operations"),
        "expected VERIFICATION to mention arithmetic checks, got:\n{stdout}"
    );
    assert!(
        stdout.contains("Array accesses"),
        "expected VERIFICATION to mention array bounds checks, got:\n{stdout}"
    );
}

#[test]
fn cli_tswiftv_help_has_annotations_section() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("--help")
        .output()
        .expect("failed to run bin/tswiftv --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("ANNOTATIONS:"),
        "expected help to contain ANNOTATIONS section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("@_requires"),
        "expected ANNOTATIONS to mention @_requires, got:\n{stdout}"
    );
    assert!(
        stdout.contains("@_ensures"),
        "expected ANNOTATIONS to mention @_ensures, got:\n{stdout}"
    );
    assert!(
        stdout.contains("@_trusted"),
        "expected ANNOTATIONS to mention @_trusted, got:\n{stdout}"
    );
}

#[test]
fn cli_tswiftv_help_has_environment_section() {
    let repo_root = get_repo_root();
    let tswiftv = repo_root.join("bin/tswiftv");

    let output = Command::new(&tswiftv)
        .current_dir(&repo_root)
        .arg("--help")
        .output()
        .expect("failed to run bin/tswiftv --help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("ENVIRONMENT:"),
        "expected help to contain ENVIRONMENT section, got:\n{stdout}"
    );
    assert!(
        stdout.contains("SWIFT_FRONTEND"),
        "expected ENVIRONMENT to mention SWIFT_FRONTEND, got:\n{stdout}"
    );
    assert!(
        stdout.contains("MACOSX_SDK"),
        "expected ENVIRONMENT to mention MACOSX_SDK, got:\n{stdout}"
    );
}
