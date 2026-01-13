//! Integration tests for tswift-verify help output.

use std::process::Command;

fn get_help_output() -> (bool, String, String) {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--help")
        .output()
        .expect("failed to run tswift-verify --help");

    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

#[test]
fn cli_help_mentions_z4_and_has_no_tabs() {
    let (success, _stdout, stderr) = get_help_output();

    assert!(success, "expected success\nstderr:\n{stderr}");

    assert!(
        stderr.contains("using Z4 SMT solver"),
        "expected help to mention Z4 SMT solver, got:\n{stderr}"
    );
    assert!(
        !stderr.contains('\t'),
        "expected help output to not contain tab characters, got:\n{stderr}"
    );
    assert!(
        stderr.contains("--incremental   Enable incremental verification"),
        "expected help to include incremental option line, got:\n{stderr}"
    );
}

#[test]
fn cli_help_short_flag() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("-h")
        .output()
        .expect("failed to run tswift-verify -h");

    assert!(
        output.status.success(),
        "expected -h to succeed, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("tswift-verify - Verify Swift verification bundles"),
        "expected -h to show help, got:\n{stderr}"
    );
}

#[test]
fn cli_help_has_usage_section() {
    let (_success, _stdout, stderr) = get_help_output();

    assert!(
        stderr.contains("USAGE:"),
        "expected help to contain USAGE section, got:\n{stderr}"
    );
    assert!(
        stderr.contains("<INPUT>"),
        "expected USAGE to reference INPUT arg, got:\n{stderr}"
    );
}

#[test]
fn cli_help_has_options_section() {
    let (_success, _stdout, stderr) = get_help_output();

    assert!(
        stderr.contains("OPTIONS:"),
        "expected help to contain OPTIONS section, got:\n{stderr}"
    );
    assert!(
        stderr.contains("--sil"),
        "expected OPTIONS to include --sil, got:\n{stderr}"
    );
    assert!(
        stderr.contains("--swift"),
        "expected OPTIONS to include --swift, got:\n{stderr}"
    );
    assert!(
        stderr.contains("--json"),
        "expected OPTIONS to include --json, got:\n{stderr}"
    );
    assert!(
        stderr.contains("--verbose"),
        "expected OPTIONS to include --verbose, got:\n{stderr}"
    );
}

#[test]
fn cli_help_has_examples_section() {
    let (_success, _stdout, stderr) = get_help_output();

    assert!(
        stderr.contains("EXAMPLES:"),
        "expected help to contain EXAMPLES section, got:\n{stderr}"
    );
    assert!(
        stderr.contains("tswift-verify bundle.json"),
        "expected EXAMPLES to include bundle verification, got:\n{stderr}"
    );
    assert!(
        stderr.contains("tswift-verify --sil"),
        "expected EXAMPLES to include SIL verification, got:\n{stderr}"
    );
}

#[test]
fn cli_help_has_output_section() {
    let (_success, _stdout, stderr) = get_help_output();

    assert!(
        stderr.contains("OUTPUT:"),
        "expected help to contain OUTPUT section, got:\n{stderr}"
    );
    assert!(
        stderr.contains("Exit code 0"),
        "expected OUTPUT to document exit code 0, got:\n{stderr}"
    );
    assert!(
        stderr.contains("Exit code 1"),
        "expected OUTPUT to document exit code 1, got:\n{stderr}"
    );
    assert!(
        stderr.contains("Exit code 2"),
        "expected OUTPUT to document exit code 2, got:\n{stderr}"
    );
}

#[test]
fn cli_help_has_kani_options() {
    let (_success, _stdout, stderr) = get_help_output();

    assert!(
        stderr.contains("--export-kani"),
        "expected help to include --export-kani, got:\n{stderr}"
    );
    assert!(
        stderr.contains("--run-kani"),
        "expected help to include --run-kani, got:\n{stderr}"
    );
    assert!(
        stderr.contains("--kani-bitvector"),
        "expected help to include --kani-bitvector, got:\n{stderr}"
    );
}

#[test]
fn cli_help_has_args_section() {
    let (_success, _stdout, stderr) = get_help_output();

    assert!(
        stderr.contains("ARGS:"),
        "expected help to contain ARGS section, got:\n{stderr}"
    );
    assert!(
        stderr.contains("<INPUT>"),
        "expected ARGS to document INPUT, got:\n{stderr}"
    );
    assert!(
        stderr.contains("Path to bundle file"),
        "expected ARGS to describe bundle file, got:\n{stderr}"
    );
}

#[test]
fn cli_help_has_diagnostic_format_section() {
    let (_success, _stdout, stderr) = get_help_output();

    assert!(
        stderr.contains("DIAGNOSTIC FORMAT:"),
        "expected help to contain DIAGNOSTIC FORMAT section, got:\n{stderr}"
    );
    assert!(
        stderr.contains("compiler format for IDE integration"),
        "expected DIAGNOSTIC FORMAT to mention IDE integration, got:\n{stderr}"
    );
}

#[test]
fn cli_help_has_json_progress_format_section() {
    let (_success, _stdout, stderr) = get_help_output();

    assert!(
        stderr.contains("JSON PROGRESS FORMAT:"),
        "expected help to contain JSON PROGRESS FORMAT section, got:\n{stderr}"
    );
    assert!(
        stderr.contains("function_start"),
        "expected JSON PROGRESS to document function_start event, got:\n{stderr}"
    );
    assert!(
        stderr.contains("vc_complete"),
        "expected JSON PROGRESS to document vc_complete event, got:\n{stderr}"
    );
    assert!(
        stderr.contains("summary"),
        "expected JSON PROGRESS to document summary event, got:\n{stderr}"
    );
}
