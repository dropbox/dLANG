use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

fn unique_temp_contract_path() -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let pid = std::process::id();
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("tswift_ffi_contract_{pid}_{now}_{n}.ffi.json"))
}

#[test]
fn cli_accepts_emit_ffi_contract_alias() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let contract_path = unique_temp_contract_path();

    let _ = fs::remove_file(&contract_path);

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--emit-ffi-contract")
        .arg(&contract_path)
        .arg("--rust")
        .arg("tests/ffi_examples/math_export.rs")
        .arg("--crate-name")
        .arg("math")
        .output()
        .expect("failed to run tswift-ffi-verify");

    assert!(
        output.status.success(),
        "expected success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let json = fs::read_to_string(&contract_path).expect("expected contract file to be created");
    assert!(json.contains("\"crate_name\""));
    assert!(json.contains("math"));

    let _ = fs::remove_file(&contract_path);
}

#[test]
fn cli_accepts_equals_form_for_ffi_contract() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let contract_path = unique_temp_contract_path();

    let _ = fs::remove_file(&contract_path);

    let emit = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--emit-contract")
        .arg(&contract_path)
        .arg("--rust")
        .arg("tests/ffi_examples/math_export.rs")
        .arg("--crate-name")
        .arg("math")
        .output()
        .expect("failed to run tswift-ffi-verify --emit-contract");
    assert!(
        emit.status.success(),
        "expected emit-contract success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        emit.status.code(),
        String::from_utf8_lossy(&emit.stdout),
        String::from_utf8_lossy(&emit.stderr),
    );

    let contract_arg = format!("--ffi-contract={}", contract_path.display());
    let verify = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/math_import.swift")
        .arg(contract_arg)
        .output()
        .expect("failed to run tswift-ffi-verify --ffi-contract=...");

    assert!(
        verify.status.success(),
        "expected verify success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        verify.status.code(),
        String::from_utf8_lossy(&verify.stdout),
        String::from_utf8_lossy(&verify.stderr),
    );

    let _ = fs::remove_file(&contract_path);
}

#[test]
fn cli_z4_verification_compatible_ffi() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/math_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/math_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected compatible FFI to pass, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Verify Z4 was actually used
    assert!(
        stdout.contains("Z4 proved") || stderr.contains("Z4 proved"),
        "expected Z4 proofs in output\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_verification_incompatible_ffi_fails_with_counterexample() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/incompatible_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/math_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Should fail with exit code 1 (incompatible)
    assert!(
        !output.status.success(),
        "expected incompatible FFI to fail, but it passed\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (incompatible), got {:?}",
        output.status.code()
    );

    // Should show FAIL and counterexample
    assert!(
        stdout.contains("FAIL") || stderr.contains("FAIL"),
        "expected FAIL in output\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
    assert!(
        stdout.contains("counterexample") || stderr.contains("counterexample"),
        "expected counterexample in output\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_buffer_ops_compatible() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/buffer_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/buffer_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected buffer FFI to pass, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_buffer_ops_unsafe_fails() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/buffer_import_unsafe.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/buffer_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Should fail with exit code 1 (incompatible)
    assert!(
        !output.status.success(),
        "expected unsafe buffer FFI to fail, but it passed\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (incompatible), got {:?}",
        output.status.code()
    );

    // Should show FAIL for at least one function
    assert!(
        stdout.contains("FAIL"),
        "expected FAIL in output for unsafe imports\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_voice_ffi_swift_bridge_syntax() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/voice_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/voice_bridge.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected voice FFI to pass, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );
}

#[test]
fn cli_emit_contract_buffer_ops() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let contract_path = unique_temp_contract_path();

    let _ = fs::remove_file(&contract_path);

    // Generate contract from buffer_export.rs
    let emit = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--emit-contract")
        .arg(&contract_path)
        .arg("--rust")
        .arg("tests/ffi_examples/buffer_export.rs")
        .arg("--crate-name")
        .arg("buffer-core")
        .output()
        .expect("failed to run tswift-ffi-verify --emit-contract");

    assert!(
        emit.status.success(),
        "expected emit-contract success, got {:?}\nstdout:\n{}\nstderr:\n{}",
        emit.status.code(),
        String::from_utf8_lossy(&emit.stdout),
        String::from_utf8_lossy(&emit.stderr),
    );

    // Verify contract file was created with expected content
    let json = fs::read_to_string(&contract_path).expect("contract file should exist");
    assert!(
        json.contains("parse_buffer"),
        "contract should include parse_buffer"
    );
    assert!(
        json.contains("compare_buffers"),
        "contract should include compare_buffers"
    );
    assert!(
        json.contains("buffer-core"),
        "contract should include crate name"
    );

    // Verify Swift imports against the contract
    let verify = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/buffer_import.swift")
        .arg(format!("--ffi-contract={}", contract_path.display()))
        .arg("--z4")
        .output()
        .expect("failed to run contract verification");

    assert!(
        verify.status.success(),
        "expected contract verification to pass, got {:?}\nstdout:\n{}\nstderr:\n{}",
        verify.status.code(),
        String::from_utf8_lossy(&verify.stdout),
        String::from_utf8_lossy(&verify.stderr),
    );

    let _ = fs::remove_file(&contract_path);
}

#[test]
fn cli_json_output_format() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/math_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/math_export.rs")
        .arg("--json")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "expected JSON output success\nstdout:\n{}\nstderr:\n{}",
        stdout,
        String::from_utf8_lossy(&output.stderr),
    );

    // Should be valid JSON with expected fields
    assert!(
        stdout.contains("\"results\""),
        "JSON should have results array"
    );
    assert!(
        stdout.contains("\"summary\""),
        "JSON should have summary object"
    );
    assert!(
        stdout.contains("\"function\""),
        "JSON should have function names"
    );
    assert!(
        stdout.contains("\"compatible\""),
        "JSON should have compatible count"
    );
}

#[test]
fn cli_multiple_swift_files() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    // Verify multiple Swift files against multiple Rust files
    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/math_import.swift")
        .arg("tests/ffi_examples/buffer_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/math_export.rs")
        .arg("tests/ffi_examples/buffer_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected multi-file verification to pass\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );

    // Should process functions from both files
    assert!(
        stdout.contains("increment") || stdout.contains("parse_buffer"),
        "should verify functions from both files\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_is_empty_normalization() {
    // Test that Rust .is_empty() conditions are normalized and verified correctly
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/is_empty_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/is_empty_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected is_empty FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for is_empty-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for is_empty conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_first_last_normalization() {
    // Test that Rust .first().is_some() and .last().is_some() conditions
    // are normalized to count comparisons and verified correctly
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/first_last_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/first_last_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected first/last FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for first/last-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for first/last conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_get_index_normalization() {
    // Test that Rust .get(index).is_some() conditions are normalized
    // to bounds comparisons (index < count) and verified correctly
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/get_index_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/get_index_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected get(index) FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for get(index)-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for get(index) conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_iter_count_normalization() {
    // Test that Rust .iter().count() conditions are normalized
    // to .count and verified correctly against Swift .count
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/iter_count_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/iter_count_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected iter().count() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for iter().count()-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for iter().count() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_range_contains_normalization() {
    // Test that Rust range `.contains(&index)` conditions are normalized
    // to bounds comparisons and verified correctly against Swift comparisons.
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/range_contains_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/range_contains_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected range.contains FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for range.contains conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_range_len_normalization() {
    // Test that Rust range `.len()` expressions are normalized
    // to arithmetic and verified correctly against Swift arithmetic.
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/range_len_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/range_len_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected range.len() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for range.len() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_option_is_some_is_none_normalization() {
    // Test that Rust Option `.is_some()` / `.is_none()` conditions are normalized
    // to `!= nil` / `== nil` and verified correctly against Swift nil comparisons.
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/option_some_none_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/option_some_none_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected Option is_some/is_none FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for Option is_some/is_none conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_into_iter_mut_count_normalization() {
    // Test that Rust .into_iter().count() and .iter_mut().count() conditions are normalized
    // to .count and verified correctly against Swift .count
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/into_iter_mut_count_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/into_iter_mut_count_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected into_iter()/iter_mut().count() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for into_iter()/iter_mut().count()-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for into_iter()/iter_mut().count() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_chars_count_normalization() {
    // Test that Rust .chars().count() conditions are normalized
    // to .count and verified correctly against Swift .count
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/chars_count_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/chars_count_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected chars().count() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for chars().count()-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for chars().count() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_bytes_count_normalization() {
    // Test that Rust .bytes().count() conditions are normalized
    // to .utf8.count and verified correctly against Swift .utf8.count
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/bytes_count_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/bytes_count_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected bytes().count() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for bytes().count()-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for bytes().count() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_lines_count_normalization() {
    // Test that Rust .lines().count() conditions are normalized
    // to .lines.count and verified correctly against Swift .lines.count
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/lines_count_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/lines_count_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected lines().count() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for lines().count()-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for lines().count() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_split_count_normalization() {
    // Test that Rust .split(delimiter).count() conditions are normalized
    // to .split(delimiter).count and verified correctly against Swift
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/split_count_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/split_count_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected split().count() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for split().count()-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for split().count() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_result_ok_err_normalization() {
    // Test that Rust Result .ok().is_some()/.is_none()/.err().is_some()/.is_none()
    // conditions are normalized to .isSuccess and verified correctly against Swift
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/result_ok_err_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/result_ok_err_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected Result .ok()/.err() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for Result-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for Result .ok()/.err() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_result_is_ok_err_normalization() {
    // Test that Rust Result .is_ok()/.is_err() and unwrap() conditions are normalized
    // and verified correctly against Swift.
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/result_is_ok_err_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/result_is_ok_err_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected Result .is_ok()/.is_err() FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for Result .is_ok()/.is_err() conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_z4_take_skip_count_normalization() {
    // Test that Rust .iter().take(n).count() and .iter().skip(n).count() conditions
    // are normalized to .take(n).count and .skip(n).count for FFI verification.
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--swift")
        .arg("tests/ffi_examples/take_skip_import.swift")
        .arg("--rust")
        .arg("tests/ffi_examples/take_skip_export.rs")
        .arg("--z4")
        .arg("--verbose")
        .output()
        .expect("failed to run tswift-ffi-verify");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected take/skip count FFI to pass (normalization should work), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );

    // Should show compatible results for take/skip-based conditions
    assert!(
        stdout.contains("compatible") || stdout.contains("OK"),
        "expected compatible status for take/skip conditions\nstdout:\n{stdout}\nstderr:\n{stderr}",
    );
}

#[test]
fn cli_ffi_verify_rejects_unknown_flag() {
    let bin = env!("CARGO_BIN_EXE_tswift-ffi-verify");

    let output = Command::new(bin)
        .arg("--unknown-flag")
        .output()
        .expect("failed to run tswift-ffi-verify");

    assert!(
        !output.status.success(),
        "expected failure for unknown flag"
    );
    assert_eq!(
        output.status.code(),
        Some(2),
        "expected exit code 2 for unknown flag"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unknown argument") && stderr.contains("--unknown-flag"),
        "expected error message about unknown argument, got:\n{stderr}"
    );
}
