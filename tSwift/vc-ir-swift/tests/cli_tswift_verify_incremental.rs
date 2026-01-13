//! Integration tests for tswift-verify --incremental, --cache-dir, and --source-file flags

use std::fs;
use std::process::Command;

/// Test that --incremental creates a cache file
#[test]
fn cli_incremental_creates_cache_file() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let tmp_dir = std::env::temp_dir().join("tswift_test_incremental_creates_cache");
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).expect("create temp dir");

    // Create a test SIL file
    let sil_file = tmp_dir.join("test_incremental.sil");
    let sil_content = r#"
sil_stage canonical

sil [ossa] @addOne : $@convention(thin) (Int64) -> Int64 {
bb0(%0 : $Int64):
  %1 = struct_extract %0, #Int64._value
  %2 = integer_literal $Builtin.Int64, 1
  %3 = builtin "sadd_with_overflow_Int64"(%1, %2) : $(Builtin.Int64, Builtin.Int1)
  %4 = tuple_extract %3, 0
  %5 = struct $Int64 (%4)
  return %5
}
"#;
    fs::write(&sil_file, sil_content).expect("write test sil");

    let output = Command::new(bin)
        .arg("--sil")
        .arg("--incremental")
        .arg(&sil_file)
        .output()
        .expect("failed to run tswift-verify");

    // Should run successfully (exit 0 or 1 depending on verification)
    assert!(
        output.status.code().is_some(),
        "expected command to complete"
    );

    // Check that a cache directory was created
    let cache_dir = tmp_dir.join(".tswift_cache");
    assert!(
        cache_dir.exists(),
        "expected .tswift_cache directory to be created"
    );

    // Check that a cache file exists
    let cache_file = cache_dir.join("test_incremental.sil.cache.json");
    assert!(
        cache_file.exists(),
        "expected cache file to be created at {cache_file:?}"
    );

    // Verify the cache file is valid JSON
    let cache_content = fs::read_to_string(&cache_file).expect("read cache file");
    let cache: serde_json::Value = serde_json::from_str(&cache_content).expect("parse cache JSON");
    assert!(
        cache.get("version").is_some(),
        "expected cache to have version field"
    );
    assert!(
        cache.get("entries").is_some(),
        "expected cache to have entries field"
    );

    // Cleanup
    let _ = fs::remove_dir_all(&tmp_dir);
}

/// Test that --cache-dir puts cache in custom location
#[test]
fn cli_cache_dir_custom_location() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let tmp_dir = std::env::temp_dir().join("tswift_test_cache_dir_custom");
    let custom_cache = tmp_dir.join("my_custom_cache");
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).expect("create temp dir");

    // Create a test SIL file
    let sil_file = tmp_dir.join("test_custom_cache.sil");
    let sil_content = r"
sil_stage canonical

sil [ossa] @identity : $@convention(thin) (Int64) -> Int64 {
bb0(%0 : $Int64):
  return %0
}
";
    fs::write(&sil_file, sil_content).expect("write test sil");

    let output = Command::new(bin)
        .arg("--sil")
        .arg("--incremental")
        .arg(format!("--cache-dir={}", custom_cache.display()))
        .arg(&sil_file)
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.code().is_some(),
        "expected command to complete"
    );

    // Check that custom cache directory was used
    assert!(
        custom_cache.exists(),
        "expected custom cache directory to be created at {custom_cache:?}"
    );

    // Check that cache file is in custom location
    let cache_file = custom_cache.join("test_custom_cache.sil.cache.json");
    assert!(
        cache_file.exists(),
        "expected cache file in custom location at {cache_file:?}"
    );

    // Verify the default .tswift_cache was NOT created
    let default_cache = tmp_dir.join(".tswift_cache");
    assert!(
        !default_cache.exists(),
        "expected default cache directory NOT to be created when --cache-dir is used"
    );

    // Cleanup
    let _ = fs::remove_dir_all(&tmp_dir);
}

/// Test that --cache-dir with space-separated syntax works
#[test]
fn cli_cache_dir_space_separated() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let tmp_dir = std::env::temp_dir().join("tswift_test_cache_dir_space");
    let custom_cache = tmp_dir.join("space_cache");
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).expect("create temp dir");

    let sil_file = tmp_dir.join("test_space_cache.sil");
    let sil_content = r"
sil_stage canonical

sil [ossa] @noop : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
";
    fs::write(&sil_file, sil_content).expect("write test sil");

    let output = Command::new(bin)
        .arg("--sil")
        .arg("--incremental")
        .arg("--cache-dir")
        .arg(&custom_cache)
        .arg(&sil_file)
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.code().is_some(),
        "expected command to complete"
    );

    assert!(
        custom_cache.exists(),
        "expected cache directory to be created with space-separated syntax"
    );

    // Cleanup
    let _ = fs::remove_dir_all(&tmp_dir);
}

/// Test that running with --incremental twice uses cached results
#[test]
fn cli_incremental_uses_cache_on_second_run() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let tmp_dir = std::env::temp_dir().join("tswift_test_incremental_second_run");
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).expect("create temp dir");

    let sil_file = tmp_dir.join("test_cache_reuse.sil");
    let sil_content = r#"
sil_stage canonical

sil [ossa] @simpleAdd : $@convention(thin) (Int64, Int64) -> Int64 {
bb0(%0 : $Int64, %1 : $Int64):
  %2 = struct_extract %0, #Int64._value
  %3 = struct_extract %1, #Int64._value
  %4 = builtin "sadd_with_overflow_Int64"(%2, %3) : $(Builtin.Int64, Builtin.Int1)
  %5 = tuple_extract %4, 0
  %6 = struct $Int64 (%5)
  return %6
}
"#;
    fs::write(&sil_file, sil_content).expect("write test sil");

    // First run: should verify and create cache
    let output1 = Command::new(bin)
        .arg("--sil")
        .arg("--incremental")
        .arg(&sil_file)
        .output()
        .expect("failed to run first verification");

    let exit1 = output1.status.code();
    let stdout1 = String::from_utf8_lossy(&output1.stdout);

    // Second run: should use cache
    let output2 = Command::new(bin)
        .arg("--sil")
        .arg("--incremental")
        .arg(&sil_file)
        .output()
        .expect("failed to run second verification");

    let exit2 = output2.status.code();
    let stdout2 = String::from_utf8_lossy(&output2.stdout);

    // Both runs should have the same exit code
    assert_eq!(
        exit1, exit2,
        "expected same exit code for cached run\nFirst:\n{stdout1}\nSecond:\n{stdout2}"
    );

    // Cleanup
    let _ = fs::remove_dir_all(&tmp_dir);
}

/// Test that --source-file filters functions by source file
#[test]
fn cli_source_file_filters_functions() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let tmp_dir = std::env::temp_dir().join("tswift_test_source_file_filter");
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).expect("create temp dir");

    // Create a bundle with functions from multiple source files
    let bundle_file = tmp_dir.join("multi_source.json");
    let bundle_content = r#"[
  {
    "function_name": "funcFromA",
    "source_file": "a.swift",
    "source_line": 1,
    "spec": null,
    "auto_vcs": []
  },
  {
    "function_name": "funcFromB",
    "source_file": "b.swift",
    "source_line": 1,
    "spec": null,
    "auto_vcs": []
  },
  {
    "function_name": "funcFromA2",
    "source_file": "a.swift",
    "source_line": 10,
    "spec": null,
    "auto_vcs": []
  }
]"#;
    fs::write(&bundle_file, bundle_content).expect("write bundle");

    // Run without filter - should see all functions
    let output_all = Command::new(bin)
        .current_dir(manifest_dir)
        .arg(&bundle_file)
        .output()
        .expect("failed to run without filter");

    let stdout_all = String::from_utf8_lossy(&output_all.stdout);
    assert!(
        stdout_all.contains("funcFromA") && stdout_all.contains("funcFromB"),
        "expected all functions without filter, got:\n{stdout_all}"
    );

    // Run with --source-file=a.swift - should only see funcFromA and funcFromA2
    let output_filtered = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--source-file=a.swift")
        .arg(&bundle_file)
        .output()
        .expect("failed to run with filter");

    let stdout_filtered = String::from_utf8_lossy(&output_filtered.stdout);
    assert!(
        stdout_filtered.contains("funcFromA"),
        "expected funcFromA in filtered output, got:\n{stdout_filtered}"
    );
    assert!(
        !stdout_filtered.contains("funcFromB"),
        "expected funcFromB to be filtered out, got:\n{stdout_filtered}"
    );
    assert!(
        stdout_filtered.contains("funcFromA2"),
        "expected funcFromA2 in filtered output, got:\n{stdout_filtered}"
    );

    // Cleanup
    let _ = fs::remove_dir_all(&tmp_dir);
}

/// Test that --source-file with space-separated syntax works
#[test]
fn cli_source_file_space_separated() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let tmp_dir = std::env::temp_dir().join("tswift_test_source_file_space");
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).expect("create temp dir");

    let bundle_file = tmp_dir.join("source_space_test.json");
    let bundle_content = r#"[
  {
    "function_name": "funcX",
    "source_file": "x.swift",
    "source_line": 1,
    "spec": null,
    "auto_vcs": []
  },
  {
    "function_name": "funcY",
    "source_file": "y.swift",
    "source_line": 1,
    "spec": null,
    "auto_vcs": []
  }
]"#;
    fs::write(&bundle_file, bundle_content).expect("write bundle");

    let output = Command::new(bin)
        .arg("--source-file")
        .arg("x.swift")
        .arg(&bundle_file)
        .output()
        .expect("failed to run with space-separated source-file");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("funcX"),
        "expected funcX with space-separated --source-file, got:\n{stdout}"
    );
    assert!(
        !stdout.contains("funcY"),
        "expected funcY filtered with space-separated --source-file, got:\n{stdout}"
    );

    // Cleanup
    let _ = fs::remove_dir_all(&tmp_dir);
}

/// Test that --incremental without --cache-dir uses default location
#[test]
fn cli_incremental_default_cache_location() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let tmp_dir = std::env::temp_dir().join("tswift_test_incremental_default_loc");
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).expect("create temp dir");

    let sil_file = tmp_dir.join("default_loc_test.sil");
    let sil_content = r"
sil_stage canonical

sil [ossa] @defaultLoc : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
";
    fs::write(&sil_file, sil_content).expect("write test sil");

    let output = Command::new(bin)
        .arg("--sil")
        .arg("--incremental")
        .arg(&sil_file)
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.code().is_some(),
        "expected command to complete"
    );

    // Default cache should be in .tswift_cache subdirectory of the source file's directory
    let default_cache_dir = tmp_dir.join(".tswift_cache");
    assert!(
        default_cache_dir.exists(),
        "expected default cache directory at {default_cache_dir:?}"
    );

    let cache_file = default_cache_dir.join("default_loc_test.sil.cache.json");
    assert!(cache_file.exists(), "expected cache file at {cache_file:?}");

    // Cleanup
    let _ = fs::remove_dir_all(&tmp_dir);
}

/// Test that --cache-dir creates the directory if it doesn't exist
#[test]
fn cli_cache_dir_creates_nonexistent_directory() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let tmp_dir = std::env::temp_dir().join("tswift_test_cache_dir_create");
    let nested_cache = tmp_dir.join("nested").join("deep").join("cache");
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir).expect("create temp dir");

    // Ensure nested directory doesn't exist
    assert!(
        !nested_cache.exists(),
        "nested cache dir should not exist initially"
    );

    let sil_file = tmp_dir.join("create_dir_test.sil");
    let sil_content = r"
sil_stage canonical

sil [ossa] @createDirTest : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
";
    fs::write(&sil_file, sil_content).expect("write test sil");

    let output = Command::new(bin)
        .arg("--sil")
        .arg("--incremental")
        .arg(format!("--cache-dir={}", nested_cache.display()))
        .arg(&sil_file)
        .output()
        .expect("failed to run tswift-verify");

    assert!(
        output.status.code().is_some(),
        "expected command to complete"
    );

    // Nested directory should now exist
    assert!(
        nested_cache.exists(),
        "expected nested cache directory to be created at {nested_cache:?}"
    );

    // Cleanup
    let _ = fs::remove_dir_all(&tmp_dir);
}
