//! Integration tests for tswift-verify --json-progress output.

use std::process::Command;

fn parse_json_lines(stderr: &str) -> Vec<serde_json::Value> {
    let mut values = Vec::new();
    for (i, line) in stderr.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let value: serde_json::Value = serde_json::from_str(line).unwrap_or_else(|e| {
            panic!(
                "stderr line {} is not valid JSON: {}\nline:\n{}",
                i + 1,
                e,
                line
            )
        });
        values.push(value);
    }
    values
}

#[test]
fn cli_json_progress_emits_events_and_stdout_is_json() {
    let bin = env!("CARGO_BIN_EXE_tswift-verify");
    let manifest_dir = env!("CARGO_MANIFEST_DIR");

    let output = Command::new(bin)
        .current_dir(manifest_dir)
        .arg("--sil")
        .arg("tests/sil_examples/add_overflow_unsafe.sil")
        .arg("--json")
        .arg("--json-progress")
        .output()
        .expect("failed to run tswift-verify --json-progress");

    // add_overflow_unsafe.sil is intentionally missing preconditions; it should fail verification.
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 (verification failure), got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let response: serde_json::Value = serde_json::from_str(&stdout).expect("stdout must be JSON");
    let contains_add = response
        .get("function_name")
        .and_then(|v| v.as_str())
        .is_some_and(|name| name == "add")
        || response
            .get("bundles")
            .and_then(|v| v.as_array())
            .is_some_and(|bundles| {
                bundles
                    .iter()
                    .any(|b| b.get("function_name").and_then(|v| v.as_str()) == Some("add"))
            });
    assert!(
        contains_add,
        "expected JSON response to include function 'add', got:\n{stdout}"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let events = parse_json_lines(&stderr);
    assert!(
        !events.is_empty(),
        "expected JSON progress events on stderr, got empty stderr"
    );

    let has_function_start = events.iter().any(|e| {
        e.get("event").and_then(|v| v.as_str()) == Some("function_start")
            && e.get("function").and_then(|v| v.as_str()) == Some("add")
    });
    assert!(has_function_start, "expected function_start for add");

    let has_vc_complete = events
        .iter()
        .any(|e| e.get("event").and_then(|v| v.as_str()) == Some("vc_complete"));
    assert!(has_vc_complete, "expected at least one vc_complete event");

    let has_function_complete = events.iter().any(|e| {
        e.get("event").and_then(|v| v.as_str()) == Some("function_complete")
            && e.get("function").and_then(|v| v.as_str()) == Some("add")
    });
    assert!(has_function_complete, "expected function_complete for add");

    let has_summary = events
        .iter()
        .any(|e| e.get("event").and_then(|v| v.as_str()) == Some("summary"));
    assert!(has_summary, "expected summary event");
}
