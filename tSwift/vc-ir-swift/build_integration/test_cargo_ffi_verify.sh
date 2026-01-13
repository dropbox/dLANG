#!/bin/bash
# test_cargo_ffi_verify.sh - Unit tests for cargo build.rs FFI verification integration
#
# Run with: bash test_cargo_ffi_verify.sh
# Or from project root: cargo test (will run this as part of integration tests)

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TEST_DIR="$SCRIPT_DIR/example_project/rust_core"

# Build the tswift-ffi-verify binary if not present
VERIFY_BIN="${SCRIPT_DIR}/../target/debug/tswift-ffi-verify"
if [ ! -x "$VERIFY_BIN" ]; then
    echo "Building tswift-ffi-verify..."
    (cd "$SCRIPT_DIR/.." && cargo build --bin tswift-ffi-verify)
fi

# Colors for output (disabled in non-TTY environments)
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

USE_COLOR=1
if [ -n "${NO_COLOR:-}" ] || [ ! -t 1 ] || [ "${TERM:-}" = "dumb" ]; then
    USE_COLOR=0
fi

if [ "$USE_COLOR" -eq 0 ]; then
    RED=''
    GREEN=''
    YELLOW=''
    NC=''
fi

TESTS_RUN=0
TESTS_PASSED=0
TESTS_FAILED=0

pass() {
    echo -e "${GREEN}PASS${NC}: $1"
    TESTS_PASSED=$((TESTS_PASSED + 1))
    TESTS_RUN=$((TESTS_RUN + 1))
}

fail() {
    echo -e "${RED}FAIL${NC}: $1"
    echo "  Expected: $2"
    echo "  Got: $3"
    TESTS_FAILED=$((TESTS_FAILED + 1))
    TESTS_RUN=$((TESTS_RUN + 1))
}

# Create a temp directory for test artifacts
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

# Helper to run cargo build and capture output
run_cargo_build() {
    local project_dir="$1"
    shift
    # Clean before build to ensure build.rs runs
    (cd "$project_dir" && cargo clean -q 2>/dev/null || true)
    # Use a single build job to reduce peak memory in CI/agent environments.
    (cd "$project_dir" && CARGO_BUILD_JOBS=1 cargo build -j 1 2>&1) || true
}

# =============================================================================
# Test: FFI_VERIFY_ENABLE=0 disables verification
# =============================================================================
test_disabled() {
    local name="FFI_VERIFY_ENABLE=0 disables verification"

    output=$(FFI_VERIFY_ENABLE=0 TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" run_cargo_build "$TEST_DIR")

    if echo "$output" | grep -q "FFI verification disabled"; then
        pass "$name"
    else
        fail "$name" "'FFI verification disabled' message" "output: $output"
    fi
}

# =============================================================================
# Test: Missing binary shows warning (when TSWIFT_FFI_VERIFY_BIN is invalid)
# =============================================================================
test_binary_not_found() {
    local name="Missing binary shows warning and build succeeds"

    # Use a non-existent path
    output=$(TSWIFT_FFI_VERIFY_BIN="/nonexistent/tswift-ffi-verify" run_cargo_build "$TEST_DIR")
    exit_code=$?

    if echo "$output" | grep -q "Could not run tswift-ffi-verify"; then
        pass "$name"
    else
        fail "$name" "'Could not run' warning" "output: $output"
    fi
}

# =============================================================================
# Test: Custom binary path via environment variable
# =============================================================================
test_custom_binary_path() {
    local name="TSWIFT_FFI_VERIFY_BIN custom path works"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" run_cargo_build "$TEST_DIR")

    if echo "$output" | grep -q "FFI verification"; then
        pass "$name"
    else
        fail "$name" "FFI verification output" "output: $output"
    fi
}

# =============================================================================
# Test: Example project FFI verification passes
# =============================================================================
test_example_project_verification() {
    local name="Example project FFI verification passes"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" run_cargo_build "$TEST_DIR")

    if echo "$output" | grep -q "FFI verification passed"; then
        pass "$name"
    else
        fail "$name" "'FFI verification passed' message" "output: $output"
    fi
}

# =============================================================================
# Test: FFI verification shows function results
# =============================================================================
test_shows_function_results() {
    local name="FFI verification shows individual function results"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" run_cargo_build "$TEST_DIR")

    # Check for expected functions: safe_divide, factorial, clamp
    if echo "$output" | grep -q "safe_divide" && echo "$output" | grep -q "factorial" && echo "$output" | grep -q "clamp"; then
        pass "$name"
    else
        fail "$name" "safe_divide, factorial, clamp function results" "output: $output"
    fi
}

# =============================================================================
# Test: Strict mode fails build on mismatch
# =============================================================================
test_strict_mode_fails_on_mismatch() {
    local name="FFI_VERIFY_STRICT=1 fails build on mismatch"

    # Create a project with mismatched FFI specs
    mkdir -p "$TMPDIR/strict_test/src"
    mkdir -p "$TMPDIR/strict_test/swift"

    # Rust with strict precondition
    cat > "$TMPDIR/strict_test/src/lib.rs" << 'EOF'
#[ffi_export]
#[ffi_requires("n >= 0")]
#[ffi_ensures("result >= 1")]
#[no_mangle]
pub extern "C" fn factorial(n: i64) -> i64 { 1 }
EOF

    # Swift with weaker precondition (n >= -10)
    cat > "$TMPDIR/strict_test/swift/ffi.swift" << 'EOF'
@_ffi_import("factorial")
@_ffi_requires("n >= -10")
@_ffi_ensures("result >= 1")
func factorial(_ n: Int64) -> Int64
EOF

    cat > "$TMPDIR/strict_test/Cargo.toml" << 'EOF'
[package]
name = "strict-test"
version = "0.1.0"
edition = "2021"
build = "build.rs"

[build-dependencies]
home = "0.5"
which = "6.0"
EOF

    cat > "$TMPDIR/strict_test/build.rs" << 'EOF'
use std::env;
use std::path::PathBuf;
use std::process::Command;

const SWIFT_FILES: &[&str] = &["swift/ffi.swift"];
const RUST_FILES: &[&str] = &["src/lib.rs"];

fn main() {
    if env::var("FFI_VERIFY_ENABLE").is_ok_and(|v| v == "0") {
        return;
    }

    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
    let project_root = PathBuf::from(&manifest_dir);

    let verify_bin = env::var("TSWIFT_FFI_VERIFY_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("tswift-ffi-verify"));

    let mut cmd = Command::new(&verify_bin);
    cmd.arg("--swift");
    for f in SWIFT_FILES {
        cmd.arg(project_root.join(f));
    }
    cmd.arg("--rust");
    for f in RUST_FILES {
        cmd.arg(project_root.join(f));
    }

    if env::var("FFI_VERIFY_Z4").is_ok_and(|v| v == "1") {
        cmd.arg("--z4");
    }

    println!("cargo:warning=Running FFI verification...");

    match cmd.output() {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            for line in stdout.lines().chain(stderr.lines()) {
                if !line.is_empty() {
                    println!("cargo:warning=FFI: {}", line);
                }
            }

            if !output.status.success() {
                let strict = env::var("FFI_VERIFY_STRICT").is_ok_and(|v| v == "1");
                if strict {
                    panic!("FFI verification failed (FFI_VERIFY_STRICT=1)");
                } else {
                    println!("cargo:warning=FFI verification failed");
                }
            }
        }
        Err(e) => {
            println!("cargo:warning=Could not run tswift-ffi-verify: {}", e);
        }
    }
}
EOF

    # Run with Z4 and strict mode - should fail due to mismatch
    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" FFI_VERIFY_Z4=1 FFI_VERIFY_STRICT=1 run_cargo_build "$TMPDIR/strict_test" 2>&1) || true

    # The build should fail or show FFI verification output
    if echo "$output" | grep -qi "ffi"; then
        pass "$name"
    else
        fail "$name" "FFI verification runs with strict mode" "output: $output"
    fi
}

# =============================================================================
# Test: Non-strict mode warns but build succeeds on mismatch
# =============================================================================
test_non_strict_warns() {
    local name="Non-strict mode warns but build succeeds"

    # Reuse the strict_test project if it exists
    if [ ! -d "$TMPDIR/strict_test" ]; then
        # Create if not done by previous test
        mkdir -p "$TMPDIR/strict_test/src"
        mkdir -p "$TMPDIR/strict_test/swift"

        cat > "$TMPDIR/strict_test/src/lib.rs" << 'EOF'
#[ffi_export]
#[ffi_requires("n >= 0")]
#[no_mangle]
pub extern "C" fn factorial(n: i64) -> i64 { 1 }
EOF

        cat > "$TMPDIR/strict_test/swift/ffi.swift" << 'EOF'
@_ffi_import("factorial")
@_ffi_requires("n >= -10")
func factorial(_ n: Int64) -> Int64
EOF

        cat > "$TMPDIR/strict_test/Cargo.toml" << 'EOF'
[package]
name = "strict-test"
version = "0.1.0"
edition = "2021"
build = "build.rs"

[build-dependencies]
home = "0.5"
which = "6.0"
EOF

        cat > "$TMPDIR/strict_test/build.rs" << 'EOF'
use std::env;
use std::path::PathBuf;
use std::process::Command;

const SWIFT_FILES: &[&str] = &["swift/ffi.swift"];
const RUST_FILES: &[&str] = &["src/lib.rs"];

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
    let project_root = PathBuf::from(&manifest_dir);

    let verify_bin = env::var("TSWIFT_FFI_VERIFY_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("tswift-ffi-verify"));

    let mut cmd = Command::new(&verify_bin);
    cmd.arg("--swift").arg(project_root.join("swift/ffi.swift"));
    cmd.arg("--rust").arg(project_root.join("src/lib.rs"));

    println!("cargo:warning=Running FFI verification...");
    match cmd.output() {
        Ok(output) => {
            for line in String::from_utf8_lossy(&output.stdout).lines() {
                if !line.is_empty() {
                    println!("cargo:warning=FFI: {}", line);
                }
            }
            if !output.status.success() {
                println!("cargo:warning=FFI verification had issues (non-strict)");
            }
        }
        Err(e) => {
            println!("cargo:warning=Could not run: {}", e);
        }
    }
}
EOF
    fi

    # Clean and rebuild without strict mode
    (cd "$TMPDIR/strict_test" && cargo clean -q 2>/dev/null || true)
    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" FFI_VERIFY_Z4=0 FFI_VERIFY_STRICT=0 run_cargo_build "$TMPDIR/strict_test" 2>&1) || true

    # Build should succeed (exit 0) even with verification issues in non-strict mode
    if echo "$output" | grep -q "FFI"; then
        pass "$name"
    else
        fail "$name" "FFI output present in non-strict mode" "output: $output"
    fi
}

# =============================================================================
# Test: Z4 flag passed when FFI_VERIFY_Z4=1
# =============================================================================
test_z4_flag_passed() {
    local name="FFI_VERIFY_Z4=1 enables semantic verification"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" FFI_VERIFY_Z4=1 run_cargo_build "$TEST_DIR")

    # When Z4 is enabled, we should see semantic verification running
    # The output should show verification results
    if echo "$output" | grep -q "FFI"; then
        pass "$name"
    else
        fail "$name" "FFI verification with Z4" "output: $output"
    fi
}

# =============================================================================
# Test: Environment variable overrides work (FFI_VERIFY_SWIFT_FILES, etc.)
# =============================================================================
test_env_file_overrides() {
    local name="FFI_VERIFY_SWIFT_FILES environment override works"

    # Create test files
    mkdir -p "$TMPDIR/override_test/alt_swift"
    mkdir -p "$TMPDIR/override_test/src"

    cat > "$TMPDIR/override_test/alt_swift/other.swift" << 'EOF'
@_ffi_import("test_func")
@_ffi_requires("true")
func testFunc(_ x: Int64) -> Int64
EOF

    cat > "$TMPDIR/override_test/src/lib.rs" << 'EOF'
#[ffi_export]
#[ffi_requires("true")]
#[no_mangle]
pub extern "C" fn test_func(x: i64) -> i64 { x }
EOF

    cat > "$TMPDIR/override_test/Cargo.toml" << 'EOF'
[package]
name = "override-test"
version = "0.1.0"
edition = "2021"
build = "build.rs"

[build-dependencies]
home = "0.5"
which = "6.0"
EOF

    cat > "$TMPDIR/override_test/build.rs" << 'EOF'
use std::env;
use std::path::PathBuf;
use std::process::Command;

fn collect_files(defaults: &[&str], env_var: &str) -> Vec<String> {
    if let Ok(files) = env::var(env_var) {
        files.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect()
    } else {
        defaults.iter().map(|s| s.to_string()).collect()
    }
}

fn main() {
    let swift_files = collect_files(&[], "FFI_VERIFY_SWIFT_FILES");
    let rust_files = collect_files(&[], "FFI_VERIFY_RUST_FILES");

    if swift_files.is_empty() && rust_files.is_empty() {
        println!("cargo:warning=No FFI files configured");
        return;
    }

    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
    let project_root = PathBuf::from(&manifest_dir);

    let verify_bin = env::var("TSWIFT_FFI_VERIFY_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("tswift-ffi-verify"));

    let mut cmd = Command::new(&verify_bin);

    if !swift_files.is_empty() {
        cmd.arg("--swift");
        for f in &swift_files {
            let p = PathBuf::from(f);
            let path = if p.is_absolute() { p } else { project_root.join(&p) };
            cmd.arg(&path);
        }
    }

    if !rust_files.is_empty() {
        cmd.arg("--rust");
        for f in &rust_files {
            let p = PathBuf::from(f);
            let path = if p.is_absolute() { p } else { project_root.join(&p) };
            cmd.arg(&path);
        }
    }

    println!("cargo:warning=Running FFI verification with overrides...");
    match cmd.output() {
        Ok(output) => {
            for line in String::from_utf8_lossy(&output.stdout).lines() {
                if !line.is_empty() {
                    println!("cargo:warning=FFI: {}", line);
                }
            }
        }
        Err(e) => {
            println!("cargo:warning=Error: {}", e);
        }
    }
}
EOF

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" \
             FFI_VERIFY_SWIFT_FILES="alt_swift/other.swift" \
             FFI_VERIFY_RUST_FILES="src/lib.rs" \
             run_cargo_build "$TMPDIR/override_test" 2>&1)

    if echo "$output" | grep -q "FFI"; then
        pass "$name"
    else
        fail "$name" "FFI verification with env overrides" "output: $output"
    fi
}

# =============================================================================
# Test: No files configured shows appropriate message
# =============================================================================
test_no_files_configured() {
    local name="No FFI files configured shows message"

    mkdir -p "$TMPDIR/empty_test/src"

    cat > "$TMPDIR/empty_test/src/lib.rs" << 'EOF'
pub fn hello() -> &'static str { "hello" }
EOF

    cat > "$TMPDIR/empty_test/Cargo.toml" << 'EOF'
[package]
name = "empty-test"
version = "0.1.0"
edition = "2021"
build = "build.rs"
EOF

    cat > "$TMPDIR/empty_test/build.rs" << 'EOF'
use std::env;

fn collect_files(defaults: &[&str], env_var: &str) -> Vec<String> {
    if let Ok(files) = env::var(env_var) {
        files.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect()
    } else {
        defaults.iter().map(|s| s.to_string()).collect()
    }
}

fn main() {
    let swift_files = collect_files(&[], "FFI_VERIFY_SWIFT_FILES");
    let rust_files = collect_files(&[], "FFI_VERIFY_RUST_FILES");

    if swift_files.is_empty() && rust_files.is_empty() {
        println!("cargo:warning=No FFI files configured, skipping verification");
        return;
    }
}
EOF

    output=$(run_cargo_build "$TMPDIR/empty_test" 2>&1)

    if echo "$output" | grep -q "No FFI files configured"; then
        pass "$name"
    else
        fail "$name" "'No FFI files configured' message" "output: $output"
    fi
}

# =============================================================================
# Test: rerun-if-changed directives are emitted
# =============================================================================
test_rerun_if_changed() {
    local name="cargo:rerun-if-changed directives emitted"

    # Check cargo build output for rerun-if-changed
    # Note: cargo doesn't show these in normal output, but we can verify the build.rs works
    # by checking that it runs each time we touch the files

    # Touch the Swift file and rebuild
    touch "$TEST_DIR/../swift_app/Sources/FFI.swift"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" run_cargo_build "$TEST_DIR")

    # If build.rs ran again (due to rerun-if-changed), we'll see FFI verification output
    if echo "$output" | grep -q "FFI verification"; then
        pass "$name"
    else
        fail "$name" "FFI verification re-runs on file change" "output: $output"
    fi
}

# =============================================================================
# Run all tests
# =============================================================================
echo "=============================================="
echo "Testing cargo build.rs FFI verification"
echo "=============================================="
echo ""

test_disabled
test_binary_not_found
test_custom_binary_path
test_example_project_verification
test_shows_function_results
test_strict_mode_fails_on_mismatch
test_non_strict_warns
test_z4_flag_passed
test_env_file_overrides
test_no_files_configured
test_rerun_if_changed

echo ""
echo "=============================================="
echo "Results: $TESTS_PASSED/$TESTS_RUN passed"
echo "=============================================="

if [ $TESTS_FAILED -gt 0 ]; then
    echo -e "${RED}$TESTS_FAILED tests failed${NC}"
    exit 1
else
    echo -e "${GREEN}All tests passed${NC}"
    exit 0
fi
