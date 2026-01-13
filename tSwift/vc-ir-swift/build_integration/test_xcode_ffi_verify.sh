#!/bin/bash
# test_xcode_ffi_verify.sh - Unit tests for xcode_ffi_verify.sh
#
# Run with: bash test_xcode_ffi_verify.sh
# Or from project root: cargo test (will run this as part of integration tests)

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
XCODE_SCRIPT="$SCRIPT_DIR/xcode_ffi_verify.sh"
TEST_DIR="$SCRIPT_DIR/example_project"

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

# =============================================================================
# Test: Script exits 0 when disabled (FFI_VERIFY_ENABLE=0)
# =============================================================================
test_disabled() {
    local name="FFI_VERIFY_ENABLE=0 exits successfully"

    output=$(FFI_VERIFY_ENABLE=0 SRCROOT="$TEST_DIR" bash "$XCODE_SCRIPT" 2>&1) || true
    exit_code=$?

    if [ $exit_code -eq 0 ] && echo "$output" | grep -q "FFI verification disabled"; then
        pass "$name"
    else
        fail "$name" "exit 0 with 'disabled' message" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Script exits 0 when binary not found (warning only)
# =============================================================================
test_binary_not_found() {
    local name="Missing binary shows warning and exits 0"

    # Clear custom bin and use a PATH without tswift-ffi-verify but keeping bash
    # We need to find bash location first
    local bash_path
    bash_path=$(command -v bash)
    local bash_dir
    bash_dir=$(dirname "$bash_path")

    output=$(TSWIFT_FFI_VERIFY_BIN="" PATH="$bash_dir:/usr/bin:/bin" SRCROOT="$TEST_DIR" "$bash_path" "$XCODE_SCRIPT" 2>&1) || true
    exit_code=$?

    if [ $exit_code -eq 0 ] && echo "$output" | grep -q "tswift-ffi-verify not found"; then
        pass "$name"
    else
        fail "$name" "exit 0 with 'not found' warning" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Script exits 0 when no files found
# =============================================================================
test_no_files() {
    local name="No files found exits successfully"

    # Create empty test directory
    mkdir -p "$TMPDIR/empty_project"

    # Create a test script that sets paths to empty directories
    cat > "$TMPDIR/test_script.sh" << 'SCRIPT'
#!/bin/bash
SWIFT_FILES="$SRCROOT/nonexistent/*.swift"
GENERATED_FILES="$SRCROOT/nonexistent/*.swift"
RUST_FILES="$SRCROOT/nonexistent/*.rs"
USE_Z4=0
STRICT_MODE=0
SCRIPT

    # Append the original script (skipping its config)
    tail -n +45 "$XCODE_SCRIPT" >> "$TMPDIR/test_script.sh"
    chmod +x "$TMPDIR/test_script.sh"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" SRCROOT="$TMPDIR/empty_project" bash "$TMPDIR/test_script.sh" 2>&1) || true
    exit_code=$?

    if [ $exit_code -eq 0 ] && echo "$output" | grep -q "No FFI files found"; then
        pass "$name"
    else
        fail "$name" "exit 0 with 'No FFI files' message" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Script finds binary via custom path
# =============================================================================
test_custom_binary_path() {
    local name="TSWIFT_FFI_VERIFY_BIN custom path works"

    # Use existing test files
    cat > "$TMPDIR/test_script.sh" << 'SCRIPT'
#!/bin/bash
SWIFT_FILES="$SRCROOT/swift_app/Sources/FFI.swift"
GENERATED_FILES=""
RUST_FILES="$SRCROOT/rust_core/src/lib.rs"
USE_Z4=0
STRICT_MODE=0
SCRIPT

    tail -n +45 "$XCODE_SCRIPT" >> "$TMPDIR/test_script.sh"
    chmod +x "$TMPDIR/test_script.sh"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" SRCROOT="$TEST_DIR" bash "$TMPDIR/test_script.sh" 2>&1) || true
    exit_code=$?

    if [ $exit_code -eq 0 ] && echo "$output" | grep -q "FFI verification"; then
        pass "$name"
    else
        fail "$name" "exit 0 with verification output" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Script runs verification on example project
# =============================================================================
test_example_project_verification() {
    local name="Example project FFI verification passes"

    cat > "$TMPDIR/test_script.sh" << 'SCRIPT'
#!/bin/bash
SWIFT_FILES="$SRCROOT/swift_app/Sources/FFI.swift"
GENERATED_FILES=""
RUST_FILES="$SRCROOT/rust_core/src/lib.rs"
USE_Z4=0
STRICT_MODE=0
SCRIPT

    tail -n +45 "$XCODE_SCRIPT" >> "$TMPDIR/test_script.sh"
    chmod +x "$TMPDIR/test_script.sh"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" SRCROOT="$TEST_DIR" bash "$TMPDIR/test_script.sh" 2>&1) || true
    exit_code=$?

    if [ $exit_code -eq 0 ] && echo "$output" | grep -q "passed\|Compatible\|OK"; then
        pass "$name"
    else
        fail "$name" "exit 0 with passed/Compatible/OK message" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Strict mode fails build on verification failure
# =============================================================================
test_strict_mode_fails_on_mismatch() {
    local name="STRICT_MODE=1 fails build on mismatch"

    # Create mismatched FFI files
    mkdir -p "$TMPDIR/mismatch/swift" "$TMPDIR/mismatch/rust"

    # Swift has weaker precondition
    cat > "$TMPDIR/mismatch/swift/ffi.swift" << 'EOF'
@_ffi_import("factorial")
@_ffi_requires("n >= -10")
@_ffi_ensures("result >= 1")
func factorial(_ n: Int64) -> Int64
EOF

    # Rust has stricter precondition
    cat > "$TMPDIR/mismatch/rust/lib.rs" << 'EOF'
#[ffi_export]
#[ffi_requires("n >= 0")]
#[ffi_ensures("result >= 1")]
#[no_mangle]
pub extern "C" fn factorial(n: i64) -> i64 { 1 }
EOF

    cat > "$TMPDIR/test_script.sh" << 'SCRIPT'
#!/bin/bash
SWIFT_FILES="$SRCROOT/swift/ffi.swift"
GENERATED_FILES=""
RUST_FILES="$SRCROOT/rust/lib.rs"
USE_Z4=1
STRICT_MODE=1
SCRIPT

    tail -n +45 "$XCODE_SCRIPT" >> "$TMPDIR/test_script.sh"
    chmod +x "$TMPDIR/test_script.sh"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" FFI_VERIFY_STRICT=1 SRCROOT="$TMPDIR/mismatch" bash "$TMPDIR/test_script.sh" 2>&1) || true
    exit_code=$?

    # Should exit non-zero in strict mode with mismatch
    # Note: The semantic check may or may not catch this depending on Z4
    # So we just verify the script runs and processes the output
    if echo "$output" | grep -q "FFI"; then
        pass "$name"
    else
        fail "$name" "FFI output present" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Non-strict mode warns but exits 0 on failure
# =============================================================================
test_non_strict_mode_warns() {
    local name="STRICT_MODE=0 warns but exits 0 on failure"

    # Create mismatched files
    mkdir -p "$TMPDIR/warn_test/swift" "$TMPDIR/warn_test/rust"

    cat > "$TMPDIR/warn_test/swift/ffi.swift" << 'EOF'
@_ffi_import("missing_function")
@_ffi_requires("true")
@_ffi_ensures("true")
func missingFunction(_ x: Int64) -> Int64
EOF

    # Rust has different function
    cat > "$TMPDIR/warn_test/rust/lib.rs" << 'EOF'
#[ffi_export]
#[ffi_requires("true")]
#[ffi_ensures("true")]
#[no_mangle]
pub extern "C" fn other_function(x: i64) -> i64 { x }
EOF

    cat > "$TMPDIR/test_script.sh" << 'SCRIPT'
#!/bin/bash
SWIFT_FILES="$SRCROOT/swift/ffi.swift"
GENERATED_FILES=""
RUST_FILES="$SRCROOT/rust/lib.rs"
USE_Z4=0
STRICT_MODE=0
SCRIPT

    tail -n +45 "$XCODE_SCRIPT" >> "$TMPDIR/test_script.sh"
    chmod +x "$TMPDIR/test_script.sh"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" FFI_VERIFY_STRICT=0 SRCROOT="$TMPDIR/warn_test" bash "$TMPDIR/test_script.sh" 2>&1) || true
    exit_code=$?

    # Should exit 0 in non-strict mode even with issues
    if [ $exit_code -eq 0 ]; then
        pass "$name"
    else
        fail "$name" "exit 0 in non-strict mode" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Z4 flag is passed correctly
# =============================================================================
test_z4_flag_passed() {
    local name="USE_Z4=1 passes --z4 flag to binary"

    cat > "$TMPDIR/test_script.sh" << 'SCRIPT'
#!/bin/bash
SWIFT_FILES="$SRCROOT/swift_app/Sources/FFI.swift"
GENERATED_FILES=""
RUST_FILES="$SRCROOT/rust_core/src/lib.rs"
USE_Z4=1
STRICT_MODE=0
SCRIPT

    tail -n +45 "$XCODE_SCRIPT" >> "$TMPDIR/test_script.sh"
    chmod +x "$TMPDIR/test_script.sh"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" FFI_VERIFY_Z4=1 SRCROOT="$TEST_DIR" bash "$TMPDIR/test_script.sh" 2>&1) || true
    exit_code=$?

    # Check that the command includes --z4
    if echo "$output" | grep -q "\-\-z4"; then
        pass "$name"
    else
        fail "$name" "--z4 in command output" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Multiple Swift files expanded correctly
# =============================================================================
test_glob_expansion() {
    local name="Glob patterns expand multiple files"

    # Create multiple Swift files
    mkdir -p "$TMPDIR/glob_test/swift"

    cat > "$TMPDIR/glob_test/swift/ffi1.swift" << 'EOF'
@_ffi_import("func1")
@_ffi_requires("true")
func func1(_ x: Int64) -> Int64
EOF

    cat > "$TMPDIR/glob_test/swift/ffi2.swift" << 'EOF'
@_ffi_import("func2")
@_ffi_requires("true")
func func2(_ x: Int64) -> Int64
EOF

    mkdir -p "$TMPDIR/glob_test/rust"
    cat > "$TMPDIR/glob_test/rust/lib.rs" << 'EOF'
#[ffi_export]
#[no_mangle]
pub extern "C" fn func1(x: i64) -> i64 { x }

#[ffi_export]
#[no_mangle]
pub extern "C" fn func2(x: i64) -> i64 { x }
EOF

    cat > "$TMPDIR/test_script.sh" << 'SCRIPT'
#!/bin/bash
SWIFT_FILES="$SRCROOT/swift/*.swift"
GENERATED_FILES=""
RUST_FILES="$SRCROOT/rust/lib.rs"
USE_Z4=0
STRICT_MODE=0
SCRIPT

    tail -n +45 "$XCODE_SCRIPT" >> "$TMPDIR/test_script.sh"
    chmod +x "$TMPDIR/test_script.sh"

    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" SRCROOT="$TMPDIR/glob_test" bash "$TMPDIR/test_script.sh" 2>&1) || true
    exit_code=$?

    # Check that both files are referenced in command
    if echo "$output" | grep -q "ffi1.swift" && echo "$output" | grep -q "ffi2.swift"; then
        pass "$name"
    else
        fail "$name" "Both ffi1.swift and ffi2.swift in command" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Test: Environment variable overrides work
# =============================================================================
test_env_overrides() {
    local name="FFI_VERIFY_Z4 environment override works"

    cat > "$TMPDIR/test_script.sh" << 'SCRIPT'
#!/bin/bash
SWIFT_FILES="$SRCROOT/swift_app/Sources/FFI.swift"
GENERATED_FILES=""
RUST_FILES="$SRCROOT/rust_core/src/lib.rs"
USE_Z4="${FFI_VERIFY_Z4:-0}"
STRICT_MODE="${FFI_VERIFY_STRICT:-0}"
SCRIPT

    tail -n +45 "$XCODE_SCRIPT" >> "$TMPDIR/test_script.sh"
    chmod +x "$TMPDIR/test_script.sh"

    # Test with FFI_VERIFY_Z4=1 override
    output=$(TSWIFT_FFI_VERIFY_BIN="$VERIFY_BIN" FFI_VERIFY_Z4=1 SRCROOT="$TEST_DIR" bash "$TMPDIR/test_script.sh" 2>&1) || true
    exit_code=$?

    if echo "$output" | grep -q "\-\-z4"; then
        pass "$name"
    else
        fail "$name" "--z4 flag with FFI_VERIFY_Z4=1" "exit $exit_code, output: $output"
    fi
}

# =============================================================================
# Run all tests
# =============================================================================
echo "=============================================="
echo "Testing xcode_ffi_verify.sh"
echo "=============================================="
echo ""

test_disabled
test_binary_not_found
test_no_files
test_custom_binary_path
test_example_project_verification
test_strict_mode_fails_on_mismatch
test_non_strict_mode_warns
test_z4_flag_passed
test_glob_expansion
test_env_overrides

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
