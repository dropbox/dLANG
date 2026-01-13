#!/bin/bash
#
# tRust Runtime Test Runner
#
# This script complements run_tests.sh by actually EXECUTING test binaries.
# While run_tests.sh verifies contracts at compile-time with -Zverify,
# this script runs the binaries to exercise runtime assertions (assert_eq!, etc.)
#
# Use this to catch runtime bugs that the verifier can't prove
# (e.g., ct_eq_bytes functions with array references).
#

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
UPSTREAM_SYSROOT="$SCRIPT_DIR/upstream/rustc/build/host/stage1"
DEFAULT_SYSROOT="$SCRIPT_DIR/build/host/stage1"
if [ -d "$UPSTREAM_SYSROOT" ]; then
    DEFAULT_SYSROOT="$UPSTREAM_SYSROOT"
fi
SYSROOT="${TRUST_SYSROOT:-$DEFAULT_SYSROOT}"
RUSTC="$SYSROOT/bin/rustc"

if [ ! -x "$RUSTC" ]; then
    echo "Error: rustc not found at $RUSTC" >&2
    exit 1
fi

# Tests that should be executed for runtime verification
# These have main() functions with assert_eq! and other runtime checks
RUNTIME_TESTS="real_validation_subtle_test real_validation_hex_test real_validation_base64_test"

count=0
passed=0
failed=0

echo "=== tRust Runtime Test Runner ==="
echo "Compiles tests WITHOUT -Zverify and EXECUTES the binaries"
echo ""

for name in $RUNTIME_TESTS; do
    f="$SCRIPT_DIR/examples/${name}.rs"

    if [ ! -f "$f" ]; then
        echo "$name: SKIP (file not found)"
        continue
    fi

    count=$((count+1))

    # Create temp directory for output
    tmpdir=$(mktemp -d "/tmp/trust_runtime_${name}_XXXXXX")
    binary="$tmpdir/test_binary"

    # Compile WITHOUT -Zverify (standard compilation for execution)
    compile_out=$($RUSTC --edition=2021 "$f" -o "$binary" 2>&1)
    compile_status=$?

    if [ $compile_status -ne 0 ]; then
        failed=$((failed+1))
        echo "$name: FAIL (compilation error)"
        echo "$compile_out" | head -5
        rm -rf "$tmpdir"
        continue
    fi

    # Execute the binary
    run_out=$("$binary" 2>&1)
    run_status=$?

    if [ $run_status -eq 0 ]; then
        passed=$((passed+1))
        echo "$name: PASS (runtime assertions passed)"
    else
        failed=$((failed+1))
        echo "$name: FAIL (runtime assertion failed, exit code $run_status)"
        echo "$run_out" | tail -10
    fi

    rm -rf "$tmpdir"
done

echo ""
echo "Runtime Results: $passed/$count passed, $failed failed"

if [ $failed -gt 0 ]; then
    exit 1
fi
exit 0
