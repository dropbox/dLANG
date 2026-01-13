#!/bin/bash
# Verification attributes pipeline test
# Tests that @_requires, @_ensures, @_invariant, @_trusted survive
# through parsing, semantic analysis, and SIL generation
#
# Run: ./tests/verification_attrs_pipeline_test.sh
# Exit code 0 = success, 1 = failure

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TSWIFT_ROOT="$(dirname "$SCRIPT_DIR")"

# Colors for output (disabled in non-TTY environments)
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

USE_COLOR=1
if [ -n "${NO_COLOR:-}" ] || [ ! -t 1 ] || [ "${TERM:-}" = "dumb" ]; then
    USE_COLOR=0
fi

if [ "$USE_COLOR" -eq 0 ]; then
    RED=''
    GREEN=''
    NC=''
fi

# Unicode symbols (use ASCII fallbacks when not in TTY or when NO_COLOR set)
CHECK_MARK="[OK]"
CROSS_MARK="[FAIL]"
if [ "$USE_COLOR" -eq 1 ]; then
    CHECK_MARK="✓"
    CROSS_MARK="✗"
fi

# Find swiftc
SWIFTC="${SWIFTC:-$HOME/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-$(uname -m)/bin/swiftc}"

if [[ ! -x "$SWIFTC" ]]; then
    echo "ERROR: swiftc not found at $SWIFTC"
    echo "Set SWIFTC environment variable to point to the built compiler"
    exit 1
fi

echo "Using swiftc: $SWIFTC"
echo ""

PASS=0
FAIL=0

pass() { ((PASS++)); echo -e "${GREEN}${CHECK_MARK}${NC} $1"; }
fail() { ((FAIL++)); echo -e "${RED}${CROSS_MARK}${NC} $1"; }

# Test 1: Parse and typecheck valid attributes
echo "=== Test 1: Parse and typecheck valid attributes ==="
if "$SWIFTC" -frontend -typecheck "$SCRIPT_DIR/verification_attrs_test.swift" 2>/dev/null; then
    pass "Valid attributes parse and typecheck"
else
    fail "Valid attributes should parse and typecheck"
fi

# Test 2: AST contains attributes
echo ""
echo "=== Test 2: AST contains attributes ==="
AST_OUTPUT=$("$SWIFTC" -frontend -dump-ast "$SCRIPT_DIR/verification_attrs_test.swift" 2>&1)

if echo "$AST_OUTPUT" | grep -q "_requires_attr"; then
    pass "@_requires survives to AST"
else
    fail "@_requires missing from AST"
fi

if echo "$AST_OUTPUT" | grep -q "_ensures_attr"; then
    pass "@_ensures survives to AST"
else
    fail "@_ensures missing from AST"
fi

if echo "$AST_OUTPUT" | grep -q "_invariant_attr"; then
    pass "@_invariant survives to AST"
else
    fail "@_invariant missing from AST"
fi

# Test 3: SIL contains attributes
echo ""
echo "=== Test 3: SIL contains attributes ==="
SDK_PATH=$(xcrun --show-sdk-path 2>/dev/null || echo "")
SDK_ARGS=()
[[ -n "$SDK_PATH" ]] && SDK_ARGS=(-sdk "$SDK_PATH")

SIL_OUTPUT=$("$SWIFTC" -frontend -emit-sil "${SDK_ARGS[@]}" "$SCRIPT_DIR/verification_attrs_test.swift" 2>&1)

if echo "$SIL_OUTPUT" | grep -q '@_requires("x > 0")'; then
    pass "@_requires survives to SIL"
else
    fail "@_requires missing from SIL"
fi

if echo "$SIL_OUTPUT" | grep -q '@_ensures("result >= 0")'; then
    pass "@_ensures survives to SIL"
else
    fail "@_ensures missing from SIL"
fi

if echo "$SIL_OUTPUT" | grep -q '@_invariant("count >= 0")'; then
    pass "@_invariant survives to SIL"
else
    fail "@_invariant missing from SIL"
fi

if echo "$SIL_OUTPUT" | grep -q '@_trusted'; then
    pass "@_trusted survives to SIL"
else
    fail "@_trusted missing from SIL"
fi

# Test 4: Diagnostics for malformed attributes
echo ""
echo "=== Test 4: Diagnostics for malformed attributes ==="
DIAG_OUTPUT=$("$SWIFTC" -frontend -typecheck "$SCRIPT_DIR/verification_attrs_malformed.swift" 2>&1 || true)

if echo "$DIAG_OUTPUT" | grep -q "expected '(' in '_requires' attribute"; then
    pass "Missing paren diagnostic"
else
    fail "Missing paren diagnostic not found"
fi

if echo "$DIAG_OUTPUT" | grep -q "expected string literal in '_requires' attribute"; then
    pass "Wrong type diagnostic"
else
    fail "Wrong type diagnostic not found"
fi

if echo "$DIAG_OUTPUT" | grep -q "cannot be an interpolated string literal"; then
    pass "Interpolation diagnostic"
else
    fail "Interpolation diagnostic not found"
fi

# Test 5: Diagnostics for wrong declaration type
echo ""
echo "=== Test 5: Diagnostics for wrong declaration type ==="
WRONG_DECL_OUTPUT=$("$SWIFTC" -frontend -typecheck "$SCRIPT_DIR/verification_attrs_wrong_decl.swift" 2>&1 || true)

if echo "$WRONG_DECL_OUTPUT" | grep -q "'@_requires' attribute cannot be applied to this declaration"; then
    pass "@_requires on var rejected"
else
    fail "@_requires on var should be rejected"
fi

if echo "$WRONG_DECL_OUTPUT" | grep -q "'@_ensures' attribute cannot be applied to this declaration"; then
    pass "@_ensures on struct rejected"
else
    fail "@_ensures on struct should be rejected"
fi

if echo "$WRONG_DECL_OUTPUT" | grep -q "'@_invariant' attribute cannot be applied to this declaration"; then
    pass "@_invariant on func rejected"
else
    fail "@_invariant on func should be rejected"
fi

# Summary
echo ""
echo "=== Summary ==="
echo "Passed: $PASS"
echo "Failed: $FAIL"

if [[ $FAIL -eq 0 ]]; then
    echo ""
    echo "All tests passed!"
    exit 0
else
    echo ""
    echo "Some tests failed!"
    exit 1
fi
