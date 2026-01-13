#!/bin/bash
# Integration test for async state machine extraction (Phase 3 of DIRECTIVE_TLA_EXTRACT)
#
# This test:
# 1. Compiles tests/tla_extract_integration_test.rs with --extract-state-machines
# 2. Validates the JSON output
# 3. Checks that async functions are detected

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
TEST_FILE="$SCRIPT_DIR/tla_extract_integration_test.rs"
OUTPUT_FILE="/tmp/tla_extract_test_output.json"
OUTPUT_DIR="${OUTPUT_FILE%.json}_tla"

echo "=== TLA Extract Integration Test ==="
echo "Test file: $TEST_FILE"
echo "Output file: $OUTPUT_FILE"
echo "Output dir: $OUTPUT_DIR"
echo ""

# Clear cache to ensure fresh verification
"$ROOT_DIR/bin/trustc" --cache-clear > /dev/null 2>&1 || true
rm -f "$OUTPUT_FILE"
rm -rf "$OUTPUT_DIR"

# Run extraction
echo "Running extraction..."
"$ROOT_DIR/bin/trustc" --edition 2021 --extract-state-machines="$OUTPUT_FILE" "$TEST_FILE" 2>&1 | grep -v "^warning:" || true

# Check output file exists
if [ ! -f "$OUTPUT_FILE" ]; then
    echo "FAIL: Output file not created"
    exit 1
fi

# Validate JSON structure
echo ""
echo "Validating JSON output..."

# Check for required fields
if ! grep -q '"async_functions"' "$OUTPUT_FILE"; then
    echo "FAIL: Missing 'async_functions' field"
    exit 1
fi

if ! grep -q '"state_machines"' "$OUTPUT_FILE"; then
    echo "FAIL: Missing 'state_machines' field"
    exit 1
fi

# Extract async function count
ASYNC_COUNT=$(grep -o '"async_functions": [0-9]*' "$OUTPUT_FILE" | grep -o '[0-9]*')
echo "Detected $ASYNC_COUNT async function(s)"

if [ "$ASYNC_COUNT" -lt 3 ]; then
    echo "FAIL: Expected at least 3 async functions (simple_async, with_await, two_awaits)"
    echo "Output:"
    cat "$OUTPUT_FILE"
    exit 1
fi

# Check state machines have required fields
if ! grep -q '"version"' "$OUTPUT_FILE"; then
    echo "FAIL: State machines missing 'version' field"
    exit 1
fi

if ! grep -q '"transitions"' "$OUTPUT_FILE"; then
    echo "FAIL: State machines missing 'transitions' field"
    exit 1
fi

if ! grep -q '"initial_state"' "$OUTPUT_FILE"; then
    echo "FAIL: State machines missing 'initial_state' field"
    exit 1
fi

if ! grep -q '"terminal_states"' "$OUTPUT_FILE"; then
    echo "FAIL: State machines missing 'terminal_states' field"
    exit 1
fi

echo ""
echo "=== TLA Extract Integration Test PASSED ==="
echo "Extracted $ASYNC_COUNT state machines successfully"

# Cleanup
rm -f "$OUTPUT_FILE"
rm -rf "$OUTPUT_DIR"
