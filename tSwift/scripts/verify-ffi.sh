#!/bin/bash
# verify-ffi.sh - Local FFI verification script
#
# Usage:
#   ./scripts/verify-ffi.sh                    # Run example verification
#   ./scripts/verify-ffi.sh --swift foo.swift --rust bar.rs   # Custom files
#
# This script builds tswift-ffi-verify and runs FFI verification.
# Use --z4 for semantic proofs (slower but more thorough).

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
VC_IR_DIR="$PROJECT_ROOT/vc-ir-swift"

# Colors for output - disabled in non-TTY environments
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

if [[ -n "${NO_COLOR:-}" ]] || [[ ! -t 1 ]] || [[ "${TERM:-}" == "dumb" ]]; then
    RED=''
    GREEN=''
    YELLOW=''
    NC=''
fi

echo "Building tswift-ffi-verify..."
cd "$VC_IR_DIR"
cargo build --release --bin tswift-ffi-verify 2>&1 | tail -3

CLI="$VC_IR_DIR/target/release/tswift-ffi-verify"

# If no arguments, run example verification
if [ $# -eq 0 ]; then
    echo ""
    echo "=== Running example FFI verification ==="
    echo ""

    echo -e "${YELLOW}Structural check (fast):${NC}"
    $CLI --swift tests/ffi_examples/math_import.swift \
         --rust tests/ffi_examples/math_export.rs \
         --verbose

    echo ""
    echo -e "${YELLOW}Z4 semantic check (thorough):${NC}"
    $CLI --swift tests/ffi_examples/math_import.swift \
         --rust tests/ffi_examples/math_export.rs \
         --z4 --verbose

    echo ""
    echo -e "${YELLOW}Incompatible bindings (should fail):${NC}"
    if $CLI --swift tests/ffi_examples/incompatible_import.swift \
            --rust tests/ffi_examples/math_export.rs \
            --z4 --verbose 2>&1; then
        echo -e "${RED}ERROR: Expected failure but verification passed${NC}"
        exit 1
    else
        echo -e "${GREEN}OK: Incompatible bindings correctly detected${NC}"
    fi

    echo ""
    echo -e "${GREEN}All example verifications completed successfully${NC}"
else
    # Pass through arguments to CLI
    $CLI "$@"
fi
