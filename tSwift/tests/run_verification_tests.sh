#!/bin/bash
# tSwift Verification Test Harness
#
# Runs tswift-verify on curated SIL and Swift test files and asserts expected outcomes.
#
# Test file naming convention:
#   *safe*.sil/*.swift    - All VCs should verify (exit 0)
#   *unsafe*.sil/*.swift  - At least one VC should fail (exit 1)
#   *_should_fail.sil     - At least one VC should fail (exit 1)
#   *.sil/*.swift (other) - Informational only, may pass or fail
#
# Usage:
#   ./tests/run_verification_tests.sh              # Run all tests
#   ./tests/run_verification_tests.sh --fast       # Run fast subset (SIL only)
#   ./tests/run_verification_tests.sh --swift      # Include Swift source tests
#   ./tests/run_verification_tests.sh file.sil     # Run single file
#
# Environment:
#   TSWIFT_VERIFY  - Path to tswift-verify binary (default: find in cargo target)
#   SWIFTC         - Path to Swift compiler with verification attributes
#
# Exit codes:
#   0 - All tests passed
#   1 - Some tests failed
#   2 - Configuration error

set -u  # Error on undefined variables

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TSWIFT_ROOT="$(dirname "$SCRIPT_DIR")"
SIL_EXAMPLES="$TSWIFT_ROOT/vc-ir-swift/tests/sil_examples"
SWIFT_VERIFICATION="$SCRIPT_DIR/swift_verification"

# Find tswift-verify binary
find_tswift_verify() {
    if [[ -n "${TSWIFT_VERIFY:-}" ]]; then
        echo "$TSWIFT_VERIFY"
        return
    fi

    # Check debug build first (faster for development)
    local debug="$TSWIFT_ROOT/vc-ir-swift/target/debug/tswift-verify"
    if [[ -x "$debug" ]]; then
        echo "$debug"
        return
    fi

    # Check release build
    local release="$TSWIFT_ROOT/vc-ir-swift/target/release/tswift-verify"
    if [[ -x "$release" ]]; then
        echo "$release"
        return
    fi

    # Try cargo
    echo "cargo run --manifest-path $TSWIFT_ROOT/vc-ir-swift/Cargo.toml --bin tswift-verify --"
}

# Find forked Swift compiler
find_swiftc() {
    if [[ -n "${SWIFTC:-}" ]]; then
        echo "$SWIFTC"
        return
    fi

    # Standard fork location
    local fork="$HOME/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-$(uname -m)/bin/swiftc"
    if [[ -x "$fork" ]]; then
        echo "$fork"
        return
    fi

    # Fall back to system (won't support verification attributes)
    echo "swiftc"
}

TSWIFT_VERIFY=$(find_tswift_verify)
SWIFTC=$(find_swiftc)

# Counters
PASS=0
FAIL=0
SKIP=0

# Output formatting - colors disabled in non-TTY environments
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m' # No Color

if [[ -n "${NO_COLOR:-}" ]] || [[ ! -t 1 ]] || [[ "${TERM:-}" == "dumb" ]]; then
    RED=''
    GREEN=''
    YELLOW=''
    NC=''
fi

pass() {
    ((PASS++))
    printf "${GREEN}PASS${NC} %s\n" "$1"
}

fail() {
    ((FAIL++))
    printf "${RED}FAIL${NC} %s\n" "$1"
    if [[ -n "${2:-}" ]]; then
        printf "     Expected: %s\n" "$2"
        printf "     Got:      %s\n" "$3"
    fi
}

skip() {
    ((SKIP++))
    printf "${YELLOW}SKIP${NC} %s (%s)\n" "$1" "$2"
}

# Determine expected outcome from filename
get_expected_outcome() {
    local filename="$1"
    local base=$(basename "$filename")

    # Check naming conventions
    if [[ "$base" == *"safe"* ]] && [[ "$base" != *"unsafe"* ]]; then
        echo "pass"
    elif [[ "$base" == *"unsafe"* ]] || [[ "$base" == *"_should_fail"* ]]; then
        echo "fail"
    else
        echo "info"  # No expectation, just run for information
    fi
}

# Run a single SIL test
run_sil_test() {
    local sil_file="$1"
    local base=$(basename "$sil_file")
    local expected=$(get_expected_outcome "$sil_file")

    # Run verification (capture output and exit code)
    local output
    local exit_code

    if [[ "$TSWIFT_VERIFY" == "cargo run"* ]]; then
        output=$($TSWIFT_VERIFY --sil "$sil_file" --json 2>&1)
        exit_code=$?
    else
        output=$("$TSWIFT_VERIFY" --sil "$sil_file" --json 2>&1)
        exit_code=$?
    fi

    check_result "$base" "$expected" "$exit_code"
}

# Run a single Swift source test
run_swift_test() {
    local swift_file="$1"
    local base=$(basename "$swift_file")
    local expected=$(get_expected_outcome "$swift_file")

    # Run verification with forked compiler
    local output
    local exit_code

    if [[ "$TSWIFT_VERIFY" == "cargo run"* ]]; then
        output=$(SWIFTC="$SWIFTC" $TSWIFT_VERIFY --swift "$swift_file" --json 2>&1)
        exit_code=$?
    else
        output=$(SWIFTC="$SWIFTC" "$TSWIFT_VERIFY" --swift "$swift_file" --json 2>&1)
        exit_code=$?
    fi

    # Check for Swift compilation errors (exit code 2)
    if [[ $exit_code -eq 2 ]]; then
        if echo "$output" | grep -q "unknown attribute"; then
            skip "$base" "Swift compiler doesn't support verification attributes"
            return
        fi
    fi

    check_result "$base [Swift]" "$expected" "$exit_code"
}

# Check result and report
check_result() {
    local name="$1"
    local expected="$2"
    local exit_code="$3"

    case "$expected" in
        pass)
            if [[ $exit_code -eq 0 ]]; then
                pass "$name (all VCs verified)"
            else
                fail "$name" "exit 0 (all VCs verified)" "exit $exit_code"
            fi
            ;;
        fail)
            if [[ $exit_code -eq 1 ]]; then
                pass "$name (expected failure detected)"
            elif [[ $exit_code -eq 0 ]]; then
                fail "$name" "exit 1 (at least one VC should fail)" "exit 0 (all verified)"
            else
                fail "$name" "exit 1 (expected failure)" "exit $exit_code (parse/input error?)"
            fi
            ;;
        info)
            # Informational only - report but don't count as pass/fail
            if [[ $exit_code -eq 0 ]]; then
                printf "INFO %s (verified, exit 0)\n" "$name"
            elif [[ $exit_code -eq 1 ]]; then
                printf "INFO %s (some VCs failed, exit 1)\n" "$name"
            else
                printf "INFO %s (error, exit %d)\n" "$name" "$exit_code"
            fi
            ;;
    esac
}

# Main execution
main() {
    local fast_mode=false
    local swift_mode=false
    local single_file=""

    # Parse arguments
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --fast)
                fast_mode=true
                shift
                ;;
            --swift)
                swift_mode=true
                shift
                ;;
            --help|-h)
                echo "Usage: $0 [--fast] [--swift] [file.sil|file.swift]"
                echo ""
                echo "Options:"
                echo "  --fast    Run fast subset only (SIL files with expected outcomes)"
                echo "  --swift   Include Swift source file tests (requires forked compiler)"
                echo "  file      Run single specified file"
                echo ""
                echo "Environment:"
                echo "  SWIFTC    Path to Swift compiler with verification attributes"
                exit 0
                ;;
            *)
                single_file="$1"
                shift
                ;;
        esac
    done

    echo "tSwift Verification Test Harness"
    echo "================================"
    echo ""
    echo "Verifier: $TSWIFT_VERIFY"
    if $swift_mode || [[ -n "$single_file" && "$single_file" == *.swift ]]; then
        echo "Swift:    $SWIFTC"
    fi
    echo ""

    if [[ -n "$single_file" ]]; then
        # Single file mode
        if [[ ! -f "$single_file" ]]; then
            echo "ERROR: File not found: $single_file"
            exit 2
        fi
        if [[ "$single_file" == *.swift ]]; then
            run_swift_test "$single_file"
        else
            run_sil_test "$single_file"
        fi
    else
        # Directory mode - SIL tests
        if [[ ! -d "$SIL_EXAMPLES" ]]; then
            echo "ERROR: SIL test directory not found: $SIL_EXAMPLES"
            exit 2
        fi

        # Collect SIL test files
        local sil_files=()

        if $fast_mode; then
            # Fast mode: only files with expected outcomes
            for f in "$SIL_EXAMPLES"/*safe*.sil "$SIL_EXAMPLES"/*_should_fail.sil; do
                [[ -f "$f" ]] && sil_files+=("$f")
            done
        else
            # Full mode: all SIL files
            for f in "$SIL_EXAMPLES"/*.sil; do
                [[ -f "$f" ]] && sil_files+=("$f")
            done
        fi

        echo "Running ${#sil_files[@]} SIL test files..."
        echo ""

        for sil_file in "${sil_files[@]}"; do
            run_sil_test "$sil_file"
        done

        # Swift source tests (optional)
        if $swift_mode && [[ -d "$SWIFT_VERIFICATION" ]]; then
            echo ""
            echo "--- Swift Source Tests ---"
            echo ""

            local swift_files=()
            for f in "$SWIFT_VERIFICATION"/*.swift; do
                [[ -f "$f" ]] && swift_files+=("$f")
            done

            echo "Running ${#swift_files[@]} Swift test files..."
            echo ""

            for swift_file in "${swift_files[@]}"; do
                run_swift_test "$swift_file"
            done
        fi
    fi

    echo ""
    echo "================================"
    echo "Results: $PASS passed, $FAIL failed, $SKIP skipped"

    if [[ $FAIL -gt 0 ]]; then
        exit 1
    fi
    exit 0
}

main "$@"
