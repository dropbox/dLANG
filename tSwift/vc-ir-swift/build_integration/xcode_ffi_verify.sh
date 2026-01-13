#!/bin/bash
# xcode_ffi_verify.sh - Xcode Build Phase Script for FFI Verification
#
# Add this as a "Run Script" build phase in your Xcode project to automatically
# verify FFI compatibility between Swift and Rust sources during builds.
#
# INSTALLATION:
#
# 1. Install tswift-ffi-verify:
#    cargo install --git https://github.com/dropbox/dLANG/tSwift --bin tswift-ffi-verify
#
# 2. In Xcode:
#    - Select your target
#    - Go to "Build Phases"
#    - Click "+" -> "New Run Script Phase"
#    - Copy this script into the phase (or reference it)
#    - Move the phase BEFORE "Compile Sources"
#
# 3. Configure paths below for your project structure.
#
# CONFIGURATION:
#
# Set these variables to match your project structure:

# Swift source files with @_ffi_* annotations (space-separated)
SWIFT_FILES="${SRCROOT}/Sources/FFI/*.swift"

# swift-bridge generated Swift files (space-separated)
GENERATED_FILES="${SRCROOT}/Generated/*.swift"

# Rust source files with #[ffi_export] functions (space-separated)
RUST_FILES="${SRCROOT}/../rust/src/ffi/*.rs"

# Enable Z4 semantic proofs (slower but more thorough)
# Set to "1" to enable, "0" to disable
USE_Z4="${FFI_VERIFY_Z4:-0}"

# Strict mode: fail build on verification failure
# Set to "1" to fail, "0" to warn only
STRICT_MODE="${FFI_VERIFY_STRICT:-0}"

# ============================================================================
# Script implementation - typically no changes needed below
# ============================================================================

set -o pipefail

# Skip if disabled
if [ "${FFI_VERIFY_ENABLE:-1}" = "0" ]; then
    echo "note: FFI verification disabled (FFI_VERIFY_ENABLE=0)"
    exit 0
fi

# Find tswift-ffi-verify binary
find_verify_binary() {
    if [ -n "$TSWIFT_FFI_VERIFY_BIN" ] && [ -x "$TSWIFT_FFI_VERIFY_BIN" ]; then
        echo "$TSWIFT_FFI_VERIFY_BIN"
        return
    fi

    # Check common locations
    local candidates=(
        "$HOME/.cargo/bin/tswift-ffi-verify"
        "/usr/local/bin/tswift-ffi-verify"
        "/opt/homebrew/bin/tswift-ffi-verify"
    )

    for bin in "${candidates[@]}"; do
        if [ -x "$bin" ]; then
            echo "$bin"
            return
        fi
    done

    # Try PATH
    if command -v tswift-ffi-verify &> /dev/null; then
        command -v tswift-ffi-verify
        return
    fi

    return 1
}

VERIFY_BIN=$(find_verify_binary)
if [ -z "$VERIFY_BIN" ]; then
    echo "warning: tswift-ffi-verify not found. Install with:"
    echo "warning:   cargo install --git https://github.com/dropbox/dLANG/tSwift --bin tswift-ffi-verify"
    exit 0
fi

# Expand globs and collect files
expand_files() {
    local pattern="$1"
    local result=()

    # Use nullglob to handle no matches gracefully
    shopt -s nullglob
    for file in $pattern; do
        if [ -f "$file" ]; then
            result+=("$file")
        fi
    done
    shopt -u nullglob

    echo "${result[@]}"
}

SWIFT_EXPANDED=($(expand_files "$SWIFT_FILES"))
GENERATED_EXPANDED=($(expand_files "$GENERATED_FILES"))
RUST_EXPANDED=($(expand_files "$RUST_FILES"))

# Skip if no files found
if [ ${#SWIFT_EXPANDED[@]} -eq 0 ] && [ ${#GENERATED_EXPANDED[@]} -eq 0 ] && [ ${#RUST_EXPANDED[@]} -eq 0 ]; then
    echo "note: No FFI files found to verify"
    exit 0
fi

# Build command
CMD=("$VERIFY_BIN")

if [ ${#SWIFT_EXPANDED[@]} -gt 0 ]; then
    CMD+=("--swift" "${SWIFT_EXPANDED[@]}")
fi

if [ ${#GENERATED_EXPANDED[@]} -gt 0 ]; then
    CMD+=("--generated" "${GENERATED_EXPANDED[@]}")
fi

if [ ${#RUST_EXPANDED[@]} -gt 0 ]; then
    CMD+=("--rust" "${RUST_EXPANDED[@]}")
fi

if [ "$USE_Z4" = "1" ]; then
    CMD+=("--z4")
fi

CMD+=("--verbose")

# Run verification
echo "note: Running FFI verification..."
echo "note: Command: ${CMD[*]}"

OUTPUT=$("${CMD[@]}" 2>&1)
EXIT_CODE=$?

# Process output
while IFS= read -r line; do
    if [[ "$line" == *"FAIL"* ]] || [[ "$line" == *"error"* ]]; then
        if [ "$STRICT_MODE" = "1" ]; then
            echo "error: FFI: $line"
        else
            echo "warning: FFI: $line"
        fi
    elif [[ "$line" == *"OK"* ]] || [[ "$line" == *"compatible"* ]]; then
        echo "note: FFI: $line"
    elif [ -n "$line" ]; then
        echo "note: FFI: $line"
    fi
done <<< "$OUTPUT"

# Handle exit code
if [ $EXIT_CODE -ne 0 ]; then
    if [ "$STRICT_MODE" = "1" ]; then
        echo "error: FFI verification failed"
        exit 1
    else
        echo "warning: FFI verification failed (set FFI_VERIFY_STRICT=1 in build settings to fail build)"
        exit 0
    fi
fi

echo "note: FFI verification passed"
exit 0
