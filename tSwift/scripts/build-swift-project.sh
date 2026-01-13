#!/bin/bash
# build-swift-project.sh - Build swift-frontend + stdlib with correct SDK
#
# This script ensures reproducible builds by:
# 1. Using Xcode SDK (not CommandLineTools) via DEVELOPER_DIR
# 2. Reconfiguring existing builds to use correct SDK paths
# 3. Setting SWIFT_CONCURRENCY_GLOBAL_EXECUTOR for dispatch support
#
# Usage:
#   ./scripts/build-swift-project.sh           # Build swift-frontend + stdlib
#   ./scripts/build-swift-project.sh --clean   # Clean reconfigure + build
#   ./scripts/build-swift-project.sh --help    # Show this help

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TSWIFT_ROOT="$(dirname "$SCRIPT_DIR")"

# Unicode symbols (use ASCII fallbacks when not in TTY or when NO_COLOR set)
CHECK_MARK="[OK]"
if [ -z "${NO_COLOR:-}" ] && [ -t 1 ] && [ "${TERM:-}" != "dumb" ]; then
    CHECK_MARK="✓"
fi

# Paths - adjust these if your setup differs
SWIFT_PROJECT="${SWIFT_PROJECT:-$HOME/swift-project}"
BUILD_DIR="${SWIFT_PROJECT}/build/Ninja-RelWithDebInfoAssert/swift-macosx-$(uname -m)"
XCODE_DEV="/Applications/Xcode.app/Contents/Developer"

# Detect SDK - prefer MacOSX15.2.sdk if available, fall back to MacOSX.sdk
detect_sdk() {
    local sdk_base="${XCODE_DEV}/Platforms/MacOSX.platform/Developer/SDKs"
    if [[ -d "${sdk_base}/MacOSX15.2.sdk" ]]; then
        echo "${sdk_base}/MacOSX15.2.sdk"
    elif [[ -d "${sdk_base}/MacOSX15.sdk" ]]; then
        echo "${sdk_base}/MacOSX15.sdk"
    elif [[ -d "${sdk_base}/MacOSX.sdk" ]]; then
        echo "${sdk_base}/MacOSX.sdk"
    else
        echo "ERROR: No MacOSX SDK found in ${sdk_base}" >&2
        exit 1
    fi
}

show_help() {
    head -15 "$0" | tail -12
    exit 0
}

# Check prerequisites
check_prereqs() {
    if [[ ! -d "$XCODE_DEV" ]]; then
        echo "ERROR: Xcode not found at $XCODE_DEV"
        echo "Install Xcode from the App Store"
        exit 1
    fi

    if [[ ! -d "$SWIFT_PROJECT" ]]; then
        echo "ERROR: swift-project not found at $SWIFT_PROJECT"
        echo "Clone it with: git clone https://github.com/apple/swift-project.git ~/swift-project"
        exit 1
    fi

    if ! command -v ninja &>/dev/null; then
        echo "ERROR: ninja not found. Install with: brew install ninja"
        exit 1
    fi

    if ! command -v cmake &>/dev/null; then
        echo "ERROR: cmake not found. Install with: brew install cmake"
        exit 1
    fi
}

# Reconfigure build to use Xcode SDK
reconfigure_build() {
    local sdk="$1"
    echo "==> Reconfiguring build to use SDK: $sdk"

    cd "$BUILD_DIR"

    # Use Xcode's developer directory, not CommandLineTools
    DEVELOPER_DIR="$XCODE_DEV" cmake \
        -DSWIFT_CONCURRENCY_GLOBAL_EXECUTOR=dispatch \
        -D"SWIFT_COMPILER_SOURCES_SDK_FLAGS=-sdk;${sdk}" \
        . 2>&1 | grep -E "(Xcode|SDK|Configuring|error)" || true

    echo "==> Reconfiguration complete"
}

# Build targets
build_targets() {
    echo "==> Building swift-frontend..."
    cd "$BUILD_DIR"
    DEVELOPER_DIR="$XCODE_DEV" ninja swift-frontend

    echo ""
    echo "==> Building swift-stdlib..."
    DEVELOPER_DIR="$XCODE_DEV" ninja swift-stdlib

    echo ""
    echo "==> Build complete!"
}

# Verify build
verify_build() {
    local sdk="$1"
    local swift_frontend="${BUILD_DIR}/bin/swift-frontend"
    local stdlib="${BUILD_DIR}/lib/swift/macosx/Swift.swiftmodule"

    echo ""
    echo "==> Verifying build..."

    if [[ ! -x "$swift_frontend" ]]; then
        echo "ERROR: swift-frontend not found at $swift_frontend"
        exit 1
    fi

    if [[ ! -d "$stdlib" ]]; then
        echo "ERROR: Swift.swiftmodule not found at $stdlib"
        exit 1
    fi

    # Smoke test - use temp directory for portable temp file with .swift suffix
    local tmp_dir
    tmp_dir=$(mktemp -d)
    local test_file="$tmp_dir/test.swift"
    echo 'print("Hello, Verified Swift!")' > "$test_file"

    if "$swift_frontend" -emit-sil "$test_file" -sdk "$sdk" \
        -resource-dir "${BUILD_DIR}/lib/swift" > /dev/null 2>&1; then
        echo "$CHECK_MARK swift-frontend works"
        echo "$CHECK_MARK stdlib present"
        echo "$CHECK_MARK hello world compiles"
        rm -rf "$tmp_dir"
    else
        echo "ERROR: Smoke test failed"
        rm -rf "$tmp_dir"
        exit 1
    fi

    echo ""
    echo "Build artifacts:"
    echo "  swift-frontend: $swift_frontend"
    echo "  stdlib:         ${BUILD_DIR}/lib/swift/macosx/"
    echo "  SDK:            $sdk"
    echo ""
    echo "To use:"
    echo "  $swift_frontend -emit-sil <file.swift> -sdk $sdk -resource-dir ${BUILD_DIR}/lib/swift"
}

main() {
    local do_clean=false

    while [[ $# -gt 0 ]]; do
        case "$1" in
            --clean) do_clean=true; shift ;;
            --help|-h) show_help ;;
            *) echo "Unknown option: $1"; show_help ;;
        esac
    done

    check_prereqs

    local sdk
    sdk=$(detect_sdk)
    echo "Using SDK: $sdk"
    echo "Build dir: $BUILD_DIR"
    echo ""

    if [[ ! -d "$BUILD_DIR" ]]; then
        echo "ERROR: Build directory not found: $BUILD_DIR"
        echo "Run the initial build-script first:"
        echo "  cd $SWIFT_PROJECT && ./swift/utils/build-script --release-debuginfo --skip-build-benchmarks --skip-ios --skip-tvos --skip-watchos"
        exit 1
    fi

    if [[ "$do_clean" == true ]]; then
        reconfigure_build "$sdk"
    fi

    # Always reconfigure to ensure correct SDK (fast if already configured)
    reconfigure_build "$sdk"

    build_targets
    verify_build "$sdk"
}

main "$@"
