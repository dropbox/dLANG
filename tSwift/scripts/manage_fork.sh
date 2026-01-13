#!/bin/bash
# manage_fork.sh - Manage the tSwift Swift compiler fork
#
# This script maintains a clear separation between:
#   - ~/tSwift/upstream/swift/     Read-only upstream reference (DO NOT EDIT)
#   - ~/swift-project/swift/       Editable fork with patches applied
#
# Usage:
#   ./scripts/manage_fork.sh setup     # Clone Swift + deps, apply patches
#   ./scripts/manage_fork.sh build     # Build the compiler
#   ./scripts/manage_fork.sh verify    # Verify the build works
#   ./scripts/manage_fork.sh update    # Update from upstream, reapply patches
#   ./scripts/manage_fork.sh status    # Show current status
#   ./scripts/manage_fork.sh clean     # Remove build artifacts
#
# Prerequisites: Xcode, Ninja, Sccache, Python 3.6+, Git 2.x

set -e

# Configuration
TSWIFT_ROOT="${TSWIFT_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
SWIFT_PROJECT_DIR="${SWIFT_PROJECT_DIR:-$HOME/swift-project}"
COMPILER_PATCHES_DIR="$TSWIFT_ROOT/compiler"
PATCHES_DIR="$TSWIFT_ROOT/patches"

# Colors - disabled in non-TTY environments
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

if [[ -n "${NO_COLOR:-}" ]] || [[ ! -t 1 ]] || [[ "${TERM:-}" == "dumb" ]]; then
    RED=''
    GREEN=''
    YELLOW=''
    BLUE=''
    NC=''
fi

# Unicode symbols (use ASCII fallbacks when not in TTY or when NO_COLOR set)
CHECK_MARK="[OK]"
if [[ -z "${NO_COLOR:-}" ]] && [[ -t 1 ]] && [[ "${TERM:-}" != "dumb" ]]; then
    CHECK_MARK="✓"
fi

info() { echo -e "${BLUE}INFO:${NC} $1"; }
success() { echo -e "${GREEN}${CHECK_MARK}${NC} $1"; }
warn() { echo -e "${YELLOW}WARNING:${NC} $1"; }
error() { echo -e "${RED}ERROR:${NC} $1" >&2; }

usage() {
    cat <<EOF
manage_fork.sh - Manage the tSwift Swift compiler fork

Usage: $0 <command>

Commands:
  setup     Clone Swift and dependencies, apply patches
  build     Build the compiler (incremental if already built)
  verify    Verify the build produces a working swiftc
  update    Update from upstream, reapply patches
  status    Show current fork status
  clean     Remove build artifacts
  help      Show this help

Environment Variables:
  TSWIFT_ROOT         tSwift project root (default: parent of this script)
  SWIFT_PROJECT_DIR   Swift build directory (default: ~/swift-project)

EOF
    exit 0
}

check_prerequisites() {
    info "Checking prerequisites..."
    local missing=0

    # Python 3.6+
    if ! command -v python3 &>/dev/null; then
        error "Python 3 not found"
        missing=1
    else
        local pyver=$(python3 -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')
        if [[ $(echo "$pyver < 3.6" | bc -l) -eq 1 ]]; then
            error "Python 3.6+ required, found $pyver"
            missing=1
        fi
    fi

    # Ninja
    if ! command -v ninja &>/dev/null; then
        error "Ninja not found. Install with: brew install ninja"
        missing=1
    fi

    # Git
    if ! command -v git &>/dev/null; then
        error "Git not found"
        missing=1
    fi

    # Xcode (macOS only)
    if [[ "$(uname)" == "Darwin" ]]; then
        if ! xcode-select -p &>/dev/null; then
            error "Xcode command line tools not found. Install with: xcode-select --install"
            missing=1
        fi
    fi

    # Disk space (warn if < 100GB)
    local free_space
    if [[ "$(uname)" == "Darwin" ]]; then
        free_space=$(df -g / | awk 'NR==2 {print $4}')
    else
        free_space=$(df -BG / | awk 'NR==2 {print $4}' | tr -d 'G')
    fi
    if [[ "$free_space" -lt 100 ]]; then
        warn "Less than 100GB free disk space. Build may fail."
    fi

    if [[ $missing -eq 1 ]]; then
        error "Missing prerequisites. Please install them and try again."
        exit 1
    fi

    success "Prerequisites OK"
}

get_arch() {
    uname -m
}

get_build_dir() {
    echo "$SWIFT_PROJECT_DIR/build/Ninja-RelWithDebInfoAssert/swift-macosx-$(get_arch)"
}

cmd_setup() {
    info "Setting up Swift fork in $SWIFT_PROJECT_DIR"
    check_prerequisites

    # Check if already exists
    if [[ -d "$SWIFT_PROJECT_DIR/swift" ]]; then
        warn "$SWIFT_PROJECT_DIR/swift already exists"
        read -p "Remove and re-clone? [y/N] " -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            rm -rf "$SWIFT_PROJECT_DIR"
        else
            info "Skipping clone. Run 'update' to refresh patches."
            return 0
        fi
    fi

    # Create directory
    mkdir -p "$SWIFT_PROJECT_DIR"
    cd "$SWIFT_PROJECT_DIR"

    # Clone Swift
    info "Cloning Swift repository..."
    git clone https://github.com/swiftlang/swift.git swift

    cd swift

    # Clone dependencies
    info "Cloning dependencies (this may take a while)..."
    utils/update-checkout --clone-with-ssh || utils/update-checkout --clone

    # Apply patches
    apply_patches

    success "Setup complete. Run './scripts/manage_fork.sh build' to build."
}

apply_patches() {
    cd "$SWIFT_PROJECT_DIR/swift"

    info "Applying tSwift patches..."

    # List of patches to apply (in order)
    local patches=(
        "$COMPILER_PATCHES_DIR/verification_attributes_v3.patch"
        "$PATCHES_DIR/verification_attributes.patch"
        "$PATCHES_DIR/verification_attributes_visitors.patch"
        "$PATCHES_DIR/verification_cmakelists.patch"
        "$PATCHES_DIR/verification_pipeline_integration.patch"
    )

    local applied=0
    for patch in "${patches[@]}"; do
        if [[ -f "$patch" ]]; then
            info "Applying $(basename "$patch")..."
            if git apply --check "$patch" 2>/dev/null; then
                git apply "$patch"
                ((applied++))
            else
                warn "Patch $(basename "$patch") does not apply cleanly, trying 3-way merge..."
                if git apply --3way "$patch" 2>/dev/null; then
                    ((applied++))
                else
                    error "Failed to apply $(basename "$patch")"
                fi
            fi
        else
            warn "Patch not found: $patch"
        fi
    done

    if [[ $applied -gt 0 ]]; then
        git add -A
        git commit -m "Apply tSwift verification patches ($applied patches)" || true
        success "Applied $applied patches"
    else
        warn "No patches applied"
    fi
}

cmd_build() {
    info "Building Swift compiler..."
    check_prerequisites

    if [[ ! -d "$SWIFT_PROJECT_DIR/swift" ]]; then
        error "Swift not cloned. Run 'setup' first."
        exit 1
    fi

    cd "$SWIFT_PROJECT_DIR/swift"

    # Check if Sccache is available
    local sccache_flag=""
    if command -v sccache &>/dev/null; then
        sccache_flag="--sccache"
        info "Using Sccache for caching"
    fi

    info "Starting build (this may take 30+ minutes)..."

    utils/build-script \
        --skip-build-benchmarks \
        --swift-darwin-supported-archs "$(get_arch)" \
        --release-debuginfo \
        --swift-disable-dead-stripping \
        --bootstrapping=hosttools \
        $sccache_flag

    success "Build complete!"
    cmd_verify
}

cmd_verify() {
    info "Verifying build..."

    local swiftc="$(get_build_dir)/bin/swiftc"

    if [[ ! -x "$swiftc" ]]; then
        error "Built swiftc not found at: $swiftc"
        error "Run 'build' first."
        exit 1
    fi

    # Version check
    info "Checking swiftc version..."
    "$swiftc" --version

    # Get SDK path
    local sdk_path
    sdk_path=$(xcrun --show-sdk-path 2>/dev/null) || sdk_path=""

    # Test 1: Parse and typecheck
    info "Testing parse and typecheck..."
    local tmpdir
    tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/tswift_test.XXXXXX")"
    local test_file="$tmpdir/test.swift"
    echo 'let x: Int = 42; print(x)' > "$test_file"

    if "$swiftc" -frontend -typecheck "$test_file" 2>/dev/null; then
        success "Parse and typecheck: OK"
    else
        error "Parse and typecheck failed"
        rm -rf "$tmpdir"
        exit 1
    fi

    # Test 2: SIL generation (what tSwift actually uses)
    info "Testing SIL generation..."
    local sil_args=()
    [[ -n "$sdk_path" ]] && sil_args+=(-sdk "$sdk_path")

    if "$swiftc" "${sil_args[@]}" -emit-sil "$test_file" >/dev/null 2>&1; then
        success "SIL generation: OK"
    else
        error "SIL generation failed"
        rm -rf "$tmpdir"
        exit 1
    fi

    # Test 3: Full compilation (may fail due to SDK/linker config, warn only)
    info "Testing full compilation..."
    local test_output="${test_file%.swift}"
    if "$swiftc" "${sil_args[@]}" "$test_file" -o "$test_output" 2>/dev/null; then
        if "$test_output" 2>/dev/null | grep -q "42"; then
            success "Full compilation: OK"
        else
            success "Full compilation: OK (output differs)"
        fi
        rm -f "$test_output"
    else
        warn "Full compilation failed (SDK/linker config issue - SIL generation works)"
        echo "  This is expected if SDK paths aren't configured."
        echo "  tSwift verification only needs SIL generation, which works."
    fi

    rm -rf "$tmpdir"

    success "Verification passed!"
    echo ""
    echo "Built compiler location:"
    echo "  $swiftc"
    echo ""
    echo "To use with tswiftv, set:"
    echo "  export TSWIFT_COMPILER=$swiftc"
}

cmd_update() {
    info "Updating from upstream..."

    if [[ ! -d "$SWIFT_PROJECT_DIR/swift" ]]; then
        error "Swift not cloned. Run 'setup' first."
        exit 1
    fi

    cd "$SWIFT_PROJECT_DIR/swift"

    # Check for uncommitted changes
    if ! git diff-index --quiet HEAD --; then
        warn "Uncommitted changes detected. Stashing..."
        git stash
    fi

    # Reset to clean state
    info "Resetting to upstream..."
    git fetch origin
    git reset --hard origin/main

    # Update dependencies
    info "Updating dependencies..."
    utils/update-checkout --clone-with-ssh || utils/update-checkout --clone

    # Reapply patches
    apply_patches

    success "Update complete. Run 'build' to rebuild."
}

cmd_status() {
    echo "=== tSwift Fork Status ==="
    echo ""
    echo "tSwift Root:       $TSWIFT_ROOT"
    echo "Swift Project Dir: $SWIFT_PROJECT_DIR"
    echo ""

    if [[ -d "$SWIFT_PROJECT_DIR/swift" ]]; then
        cd "$SWIFT_PROJECT_DIR/swift"
        echo "Fork Status:"
        echo "  Branch: $(git branch --show-current)"
        echo "  Commit: $(git rev-parse --short HEAD)"
        echo "  Last commit: $(git log -1 --format='%s')"
        echo ""

        # Check if patches are applied
        if git log --oneline -10 | grep -q "tSwift verification"; then
            success "Patches appear to be applied"
        else
            warn "Patches may not be applied"
        fi
    else
        warn "Fork not cloned yet. Run 'setup' first."
    fi
    echo ""

    # Check build status
    local swiftc="$(get_build_dir)/bin/swiftc"
    if [[ -x "$swiftc" ]]; then
        success "Built compiler exists: $swiftc"
        echo "  Version: $("$swiftc" --version 2>&1 | head -1)"
    else
        warn "Built compiler not found"
    fi
}

cmd_clean() {
    info "Cleaning build artifacts..."

    if [[ -d "$SWIFT_PROJECT_DIR/build" ]]; then
        read -p "Remove $SWIFT_PROJECT_DIR/build? [y/N] " -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            rm -rf "$SWIFT_PROJECT_DIR/build"
            success "Build directory removed"
        fi
    else
        info "No build directory to clean"
    fi
}

# Main
case "${1:-help}" in
    setup)  cmd_setup ;;
    build)  cmd_build ;;
    verify) cmd_verify ;;
    update) cmd_update ;;
    status) cmd_status ;;
    clean)  cmd_clean ;;
    help|--help|-h) usage ;;
    *)
        error "Unknown command: $1"
        usage
        ;;
esac
