#!/bin/bash
# test_dropin.sh - Test rustc-index-verified as drop-in replacement for rustc_index
#
# This script:
# 1. Backs up the original rustc_index
# 2. Copies our src/ files and Cargo.dropin.toml into rustc_index
# 3. Runs `./x check compiler/rustc_middle` (bootstrap) or `cargo check -p rustc_middle` (cargo mode)
# 4. Restores the original rustc_index
#
# SUCCESS: cargo check passes with our code
# FAILURE: cargo check fails
#
# KNOWN LIMITATION (Worker #114):
# This test requires building rustc from source, which has strict toolchain requirements.
# Rustc 1.83.0 was built with its era's nightly toolchain and may not compile with
# modern nightly versions due to stdlib API changes (e.g., ptr::sub_ptr renamed/changed).
#
# For reliable drop-in testing, use rustc's bootstrap system (default for this script):
#   ./scripts/test_dropin.sh
# Or explicitly:
#   ./scripts/test_dropin.sh --bootstrap
#
# Or use the exact toolchain rustc 1.83.0 was built with (see rust-toolchain.toml in rustc repo).

set -e
set -o pipefail  # Ensure pipeline failures propagate

RUSTC_DIR=~/tRust/upstream/rustc
OUR_DIR=$(pwd)
BACKUP_DIR=/tmp/rustc_index_backup_$$
TARGET_DIR=$RUSTC_DIR/compiler/rustc_index
MODE=bootstrap

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

usage() {
    cat << 'EOF'
Usage: ./scripts/test_dropin.sh [--bootstrap|--cargo]

Replaces upstream rustc's `compiler/rustc_index` with this repo's sources and checks
that rustc still builds.

Modes:
  --bootstrap (default)  Uses rustc's bootstrap system: `./x check ...`
  --cargo                Uses direct workspace build: `RUSTC_BOOTSTRAP=1 cargo check ...`
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --bootstrap)
            MODE=bootstrap
            shift
            ;;
        --cargo)
            MODE=cargo
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo -e "${RED}ERROR: Unknown argument: $1${NC}"
            usage
            exit 2
            ;;
    esac
done

cleanup() {
    echo ""
    echo "=== Restoring original rustc_index ==="
    if [[ -d "$BACKUP_DIR" ]]; then
        rm -rf "$TARGET_DIR"
        mv "$BACKUP_DIR" "$TARGET_DIR"
        echo -e "${GREEN}Restored${NC}"
    else
        echo -e "${YELLOW}No backup to restore${NC}"
    fi
}

trap cleanup EXIT

echo "========================================"
echo "  DROP-IN REPLACEMENT TEST"
echo "========================================"
echo ""
echo "Our directory:     $OUR_DIR"
echo "Target directory:  $TARGET_DIR"
echo "Backup directory:  $BACKUP_DIR"
echo ""

# Verify paths exist
if [[ ! -d "$TARGET_DIR" ]]; then
    echo -e "${RED}ERROR: Target directory not found: $TARGET_DIR${NC}"
    echo "Make sure upstream rustc is cloned at ~/tRust/upstream/rustc"
    exit 1
fi

if [[ ! -f "$OUR_DIR/Cargo.dropin.toml" ]]; then
    echo -e "${RED}ERROR: Cargo.dropin.toml not found${NC}"
    exit 1
fi

# Step 1: Backup original
echo "=== Step 1: Backing up original rustc_index ==="
cp -r "$TARGET_DIR" "$BACKUP_DIR"
echo "Backed up to $BACKUP_DIR"

# Step 2: Replace with our code
echo ""
echo "=== Step 2: Installing our verified version ==="

# Remove original src
rm -rf "$TARGET_DIR/src"

# Copy our src (excluding test subdirectories)
mkdir -p "$TARGET_DIR/src"
cp "$OUR_DIR/src/lib.rs" "$TARGET_DIR/src/"
cp "$OUR_DIR/src/idx.rs" "$TARGET_DIR/src/"
cp "$OUR_DIR/src/vec.rs" "$TARGET_DIR/src/"
cp "$OUR_DIR/src/slice.rs" "$TARGET_DIR/src/"
cp "$OUR_DIR/src/bit_set.rs" "$TARGET_DIR/src/"
cp "$OUR_DIR/src/interval.rs" "$TARGET_DIR/src/"

# Copy Cargo.dropin.toml as Cargo.toml
cp "$OUR_DIR/Cargo.dropin.toml" "$TARGET_DIR/Cargo.toml"

echo "Installed files:"
ls -la "$TARGET_DIR/src/" | head -10

# Step 3: Modify our lib.rs to work in rustc context
# Remove our doc comments and standalone-only code
echo ""
echo "=== Step 3: Adapting lib.rs for rustc context ==="

# Create a clean lib.rs that matches upstream structure exactly
cat > "$TARGET_DIR/src/lib.rs" << 'EOF'
// tidy-alphabetical-start
#![cfg_attr(all(feature = "nightly", test), feature(stmt_expr_attributes))]
#![cfg_attr(feature = "nightly", feature(extend_one, step_trait, test))]
#![cfg_attr(feature = "nightly", feature(new_range_api))]
// tidy-alphabetical-end

pub mod bit_set;
#[cfg(feature = "nightly")]
pub mod interval;

mod idx;
mod slice;
mod vec;

pub use idx::Idx;
pub use idx::IntoSliceIdx;
pub use rustc_index_macros::newtype_index;
pub use slice::IndexSlice;
#[doc(no_inline)]
pub use vec::IndexVec;

/// Type size assertion. The first argument is a type and the second argument is its expected size.
///
/// <div class="warning">
///
/// Emitting hard errors from size assertions like this is generally not
/// recommended, especially in libraries, because they can cause build failures if the layout
/// algorithm or dependencies change. Here in rustc we control the toolchain and layout algorithm,
/// so the former is not a problem. For the latter we have a lockfile as rustc is an application and
/// precompiled library.
///
/// Short version: Don't copy this macro into your own code. Use a `#[test]` instead.
///
/// </div>
#[macro_export]
#[cfg(not(feature = "rustc_randomized_layouts"))]
macro_rules! static_assert_size {
    ($ty:ty, $size:expr) => {
        const _: [(); $size] = [(); ::std::mem::size_of::<$ty>()];
    };
}

#[macro_export]
#[cfg(feature = "rustc_randomized_layouts")]
macro_rules! static_assert_size {
    ($ty:ty, $size:expr) => {
        // no effect other than using the statements.
        // struct sizes are not deterministic under randomized layouts
        const _: (usize, usize) = ($size, ::std::mem::size_of::<$ty>());
    };
}
EOF

echo "Created clean lib.rs for rustc context"

# Step 4: Strip trust_macros from our source files
echo ""
echo "=== Step 4: Stripping trust_macros from source files ==="

for file in idx.rs vec.rs slice.rs bit_set.rs interval.rs; do
    if [[ -f "$TARGET_DIR/src/$file" ]]; then
        # Remove trust_macros use statements (not present in upstream rustc).
        sed -i '' '/use trust_macros/d' "$TARGET_DIR/src/$file" 2>/dev/null || \
        sed -i '/use trust_macros/d' "$TARGET_DIR/src/$file"

        # Remove `cfg_attr(trust_verify, ...)` specs to avoid `unexpected_cfgs` warnings under
        # rustc's `check-cfg` configuration.
        sed -i '' '/cfg_attr(trust_verify/d' "$TARGET_DIR/src/$file" 2>/dev/null || \
        sed -i '/cfg_attr(trust_verify/d' "$TARGET_DIR/src/$file"

        # Our standalone crate keeps interval tests in `src/interval/tests.rs`; upstream rustc
        # doesn't, and `./x check` may build `rustc_index` as a lib test.
        if [[ "$file" == "interval.rs" ]]; then
            sed -i '' '/^#[[]cfg(test)[]]$/d' "$TARGET_DIR/src/$file" 2>/dev/null || \
            sed -i '/^#[[]cfg(test)[]]$/d' "$TARGET_DIR/src/$file"
            sed -i '' '/^mod tests;$/d' "$TARGET_DIR/src/$file" 2>/dev/null || \
            sed -i '/^mod tests;$/d' "$TARGET_DIR/src/$file"
        fi

        echo "  Processed $file"
    fi
done

# Step 5: Try to build
echo ""
echo "=== Step 5: Building rustc_middle (uses rustc_index heavily) ==="
echo ""

cd "$RUSTC_DIR"

if [[ "$MODE" == "bootstrap" ]]; then
    if [[ -x "./x" ]]; then
        X_CMD=(./x)
    elif [[ -f "./x.py" ]]; then
        X_CMD=(python3 ./x.py)
    else
        echo -e "${RED}ERROR: rustc bootstrap command not found (expected ./x or ./x.py)${NC}"
        echo "Try --cargo mode, or check your rustc checkout at: $RUSTC_DIR"
        exit 1
    fi

    echo "Testing (bootstrap): ${X_CMD[*]} check compiler/rustc_index"
    set +e  # Temporarily disable exit on error
    "${X_CMD[@]}" check compiler/rustc_index > /tmp/dropin_x_check_index.log 2>&1
    INDEX_RESULT=$?
    set -e
    tail -40 /tmp/dropin_x_check_index.log
    if [[ $INDEX_RESULT -eq 0 ]]; then
        echo -e "${GREEN}bootstrap rustc_index check PASSED${NC}"
    else
        echo -e "${RED}bootstrap rustc_index check FAILED (exit code: $INDEX_RESULT)${NC}"
        echo "See /tmp/dropin_x_check_index.log for full output"
        grep -E "^(error|fatal)" /tmp/dropin_x_check_index.log | head -50 || true
        exit 1
    fi

    echo ""
    echo "Testing (bootstrap): ${X_CMD[*]} check compiler/rustc_middle"
    set +e
    "${X_CMD[@]}" check compiler/rustc_middle > /tmp/dropin_x_check_middle.log 2>&1
    MIDDLE_RESULT=$?
    set -e
    tail -40 /tmp/dropin_x_check_middle.log
    if [[ $MIDDLE_RESULT -eq 0 ]]; then
        echo -e "${GREEN}bootstrap rustc_middle check PASSED${NC}"
        RESULT=0
    else
        echo -e "${RED}bootstrap rustc_middle check FAILED (exit code: $MIDDLE_RESULT)${NC}"
        echo "See /tmp/dropin_x_check_middle.log for full output"
        grep -E "^(error|fatal)" /tmp/dropin_x_check_middle.log | head -50 || true
        RESULT=1
    fi
else
    # NOTE: rustc requires RUSTC_BOOTSTRAP for building without the bootstrap system.
    echo "Testing (cargo): RUSTC_BOOTSTRAP=1 cargo check -p rustc_index"
    set +e  # Temporarily disable exit on error
    RUSTC_BOOTSTRAP=1 cargo check -p rustc_index > /tmp/dropin_check_index.log 2>&1
    INDEX_RESULT=$?
    set -e
    tail -40 /tmp/dropin_check_index.log
    if [[ $INDEX_RESULT -eq 0 ]]; then
        echo -e "${GREEN}rustc_index check PASSED${NC}"
    else
        echo -e "${RED}rustc_index check FAILED (exit code: $INDEX_RESULT)${NC}"
        echo "See /tmp/dropin_check_index.log for full output"
        grep -E "^error" /tmp/dropin_check_index.log | head -50 || true
        exit 1
    fi

    echo ""
    echo "Testing (cargo): RUSTC_BOOTSTRAP=1 cargo check -p rustc_middle"
    set +e
    RUSTC_BOOTSTRAP=1 cargo check -p rustc_middle > /tmp/dropin_check_middle.log 2>&1
    MIDDLE_RESULT=$?
    set -e
    tail -40 /tmp/dropin_check_middle.log
    if [[ $MIDDLE_RESULT -eq 0 ]]; then
        echo -e "${GREEN}rustc_middle check PASSED${NC}"
        RESULT=0
    else
        echo -e "${RED}rustc_middle check FAILED (exit code: $MIDDLE_RESULT)${NC}"
        echo "See /tmp/dropin_check_middle.log for full output"
        grep -E "^error" /tmp/dropin_check_middle.log | head -50 || true
        RESULT=1
    fi
fi

echo ""
echo "========================================"
if [[ $RESULT -eq 0 ]]; then
    echo -e "${GREEN}SUCCESS: Drop-in replacement works!${NC}"
    echo "Our verified rustc_index is compatible with rustc_middle"
else
    echo -e "${RED}FAILURE: Drop-in replacement broke the build${NC}"
    echo "Fix errors in /tmp/dropin_check_*.log"
fi
echo "========================================"

exit $RESULT
