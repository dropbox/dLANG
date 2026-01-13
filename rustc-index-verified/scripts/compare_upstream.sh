#!/bin/bash
# compare_upstream.sh - Compare our API against upstream rustc_index
# Exit 1 if any critical differences found

set -e

UPSTREAM=~/tRust/upstream/rustc/compiler/rustc_index/src
OURS=./src
UPSTREAM_CARGO=~/tRust/upstream/rustc/compiler/rustc_index/Cargo.toml
OURS_CARGO=./Cargo.toml

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

ERRORS=0

echo "=== rustc-index-verified vs upstream rustc_index ==="
echo ""

# 1. Check lib.rs structure
echo "=== Checking lib.rs ==="
echo ""

# Check for newtype_index re-export
if grep -q "pub use rustc_index_macros::newtype_index" $UPSTREAM/lib.rs; then
    if grep -q "pub use rustc_index_macros::newtype_index" $OURS/lib.rs 2>/dev/null; then
        echo -e "${GREEN}[OK]${NC} newtype_index re-export present"
    else
        echo -e "${RED}[MISSING]${NC} newtype_index re-export"
        ERRORS=$((ERRORS + 1))
    fi
fi

# Check for static_assert_size macro
if grep -q "macro_rules! static_assert_size" $UPSTREAM/lib.rs; then
    if grep -q "macro_rules! static_assert_size" $OURS/lib.rs 2>/dev/null; then
        echo -e "${GREEN}[OK]${NC} static_assert_size macro present"
    else
        echo -e "${RED}[MISSING]${NC} static_assert_size macro"
        ERRORS=$((ERRORS + 1))
    fi
fi

# Check module visibility
echo ""
echo "--- Module visibility ---"

# bit_set should be public
if grep -q "^pub mod bit_set" $UPSTREAM/lib.rs; then
    if grep -q "^pub mod bit_set" $OURS/lib.rs; then
        echo -e "${GREEN}[OK]${NC} bit_set is public"
    else
        echo -e "${RED}[MISMATCH]${NC} bit_set should be public"
        ERRORS=$((ERRORS + 1))
    fi
fi

# interval should be pub (with cfg)
if grep -q "pub mod interval" $UPSTREAM/lib.rs; then
    if grep -q "pub mod interval" $OURS/lib.rs 2>/dev/null; then
        echo -e "${GREEN}[OK]${NC} interval is public"
    else
        echo -e "${RED}[MISMATCH]${NC} interval should be public (with #[cfg(feature = \"nightly\")])"
        ERRORS=$((ERRORS + 1))
    fi
fi

# Check cfg attributes
echo ""
echo "--- cfg attributes ---"
for attr in 'cfg_attr(feature = "nightly"' 'warn(unreachable_pub)'; do
    if grep -q "$attr" $UPSTREAM/lib.rs; then
        if grep -q "$attr" $OURS/lib.rs 2>/dev/null; then
            echo -e "${GREEN}[OK]${NC} Has $attr"
        else
            echo -e "${YELLOW}[WARN]${NC} Missing $attr"
        fi
    fi
done

# 2. Compare public functions
echo ""
echo "=== Comparing Public Functions ==="
echo ""

for mod in bit_set interval slice vec idx; do
    upstream_file="$UPSTREAM/$mod.rs"
    ours_file="$OURS/$mod.rs"

    if [[ -f "$upstream_file" && -f "$ours_file" ]]; then
        # Count public functions
        upstream_count=$(grep -c "pub fn\|pub const fn" "$upstream_file" 2>/dev/null || echo 0)
        ours_count=$(grep -c "pub fn\|pub const fn" "$ours_file" 2>/dev/null || echo 0)

        if [[ "$upstream_count" -eq "$ours_count" ]]; then
            echo -e "${GREEN}[OK]${NC} $mod.rs: $ours_count pub functions (matches upstream)"
        else
            echo -e "${YELLOW}[DIFF]${NC} $mod.rs: upstream=$upstream_count, ours=$ours_count"
        fi

        # Check for specific missing functions by extracting function names
        echo "  Checking function signatures..."

        # Extract function names from upstream
        upstream_funcs=$(grep "pub fn\|pub const fn" "$upstream_file" 2>/dev/null | sed 's/.*fn \([a-zA-Z_][a-zA-Z0-9_]*\).*/\1/' | sort -u)
        ours_funcs=$(grep "pub fn\|pub const fn" "$ours_file" 2>/dev/null | sed 's/.*fn \([a-zA-Z_][a-zA-Z0-9_]*\).*/\1/' | sort -u)

        # Find missing functions
        missing=$(comm -23 <(echo "$upstream_funcs") <(echo "$ours_funcs"))
        if [[ -n "$missing" ]]; then
            echo -e "  ${RED}[MISSING]${NC} Functions in $mod.rs:"
            echo "$missing" | sed 's/^/    - /'
            ERRORS=$((ERRORS + 1))
        fi

        # Find extra functions (we have but upstream doesn't)
        extra=$(comm -13 <(echo "$upstream_funcs") <(echo "$ours_funcs"))
        if [[ -n "$extra" ]]; then
            echo -e "  ${YELLOW}[EXTRA]${NC} Functions in $mod.rs (not in upstream):"
            echo "$extra" | sed 's/^/    - /'
        fi
    elif [[ -f "$upstream_file" && ! -f "$ours_file" ]]; then
        echo -e "${RED}[MISSING]${NC} $mod.rs file missing entirely"
        ERRORS=$((ERRORS + 1))
    fi
done

# 3. Check for unimplemented!() calls
echo ""
echo "=== Checking for unimplemented!() ==="
echo ""

unimpl_count=$(grep -c "unimplemented!" $OURS/*.rs 2>/dev/null || echo 0)
if [[ "$unimpl_count" -gt 0 ]]; then
    echo -e "${RED}[CRITICAL]${NC} Found $unimpl_count unimplemented!() calls:"
    grep -n "unimplemented!" $OURS/*.rs 2>/dev/null | head -10
    ERRORS=$((ERRORS + 1))
else
    echo -e "${GREEN}[OK]${NC} No unimplemented!() calls"
fi

# 4. Compare public types
echo ""
echo "=== Comparing Public Types ==="
echo ""

upstream_types=$(grep -h "^pub struct\|^pub enum\|^pub trait" $UPSTREAM/*.rs 2>/dev/null | sed 's/pub \(struct\|enum\|trait\) \([a-zA-Z_][a-zA-Z0-9_]*\).*/\2/' | sort -u)
ours_types=$(grep -h "^pub struct\|^pub enum\|^pub trait" $OURS/*.rs 2>/dev/null | sed 's/pub \(struct\|enum\|trait\) \([a-zA-Z_][a-zA-Z0-9_]*\).*/\2/' | sort -u)

missing_types=$(comm -23 <(echo "$upstream_types") <(echo "$ours_types"))
if [[ -n "$missing_types" ]]; then
    echo -e "${RED}[MISSING]${NC} Types:"
    echo "$missing_types" | sed 's/^/  - /'
    ERRORS=$((ERRORS + 1))
else
    echo -e "${GREEN}[OK]${NC} All public types present"
fi

# 5. Check Cargo.toml
echo ""
echo "=== Checking Cargo.toml ==="
echo ""

# Package name
upstream_name=$(grep "^name = " $UPSTREAM_CARGO | head -1 | sed 's/name = "\(.*\)"/\1/')
ours_name=$(grep "^name = " $OURS_CARGO | head -1 | sed 's/name = "\(.*\)"/\1/')

if [[ "$upstream_name" == "$ours_name" ]]; then
    echo -e "${GREEN}[OK]${NC} Package name: $ours_name"
else
    echo -e "${RED}[MISMATCH]${NC} Package name: upstream='$upstream_name', ours='$ours_name'"
    ERRORS=$((ERRORS + 1))
fi

# Key dependencies
for dep in "rustc_index_macros" "arrayvec" "smallvec"; do
    if grep -q "$dep" $UPSTREAM_CARGO; then
        if grep -q "$dep" $OURS_CARGO; then
            echo -e "${GREEN}[OK]${NC} Dependency: $dep"
        else
            echo -e "${RED}[MISSING]${NC} Dependency: $dep"
            ERRORS=$((ERRORS + 1))
        fi
    fi
done

# Features
echo ""
echo "--- Features ---"
if grep -q "rustc_randomized_layouts" $UPSTREAM_CARGO; then
    if grep -q "rustc_randomized_layouts" $OURS_CARGO; then
        echo -e "${GREEN}[OK]${NC} Feature: rustc_randomized_layouts"
    else
        echo -e "${YELLOW}[WARN]${NC} Feature: rustc_randomized_layouts missing"
    fi
fi

# 6. Summary
echo ""
echo "========================================"
if [[ $ERRORS -gt 0 ]]; then
    echo -e "${RED}FAILED: $ERRORS critical differences found${NC}"
    echo "Fix these before testing as drop-in replacement"
    exit 1
else
    echo -e "${GREEN}PASSED: No critical differences found${NC}"
    echo "Ready to test as drop-in replacement"
    exit 0
fi
