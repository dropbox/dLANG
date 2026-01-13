# tSwift Compiler Integration Guide

This document explains how to integrate the tSwift formal verification pass into the Apple Swift compiler.

## Prerequisites

### macOS Build Environment

**CRITICAL:** The Swift compiler build requires **Xcode** (not just CommandLineTools). The build will fail with SDK/toolchain mismatches if the wrong developer tools are selected.

1. **Install Xcode** from the App Store

2. **Set DEVELOPER_DIR** (don't use `sudo xcode-select`):
   ```bash
   # Always use DEVELOPER_DIR instead of xcode-select
   export DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer
   ```

3. **Verify SDK version matches toolchain:**
   ```bash
   # Check Xcode version
   DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer xcodebuild -version

   # Check available SDKs
   ls /Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/
   ```

**Common Error:** If you see this error, your developer tools are pointing to CommandLineTools:
```
error: failed to build module 'Swift'; this SDK is not supported by the compiler
(the SDK is built with 'Apple Swift version 6.2 effective-5.10', while this
compiler is 'Apple Swift version 6.0.3 effective-5.10')
```

**Fix:** Reconfigure CMake with the correct SDK:
```bash
cd ~/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-arm64
DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer cmake \
    -DSWIFT_CONCURRENCY_GLOBAL_EXECUTOR=dispatch \
    -D"SWIFT_COMPILER_SOURCES_SDK_FLAGS=-sdk;/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk" \
    .
```

Or use the helper script: `./scripts/build-swift-project.sh`

### Swift Source Checkout

1. **Swift source checkout:**
   ```bash
   mkdir ~/swift-project
   cd ~/swift-project
   git clone https://github.com/apple/swift.git swift
   # Or use update-checkout: ./swift/utils/update-checkout --clone
   ```

2. **Build dependencies:**
   Follow [Getting Started](https://github.com/apple/swift/blob/main/docs/HowToGuides/GettingStarted.md)

## Integration Steps

### Step 1: Apply Patches

Apply the tSwift verification patches to the Swift source:

```bash
cd ~/swift-project/swift

# Apply verification attributes (AST additions)
patch -p1 < ~/tSwift/compiler/verification_attributes_v3.patch

# Apply attribute visitor hooks
patch -p1 < ~/tSwift/patches/verification_attributes_visitors.patch

# Apply pipeline integration (compiler options, pass registration)
patch -p1 < ~/tSwift/patches/verification_pipeline_integration.patch
```

### Step 2: Copy Verification Sources

Copy the verification pass implementation:

```bash
# Create the Verification directory
mkdir -p ~/swift-project/swift/lib/SILOptimizer/Verification

# Copy source files
cp ~/tSwift/compiler/lib/SILOptimizer/Verification/*.cpp \
   ~/swift-project/swift/lib/SILOptimizer/Verification/

cp ~/tSwift/compiler/lib/SILOptimizer/Verification/*.h \
   ~/swift-project/swift/lib/SILOptimizer/Verification/

# Copy include file for VerificationSpec
mkdir -p ~/swift-project/swift/include/swift/SILOptimizer/Verification
cp ~/tSwift/compiler/include/swift/SILOptimizer/Verification/*.h \
   ~/swift-project/swift/include/swift/SILOptimizer/Verification/
```

### Step 3: Create CMakeLists.txt

Create the CMakeLists.txt for the Verification directory:

```bash
cat > ~/swift-project/swift/lib/SILOptimizer/Verification/CMakeLists.txt << 'EOF'
target_sources(swiftSILOptimizer PRIVATE
  ConditionParser.cpp
  SilTranslator.cpp
  SpecExtraction.cpp
  SILVerificationPass.cpp
  SolverInterface.cpp
  VcIrGen.cpp
)
EOF
```

### Step 4: Build Swift

Build the Swift compiler with verification support:

```bash
cd ~/swift-project
./swift/utils/build-script --release-debuginfo \
    --skip-build-benchmarks \
    --skip-ios --skip-tvos --skip-watchos
```

For faster incremental builds after changes:

```bash
cd ~/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-arm64
ninja swift-frontend
```

## Usage

### Command-Line Flags

| Flag | Description |
|------|-------------|
| `-enable-formal-verification` | Enable formal verification of @_requires/@_ensures contracts |
| `-verify-timeout <ms>` | Solver timeout in milliseconds (default: 30000) |
| `-verify-report <path>` | Output JSON verification report |
| `-verify-json-export <path>` | Export VC bundles as JSONL (machine-readable VC IR) |

### Example

```swift
// verify_test.swift

@_requires("x > 0")
@_ensures("result > 0")
func positiveDouble(_ x: Int) -> Int {
    return x * 2
}
```

```bash
# Set up paths
SWIFT_FRONTEND=~/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-arm64/bin/swift-frontend
SDK=/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk
RESOURCE_DIR=~/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-arm64/lib/swift

# Compile with verification
$SWIFT_FRONTEND -enable-formal-verification \
    -verify-timeout 1000 \
    -verify-report /tmp/verify_report.json \
    -verify-json-export /tmp/vc_bundle.jsonl \
    -emit-sil verify_test.swift \
    -sdk $SDK -resource-dir $RESOURCE_DIR

# Expected output:
# [VERIFY] $s11verify_test14positiveDoubleyS2iF: VERIFIED (unsat) [0.008s]
# [AUTO-VC] positiveDouble (verify_test.swift:5:12): overflow check for mul operation - POTENTIAL OVERFLOW [0.01s]
```

**Note:** The auto-VC correctly detects that `x * 2` can overflow when `x > Int.max/2`, even though the contract is verified.

### Auto-VC Mode

The verification pass automatically detects potential issues without explicit annotations:

```bash
# Verification runs automatically on all functions
$SWIFT_FRONTEND -enable-formal-verification -emit-sil test.swift -sdk $SDK -resource-dir $RESOURCE_DIR
```

Output includes:
```
[VERIFY] $s... : VERIFIED (unsat) [0.008s]      # Proven by SMT solver
[VERIFY] $s... : TRUSTED (assumed correct) [0.000s]  # @_trusted functions
[AUTO-VC] functionName (file.swift:42:10): overflow check for mul operation - SAFE [0.003s]
[AUTO-VC] functionName (file.swift:45:5): bounds check for index - POTENTIAL OUT OF BOUNDS [0.005s]
[VERIFY SUMMARY] 3 verified, 1 trusted (0.016s total)  # Aggregate summary
```

The `[VERIFY SUMMARY]` line outputs at the end of compilation showing aggregate counts:
- **verified**: Functions proven correct by SMT solver
- **trusted**: Functions marked `@_trusted` (assumed correct)
- **failed**: Functions with verification failures
- **unknown**: Functions where solver returned unknown
- **timeout**: Functions that timed out
- **error**: Functions with verification errors

The `[VERIFY]` output distinguishes between:
- **VERIFIED (unsat)**: Postconditions proven correct by SMT solver
- **TRUSTED (assumed correct)**: Functions marked `@_trusted` (not verified, assumed correct)

Auto-VCs detect:
- Integer overflow (signed multiplication, addition, subtraction)
- Division by zero
- Array bounds checks

### JSON Report

```bash
$SWIFT_FRONTEND -enable-formal-verification \
    -verify-report /tmp/report.json \
    -emit-sil test.swift -sdk $SDK -resource-dir $RESOURCE_DIR
```

Report format (one JSON object per line):
```json
{"function":"double","mangled":"$s...","file":"test.swift","line":3,"column":6,"result":"verified","time_seconds":0.008,"specs":[{"kind":"requires","condition":"x > 0"},{"kind":"ensures","condition":"result > 0"}]}
{"function":"trustedFn","mangled":"$s...","file":"test.swift","line":10,"column":1,"result":"trusted","time_seconds":0,"is_trusted":true,"specs":[]}
{"type":"auto_vc","function":"double","kind":"overflow","description":"overflow check for mul operation","result":"potential_overflow","time_seconds":0.01,"file":"test.swift","line":4,"column":14,"counterexample":"..."}
{"type":"summary","verified":3,"trusted":1,"failed":0,"unknown":0,"timeout":0,"error":0,"no_specs":2,"total_time_seconds":0.123}
```

The summary line (`"type":"summary"`) is always written last, containing aggregate counts:
- `verified`: Functions proven correct by SMT solver
- `trusted`: Functions marked `@_trusted` (assumed correct, not verified)
- `failed`: Functions with verification failures
- `unknown`: Functions where solver returned unknown
- `timeout`: Functions that timed out
- `error`: Functions with verification errors
- `no_specs`: Functions without @_requires/@_ensures (in `-verify-all-functions` mode)
- `total_time_seconds`: Total verification time

The `result` field can be:
- `"verified"`: Proven correct by SMT solver
- `"trusted"`: Function marked `@_trusted` (not verified)
- `"failed"`: Verification failed (counterexample found)
- `"unknown"`: Solver returned unknown
- `"timeout"`: Solver timed out
- `"error"`: Verification error

### VC Bundle Export (Machine-Readable)

```bash
$SWIFT_FRONTEND -enable-formal-verification \
    -verify-json-export /tmp/vc_bundle.jsonl \
    -emit-sil test.swift -sdk $SDK -resource-dir $RESOURCE_DIR
```

This exports the full VC IR AST including parsed conditions, parameters, and auto-VCs in a machine-readable format.

## Architecture

```
Swift Source
     │
     ▼
┌─────────────┐
│   Parser    │  ← @_requires, @_ensures, @_invariant, @_trusted
└─────────────┘
     │
     ▼
┌─────────────┐
│    AST      │  ← RequiresAttr, EnsuresAttr, InvariantAttr
└─────────────┘
     │
     ▼
┌─────────────┐
│   SILGen    │  ← Lowering to SIL
└─────────────┘
     │
     ▼
┌─────────────────────────────────────┐
│   Mandatory Diagnostic Passes       │
└─────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────┐
│   SILVerificationPass (tSwift)      │  ← Runs here, AST still accessible
│   - Extract specs from AST          │
│   - Collect auto-VCs from SIL       │
│   - Generate SMT-LIB2               │
│   - Invoke Z3/Z4 solver             │
│   - Report results                  │
└─────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────┐
│   Optimization / Lowering Passes    │
└─────────────────────────────────────┘
     │
     ▼
   IRGen
```

## Files Overview

| File | Purpose |
|------|---------|
| `SILVerificationPass.cpp` | Main pass entry point |
| `SpecExtraction.cpp` | Extract @requires/@ensures from AST |
| `ConditionParser.cpp` | Parse condition strings into AST |
| `ConditionAST.h` | Condition expression AST |
| `SilTranslator.cpp` | SIL → ConditionExpr translation |
| `VcIrGen.cpp` | Generate SMT-LIB2 verification conditions |
| `SolverInterface.cpp` | Invoke Z3/Z4 solver |

## Troubleshooting

### "No AbstractFunctionDecl, skipping"

This means the pass cannot access the AST. Ensure:
1. Pass runs during diagnostic pipeline (not via sil-opt)
2. Patches are applied correctly
3. Pass is scheduled after SILGen but before lowering

### Solver not found

The pass looks for `z3` in PATH. Install Z3:
```bash
brew install z3
```

### Build errors about undefined types

Ensure the verification attributes patch is applied:
```bash
patch -p1 < ~/tSwift/compiler/verification_attributes_v3.patch
```

## Test Suite

### Rust CLI Tests

```bash
cd ~/tSwift/vc-ir-swift
cargo test
```

Expected: 425+ tests passing

### End-to-End Verification Test

```bash
# Create test file
cat > /tmp/verify_test.swift << 'EOF'
@_requires("x > 0")
@_ensures("result > 0")
func double(_ x: Int) -> Int {
    return x * 2
}
EOF

# Run verification
$SWIFT_FRONTEND -enable-formal-verification \
    -verify-report /tmp/verify_report.json \
    -emit-sil /tmp/verify_test.swift \
    -sdk $SDK -resource-dir $RESOURCE_DIR
```

Expected output:
```
[VERIFY] $s11verify_test6doubleyS2iF: VERIFIED (unsat) [0.008s]
[AUTO-VC] double (verify_test.swift:4:14): overflow check for mul operation - POTENTIAL OVERFLOW [0.01s]
```

## Next Steps

After successful integration:
1. Test with real Swift projects
2. Tune solver timeout for your hardware
3. Consider implementing Kani/Lean backends
4. Integrate with tRust for FFI boundary verification

See [ROADMAP_UNIFIED.md](ROADMAP_UNIFIED.md) for the full project plan.
