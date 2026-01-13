# tSwift Compiler Build Guide

This document describes how to build the tSwift-modified Swift compiler on macOS.

## Directory Layout

tSwift maintains a clear separation between upstream Swift and our modifications:

```
~/tSwift/                           # tSwift project root
├── upstream/swift/                 # Read-only upstream reference (DO NOT EDIT)
├── compiler/                       # Our modification patches
│   ├── verification_attributes_v3.patch
│   └── ...
├── patches/                        # Additional integration patches
│   ├── verification_attributes.patch
│   ├── verification_attributes_visitors.patch
│   ├── verification_cmakelists.patch
│   └── verification_pipeline_integration.patch
└── vc-ir-swift/                    # Rust verification toolchain

~/swift-project/                    # Swift build environment (separate from tSwift)
├── swift/                          # Editable fork (patches applied here)
├── llvm-project/                   # Cloned by update-checkout
├── swift-syntax/
├── swiftpm/
├── swift-corelibs-foundation/
├── swift-corelibs-libdispatch/
├── swift-corelibs-xctest/
└── build/                          # Build output
    └── Ninja-RelWithDebInfoAssert/
        └── swift-macosx-arm64/bin/swiftc  # Built compiler
```

**Key principle**: `~/tSwift/upstream/swift/` is a read-only reference. All edits happen in `~/swift-project/swift/` after patches are applied.

## Prerequisites

### macOS

1. **Xcode** (check minimum version at https://ci.swift.org)
   ```sh
   xcode-select --install
   ```

2. **Ninja and Sccache**
   ```sh
   brew install ninja sccache
   ```

3. **Python 3.6+**
   ```sh
   python3 --version  # Should be 3.6 or higher
   ```

4. **Git 2.x**
   ```sh
   git --version
   ```

5. **Disk Space**: At least 150 GB free
6. **RAM**: At least 8 GB (16 GB recommended)

### Apple Silicon Note

On M1/M2/M3 Macs, ensure you're running native arm64 tools:
```sh
uname -m                      # Should print "arm64"
file $(which python3)         # Should contain "arm64"
```

If it prints "x86_64", your terminal is running in Rosetta mode.

## Quick Start

### Option 1: Using the Fork Management Script (Recommended)

```sh
cd ~/tSwift
./scripts/manage_fork.sh setup    # Clone Swift + dependencies, apply patches
./scripts/manage_fork.sh build    # Build the compiler
./scripts/manage_fork.sh verify   # Verify the build
```

### Option 2: Manual Steps

#### Step 1: Clone Swift and Dependencies

```sh
mkdir -p ~/swift-project
cd ~/swift-project

# Clone Swift
git clone https://github.com/swiftlang/swift.git swift
cd swift

# Clone all dependencies (llvm-project, swift-syntax, etc.)
utils/update-checkout --clone-with-ssh
# Or via HTTPS:
# utils/update-checkout --clone

cd ..
ls  # Should show: swift, llvm-project, swift-syntax, swiftpm, etc.
```

#### Step 2: Apply tSwift Patches

```sh
cd ~/swift-project/swift

# Apply verification attribute patches
git apply ~/tSwift/compiler/verification_attributes_v3.patch
git apply ~/tSwift/patches/verification_attributes.patch
git apply ~/tSwift/patches/verification_attributes_visitors.patch
git apply ~/tSwift/patches/verification_cmakelists.patch
git apply ~/tSwift/patches/verification_pipeline_integration.patch

# Commit the changes (creates a checkpoint)
git add -A
git commit -m "Apply tSwift verification attribute patches"
```

#### Step 3: Build the Compiler

```sh
cd ~/swift-project/swift

# macOS build (adjust --sccache flag based on your setup)
utils/build-script \
  --skip-build-benchmarks \
  --swift-darwin-supported-archs "$(uname -m)" \
  --release-debuginfo \
  --swift-disable-dead-stripping \
  --bootstrapping=hosttools \
  --sccache
```

Build time: 30 minutes to several hours depending on your machine.

#### Step 4: Verify the Build

```sh
# Test the built compiler
~/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-$(uname -m)/bin/swiftc --version

# Compile a simple test
echo 'print("Hello, tSwift!")' > /tmp/test.swift
~/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-$(uname -m)/bin/swiftc /tmp/test.swift -o /tmp/test
/tmp/test
```

## Updating from Upstream

To pull new changes from upstream Swift:

```sh
cd ~/swift-project/swift

# Save your local changes
git stash

# Update all repos to latest
utils/update-checkout --clone-with-ssh

# Reapply patches
git stash pop  # If you had changes
# OR re-apply patches:
git apply ~/tSwift/compiler/verification_attributes_v3.patch
# ... etc.

# Rebuild
utils/build-script ...
```

## Patch Development Workflow

When developing new compiler modifications:

1. **Make changes** in `~/swift-project/swift/`
2. **Test** by rebuilding and running tests
3. **Create patch** when ready:
   ```sh
   cd ~/swift-project/swift
   git diff HEAD > ~/tSwift/patches/my_new_feature.patch
   ```
4. **Commit patch** to tSwift repo

## Build Configurations

### Debug Build (Faster Compilation, Slower Runtime)

```sh
utils/build-script --debug
```

### Release Build (Slower Compilation, Faster Runtime)

```sh
utils/build-script --release
```

### Incremental Builds

After the first build, incremental builds are much faster:
```sh
cd ~/swift-project/build/Ninja-RelWithDebInfoAssert
ninja swift-frontend
```

## Troubleshooting

### Build Fails with Missing Dependencies

Ensure all sibling repos are cloned:
```sh
cd ~/swift-project
ls  # Should show: swift, llvm-project, swift-syntax, swiftpm, etc.
```

If repos are missing:
```sh
cd ~/swift-project/swift
utils/update-checkout --clone-with-ssh
```

### Patch Application Fails

If patches fail to apply cleanly:
1. Check if upstream has changed the target files
2. Use `git apply --3way` for three-way merge
3. Update patches to match current upstream

### Out of Memory

Add swap or reduce parallelism:
```sh
utils/build-script ... --jobs 4  # Limit to 4 parallel jobs
```

### Xcode Version Issues

Check minimum required Xcode version at https://ci.swift.org

## Integration with tSwift Verifier

Once the compiler is built, configure `tswiftv` to use it:

```sh
export TSWIFT_COMPILER=~/swift-project/build/Ninja-RelWithDebInfoAssert/swift-macosx-$(uname -m)/bin/swiftc
```

Or edit `bin/tswiftv` to use the custom compiler path.

## References

- [Swift Getting Started Guide](https://github.com/swiftlang/swift/blob/main/docs/HowToGuides/GettingStarted.md)
- [Swift Build Manifesto](https://github.com/swiftlang/swift/blob/main/docs/BuildManifesto.md)
- [Debugging the Swift Compiler](https://github.com/swiftlang/swift/blob/main/docs/DebuggingTheCompiler.md)
