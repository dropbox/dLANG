# vc-ir-swift

Rust bridge + verifier for tSwift verification conditions.

## Z4 (default)

This crate uses the pure-Rust Z4 SMT solver by default.

```bash
cargo test
```

## Z3 fallback (optional)

Enable Z3 as a fallback solver for non-linear arithmetic.

### Option 1: System Z3 (`z3-fallback`)

```bash
cargo test --features z3-fallback
```

Requires a system Z3 install (headers + library). On macOS with Homebrew:

```bash
brew install z3
export Z3_SYS_Z3_HEADER=/opt/homebrew/include/z3.h
export LIBRARY_PATH=/opt/homebrew/lib${LIBRARY_PATH:+:$LIBRARY_PATH}
```

If you see `z3.h file not found`, verify `Z3_SYS_Z3_HEADER` points to the correct `z3.h`.

### Option 2: Static linking (`z3-static`) - DEPRECATED

**Status: BROKEN** - The z3-sys 0.8.1 bundled Z3 source has C++ compiler compatibility
issues with modern toolchains (typo: `m_low_bound` vs `m_lower_bound` in lp solver).

```bash
# This will fail to build
cargo test --features z3-static
```

Use `z3-fallback` with system Z3 instead.

### Future: z3 0.19+ upgrade

The z3 crate v0.19 uses z3-sys 0.10.4 which has fixed bundled build support, but
requires significant API migration (context management redesigned). See Cargo.toml
for details. Migration tracked for future work.
