# URGENT: STOP POLISHING, START INTEGRATING

**Date**: 2024-12-30
**Priority**: IMMEDIATE - DROP EVERYTHING ELSE

## THE PROBLEM

We have 186 tests passing on **fake MIR**. Zero real Rust code verified.

```
CURRENT (USELESS):
  hand_written_mir() → VC → Z3 → ✓

NEEDED (THE GOAL):
  actual_rust_code.rs → rustc → MIR → VC → Z3 → ✓
```

## STOP DOING

- ❌ Adding more tests to vc_ir
- ❌ Polishing WP calculus
- ❌ Fixing warnings
- ❌ Anything that doesn't connect to real rustc

## START DOING

### Option A: cargo-trust binary (FASTEST)

Create a binary that uses rustc as a library to compile real Rust and extract MIR:

```rust
// tools/cargo-trust/src/main.rs
use rustc_driver::Callbacks;
use rustc_interface::interface;
use rustc_middle::mir::Body;

fn main() {
    // 1. Parse command line (file to verify)
    // 2. Invoke rustc to compile it
    // 3. Extract MIR for functions with #[requires]/#[ensures]
    // 4. Run through our VC pipeline
    // 5. Report results
}
```

### Option B: rustc_private integration

Add our verification as a rustc callback:

```rust
struct TrustCallbacks;

impl Callbacks for TrustCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            // For each function with specs, verify it
            for def_id in tcx.mir_keys(()) {
                let mir = tcx.optimized_mir(def_id);
                // Convert to our MIR, generate VCs, check with Z3
            }
        });
        Compilation::Continue
    }
}
```

## IMMEDIATE TASK

1. Create `tools/cargo-trust/` directory
2. Set up Cargo.toml with rustc_private dependencies
3. Write minimal driver that:
   - Compiles a single .rs file
   - Prints MIR for one function
4. That's it. Just prove we can access real MIR.

## SUCCESS CRITERIA

```bash
$ cargo trust verify examples/hello_verified.rs
Compiling hello_verified.rs...
Extracting MIR for clamp_positive...
[MIR dump appears here]
```

**If you can print real MIR, we can verify real code.**

## REFERENCE

- rustc dev guide: https://rustc-dev-guide.rust-lang.org/
- rustc_driver: upstream/rustc/compiler/rustc_driver/
- rustc_interface: upstream/rustc/compiler/rustc_interface/
- Kani does this: https://github.com/model-checking/kani

## DO NOT

- Do not add more unit tests
- Do not refactor existing code
- Do not fix warnings
- Do not touch vc_ir, trust_z3, trust_macros

**FOCUS: Get real MIR from real Rust code.**
