# tSwift

| Director | Status |
|:--------:|:------:|
| LANG | ACTIVE |

**Swift where compilation is verification.**

A fork of Apple's Swift compiler that integrates formal verification directly into compilation. Combined with [tRust](https://github.com/dropbox/tRust), enables end-to-end verified native iOS/macOS applications.

## Philosophy

> Everything that CAN be verified automatically MUST be verified by default.

No annotations required for safety properties. If the compiler can prove it, it proves it.

```swift
// NO SPECS - tSwift auto-verifies these:

func guardedAdd(_ a: UInt8, _ b: UInt8) -> UInt8 {
    if a < 100 && b < 100 {
        return a + b  // ✓ VERIFIED: 99 + 99 = 198 <= 255
    }
    return 0
}

func guardedDivide(_ a: Int, _ b: Int) -> Int {
    if b != 0 {
        return a / b  // ✓ VERIFIED: b != 0 from path condition
    }
    return 0
}

func guardedIndex(_ arr: [Int], _ i: Int) -> Int {
    if i >= 0 && i < arr.count {
        return arr[i]  // ✓ VERIFIED: i in bounds
    }
    return 0
}
```

Specs are only needed for business logic the compiler can't infer:

```swift
@requires("account.isActive")
@requires("amount <= account.balance")
@ensures("account.balance == old(account.balance) - amount")
func withdraw(from account: inout Account, amount: UInt) {
    account.balance -= amount  // Overflow already auto-verified
}
```

## Architecture

```
┌─────────────┐     ┌─────────────┐
│   tRust     │     │   tSwift    │
│  (rustc)    │     │  (swiftc)   │
│     ↓       │     │     ↓       │
│    MIR      │     │    SIL      │
└──────┬──────┘     └──────┬──────┘
       └─────────┬─────────┘
                 ↓
          ┌─────────────┐
          │   VC IR     │  ← Shared verification format
          └──────┬──────┘
                 ↓
     ┌───────────┼───────────┐
     ↓           ↓           ↓
  ┌─────┐   ┌─────────┐  ┌──────┐
  │ Z4  │   │  Kani   │  │ Lean │
  │ SMT │   │  Fast   │  │  5   │
  └─────┘   └─────────┘  └──────┘
```

## Project Structure

```
tSwift/
├── upstream/swift/     # Apple's Swift compiler (clone separately)
├── tswift-macros/      # Swift macros: @requires, @ensures, @invariant, @trusted
├── vc-ir-swift/        # Swift bindings to VC IR crate
├── bin/                # Wrapper scripts (tswift verify)
├── examples/           # Demo verification examples
├── tests/              # Verification test cases
└── docs/               # Design documents
```

## Quick Start

```bash
# Clone the repo
git clone git@github.com:dropbox/dLANG/tSwift.git
cd tSwift

# Build the verifier
cd vc-ir-swift
cargo build --release
cd ..

# Use as drop-in replacement for swiftc
bin/tswiftv main.swift -o main      # Compile WITH verification (default)
bin/tswiftv --no-verify main.swift  # Skip verification (passthrough to swiftc)
bin/tswiftv verify main.swift       # Verify only (no output binary)

# All swiftc flags work
bin/tswiftv -emit-executable main.swift -o main
bin/tswiftv -emit-library lib.swift -o libfoo.dylib
bin/tswiftv -emit-sil main.swift
```

### Example Output

```
=== examples/hello_verified.swift ===
  Function: main (hello_verified.swift:48)
      Specification VERIFIED (0.000s)
  Auto-VC #1 (call to ... requires: x > -9223372036854775807) VERIFIED (0.003s)
  Function: absoluteValue (hello_verified.swift:15)
      Specification VERIFIED (0.001s)
  Auto-VC #1 (arithmetic overflow) at hello_verified.swift:19:16 VERIFIED (0.000s)
  Function: isPositive (hello_verified.swift:28)
      Specification VERIFIED (0.000s)
  Function: max (hello_verified.swift:37)
      Specification VERIFIED (0.000s)

Summary: 6 verified, 0 failed, 0 unknown (0.004s)
```

### Try the Examples

```bash
# User specs are proven correct
bin/tswiftv verify examples/hello_verified.swift --verbose

# Auto-VC detects potential overflow
bin/tswiftv verify examples/overflow_bug.swift --verbose

# Division by zero detection
bin/tswiftv verify examples/division_safe.swift --verbose

# Array bounds checking
bin/tswiftv verify examples/bounds_check.swift --verbose

# Force unwrap (nil check) detection
bin/tswiftv verify examples/force_unwrap.swift --verbose

# Forced type cast detection
bin/tswiftv verify examples/forced_cast.swift --verbose

# Integer truncation detection
bin/tswiftv verify examples/truncation.swift --verbose

# Range bounds violation detection
bin/tswiftv verify examples/range_bounds.swift --verbose
```

## Verification Macros

| Macro | Purpose |
|-------|---------|
| `@requires("condition")` | Precondition - must hold at function entry |
| `@ensures("condition")` | Postcondition - guaranteed at function exit |
| `@invariant("condition")` | Type/property invariant |
| `@trusted` | Skip verification (use sparingly) |

**Note:** Use `@inline(never)` on functions you want to verify to prevent the optimizer from inlining or removing them:

```swift
@inline(never)
@_requires("x >= 0")
@_ensures("result >= 0")
func sqrt(_ x: Int) -> Int { ... }
```

## Auto-VCs (Automatic Verification Conditions)

Auto-VCs are safety checks that tSwift generates **automatically** without any user annotations. The compiler proves these conditions hold at compile time, or shows a counterexample when they can fail.

### Safety Auto-VCs

| Auto-VC | What it catches | Example |
|---------|-----------------|---------|
| **Overflow** | Integer overflow/underflow | `x + 1` when `x = INT_MAX` |
| **DivByZero** | Division by zero | `a / b` when `b = 0` |
| **BoundsCheck** | Array index out of bounds | `arr[i]` when `i < 0` or `i >= count` |
| **NilCheck** | Force unwrap of nil | `optional!` when `optional = nil` |
| **CastCheck** | Invalid forced cast | `x as! String` when `x` isn't a String |
| **CondFail** | Generic runtime assertions | `Int8(x)` when `x > 127` (truncation) |
| **CallPrecondition** | Caller must satisfy callee @requires | `sqrt(-1)` when `@requires("x >= 0")` |
| **ShiftOverflow** | Invalid shift amount | `x << n` when `n >= 64` |
| **UnownedAccess** | Unowned reference after deallocation | `unowned var.value` (flagged) |
| **ActorIsolationCrossing** | Actor boundary crossing | `await actor.method()` (flagged) |

### Termination Auto-VCs

| Auto-VC | What it proves |
|---------|----------------|
| **Termination** | Simple bounded loops terminate |
| **RecursiveTermination** | Recursive calls with decreasing arg |
| **MutualRecursiveTermination** | Mutually recursive function cycles |
| **LexicographicTermination** | Multi-param recursive termination |
| **LexicographicMutualRecursiveTermination** | Multi-param mutual recursion |

### State Invariant Auto-VCs

| Auto-VC | What it checks |
|---------|----------------|
| **StateInvariant** | Method-level invariants after mutations |
| **TypeInvariant** | Type-level invariants (from init) |
| **MethodCallStateEffect** | Invariants after calling state-modifying methods |

### Example: Division by Zero

```swift
func divide(a: Int, b: Int) -> Int {
    return a / b  // Auto-VC: Is b != 0?
}
```

tSwift output:
```
Auto-VC #1 (div by zero check) FAILED
  Counterexample:
    b = 0
```

### Fix with `@_requires`

Add a precondition to shift the proof obligation to callers:

```swift
@_requires("b != 0")
func divide(a: Int, b: Int) -> Int {
    return a / b  // VERIFIED - caller must ensure b != 0
}
```

### Example: Array Bounds

```swift
func getElement(_ arr: [Int], _ index: Int) -> Int {
    return arr[index]  // Auto-VC: Is 0 <= index < arr.count?
}
```

tSwift output:
```
Auto-VC #1 (array subscript index out of bounds) FAILED
  Counterexample:
    index = -1
```

### Path Conditions

tSwift tracks conditions from `if`/`guard` statements:

```swift
func safeDivide(_ a: Int, _ b: Int) -> Int {
    if b != 0 {
        return a / b  // VERIFIED - path condition proves b != 0
    }
    return 0
}
```

No annotations needed - the compiler infers safety from control flow.

## Kani Integration

tSwift integrates with [Kani](https://github.com/model-checking/kani), a Rust model checker, for bounded verification with exact integer semantics.

### Why Kani?

The default Z4 solver uses unbounded integers, which is fast but may miss real overflow bugs. Kani's bitvector mode catches overflows that actually occur on 64-bit machines.

```bash
# Default verification (Z4 - fast, unbounded integers)
bin/tswiftv verify overflow.swift

# Kani verification (bitvector mode - catches real overflows)
bin/tswiftv verify overflow.swift --run-kani --kani-bitvector
```

### Example: Detecting Real Overflow

```swift
func willOverflow(_ x: Int64) -> Int64 {
    return x * 2  // Overflows when x > INT64_MAX/2
}
```

- **Z4 (default):** May report VERIFIED (unbounded math)
- **Kani (bitvector):** Reports FAILED with counterexample `x = 4611686018427387904`

### Requirements

Kani requires installation:

```bash
cargo install --locked kani-verifier
cargo kani setup
```

### Export for Manual Review

Export Kani harnesses without running:

```bash
bin/tswiftv verify file.swift --export-kani=./harnesses
cd harnesses && cargo kani  # Run manually
```

## Testing

Run the verification test suite:

```bash
# Fast test suite (SIL files with expected outcomes)
./tests/run_verification_tests.sh --fast

# Full test suite including Swift source files
./tests/run_verification_tests.sh --fast --swift

# Run all tests (includes informational tests)
./tests/run_verification_tests.sh
```

### Test Naming Convention

| Pattern | Expected Outcome |
|---------|------------------|
| `*safe*.sil/*.swift` | All VCs should verify (exit 0) |
| `*unsafe*.sil/*.swift` | At least one VC should fail (exit 1) |
| `*_should_fail.sil` | At least one VC should fail (exit 1) |
| Other files | Informational only |

### Requirements

- SIL tests: Only require the `tswift-verify` binary
- Swift tests: Require the forked Swift compiler with verification attributes

Set `SWIFTC` environment variable to override the Swift compiler path.

## Related Projects

- [tRust](https://github.com/dropbox/tRust) - Verified Rust compiler
- [swift-bridge](https://github.com/chinedufn/swift-bridge) - Rust-Swift FFI

## License

Apache 2.0 - See [LICENSE](LICENSE)
