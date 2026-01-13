# tSwift Verification Limitations

**Version:** 670
**Date:** 2026-01-07
**Status:** Active

This document describes what tSwift **does NOT verify**. Understanding these limitations is critical for correct usage.

---

## Summary

tSwift provides **automatic verification condition extraction** for common bugs:
- Integer overflow/underflow
- Array bounds checking
- Nil dereference
- Division by zero
- Shift overflow (shift amount must be < bit width)
- Unowned reference access (v347 - flags potentially unsafe accesses)
- Actor isolation crossings (v348 - flags where actor boundaries are crossed)
- User-provided specifications (`@requires`, `@ensures`)

tSwift **does NOT verify**:
- Termination (loops may not terminate)
- Full memory safety (heap allocation, ARC, retain cycles) - but unowned reference access is flagged
- Full concurrency correctness (data races, deadlocks) - but actor isolation crossings are flagged
- Full floating-point arithmetic
- Non-linear arithmetic patterns (requires Z3 fallback - see below)

---

## Critical Limitations

### 1. Z4 Solver Limitations (with Z3 Fallback)

tSwift uses the Z4 pure-Rust SMT solver with **QF_LIA (Quantifier-Free Linear Integer Arithmetic)**.

| Z4 Pattern | Impact | Result | Z3 Fallback |
|-------------|--------|--------|-------------|
| **Non-linear arithmetic** (`x * y` where both are variables) | Cannot verify multiplication of variables | UNKNOWN | **Supported** |
| **Division/modulo with variables** | Reasoning about `x / y`, `x % y` | UNKNOWN | **Supported** |
| **Bitvector operations** | Cannot model exact overflow semantics | UNKNOWN | Not yet |
| **Floating point real arithmetic** | Float/Double are symbolic placeholders | UNKNOWN | Not yet |

**What UNKNOWN means:** The solver could not determine if the condition holds. This is **NOT** a proof - it means the verification is inconclusive. The code may or may not be correct.

**New in v313:** UNKNOWN results now include categorized reasons explaining *why* verification was inconclusive.

**New in v324-325:** Z3 fallback support for non-linear arithmetic. When Z4 returns UNKNOWN due to non-linear patterns (variable multiplication, division), tSwift automatically falls back to Z3 (which supports QF_NIA - Non-linear Integer Arithmetic). v325 wired the fallback into all verification entry points. Requires building with `--features z3-fallback` and having libz3 installed.

```bash
# Build with Z3 fallback support (requires libz3 installed)
Z3_SYS_Z3_HEADER=/opt/homebrew/include/z3.h \
BINDGEN_EXTRA_CLANG_ARGS="-I/opt/homebrew/include" \
cargo build --features z3-fallback
```

If your linker cannot find `-lz3`, set `TSWIFT_Z3_LIB_DIR=/path/to/z3/lib` (or use `RUSTFLAGS="-L/path/to/z3/lib"`).

**Patterns now verified with Z3:**
- `x > 0 && y > 0 => x * y > 0` - Multiplication of positives
- `x > 0 && y > 0 => x / y >= 0` - Division reasoning
- `x * x >= 0` - Squares are non-negative
- `abs(x) >= 0` - Absolute value properties

**New in v368: Z3 Test Behavior Differences**

When building with `--features z3-fallback` or `--all-features`, verification results may be stricter because Z3 can decide cases that Z4 reports as UNKNOWN:

| Test | Z4 Behavior | Z3 Behavior | Reason |
|------|-------------|-------------|--------|
| `cli_sil_mode_detects_multiplication_overflow_autovc` | UNKNOWN (success) | FAILED (overflow found) | Z3 proves `-9223372036854775807 * 2` overflows |
| `cli_sil_mode_verifies_division_with_nonzero_precondition` | VERIFIED | FAILED (overflow found) | Z3 catches `INT_MIN / -1` overflow |
| `cli_sil_mode_verifies_division_json_output` | VERIFIED | FAILED (overflow found) | Same as above |
| `cli_e2e_div_arg_*` tests | UNKNOWN (success) | FAILED | Z3 proves non-linear division expressions |

These are **correct** behaviors - Z3 is more thorough. The default test suite (`cargo test` without features) uses Z4 and passes all tests. To run with Z3:

```bash
# Build and test with Z3 fallback enabled
Z3_SYS_Z3_HEADER=/opt/homebrew/include/z3.h \
BINDGEN_EXTRA_CLANG_ARGS="-I/opt/homebrew/include" \
cargo test --features z3-fallback
```

The CLI tests assert these expected differences when Z3 fallback is enabled.

### 2. Limited Termination Proofs

**New in v314:** Basic termination checking infrastructure is now available for simple loops with detectable induction variables.

**New in v317:** Improved support for real swiftc output patterns including `struct $Int` wrapping and `struct_extract` chains.

**New in v321:** Fixed stack overflow in phi resolution for complex SIL patterns. Loops with cyclic struct operations (`phi -> struct_extract -> struct -> phi`) now translate correctly.

**New in v326:** Basic recursive function termination checking. Recursive calls with obviously decreasing arguments (e.g., `factorial(n-1)`) now generate `RecursiveTermination` VCs.

**New in v340:** Mutual recursion termination checking. When two or more functions call each other in a cycle (e.g., `isEven` calls `isOdd`, `isOdd` calls `isEven`) and a measure decreases across the cycle, `MutualRecursiveTermination` VCs are generated.

**New in v341:** Lexicographic termination ordering. When a recursive function has multiple parameters where different call sites decrease different parameters in lexicographic order, `LexicographicTermination` VCs are generated. For example, the Ackermann function pattern where `ack(m-1, ...)` and `ack(m, n-1)` both terminate because `(m, n)` decreases lexicographically.

**New in v350:** Lexicographic termination for mutual recursion. When mutually recursive functions form a cycle where different edges decrease different parameters in lexicographic order, `LexicographicMutualRecursiveTermination` VCs are generated. This extends the v341 lexicographic termination to cross-function cycles. For example, if `func_a` calls `func_b(m, n-1)` and `func_b` calls `func_a(m-1, n)`, termination is proven because `(m, n)` decreases lexicographically across the cycle.

```swift
// Simple bounded loops CAN be verified for termination:
func countdown(_ n: Int) {
    var i = n
    while i > 0 { i -= 1 }  // Termination provable: measure = i, decreases by 1
}

// Simple recursive functions CAN be verified (v326):
func factorial(_ n: Int) -> Int {
    if n <= 1 { return 1 }
    return n * factorial(n - 1)  // Termination provable: n decreases by 1
}

// Mutual recursion CAN be verified (v340):
func isEven(_ n: Int) -> Bool {
    if n == 0 { return true }
    return isOdd(n - 1)  // Calls isOdd with n-1
}

func isOdd(_ n: Int) -> Bool {
    if n == 0 { return false }
    return isEven(n - 1)  // Calls isEven with n-1
}
// Termination provable: n decreases by 2 per full cycle

// Lexicographic termination CAN be verified (v341):
func ack(_ m: Int, _ n: Int) -> Int {
    if m == 0 { return n + 1 }
    if n == 0 { return ack(m - 1, 1) }  // m decreases
    return ack(m - 1, ack(m, n - 1))    // outer: m decreases; inner: n decreases
}
// Termination provable: (m, n) decreases lexicographically

// Lexicographic MUTUAL recursion CAN be verified (v350):
func func_a(_ m: Int, _ n: Int) -> Int {
    if n == 0 { return m }
    return func_b(m, n - 1)  // n decreases, m same
}

func func_b(_ m: Int, _ n: Int) -> Int {
    if m == 0 { return n }
    return func_a(m - 1, n)  // m decreases, n same
}
// Termination provable: (m, n) decreases lexicographically across cycle

// Complex patterns still cannot be verified:
func complex(_ n: Int) {
    while someCondition() { }  // No induction variable detected
}
```

**What's supported:**
- Loops with detectable integer induction variables
- Simple increment/decrement patterns (step by 1)
- Bounded `for` loops with constant bounds
- **Recursive functions with simple decreasing arguments** (v326)
  - Pattern: `f(param - constant)` where `constant > 0`
  - Direct recursive calls (function calling itself)
- **Mutual recursion with decreasing measure** (v340)
  - Cycle detection via call graph analysis
  - Measure must decrease by constant across full cycle
  - Works for 2+ function cycles
- **Lexicographic termination ordering** (v341)
  - Multiple parameters where different call sites decrease different params
  - At each call site: some param decreases, all earlier params are non-increasing
  - Classic pattern: Ackermann function `ack(m, n)` with `ack(m-1, _)` and `ack(m, n-1)`
- **Lexicographic mutual recursion termination** (v350)
  - Extends lexicographic termination to cross-function cycles
  - At each call edge across the cycle: some param decreases, earlier params non-increasing
  - Pattern: `func_a` calls `func_b(m, n-1)` and `func_b` calls `func_a(m-1, n)`

**What's NOT supported:**
- Loops without clear induction variables
- Nested loops (outer loop only)
- Non-linear measures
- While loops with complex exit conditions
- Recursive functions with non-constant decrease
- Mutual recursion where measure changes non-uniformly

**Impact:**
- Simple bounded loops generate termination VCs
- Simple recursive functions generate `RecursiveTermination` VCs (v326)
- Mutual recursive functions generate `MutualRecursiveTermination` VCs (v340)
- Functions with lexicographic measure generate `LexicographicTermination` VCs (v341)
- Mutual recursion with lexicographic measure generates `LexicographicMutualRecursiveTermination` VCs (v350)
- Complex patterns are silently skipped (no error, but no proof)

**Workaround:** Manual review for patterns that don't generate termination VCs.

### 2.5 SwiftUI State Invariants (v327-v328, v342-v344)

**New in v327:** Basic SwiftUI state machine verification via `StateInvariant` VCs. When a function has `@invariant` annotations and performs state mutations (via `store` or property setters), tSwift generates VCs to verify the invariant holds after each mutation.

**New in v328:** Type-level invariants via `TypeInvariant` VCs. When an `init` function has `@_invariant` annotations, those invariants are registered as **type-level invariants** and are verified in ALL methods of that type that perform state mutations - not just the init.

**New in v342:** Cross-method state flow tracking via `MethodCallStateEffect` VCs. When a method with type invariants calls another method that modifies state, tSwift generates VCs to verify that the invariants still hold after the call returns. This tracks transitive effects of method calls on type invariants.

**New in v343-v344:** Transitive call chain reporting. When a method calls another method that *indirectly* modifies state (e.g., `caller()` calls `mid()` which calls `helper()` which modifies state), the full call chain is now tracked and displayed in CLI output. The VC description shows the path: `"... transitively modifies [count] via: mid -> helper"`. JSON output includes the call chain in the description field.

**New in v345:** CLI test coverage for MethodCallStateEffect VCs. Added integration tests verifying:
- Transitive call chain display in verbose CLI output
- Call chain display in JSON output description and suggestion fields

**New in v346:** Dedicated `call_chain` field in JSON output. For `MethodCallStateEffect` VCs with transitive state modifications, the JSON output now includes a dedicated `call_chain` array field (in addition to embedding the chain in the description). Example:
```json
{
  "description": "Invariant ... transitively modifies [count] via: mid -> helper",
  "call_chain": ["Counter_helper"],
  ...
}
```
Direct modifications (no intermediate calls) have an empty call_chain (omitted from JSON via serde skip_serializing_if).

```swift
// Method-level invariant (v327)
class Counter {
    var count: Int = 0

    @_invariant("count >= 0")
    func increment() {
        count += 1  // StateInvariant VC: "count >= 0" must hold after mutation
    }
}

// Type-level invariant (v328)
class Counter {
    var count: Int = 0

    @_invariant("count >= 0")  // Type-level: applies to ALL methods
    init() {
        count = 0
    }

    func decrement() {
        count -= 1  // TypeInvariant VC: type invariant "count >= 0" checked here
    }
}

// Cross-method state flow (v342)
class Counter {
    var count: Int = 0

    @_invariant("count >= 0")
    init() { count = 0 }

    func helper() {
        count = 10  // Modifies count (tracked in method_effects)
    }

    func caller() {
        helper()  // MethodCallStateEffect VC: invariant must hold after helper()
    }
}

// Transitive call chain (v343-v344)
class Counter {
    var count: Int = 0

    @_invariant("count >= 0")
    init() { count = 0 }

    func helper() { count = 10 }       // Direct modifier
    func mid() { helper() }            // Indirect (calls helper)
    func top() {
        mid()  // MethodCallStateEffect VC: "transitively modifies [count] via: mid -> helper"
    }
}
```

**What's supported:**
- Functions with `@_invariant` attribute performing state mutations (StateInvariant)
- **Type-level invariants from init functions** (TypeInvariant) - new in v328
- Detection of `store` instructions to class/struct properties
- Detection of `modify` accessor completions (coroutine patterns)
- Path-sensitive invariant checking (invariant VC includes path conditions)
- **Cross-method state flow tracking** (MethodCallStateEffect) - new in v342
  - Method effect summaries track which properties each method modifies
  - When a method with invariants calls another method that modifies state,
    VCs verify the caller's invariants still hold after the call
- **Transitive call chain tracking** (v343-v344)
  - Deep call chains are now tracked (A → B → C where only C modifies state)
  - Call chain displayed in CLI output: `"transitively modifies [prop] via: B -> C"`
  - JSON output includes `call_chain` array for programmatic access

**What's NOT supported:**
- Automatic invariant inference from @State/@StateObject usage
- View lifecycle invariants (onAppear/onDisappear transitions)
- Invariants on non-init methods don't propagate to other methods

**Impact:**
- Enables basic state machine verification for SwiftUI patterns
- `StateInvariant` VCs are generated for method-specific invariants
- `TypeInvariant` VCs are generated for type-level invariants (from init)
- Type-level invariants are verified in ALL mutating methods of the type
- `MethodCallStateEffect` VCs verify invariants after calling state-modifying methods

**Workaround:** Add explicit `@_invariant` annotations to init for class-wide invariants, or to individual methods for method-specific invariants.

### 2.6 Shift Overflow Detection (v329)

**New in v329:** Shift operations (`<<`, `>>`) now generate `ShiftOverflow` VCs when the shift amount is not a constant value known to be within bounds.

```swift
// Variable shift amount - generates ShiftOverflow VC
func shift(_ x: Int, _ n: Int) -> Int {
    return x << n  // ShiftOverflow VC: must prove 0 <= n < 64
}

// Constant shift amount in valid range - NO VC generated
func shiftByFour(_ x: Int) -> Int {
    return x << 4  // No VC needed: 4 < 64 is always true
}
```

**What's verified:**
- Shift left (`<<`): `shl_Int8`, `shl_Int16`, `shl_Int32`, `shl_Int64`
- Arithmetic shift right (`>>`): `ashr_Int8`, `ashr_Int16`, `ashr_Int32`, `ashr_Int64`
- Logical shift right: `lshr_Int8`, `lshr_Int16`, `lshr_Int32`, `lshr_Int64`

**What's NOT verified:**
- Shifts by negative amounts (may require additional guards)
- Shifts that lose precision (e.g., shifting out significant bits)

**Impact:**
- Shifting by >= bit width is undefined behavior in LLVM
- tSwift generates VCs proving `0 <= shift_amount < bits`
- Constant shift amounts in valid range are automatically skipped

**Workaround:** Add explicit bounds checks before variable shift amounts:
```swift
func safeShift(_ x: Int, _ n: Int) -> Int {
    guard n >= 0 && n < 64 else { return 0 }
    return x << n  // ShiftOverflow VC will now pass
}
```

### 3. Limited Memory Safety Verification

**New in v347:** Basic unowned reference safety checking via `UnownedAccess` VCs. When a function accesses an unowned reference (via `load_unowned` SIL instruction), tSwift generates a VC to flag this potentially unsafe operation.

```swift
class Node {
    unowned var parent: Node?  // Dangerous: crashes if parent is deallocated

    func getParentValue() -> Int {
        return parent!.value  // UnownedAccess VC generated here
        // VC: "unowned reference 'parent' accessed - object must still be alive"
    }
}
```

**What's verified:**
- Unowned reference accesses are flagged (each `load_unowned` generates a VC)
- These VCs typically FAIL or return UNKNOWN without user-provided preconditions
- Forces explicit acknowledgment of potentially unsafe lifetime assumptions

**What's NOT verified:**
- Heap allocation safety
- Memory leaks
- ARC reference counting correctness
- Retain cycles
- Stack overflow
- Weak reference validity (weak refs are safe - they return nil)

**Weak vs Unowned:**
- `weak` references are safe: Swift automatically returns `nil` if the object is deallocated
- `unowned` references are unsafe: accessing after deallocation causes a runtime trap
- Only `unowned` accesses generate VCs because they're the dangerous case

Memory instructions (`AllocRef`, `DeallocRef`, etc.) are parsed but no verification conditions are generated beyond unowned access checking.

**Workaround:** Use `weak` references where possible. For `unowned`, add `@_requires` preconditions documenting lifetime assumptions, or use `@_trusted` if the lifetime is guaranteed by external invariants.

### 4. Limited Concurrency Verification

**New in v348:** Basic actor isolation crossing detection via `ActorIsolationCrossing` VCs. When SIL apply instructions have `[caller_isolation=...]` and `[callee_isolation=...]` attributes indicating a boundary crossing, tSwift generates VCs to flag these crossings.

```swift
// Example: nonisolated code calling actor-isolated code
actor DataManager {
    var data: [String] = []

    func process() {
        // Internal actor calls don't generate crossing VCs
    }
}

func externalCaller(manager: DataManager) async {
    await manager.process()  // ActorIsolationCrossing VC generated (nonisolated → actor_instance)
}
```

**What's supported:**
- Detection of actor isolation crossings in apply instructions
- Distinction between nonisolated, actor_instance, and global actors (@MainActor)
- Path-sensitive crossing detection (respects control flow)

**What's NOT modeled:**
- Data races (memory access interleaving)
- Deadlock detection
- async/await correctness beyond isolation crossings
- Thread safety for non-actor shared state

**Impact:**
- Actor crossings are flagged for visibility and FFI verification
- Useful for auditing where concurrency boundaries exist
- Does NOT prove absence of data races or deadlocks

**Workaround:** Use Swift's actor model. Actor isolation crossings are informational - they highlight where boundary crossings occur but the compiler already enforces isolation safety.

---

## Significant Limitations

### 5. Floating Point - Symbolic Only

```swift
func badFloat(_ x: Double) -> Double {
    return x + 0.1 + 0.2  // NOT verified to equal x + 0.3
}
```

Float operations are uninterpreted functions - no real arithmetic verification.

### 6. Strings - Minimal Support

String operations are normalized for FFI verification but not proven correct:
- `.count`, `.isEmpty`, `.contains()` - structural only
- Unicode correctness - not verified
- String interpolation - not verified

### 7. Collections - Only Array Bounds

Only `Array[index]` bounds checks are generated. Not verified:
- Dictionary key presence
- Set membership
- Collection mutation safety
- Iterator validity
- Capacity guarantees

### 8. Generics - Type Erasure

```swift
func generic<T: Comparable>(_ a: T, _ b: T) -> Bool {
    return a < b  // T is just a name, not parameterized
}
```

Generic code is verified with type names as placeholders - no parametric reasoning.

### 9. Protocol Witnesses - Uninterpreted

Protocol method dispatch (`witness_method`) is modeled but contract inheritance across implementations is not verified.

### 10. Class Inheritance - No LSP

Liskov Substitution Principle is not checked. A subclass can violate superclass contracts without warning.

---

## Approximations (Sound but Incomplete)

### 11. FFI Condition Skipping

Complex FFI conditions (disjunctions, implications, negations, quantifiers) are skipped during cross-language verification. The verifier conservatively allows these.

### 12. @_trusted Bypasses Verification

```swift
@_trusted
func trustedCode() {
    // This code is NOT verified at all
    // Use only when you are certain the code is correct
}
```

### 13. Quantifiers Dropped in FFI

`forall` and `exists` quantifiers in FFI contracts have their bodies extracted but quantification is dropped.

---

## Missing Auto-VCs (Edge Cases)

| Gap | Description |
|-----|-------------|
| Integer truncation | Assignment narrowing not warned |
| Unsigned underflow | Some edge cases missed |
| Division truncation | `5/2 = 2` not warned |

Note: Modulo by zero IS checked (uses same `DivByZero` VC as division).
Note: Shift overflow IS now checked (v329) - `<<`, `>>` generate VCs for variable shift amounts.

---

## Test Coverage Limitations

### No Property-Based Testing

Tests are example-based. Edge cases may be missed.

### No Real Swift Stdlib Verification

Tests use synthetic SIL. Real Swift stdlib functions (`Array.append`, etc.) are trusted.

---

## Infrastructure Gaps

### Kani Export and Direct Integration (v330-338)

**New in v330-336:** Kani harness export functionality is available via `--export-kani` flag. This exports verification conditions as Rust harness files that can be run manually with `cargo kani`.

**New in v337:** Direct Kani integration via `--run-kani` flag. When used with `--export-kani`, this automatically creates a Cargo project and runs `cargo kani` on the exported harnesses.

**New in v338:** Kani result aggregation. When `--run-kani` is used, `tswift-verify` summarizes Kani pass/fail counts and returns a non-zero exit code when Kani finds failures.

**New in v339:** Per-VC Kani reporting. When `--run-kani` is used, Kani results are mapped back to individual VCs and displayed alongside the Z4/Z3 results. JSON output includes a `kani_result` field for each auto-VC.

```bash
# Export Kani harnesses for a SIL file
tswift-verify --sil file.sil --export-kani ./harnesses

# Then run with Kani manually
cd harnesses && cargo kani

# NEW (v337): Export AND run Kani automatically
tswift-verify --sil file.sil --export-kani ./harnesses --run-kani
```

**What's supported:**
- Export of all auto-VC types (Overflow, DivByZero, BoundsCheck, etc.)
- Generated harnesses include `#[kani::proof]` annotations
- Path conditions exported as `kani::assume()` calls
- **Kani function API (v337):** Updated to use `kani::assert(cond, "msg")` function (not macro)
- **Proper Rust type mappings (v336):**
  - Int8/16/32/64 → i128 with bounds assumptions
  - Bool → bool (no bounds needed)
  - Float32 → f32, Float64 → f64 (symbolic, with warning comments)
- **Direct Kani invocation (v337):**
  - `--run-kani` flag triggers automatic Cargo project creation
  - Runs `cargo kani` and displays results
  - Requires `cargo-kani` installed (`cargo install --locked kani-verifier && cargo kani setup`)
- **Kani result aggregation (v338):**
  - Summarizes Kani harness results (ok/failed/errors)
  - `tswift-verify` exits with code 1 when Kani reports failures
- **Per-VC Kani reporting (v339):**
  - Maps Kani harness results back to individual VCs
  - Human output shows Kani status (VERIFIED/FAILED/ERROR) per VC
  - JSON output includes `kani_result` field for each `auto_vc_results` entry
  - `KaniVcResult` enum: `Verified`, `Failed`, `Error`, `NotExported`
- **Bitvector mode (v351-353):**
  - `--kani-bitvector` flag enables exact overflow semantics in Kani harnesses
  - Without flag: integers use i128 with bounds assumptions (default, sound for logical verification)
  - With flag: integers use native Rust types (i8, i16, i32, i64, u8, u16, u32, u64)
  - Native types enable Kani to detect exact overflow behavior (e.g., Int32 wrapping)
  - Use this mode when you need to verify overflow properties precisely
  - **v352:** Fixed integer literals to be unsuffixed for type inference; array .count uses i64 in bitvector mode
  - **v353 Validation:** End-to-end flow validated: export compiles, cargo-kani runs, results map back to VCs
- **Preconditions export (v354):**
  - @_requires annotations are now emitted as `kani::assume()` calls in Kani harnesses
  - This constrains symbolic inputs to satisfy the function's contract
  - Without preconditions, Kani explores the full type domain (may find spurious counterexamples)
  - With preconditions, Kani only explores inputs satisfying the @_requires clauses
  - Both unbounded (i128) and bitvector modes support preconditions
  - Example: `@_requires(x > 0)` becomes `kani::assume((x > 0));` in the harness
- **Postconditions export (v355):**
  - @_ensures annotations are now emitted as `kani::assert()` calls in Kani harnesses
  - This verifies that the function result satisfies the output contract
  - Postconditions are emitted AFTER the main VC assertion
  - Both unbounded (i128) and bitvector modes support postconditions
  - The `result` variable is automatically declared when postconditions reference it
  - Example: `@_ensures(result >= 0)` becomes `kani::assert((result >= 0), "postcondition 1");`
  - Combined with preconditions: `@_requires(x > 0)` + `@_ensures(result >= x)` correctly constrains inputs and verifies outputs
- **CLI test coverage for pre/postconditions (v356):**
  - Added integration tests verifying @_ensures are exported as `kani::assert()` calls
  - Added integration tests verifying @_requires are exported as `kani::assume()` calls
  - Tests verify correct ordering: preconditions (assume) come before postconditions (assert)
- **old() expression support (v357-359):**
  - `old(x)` expressions in postconditions are now supported for Kani export and Z4/Z3 verification
  - Captures the entry value of parameters at function call time
  - Rendered as `old_x` variable declarations that copy the parameter before any mutation
  - Both unbounded (i128) and bitvector modes correctly type the old_x variables
  - Example: `@_ensures(result == old(x) + 1)` generates `let old_x = x;` and asserts `result == (old_x + 1)`
  - v358 fix: Z4 backend now correctly declares `x_old` variables in SMT-LIB formulas
  - **v359 fix:** Z4/Z3 postconditions with `old()` now correctly verify by substituting `old(x)` with `x` directly in the VC. This works because parameters are immutable in Swift function bodies, so `old(param) == param`. The substitution approach avoids Z4 limitations with multiple equality constraints.
  - **Limitation:** Only simple `old(var)` is supported; complex expressions like `old(x + y)` return an error
- **Auto-export Kani project for --run-kani (v360):**
  - `--run-kani` no longer requires explicit `--export-kani` flag
  - When `--run-kani` is used without `--export-kani`, a temporary directory is automatically created
  - Temporary SIL and Kani export directories are cleaned up after verification completes
  - Example: `./bin/tswiftv verify file.swift --run-kani --kani-bitvector` now works end-to-end
- **Wrapping arithmetic in bitvector mode (v361):**
  - Kani harnesses in bitvector mode now use wrapping arithmetic methods (`wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_div`, `wrapping_rem`, `wrapping_neg`)
  - This prevents Rust overflow panics during Kani exploration, allowing Kani to explore the full state space
  - Without wrapping arithmetic, Rust debug mode would panic on overflow before Kani could find counterexamples
  - The wrapped result is the same as Swift's overflow behavior in release mode
- **Enhanced Kani counterexample parsing (v361):**
  - Kani failure results now include parsed counterexample values
  - `KaniHarnessResult::Failure` includes a `counterexample: Vec<CounterexampleValue>` field
  - Each counterexample has `name` (variable name) and `value` (concrete failing value)
  - Source location parsing improved to extract failure locations from Kani output
  - Counterexample values help diagnose why a verification condition failed
- **Checked overflow detection in bitvector mode (v362):**
  - **BUG FIX:** Kani harnesses for arithmetic overflow VCs now correctly detect overflows
  - **Previous behavior:** Range checks `(x + y) >= MIN && (x + y) <= MAX` used `wrapping_add`, which always returned in-range values, making overflow assertions tautologically true
  - **New behavior:** Overflow VCs are detected by their structure and converted to `x.checked_add(y).is_some()`
  - Rust's `checked_add/checked_sub/checked_mul/checked_div/checked_rem/checked_neg` return `None` on overflow
  - Example: `x + 1 >= INT_MIN && x + 1 <= INT_MAX` now becomes `(x).checked_add(1).is_some()`
  - This correctly allows Kani to find counterexamples like `x = 9223372036854775807` (INT64_MAX)
  - **Non-overflow VCs** (e.g., `x + 1 > 0`) still use `wrapping_add` for full state space exploration
  - Overflow pattern detection supports: add, sub, mul, div, rem, neg operations

**What's NOT supported:**
- Memory safety properties (Kani supports these, but export doesn't generate them)
- Real floating-point arithmetic reasoning (floats are symbolic placeholders)

### No Lean Backend

The architecture mentions Lean 5 interactive proofs - **not implemented**.

### No Incremental Verification

Each run re-verifies everything. Large codebases may be slow.

---

## Understanding UNKNOWN Results

When you see `UNKNOWN`, check the **category**:

| Category | Meaning | Action |
|----------|---------|--------|
| `SolverReturnedUnknown` | Z4 QF_LIA limitation | Simplify formula |
| `NonLinearArithmetic` | Variable multiplication/division | Use linear expressions |
| `UnsupportedPattern` | Uninterpreted function calls (e.g. `abs(x)`) | Rewrite as explicit conditionals |
| `FloatingPointSymbolic` | Float/Double operations | Accept symbolic only |
| `NoTerminationProof` | Loop not analyzed | Manual review |
| `NoMemorySafetyProof` | Heap not modeled | Use ARC correctly |
| `NoConcurrencyProof` | Actors not modeled | Manual review |

---

## Recommendations

1. **Don't assume UNKNOWN means safe** - it means unverified
2. **Use `@_trusted` sparingly** - it disables all checks
3. **Enable Z3 fallback** for non-linear arithmetic verification (`--features z3-fallback`)
4. **Use simple loop patterns** - `for i in 0..<n` preferred for termination proofs
5. **Review complex loops** - nested/conditional loops may not generate termination VCs
6. **Test concurrency** - actors not verified

---

## Future Work

- [x] Kani export (`--export-kani` flag) for manual verification with `cargo kani` (v330-334)
- [x] Kani direct integration (v337 - `--run-kani` flag for automatic `cargo kani` execution)
- [x] Kani result aggregation into main verification pipeline (v338 - exit codes + summary)
- [x] Per-VC Kani reporting (v339 - map Kani results back to individual VCs in JSON/CLI output)
- [x] Termination checking for simple loops (v314-321 - infrastructure + phi resolution fixes)
- [x] Z3 fallback for non-linear arithmetic (v324 - QF_NIA support)
- [x] Termination checking for simple recursive functions (v326 - basic pattern detection)
- [x] SwiftUI state invariant VCs (v327 - StateInvariant auto-VC type)
- [x] Type-level invariants (v328 - TypeInvariant from init functions)
- [x] Shift overflow detection (v329 - ShiftOverflow auto-VC for shl/lshr/ashr)
- [x] Mutual recursion termination (v340 - MutualRecursiveTermination for cycle detection)
- [x] Lexicographic termination ordering (v341 - LexicographicTermination for multi-param recursion)
- [x] Cross-method state flow tracking (v342 - MethodCallStateEffect for method call effects)
- [x] Transitive call chain reporting in CLI/JSON (v343-v344 - call_chain display for deep effects)
- [x] Dedicated call_chain JSON field (v346 - programmatic access to transitive call chains)
- [x] Basic memory safety - unowned reference access (v347 - UnownedAccess VCs for load_unowned)
- [x] Actor isolation crossing detection (v348 - ActorIsolationCrossing VCs for actor boundary crossings)
- [x] Lexicographic mutual recursion termination (v350 - combined measure for mutual recursion)
- [x] Bitvector support for Kani export (v351-353 - `--kani-bitvector` flag for exact overflow semantics, v353 end-to-end validation)
- [x] Kani preconditions export (v354 - emit @_requires as kani::assume() for constrained domain verification)
- [x] Kani postconditions export (v355 - emit @_ensures as kani::assert() for output contract verification)
- [x] CLI test coverage for Kani pre/postconditions export (v356 - integration tests for @_requires/@_ensures)
- [x] old() expression support in Kani export (v357 - entry value capture for postconditions)
- [x] Z4 backend old() variable declaration fix (v358 - x_old variables now declared in SMT-LIB)
- [x] Z4/Z3 postcondition old() substitution (v359 - old(x) -> x for parameters, works around Z4 limitations)
- [x] Auto-export Kani project for --run-kani (v360 - temporary directory auto-creation and cleanup)
- [x] Wrapping arithmetic in Kani bitvector mode (v361 - prevents Rust overflow panics during exploration)
- [x] Enhanced Kani counterexample parsing (v361 - extract variable values and locations from failures)
- [x] Checked overflow detection in Kani bitvector mode (v362 - use checked_add/sub/etc. for overflow VCs instead of tautological range checks)
- [ ] Lean 5 interactive proofs

---

## Conclusion

**tSwift verifies common bugs automatically but is NOT complete verification.**

The 4178 passing tests (2 ignored) (lib + CLI/integration) verify the infrastructure works correctly. They do not prove the verifier catches all bugs.

Use tSwift as **one layer** of defense, not the only one.
