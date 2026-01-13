// force_unwrap.swift
//
// Demonstrates nil check auto-VC with force unwrap operations.
// Swift's `!` operator crashes at runtime if the optional is nil.
// The verifier automatically detects potential nil unwrap failures.
//
// Compile to SIL:  swiftc -emit-sil -O force_unwrap.swift > force_unwrap.sil
// Verify:          bin/tswift verify --sil force_unwrap.sil --verbose

/// Unconditionally unwraps an optional.
/// The verifier detects this can fail if x is nil.
@inline(never)
func unsafeUnwrap(_ x: Int?) -> Int {
    return x!  // Auto-VC: force unwrap may fail
}

/// Unwraps an optional with guard protection.
/// The guard ensures x is not nil before unwrapping.
@inline(never)
func safeUnwrapGuarded(_ x: Int?) -> Int {
    guard let value = x else { return 0 }
    return value
}

/// Chain of optional accesses.
/// Multiple force unwraps multiply the risk of failure.
@inline(never)
func unsafeChain(_ a: Int?, _ b: Int?) -> Int {
    return a! + b!  // Auto-VC: multiple potential failures + overflow
}

/// Safe optional binding pattern.
/// Swift's `if let` pattern safely handles optionals.
@inline(never)
func safeOptionalBinding(_ x: Int?, _ y: Int?) -> Int {
    if let xVal = x, let yVal = y {
        return xVal + yVal  // Auto-VC: overflow still checked
    }
    return 0
}

// Usage to prevent optimization removal
_ = unsafeUnwrap(42)
_ = safeUnwrapGuarded(nil)
_ = unsafeChain(1, 2)
_ = safeOptionalBinding(10, 20)
