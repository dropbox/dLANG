// bounds_check.swift
//
// Demonstrates array bounds checking in Swift.
// Swift's Array type includes runtime bounds checks that
// the verifier can detect and analyze.
//
// Run: tswift verify examples/bounds_check.swift --verbose

/// Gets an array element without bounds checking.
///
/// The verifier detects potential out-of-bounds access.
/// Swift will crash at runtime if index is invalid.
@inline(never)
@_ensures("true")
func unsafeGet(_ arr: [Int], _ index: Int) -> Int {
    return arr[index]  // Potential bounds violation
}

/// Gets an array element with guard protection.
///
/// The guard ensures index is valid before accessing.
@inline(never)
@_ensures("true")
func safeGetGuarded(_ arr: [Int], _ index: Int) -> Int {
    guard index >= 0 && index < arr.count else { return 0 }
    return arr[index]
}

/// Gets an array element with explicit precondition.
///
/// The @_requires annotation expresses the validity constraint.
@inline(never)
@_requires("index >= 0 && index < arr.count")
@_ensures("true")
func safeGetWithRequires(_ arr: [Int], _ index: Int) -> Int {
    return arr[index]
}

/// Gets the first element, returning a default if empty.
@inline(never)
@_ensures("true")
func getFirst(_ arr: [Int], defaultValue: Int) -> Int {
    if arr.isEmpty {
        return defaultValue
    }
    return arr[0]  // Safe: checked that array is not empty
}

// Usage to prevent optimization removal
let testArr = [1, 2, 3]
_ = unsafeGet(testArr, 0)
_ = safeGetGuarded(testArr, 1)
_ = safeGetWithRequires(testArr, 2)
_ = getFirst(testArr, defaultValue: 0)
