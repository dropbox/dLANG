// range_bounds.swift
//
// Demonstrates range bounds violation auto-VC.
// Swift's Range type requires lowerBound <= upperBound.
// Creating a range with start > end is a runtime error.
// The verifier detects potential invalid range construction.
//
// Compile to SIL:  swiftc -emit-sil -O range_bounds.swift > range_bounds.sil
// Verify:          bin/tswift verify --sil range_bounds.sil --verbose

/// Creates a range without checking bounds.
/// Swift Range requires start <= end.
@inline(never)
func unsafeRange(_ start: Int, _ end: Int) -> Range<Int> {
    return start..<end  // Auto-VC: range bounds may be invalid
}

/// Creates a closed range without checking bounds.
/// ClosedRange also requires start <= end.
@inline(never)
func unsafeClosedRange(_ start: Int, _ end: Int) -> ClosedRange<Int> {
    return start...end  // Auto-VC: range bounds may be invalid
}

/// Safe range with explicit bounds check.
/// The guard ensures valid range before creation.
@inline(never)
func safeRangeGuarded(_ start: Int, _ end: Int) -> Range<Int>? {
    guard start <= end else { return nil }
    return start..<end  // Safe: bounds verified
}

/// Array slicing with range can fail multiple ways.
/// Both range validity and array bounds are checked.
@inline(never)
func unsafeSlice(_ arr: [Int], _ start: Int, _ end: Int) -> ArraySlice<Int> {
    return arr[start..<end]  // Auto-VC: range bounds + array bounds
}

/// Safe array slicing pattern.
/// Validates both range and array bounds before slicing.
@inline(never)
func safeSlice(_ arr: [Int], _ start: Int, _ end: Int) -> ArraySlice<Int> {
    guard start >= 0, end <= arr.count, start <= end else {
        return arr[0..<0]  // Empty slice on invalid input
    }
    return arr[start..<end]
}

/// Range created from count can be invalid.
/// If count is negative, the range 0..<count is invalid.
@inline(never)
func rangeFromCount(_ count: Int) -> Range<Int> {
    return 0..<count  // Auto-VC: fails if count < 0
}

// Usage to prevent optimization removal
_ = unsafeRange(0, 10)
_ = unsafeClosedRange(5, 15)
_ = safeRangeGuarded(5, 3)
_ = unsafeSlice([1,2,3], 0, 2)
_ = safeSlice([1,2,3,4], 1, 3)
_ = rangeFromCount(5)
