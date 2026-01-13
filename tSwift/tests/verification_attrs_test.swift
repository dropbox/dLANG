// Test file for verification attribute pipeline integration
// This tests that @_requires, @_ensures, @_invariant, and @_trusted
// survive parsing, semantic analysis, and are available in SIL

// Precondition test
@_requires("x > 0")
func positiveOnly(x: Int) -> Int {
    return x * 2
}

// Postcondition test
@_ensures("result >= 0")
func absoluteValue(_ x: Int) -> Int {
    return x < 0 ? -x : x
}

// Combined pre/post conditions
@_requires("divisor != 0")
@_ensures("result * divisor == dividend")
func safeDivide(_ dividend: Int, by divisor: Int) -> Int {
    return dividend / divisor
}

// Invariant test on a struct
@_invariant("count >= 0")
struct Counter {
    var count: Int = 0

    @_requires("amount > 0")
    @_ensures("count == old(count) + amount")
    mutating func increment(by amount: Int) {
        count += amount
    }
}

// Trusted attribute test
@_trusted
func unsafeFFICall() -> Int {
    // This function is trusted and won't be verified
    return 42
}

// Multiple preconditions
@_requires("lo >= 0")
@_requires("hi <= 100")
@_requires("lo <= hi")
func rangeCheck(lo: Int, hi: Int) -> Int {
    return hi - lo
}

// Entry point
let result = positiveOnly(x: 5)
print("Result: \(result)")
