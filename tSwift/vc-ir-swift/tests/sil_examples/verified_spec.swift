// Swift source with @_requires/@_ensures specs for e2e testing
// Tests that user-specified verification conditions are extracted and verified

// A simple identity function that preserves positivity
@_requires("x > 0")
@_ensures("result > 0")
@inline(never)
func keepPositive(_ x: Int) -> Int {
    return x
}

// A function with multiple specs
@_requires("a >= 0")
@_requires("b >= 0")
@_ensures("result >= a")
@_ensures("result >= b")
@inline(never)
func maxOf(_ a: Int, _ b: Int) -> Int {
    if a > b {
        return a
    }
    return b
}

// Call functions to prevent dead code elimination
print(keepPositive(5))
print(maxOf(3, 7))
