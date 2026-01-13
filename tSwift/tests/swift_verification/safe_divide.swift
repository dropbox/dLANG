// Test: Safe division with precondition (should verify)
// The precondition prevents division by zero

@_requires("divisor != 0")
func safeDivide(_ dividend: Int, by divisor: Int) -> Int {
    return dividend / divisor
}
