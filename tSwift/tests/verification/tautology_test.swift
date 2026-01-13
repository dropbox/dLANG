// Tautology Test - Verification conditions that should always pass
//
// These test the full tSwift verification pipeline using tautological specs
// that don't require precondition assumptions to verify.

// Identity - result equals itself (trivial tautology)
@_ensures("result == result")
func tautology1(_ x: Int) -> Int {
    return x
}

// Reflexive comparison
@_ensures("result >= result")
func tautology2(_ x: Int) -> Int {
    return x
}

// Boolean tautology
@_ensures("true")
func alwaysTrue(_ x: Int) -> Int {
    return x
}

// Trusted function - skips verification
@_trusted
@_requires("false")  // Unsatisfiable precondition - would fail without @_trusted
func trustedFunction(_ x: Int) -> Int {
    return x
}
