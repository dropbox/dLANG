// Test: Trusted function (should be skipped)
// The @_trusted attribute marks this function as trusted

@_trusted
func trustedFFI() -> Int {
    return 42
}

// This should still be verified
@_requires("x > 0")
func usesTrusted(_ x: Int) -> Int {
    return trustedFFI() + x
}
