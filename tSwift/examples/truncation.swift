// truncation.swift
//
// Demonstrates integer truncation auto-VC with narrowing conversions.
// Converting from a larger integer type to a smaller one (e.g., Int to Int8)
// can fail if the value is out of range. The verifier detects this.
//
// Compile to SIL:  swiftc -emit-sil -O truncation.swift > truncation.sil
// Verify:          bin/tswift verify --sil truncation.sil --verbose

/// Converts Int to Int8 without bounds checking.
/// Valid Int8 range is -128 to 127.
@inline(never)
func unsafeTruncateToInt8(_ x: Int) -> Int8 {
    return Int8(x)  // Auto-VC: truncation may overflow
}

/// Converts Int to UInt8 without bounds checking.
/// Valid UInt8 range is 0 to 255.
@inline(never)
func unsafeTruncateToUInt8(_ x: Int) -> UInt8 {
    return UInt8(x)  // Auto-VC: truncation may overflow
}

/// Safe truncation with explicit bounds check.
/// The guard ensures x fits in Int8 before conversion.
@inline(never)
func safeTruncateGuarded(_ x: Int) -> Int8 {
    guard x >= -128 && x <= 127 else { return 0 }
    return Int8(x)  // Safe: bounds verified
}

/// Truncating to Int16 is also detected.
/// Valid Int16 range is -32768 to 32767.
@inline(never)
func unsafeTruncateToInt16(_ x: Int) -> Int16 {
    return Int16(x)  // Auto-VC: truncation may overflow
}

/// Clamped conversion pattern.
/// Common pattern for safe narrowing conversions.
@inline(never)
func clampedConversion(_ x: Int) -> Int8 {
    if x < -128 {
        return Int8.min
    } else if x > 127 {
        return Int8.max
    } else {
        return Int8(x)  // Safe: in range
    }
}

// Usage to prevent optimization removal
_ = unsafeTruncateToInt8(50)
_ = unsafeTruncateToUInt8(200)
_ = safeTruncateGuarded(1000)
_ = unsafeTruncateToInt16(10000)
_ = clampedConversion(-500)
