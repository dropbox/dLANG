// forced_cast.swift
//
// Demonstrates type cast failure auto-VC with `as!` operations.
// Swift's forced cast operator crashes at runtime if the
// cast fails. The verifier detects potential cast failures.
//
// Compile to SIL:  swiftc -emit-sil -O forced_cast.swift > forced_cast.sil
// Verify:          bin/tswift verify --sil forced_cast.sil --verbose

/// Unconditionally casts Any to Int.
/// The verifier detects this can fail if value is not Int.
@inline(never)
func unsafeCast(_ value: Any) -> Int {
    return value as! Int  // Auto-VC: cast may fail
}

/// Safely casts with optional binding.
/// The `as?` operator returns nil instead of crashing.
@inline(never)
func safeCastOptional(_ value: Any) -> Int {
    if let intValue = value as? Int {
        return intValue
    }
    return 0
}

/// Casts with guard pattern.
/// Common Swift pattern for safe type casting.
@inline(never)
func safeCastGuarded(_ value: Any) -> Int {
    guard let intValue = value as? Int else { return -1 }
    return intValue
}

/// Downcasting class hierarchy.
class Animal {}
class Dog: Animal {}

/// Casting from superclass to subclass can fail.
@inline(never)
func unsafeDowncast(_ animal: Animal) -> Dog {
    return animal as! Dog  // Auto-VC: downcast may fail
}

// Usage to prevent optimization removal
_ = unsafeCast(42 as Any)
_ = safeCastOptional("not an int" as Any)
_ = safeCastGuarded(100 as Any)
_ = unsafeDowncast(Dog())
