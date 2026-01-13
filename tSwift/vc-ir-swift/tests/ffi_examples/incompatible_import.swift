// Example of INCOMPATIBLE Swift FFI imports
// These should FAIL verification due to weaker preconditions

/// Import increment with WEAKER precondition (x > -100 does NOT imply x > 0)
/// This should FAIL verification - Rust requires x > 0 but Swift only guarantees x > -100
@_ffi_import("increment")
@_ffi_requires("x > -100")
func weak_increment(_ x: Int32) -> Int32
