// Rust exports that match the swift-bridge generated Swift

#[ffi_export]
#[requires(a >= -1000000000 && a <= 1000000000)]
#[requires(b >= -1000000000 && b <= 1000000000)]
#[ensures(result == a + b)]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[ffi_export]
#[requires(denominator != 0)]
#[ensures(result == numerator / denominator)]
pub fn safe_divide(numerator: i32, denominator: i32) -> i32 {
    numerator / denominator
}

#[ffi_export]
#[requires(delta >= 0)]
#[ensures(result == value + delta)]
pub fn increment_by(value: i32, delta: i32) -> i32 {
    value + delta
}
