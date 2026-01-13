// BitOr Lower Bound Array Indexing Test
//
// This test validates that BitOr lower bounds propagate to array indexing.
// The key insight: x | mask >= mask, so if mask >= len, index is guaranteed out of bounds.
// However, this is more useful for proving a value is in a valid range.

fn main() {
    // Simple case: BitOr doesn't directly help with array upper bounds
    // but can help verify that a value meets minimum requirements
    let arr: [u8; 256] = [0; 256];

    // This pattern: use & for upper bound, | for lower bound
    for i in 0u8..10 {
        // idx has lower bound 128 from the OR
        // and upper bound 255 from the AND
        let idx = (i | 0x80) & 0xFF;
        // Since idx <= 255 < 256, this is safe
        let _ = arr[idx as usize];
    }
}
