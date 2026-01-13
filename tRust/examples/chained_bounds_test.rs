// Test chained bounds propagation through multiple operations
// This tests that bounds are tracked through chains like:
// - (x | 0x80) & 0xFF → gives 128 <= x <= 255
// - (x >> 24) as usize | 0x80 → gives combined upper (255) and lower (128) bounds

fn main() {
    // Test 1: OR then AND - combined lower and upper bounds
    // _1 = x | 0x80        → _1 >= 128 (BitOrLower)
    // _2 = _1 & 0xFF       → _2 <= 255 (BitAndMask)
    // Combined: 128 <= _2 <= 255
    test_or_then_and();

    // Test 2: Right shift, cast, then OR - chained upper bound flows to lower
    // _1 = x >> 24         → _1 <= 255 (RightShiftUpper, for unsigned x)
    // _2 = _1 as usize     → _2 <= 255 (CastAlias)
    // _3 = _2 | 0x80       → _3 >= 128 (BitOrLower)
    // Combined: 128 <= _3 <= 255
    test_shift_cast_or();

    // Test 3: Multiple masks - chain of AND operations
    // _1 = x & 0xFFFF      → _1 <= 65535
    // _2 = _1 & 0xFF       → _2 <= 255
    test_multiple_masks();

    // Test 4: Combined with array access
    test_chained_array_access();

    println!("All chained bounds tests passed!");
}

// Test OR followed by AND
fn test_or_then_and() {
    let arr = [0u8; 256];

    for x in 0u8..=127 {
        // (x | 0x80) sets bit 7, giving at least 128
        // & 0xFF ensures result <= 255
        let idx = (x | 0x80) & 0xFF;
        // idx is guaranteed to be in [128, 255], safely within arr bounds
        let _ = arr[idx as usize];
    }
    println!("test_or_then_and: PASS");
}

// Test right shift → cast → OR chain
fn test_shift_cast_or() {
    let arr = [0u8; 256];

    for x in 0x80000000u32..=0x80FFFFFF {
        // x >> 24 gives 128 for our range (0x80..=0x80 in high byte)
        // Combined with | 0x80 ensures result >= 128
        let shifted = x >> 24;
        let idx = (shifted as usize) | 0x80;
        // idx is guaranteed to be in [128, 255]
        let _ = arr[idx];
    }
    println!("test_shift_cast_or: PASS");
}

// Test multiple mask operations
fn test_multiple_masks() {
    let arr = [0u8; 256];

    for x in 0u32..1000 {
        // First mask: ensures <= 65535
        let masked1 = x & 0xFFFF;
        // Second mask: ensures <= 255
        let idx = masked1 & 0xFF;
        // idx is guaranteed <= 255
        let _ = arr[idx as usize];
    }
    println!("test_multiple_masks: PASS");
}

// Test chained bounds for actual array access patterns
fn test_chained_array_access() {
    let lookup_table = [0u8; 256];

    // Pattern from real code: extract byte and ensure minimum value
    for word in [0x12345678u32, 0xDEADBEEF, 0xCAFEBABE] {
        // Extract high byte (0-255)
        let high_byte = (word >> 24) as usize;

        // Ensure minimum value of 64 for some algorithm requirement
        let idx = high_byte | 0x40;
        // idx is in [64, 255] - safely within bounds
        let _ = lookup_table[idx];
    }

    // Pattern: constrain both ends
    for val in 0u16..1000 {
        // Ensure at least 32 but at most 127
        let constrained = ((val | 0x20) as u8) & 0x7F;
        let _ = lookup_table[constrained as usize];
    }

    println!("test_chained_array_access: PASS");
}
