// Test division bounds propagation
// This tests that dividing by a constant provides upper bounds:
// - For unsigned x / n where n > 0: 0 <= result <= type_max / n
//
// NOTE: Division bounds alone are conservative (u32::MAX / divisor).
// They're most useful when combined with masking operations.

fn main() {
    // Test 1: Division chained with mask - combined bounds
    test_division_with_mask();

    // Test 2: Division result used in modulo for tighter bounds
    test_division_modulo_chain();

    println!("All division bounds tests passed!");
}

// Test division combined with mask for tight bounds
fn test_division_with_mask() {
    let lookup = [0u8; 256];

    // x / 1000 has type-based upper bound of u32::MAX / 1000 = 4294967
    // But with & 0xFF, we get a tight bound of 255
    for x in 0u32..100000 {
        // Division alone isn't enough (upper bound = 4294967)
        // But & 0xFF gives us the tight 255 upper bound
        let idx = ((x / 1000) & 0xFF) as usize;
        let _ = lookup[idx];  // VERIFIED SAFE: idx <= 255 from mask
    }

    // Multiple divisions chained with mask
    let small_table = [0u8; 16];
    for x in 0u32..10000 {
        // x / 100 / 10 = x / 1000, but tracks through chained ops
        // & 0x0F ensures result <= 15
        let idx = (((x / 100) / 10) & 0x0F) as usize;
        let _ = small_table[idx];  // VERIFIED SAFE: idx <= 15 from mask
    }

    println!("test_division_with_mask: PASS");
}

// Test division followed by modulo for tight bounds
fn test_division_modulo_chain() {
    let buckets = [0u32; 64];

    // Division followed by modulo gives both operations' bounds
    // x / 256 has upper bound of u32::MAX / 256 = 16777215
    // Then % 64 gives upper bound of 63
    for hash in 0u64..1000000 {
        let bucket = ((hash / 256) % 64) as usize;
        let _ = buckets[bucket];  // VERIFIED SAFE: bucket <= 63 from modulo
    }

    println!("test_division_modulo_chain: PASS");
}
