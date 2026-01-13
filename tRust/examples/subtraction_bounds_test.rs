// Subtraction bounds propagation test
//
// This test verifies that tRust's -Zverify can track upper bounds through
// underflow-free subtraction patterns.
//
// Patterns:
// - const - bounded_x => upper bound = const (when bounded_x <= const)
// - bounded_x - const => upper bound = bounded_upper - const (when bounded_x >= const)

fn main() {
    // === Test 1: const - (x & mask) ===
    // x & 0xF is in [0, 15], so 15 - (x & 0xF) is in [0, 15].
    let table1: [u8; 16] = [0; 16];
    for x in 0u32..1000 {
        let masked = x & 0xF; // upper = 15
        let idx = (15 - masked) as usize;
        let _ = table1[idx];
    }

    // === Test 2: const - (x & mask), then + 1 ===
    // (15 - masked) has upper 15, so +1 has upper 16.
    let table2: [u8; 17] = [0; 17];
    for x in 0u32..1000 {
        let masked = x & 0xF; // upper = 15
        let idx = ((15 - masked) + 1) as usize; // upper = 16
        let _ = table2[idx];
    }

    // === Test 3: ((x & 0xF) | 0x10) - 0x10 ===
    // (x & 0xF) is in [0, 15], so OR 0x10 yields [16, 31].
    // Subtracting 0x10 is underflow-free and yields [0, 15].
    let table3: [u8; 16] = [0; 16];
    for x in 0u32..1000 {
        let masked = x & 0xF; // upper = 15
        let with_bit = masked | 0x10; // bounds = 16..=31
        let idx = (with_bit - 0x10) as usize; // upper = 15
        let _ = table3[idx];
    }

    // === Test 4: usize variant ===
    let table4: [u8; 16] = [0; 16];
    for x in 0usize..1000 {
        let masked = x & 0xF;
        let idx = 15usize - masked;
        let _ = table4[idx];
    }
}
