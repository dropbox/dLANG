// Exhaustive match bounds propagation test
//
// This test verifies that tRust's -Zverify can track index bounds through
// match expressions whose arms return constant indices.
//
// Motivation: Rust code often derives array indices from exhaustive matches
// over small domains (bool, enums, bounded integers). These patterns should
// be provably safe and enable bounds-check elimination.

#[derive(Copy, Clone)]
enum Small {
    A,
    B,
    C,
    D,
}

fn main() {
    // === Test 1: bool match ===
    let table1: [u8; 2] = [10, 20];
    for i in 0u8..10 {
        let flag = (i & 1) == 0;
        let idx = match flag {
            true => 0usize,
            false => 1usize,
        };
        // VERIFIED SAFE: idx ∈ {0,1}
        let _ = table1[idx];
    }

    // === Test 2: exhaustive enum match ===
    let table2: [u32; 4] = [0, 1, 2, 3];
    let inputs = [Small::A, Small::B, Small::C, Small::D];
    for x in inputs {
        let idx = match x {
            Small::A => 0usize,
            Small::B => 1usize,
            Small::C => 2usize,
            Small::D => 3usize,
        };
        // VERIFIED SAFE: idx ∈ {0,1,2,3}
        let _ = table2[idx];
    }

    // === Test 3: small-domain integer match with wildcard ===
    let table3: [u8; 4] = [0; 4];
    for x in 0u8..16 {
        let idx = match x {
            0 => 0usize,
            1 => 1usize,
            2 => 2usize,
            _ => 3usize,
        };
        // VERIFIED SAFE: idx ∈ {0,1,2,3}
        let _ = table3[idx];
    }

    println!("All exhaustive match bounds tests passed!");
}
