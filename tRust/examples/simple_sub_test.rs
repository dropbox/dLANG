// Simple subtraction bounds test
//
// This test exercises the underflow-free pattern:
//   idx = CONST - (x & MASK)
// where (x & MASK) is proven <= CONST.

fn main() {
    let table: [u8; 16] = [0; 16];
    for x in 0u32..1000 {
        let masked = x & 0xF; // in [0, 15]
        let idx = (15 - masked) as usize;
        let _ = table[idx];
    }
}
