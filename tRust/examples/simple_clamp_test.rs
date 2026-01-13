//! Simple test for clamp bounds propagation
//!
//! Without clamp bounds, this would fail verification because
//! the verifier wouldn't know idx <= 10.

fn main() {
    let table: [u8; 16] = [0; 16];

    for x in 0u32..1000 {
        // clamp guarantees: 2 <= clamped <= 10
        let clamped = x.clamp(2, 10);
        let idx = clamped as usize;
        // Without clamp bounds: WOULD FAIL (idx could be 0..1000)
        // With clamp bounds: VERIFIED SAFE (idx in [2, 10] and 10 < 16)
        let _ = table[idx];
    }
    println!("Simple clamp test passed!");
}
