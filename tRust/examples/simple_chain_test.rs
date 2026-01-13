// Simple test for chained bounds
// Tests: (x >> 24) as usize | 0x80 should have bounds [128, 255]

fn main() {
    let arr = [0u8; 256];

    let x: u32 = 0x80000000;

    // x >> 24 gives values in [0, 255]
    let shifted: u32 = x >> 24;

    // Cast preserves bounds: shifted_usize in [0, 255]
    let shifted_usize: usize = shifted as usize;

    // OR with 0x80 gives lower bound of 128
    // Upper bound should still be 255 (from shifted_usize)
    let idx: usize = shifted_usize | 0x80;

    // This should be safe: idx in [128, 255], arr has 256 elements
    let _ = arr[idx];
}
