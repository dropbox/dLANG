// Allocation stress test
fn main() {
    // Many small allocations
    let mut vecs: Vec<Vec<u8>> = Vec::new();
    for _ in 0..10000 {
        vecs.push(vec![1, 2, 3, 4, 5]);
    }

    // Large allocation
    let large: Vec<u8> = vec![0; 10_000_000];
    assert_eq!(large.len(), 10_000_000);

    // Reallocations
    let mut growing: Vec<i32> = Vec::new();
    for i in 0..100000 {
        growing.push(i);
    }

    println!("Allocation stress test passed");
}
