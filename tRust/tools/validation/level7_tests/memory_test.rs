// Memory allocation test
use std::collections::HashMap;

fn allocate_and_free() {
    let mut vec: Vec<String> = Vec::new();
    for i in 0..1000 {
        vec.push(format!("String number {}", i));
    }

    let mut map: HashMap<i32, Vec<u8>> = HashMap::new();
    for i in 0..100 {
        map.insert(i, vec![0u8; 1024]);
    }

    // All memory should be freed when going out of scope
}

fn main() {
    for _ in 0..10 {
        allocate_and_free();
    }
    println!("Memory test completed");
}
