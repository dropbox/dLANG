// Test file for constant index bounds checking
// These should NOT trigger warnings (false positives we want to eliminate)

fn get_first(arr: &[i32; 3]) -> i32 {
    arr[0]  // SAFE: constant 0 < 3
}

fn get_second(arr: &[i32; 3]) -> i32 {
    arr[1]  // SAFE: constant 1 < 3
}

fn get_third(arr: &[i32; 3]) -> i32 {
    arr[2]  // SAFE: constant 2 < 3
}

// This SHOULD still warn - constant out of bounds
fn get_fourth(arr: &[i32; 3]) -> i32 {
    arr[3]  // ERROR: constant 3 >= 3, definitely out of bounds
}

// This should warn - variable index
fn get_at(arr: &[i32; 5], i: usize) -> i32 {
    arr[i]  // WARN: i could be >= 5
}

fn main() {
    let arr = [1, 2, 3];
    println!("First: {}", get_first(&arr));
    println!("Second: {}", get_second(&arr));
    println!("Third: {}", get_third(&arr));
    // println!("Fourth: {}", get_fourth(&arr)); // Would panic at runtime

    let arr5 = [1, 2, 3, 4, 5];
    println!("At 2: {}", get_at(&arr5, 2));
}
