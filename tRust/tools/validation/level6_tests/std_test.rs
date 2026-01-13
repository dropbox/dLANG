fn add(a: i32, b: i32) -> i32 {
    a.wrapping_add(b)
}

fn main() {
    let result = add(2, 3);
    println!("Result: {}", result);
}
