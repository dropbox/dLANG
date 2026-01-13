// Multiple errors - compiler should report all, not crash
fn main() {
    let x: i32 = "string";  // type error
    let y = undefined_var;   // undefined
    println!("{}", nonexistent);  // more undefined
}
