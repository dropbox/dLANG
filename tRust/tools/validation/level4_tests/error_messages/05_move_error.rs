// Level 4.3: Error Messages - Move Error
// This code should NOT compile - testing that error is produced

fn main() {
    let s = String::from("hello");
    let s2 = s;
    println!("{}", s); // use after move
}
