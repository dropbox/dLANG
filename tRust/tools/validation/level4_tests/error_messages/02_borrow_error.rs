// Level 4.3: Error Messages - Borrow Checker Error
// This code should NOT compile - testing that error is produced

fn main() {
    let mut s = String::from("hello");
    let r1 = &mut s;
    let r2 = &mut s; // cannot borrow as mutable twice
    println!("{} {}", r1, r2);
}
