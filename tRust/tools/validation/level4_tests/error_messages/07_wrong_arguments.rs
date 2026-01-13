// Level 4.3: Error Messages - Wrong Number of Arguments
// This code should NOT compile - testing that error is produced

fn takes_two(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    let x = takes_two(1); // missing argument
    let y = takes_two(1, 2, 3); // too many arguments
}
