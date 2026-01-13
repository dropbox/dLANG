// Level 4.3: Error Messages - Lifetime Error
// This code should NOT compile - testing that error is produced

fn main() {
    let r;
    {
        let x = 5;
        r = &x; // x doesn't live long enough
    }
    println!("{}", r);
}
