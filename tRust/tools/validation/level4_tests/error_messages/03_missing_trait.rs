// Level 4.3: Error Messages - Missing Trait Implementation
// This code should NOT compile - testing that error is produced

fn needs_display<T: std::fmt::Display>(t: T) {
    println!("{}", t);
}

struct NoDisplay;

fn main() {
    needs_display(NoDisplay); // NoDisplay doesn't implement Display
}
