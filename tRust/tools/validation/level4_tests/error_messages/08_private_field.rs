// Level 4.3: Error Messages - Private Field Access
// This code should NOT compile - testing that error is produced

mod inner {
    pub struct Foo {
        secret: i32, // private
    }

    impl Foo {
        pub fn new() -> Self {
            Foo { secret: 42 }
        }
    }
}

fn main() {
    let f = inner::Foo::new();
    println!("{}", f.secret); // private field access
}
