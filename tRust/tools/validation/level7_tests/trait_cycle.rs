// This should produce an error about cyclic trait bounds, not crash
trait A: B {}
trait B: A {}

struct S;
// impl A for S {} // Would cause cycle error
// impl B for S {}

fn main() {
    println!("Trait cycle detection OK");
}
