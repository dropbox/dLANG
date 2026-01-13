// Level 4.1: Traits
// Tests trait definitions, implementations, and usage

use std::fmt::Display;

// Basic trait
trait Greet {
    fn greet(&self) -> String;
}

// Trait with default implementation
trait Describe {
    fn name(&self) -> &str;

    fn describe(&self) -> String {
        format!("This is {}", self.name())
    }
}

// Trait with associated type
trait Container {
    type Item;
    fn get(&self) -> &Self::Item;
}

// Trait with associated constant
trait Numbered {
    const NUMBER: i32;
}

// Multiple trait bounds
fn print_describable<T: Describe + Display>(item: &T) {
    println!("{}: {}", item.describe(), item);
}

// where clause (with references)
fn complex_bounds<T, U>(t: &T, u: &U)
where
    T: Describe,
    U: Greet,
{
    println!("{}", t.describe());
    println!("{}", u.greet());
}

// Structs implementing traits
struct Person {
    name: String,
}

impl Greet for Person {
    fn greet(&self) -> String {
        format!("Hello, I'm {}", self.name)
    }
}

impl Describe for Person {
    fn name(&self) -> &str {
        &self.name
    }
}

impl Display for Person {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Person({})", self.name)
    }
}

impl Container for Person {
    type Item = String;
    fn get(&self) -> &String {
        &self.name
    }
}

impl Numbered for Person {
    const NUMBER: i32 = 42;
}

// Trait object
fn greet_all(greeters: &[&dyn Greet]) {
    for g in greeters {
        println!("{}", g.greet());
    }
}

fn main() {
    let alice = Person { name: "Alice".to_string() };
    let bob = Person { name: "Bob".to_string() };

    // Direct method call
    println!("{}", alice.greet());
    println!("{}", alice.describe());

    // Trait bounds
    print_describable(&alice);

    // where clause
    complex_bounds(&alice, &bob);

    // Associated type
    println!("{}", alice.get());

    // Associated constant
    println!("{}", Person::NUMBER);

    // Trait objects
    let greeters: Vec<&dyn Greet> = vec![&alice, &bob];
    greet_all(&greeters);
}
