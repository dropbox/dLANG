// Level 3 Test: Generics and traits
// Tests: generic functions, structs, traits, trait bounds, associated types

use std::fmt::{Debug, Display};

fn main() {
    // Generic functions
    println!("=== Generic Functions ===");
    fn identity<T>(x: T) -> T { x }
    println!("identity(42): {}", identity(42));
    println!("identity(\"hello\"): {}", identity("hello"));

    fn largest<T: PartialOrd>(list: &[T]) -> &T {
        let mut largest = &list[0];
        for item in list {
            if item > largest {
                largest = item;
            }
        }
        largest
    }
    let numbers = vec![34, 50, 25, 100, 65];
    println!("largest of {:?}: {}", numbers, largest(&numbers));

    // Generic structs
    println!("\n=== Generic Structs ===");
    #[derive(Debug)]
    struct Point<T> {
        x: T,
        y: T,
    }
    impl<T> Point<T> {
        fn new(x: T, y: T) -> Self {
            Point { x, y }
        }
    }
    impl<T: Display> Point<T> {
        fn display(&self) {
            println!("Point({}, {})", self.x, self.y);
        }
    }
    let int_point = Point::new(5, 10);
    let float_point = Point::new(1.0, 4.0);
    int_point.display();
    float_point.display();

    // Multiple generic types
    #[derive(Debug)]
    struct Pair<T, U> {
        first: T,
        second: U,
    }
    let pair = Pair { first: 42, second: "hello" };
    println!("pair: {:?}", pair);

    // Traits
    println!("\n=== Traits ===");
    trait Animal {
        fn name(&self) -> &str;
        fn speak(&self) -> String;

        // Default implementation
        fn description(&self) -> String {
            format!("{} says: {}", self.name(), self.speak())
        }
    }

    struct Dog { name: String }
    struct Cat { name: String }

    impl Animal for Dog {
        fn name(&self) -> &str { &self.name }
        fn speak(&self) -> String { "Woof!".to_string() }
    }

    impl Animal for Cat {
        fn name(&self) -> &str { &self.name }
        fn speak(&self) -> String { "Meow!".to_string() }
    }

    let dog = Dog { name: "Buddy".to_string() };
    let cat = Cat { name: "Whiskers".to_string() };
    println!("{}", dog.description());
    println!("{}", cat.description());

    // Trait bounds
    println!("\n=== Trait Bounds ===");
    fn print_all<T: Display>(items: &[T]) {
        for item in items {
            print!("{} ", item);
        }
        println!();
    }
    print_all(&[1, 2, 3, 4, 5]);
    print_all(&["a", "b", "c"]);

    // Multiple bounds
    fn debug_display<T: Debug + Display>(item: T) {
        println!("Display: {}", item);
        println!("Debug: {:?}", item);
    }
    debug_display(42);

    // Where clauses
    fn longer<'a, T>(x: &'a T, y: &'a T) -> &'a T
    where
        T: PartialOrd + ?Sized,
    {
        if x > y { x } else { y }
    }
    println!("longer(3, 5): {}", longer(&3, &5));

    // Associated types
    println!("\n=== Associated Types ===");
    trait Container {
        type Item;
        fn get(&self) -> &Self::Item;
        fn count(&self) -> usize;
    }

    struct IntBox {
        value: i32,
    }
    impl Container for IntBox {
        type Item = i32;
        fn get(&self) -> &i32 { &self.value }
        fn count(&self) -> usize { 1 }
    }

    let box1 = IntBox { value: 42 };
    println!("IntBox contains: {}", box1.get());

    // Supertraits
    println!("\n=== Supertraits ===");
    trait Printable: Display + Debug {
        fn print(&self) {
            println!("Display: {}, Debug: {:?}", self, self);
        }
    }
    impl Printable for i32 {}
    42.print();

    // Trait objects
    println!("\n=== Trait Objects ===");
    fn animal_sounds(animals: &[&dyn Animal]) {
        for animal in animals {
            println!("{}", animal.description());
        }
    }
    let dog = Dog { name: "Rex".to_string() };
    let cat = Cat { name: "Felix".to_string() };
    animal_sounds(&[&dog, &cat]);

    // Static dispatch vs dynamic dispatch
    println!("\n=== Static vs Dynamic Dispatch ===");
    fn static_dispatch<T: Animal>(animal: &T) {
        println!("Static: {}", animal.speak());
    }
    fn dynamic_dispatch(animal: &dyn Animal) {
        println!("Dynamic: {}", animal.speak());
    }
    static_dispatch(&dog);
    dynamic_dispatch(&cat);

    // Blanket implementations
    println!("\n=== Blanket Implementations ===");
    trait Shout {
        fn shout(&self) -> String;
    }
    impl<T: Display> Shout for T {
        fn shout(&self) -> String {
            format!("{}!!!", self).to_uppercase()
        }
    }
    println!("42.shout(): {}", 42.shout());
    println!("\"hello\".shout(): {}", "hello".shout());

    // Const generics
    println!("\n=== Const Generics ===");
    fn array_sum<const N: usize>(arr: [i32; N]) -> i32 {
        arr.iter().sum()
    }
    println!("sum([1,2,3]): {}", array_sum([1, 2, 3]));
    println!("sum([10,20,30,40,50]): {}", array_sum([10, 20, 30, 40, 50]));
}
