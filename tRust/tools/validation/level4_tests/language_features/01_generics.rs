// Level 4.1: Generics
// Tests generic types, functions, and implementations

fn identity<T>(x: T) -> T { x }

struct Wrapper<T> {
    value: T,
}

impl<T> Wrapper<T> {
    fn new(value: T) -> Self {
        Wrapper { value }
    }

    fn get(&self) -> &T {
        &self.value
    }
}

impl<T: std::fmt::Display> Wrapper<T> {
    fn display(&self) {
        println!("Wrapper({})", self.value);
    }
}

// Multiple type parameters
fn pair<A, B>(a: A, b: B) -> (A, B) {
    (a, b)
}

// Generic with trait bounds
fn print_all<T: std::fmt::Display>(items: &[T]) {
    for item in items {
        println!("{}", item);
    }
}

// Generic enum
#[allow(dead_code)]
enum Option2<T> {
    Some(T),
    None,
}

impl<T> Option2<T> {
    fn is_some(&self) -> bool {
        matches!(self, Option2::Some(_))
    }
}

fn main() {
    // Generic function
    println!("{}", identity(42));
    println!("{}", identity("hello"));

    // Generic struct
    let w1 = Wrapper::new(100);
    let w2 = Wrapper::new("world");
    println!("{}", w1.get());
    println!("{}", w2.get());
    w1.display();

    // Multiple type params
    let p = pair(1, "two");
    println!("{} {}", p.0, p.1);

    // Generic with bounds
    print_all(&[1, 2, 3]);

    // Generic enum
    let opt: Option2<i32> = Option2::Some(5);
    println!("{}", opt.is_some());
}
