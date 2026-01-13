// Level 4.1: Return Position Impl Trait in Trait (RPITIT)
// Tests impl Trait in trait method return positions

use std::fmt::Display;

// Basic RPITIT
trait Greeter {
    fn greet(&self) -> impl Display;
}

struct EnglishGreeter;

impl Greeter for EnglishGreeter {
    fn greet(&self) -> impl Display {
        "Hello!"
    }
}

struct SpanishGreeter;

impl Greeter for SpanishGreeter {
    fn greet(&self) -> impl Display {
        "¡Hola!"
    }
}

// RPITIT with bounds
trait Sequence {
    fn elements(&self) -> impl Iterator<Item = i32>;
}

struct Range5;

impl Sequence for Range5 {
    fn elements(&self) -> impl Iterator<Item = i32> {
        0..5
    }
}

struct Odds;

impl Sequence for Odds {
    fn elements(&self) -> impl Iterator<Item = i32> {
        (0..10).filter(|n| n % 2 == 1)
    }
}

// RPITIT with multiple bounds
trait Describe {
    fn description(&self) -> impl Display + Clone;
}

struct Thing(String);

impl Describe for Thing {
    fn description(&self) -> impl Display + Clone {
        self.0.clone()
    }
}

// RPITIT with lifetime
trait Provider<'a> {
    fn provide(&'a self) -> impl Display + 'a;
}

struct Data(String);

impl<'a> Provider<'a> for Data {
    fn provide(&'a self) -> impl Display + 'a {
        &self.0
    }
}

// RPITIT with generic type
trait Transformer<T> {
    fn transform(&self, input: T) -> impl Display;
}

struct Stringify;

impl<T: Display> Transformer<T> for Stringify {
    fn transform(&self, input: T) -> impl Display {
        format!("Transformed: {}", input)
    }
}

// RPITIT returning complex iterator
trait DataProcessor {
    fn process(&self) -> impl Iterator<Item = i32> + Clone;
}

struct Doubler(Vec<i32>);

impl DataProcessor for Doubler {
    fn process(&self) -> impl Iterator<Item = i32> + Clone {
        self.0.iter().map(|n| n * 2).collect::<Vec<_>>().into_iter()
    }
}

// RPITIT with async (use trait bounds to approximate)
trait AsyncLike {
    fn async_result(&self) -> impl std::future::Future<Output = i32>;
}

struct ImmediateResult(i32);

impl AsyncLike for ImmediateResult {
    fn async_result(&self) -> impl std::future::Future<Output = i32> {
        std::future::ready(self.0)
    }
}

// Using RPITIT with generics
fn use_greeter<G: Greeter>(g: &G) {
    println!("{}", g.greet());
}

fn use_sequence<S: Sequence>(s: &S) {
    for elem in s.elements() {
        print!("{} ", elem);
    }
    println!();
}

fn main() {
    // Basic RPITIT
    let eng = EnglishGreeter;
    let spa = SpanishGreeter;
    println!("English: {}", eng.greet());
    println!("Spanish: {}", spa.greet());

    // Generic usage
    use_greeter(&eng);
    use_greeter(&spa);

    // Iterator RPITIT
    let r5 = Range5;
    let odds = Odds;
    print!("Range5: ");
    use_sequence(&r5);
    print!("Odds: ");
    use_sequence(&odds);

    // Multiple bounds
    let thing = Thing("A thing".to_string());
    let desc = thing.description();
    let desc_clone = desc.clone();
    println!("Description: {}, Clone: {}", desc, desc_clone);

    // With lifetime
    let data = Data("Lifetime data".to_string());
    println!("Provider: {}", data.provide());

    // Generic type
    let s = Stringify;
    println!("{}", s.transform(42));
    println!("{}", s.transform("hello"));

    // Complex iterator
    let d = Doubler(vec![1, 2, 3, 4, 5]);
    print!("Doubled: ");
    for n in d.process() {
        print!("{} ", n);
    }
    println!();

    // Async-like
    let ir = ImmediateResult(99);
    // Note: need runtime to actually poll, just verify it compiles
    let _future = ir.async_result();
    println!("AsyncLike compiles correctly");

    println!("All RPITIT tests passed!");
}
