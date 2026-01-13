// Level 4.1: Lifetimes
// Tests lifetime annotations and borrowing

// Explicit lifetime annotation
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// Multiple lifetimes
fn first_word<'a, 'b>(s: &'a str, _prefix: &'b str) -> &'a str {
    s.split_whitespace().next().unwrap_or(s)
}

// Lifetime in struct
struct StrRef<'a> {
    content: &'a str,
}

impl<'a> StrRef<'a> {
    fn new(content: &'a str) -> Self {
        StrRef { content }
    }

    fn get(&self) -> &str {
        self.content
    }

    // Method returning reference with struct's lifetime
    fn first_char(&self) -> Option<char> {
        self.content.chars().next()
    }
}

// Lifetime bounds
struct Wrapper<'a, T: 'a> {
    value: &'a T,
}

impl<'a, T: 'a + std::fmt::Display> Wrapper<'a, T> {
    fn print(&self) {
        println!("{}", self.value);
    }
}

// Static lifetime
static GREETING: &str = "Hello";

fn static_ref() -> &'static str {
    GREETING
}

// Lifetime elision examples
fn first_element(arr: &[i32]) -> Option<&i32> {
    arr.first()
}

fn identity_str(s: &str) -> &str {
    s
}

// Multiple references in struct
struct TwoRefs<'a, 'b> {
    first: &'a str,
    second: &'b str,
}

fn main() {
    // Basic lifetime
    let s1 = String::from("hello");
    let s2 = String::from("hi");
    let result = longest(&s1, &s2);
    println!("Longest: {}", result);

    // Multiple lifetimes
    let word = first_word("hello world", "prefix");
    println!("First word: {}", word);

    // Struct with lifetime
    let text = String::from("Rust");
    let sr = StrRef::new(&text);
    println!("Content: {}", sr.get());
    println!("First char: {:?}", sr.first_char());

    // Lifetime bounds
    let num = 42;
    let w = Wrapper { value: &num };
    w.print();

    // Static lifetime
    println!("Static: {}", static_ref());

    // Elided lifetimes
    let arr = [1, 2, 3];
    println!("First: {:?}", first_element(&arr));
    println!("Identity: {}", identity_str("test"));

    // Multiple refs
    let a = "first";
    let b = String::from("second");
    let two = TwoRefs { first: a, second: &b };
    println!("{} {}", two.first, two.second);
}
