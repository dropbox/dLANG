// Level 4.1: Closures
// Tests closure syntax, capturing, and Fn traits

fn main() {
    // Basic closure
    let add = |a, b| a + b;
    println!("{}", add(2, 3));

    // Closure with explicit types
    let multiply: fn(i32, i32) -> i32 = |x, y| x * y;
    println!("{}", multiply(4, 5));

    // Closure capturing by reference (Fn)
    let x = 10;
    let add_x = |n| n + x;
    println!("{}", add_x(5));
    println!("x is still: {}", x);

    // Closure capturing by mutable reference (FnMut)
    let mut counter = 0;
    let mut increment = || {
        counter += 1;
        counter
    };
    println!("{}", increment());
    println!("{}", increment());
    println!("Final counter: {}", counter);

    // Closure taking ownership (FnOnce with move)
    let s = String::from("hello");
    let consume = move || {
        println!("Consuming: {}", s);
        // s is moved into closure
    };
    consume();
    // s is no longer accessible here

    // Higher-order functions
    let numbers = vec![1, 2, 3, 4, 5];
    let doubled: Vec<i32> = numbers.iter().map(|n| n * 2).collect();
    println!("Doubled: {:?}", doubled);

    let evens: Vec<&i32> = numbers.iter().filter(|n| *n % 2 == 0).collect();
    println!("Evens: {:?}", evens);

    let sum: i32 = numbers.iter().fold(0, |acc, n| acc + n);
    println!("Sum: {}", sum);

    // Closure as function parameter
    fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
        f(x)
    }
    println!("Applied: {}", apply(|n| n * n, 7));

    // Closure returning closure
    fn make_adder(n: i32) -> impl Fn(i32) -> i32 {
        move |x| x + n
    }
    let add_10 = make_adder(10);
    println!("Add 10: {}", add_10(5));

    // FnOnce
    fn consume_and_call<F: FnOnce() -> String>(f: F) -> String {
        f()
    }
    let s = String::from("owned");
    let result = consume_and_call(|| s);
    println!("Consumed: {}", result);

    // FnMut
    fn apply_mut<F: FnMut()>(mut f: F) {
        f();
        f();
    }
    let mut v = Vec::new();
    apply_mut(|| v.push(1));
    println!("Vector: {:?}", v);
}
