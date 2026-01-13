// Level 4.1: Advanced Pattern Matching
// Tests pattern syntax and matching

fn main() {
    // Basic patterns
    let x = 5;
    match x {
        1 => println!("one"),
        2 | 3 => println!("two or three"),
        4..=10 => println!("four to ten"),
        _ => println!("other"),
    }

    // Destructuring tuples
    let pair = (1, "hello");
    let (num, text) = pair;
    println!("Tuple: {} {}", num, text);

    // Destructuring structs
    struct Point { x: i32, y: i32 }
    let p = Point { x: 10, y: 20 };
    let Point { x: px, y: py } = p;
    println!("Point: ({}, {})", px, py);

    // Shorthand
    let Point { x, y } = p;
    println!("Shorthand: ({}, {})", x, y);

    // Ignoring with ..
    #[allow(dead_code)]
    struct Point3D { x: i32, y: i32, z: i32 }
    let p3 = Point3D { x: 1, y: 2, z: 3 };
    let Point3D { x, .. } = p3;
    println!("Only x: {}", x);

    // Enum destructuring
    enum Message {
        Quit,
        Move { x: i32, y: i32 },
        Write(String),
        Color(i32, i32, i32),
    }

    let msgs = [
        Message::Quit,
        Message::Move { x: 10, y: 20 },
        Message::Write("hello".to_string()),
        Message::Color(255, 128, 0),
    ];

    for msg in msgs {
        match msg {
            Message::Quit => println!("Quit"),
            Message::Move { x, y } => println!("Move to ({}, {})", x, y),
            Message::Write(s) => println!("Write: {}", s),
            Message::Color(r, g, b) => println!("Color: RGB({}, {}, {})", r, g, b),
        }
    }

    // Guards
    let num = 15;
    match num {
        n if n < 0 => println!("negative"),
        n if n == 0 => println!("zero"),
        n if n < 10 => println!("small positive"),
        _ => println!("large positive"),
    }

    // @ bindings
    match num {
        n @ 1..=20 => println!("1-20: {}", n),
        n @ 21..=100 => println!("21-100: {}", n),
        other => println!("Other: {}", other),
    }

    // Nested patterns
    let nested = Some(Some(42));
    match nested {
        Some(Some(n)) => println!("Nested: {}", n),
        Some(None) => println!("Inner none"),
        None => println!("Outer none"),
    }

    // Slice patterns
    let arr = [1, 2, 3, 4, 5];
    match &arr[..] {
        [first, .., last] => println!("First: {}, Last: {}", first, last),
        _ => println!("Empty or single"),
    }

    match &arr[..] {
        [a, b, rest @ ..] => println!("a={}, b={}, rest={:?}", a, b, rest),
        _ => println!("Too short"),
    }

    // Reference patterns
    let reference = &5;
    match reference {
        &val => println!("Matched &val: {}", val),
    }

    // Or patterns in match
    let result: Result<i32, i32> = Ok(42);
    let n = match result {
        Ok(v) | Err(v) => v,
    };
    println!("Or pattern: {}", n);

    // if let chains
    let opt = Some(42);
    if let Some(n) = opt {
        if n > 10 {
            println!("Some > 10: {}", n);
        }
    }

    // while let
    let mut stack = vec![1, 2, 3];
    while let Some(top) = stack.pop() {
        println!("Popped: {}", top);
    }

    // let else
    fn get_value(opt: Option<i32>) -> i32 {
        let Some(v) = opt else {
            return 0;
        };
        v
    }
    println!("let else Some: {}", get_value(Some(5)));
    println!("let else None: {}", get_value(None));

    // Box patterns (requires nightly, simulate with ref)
    let boxed: Box<i32> = Box::new(42);
    match *boxed {
        n if n > 0 => println!("Positive boxed: {}", n),
        _ => println!("Non-positive"),
    }

    println!("All pattern tests passed!");
}
