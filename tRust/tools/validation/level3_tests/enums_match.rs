// Level 3 Test: Enums and pattern matching
// Tests: enum variants, match expressions, if let, while let

fn main() {
    // Basic enum
    println!("=== Basic Enum ===");
    #[derive(Debug)]
    enum Direction {
        North,
        South,
        East,
        West,
    }

    let dir = Direction::North;
    match dir {
        Direction::North => println!("Going north"),
        Direction::South => println!("Going south"),
        Direction::East => println!("Going east"),
        Direction::West => println!("Going west"),
    }

    // Enum with data
    println!("\n=== Enum with Data ===");
    #[derive(Debug)]
    enum Message {
        Quit,
        Move { x: i32, y: i32 },
        Write(String),
        ChangeColor(u8, u8, u8),
    }

    fn process_message(msg: Message) {
        match msg {
            Message::Quit => println!("Quit"),
            Message::Move { x, y } => println!("Move to ({}, {})", x, y),
            Message::Write(text) => println!("Write: {}", text),
            Message::ChangeColor(r, g, b) => println!("Color: rgb({}, {}, {})", r, g, b),
        }
    }

    process_message(Message::Quit);
    process_message(Message::Move { x: 10, y: 20 });
    process_message(Message::Write("Hello".to_string()));
    process_message(Message::ChangeColor(255, 128, 0));

    // Option enum
    println!("\n=== Option ===");
    let some_num: Option<i32> = Some(42);
    let no_num: Option<i32> = None;

    match some_num {
        Some(n) => println!("Got number: {}", n),
        None => println!("No number"),
    }

    match no_num {
        Some(n) => println!("Got number: {}", n),
        None => println!("No number"),
    }

    // Result enum
    println!("\n=== Result ===");
    fn divide(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }

    match divide(10, 2) {
        Ok(result) => println!("10 / 2 = {}", result),
        Err(e) => println!("Error: {}", e),
    }

    match divide(10, 0) {
        Ok(result) => println!("10 / 0 = {}", result),
        Err(e) => println!("Error: {}", e),
    }

    // if let
    println!("\n=== if let ===");
    let opt = Some(42);
    if let Some(n) = opt {
        println!("if let: got {}", n);
    }

    let empty: Option<i32> = None;
    if let Some(n) = empty {
        println!("This won't print: {}", n);
    } else {
        println!("if let else: was None");
    }

    // while let
    println!("\n=== while let ===");
    let mut stack = vec![1, 2, 3];
    print!("while let pop: ");
    while let Some(top) = stack.pop() {
        print!("{} ", top);
    }
    println!();

    // Pattern guards
    println!("\n=== Pattern Guards ===");
    let num = Some(4);
    match num {
        Some(x) if x < 5 => println!("{} is less than 5", x),
        Some(x) => println!("{} is >= 5", x),
        None => println!("None"),
    }

    // Multiple patterns
    println!("\n=== Multiple Patterns ===");
    for x in 0..6 {
        match x {
            0 | 1 => print!("zero or one "),
            2..=4 => print!("two to four "),
            _ => print!("something else "),
        }
    }
    println!();

    // Destructuring
    println!("\n=== Destructuring ===");
    struct Point { x: i32, y: i32 }
    let p = Point { x: 0, y: 7 };
    match p {
        Point { x: 0, y } => println!("On y axis at y={}", y),
        Point { x, y: 0 } => println!("On x axis at x={}", x),
        Point { x, y } => println!("At ({}, {})", x, y),
    }

    // Nested patterns
    println!("\n=== Nested Patterns ===");
    let nested = Some(Some(42));
    match nested {
        Some(Some(n)) => println!("Nested: {}", n),
        Some(None) => println!("Outer Some, inner None"),
        None => println!("Outer None"),
    }

    // @ bindings
    println!("\n=== @ Bindings ===");
    enum E {
        Value(i32),
    }
    let e = E::Value(5);
    match e {
        E::Value(n @ 1..=10) => println!("Got {} in range 1-10", n),
        E::Value(n) => println!("Got {} outside range", n),
    }

    // Tuple matching
    println!("\n=== Tuple Matching ===");
    let pair = (0, -2);
    match pair {
        (0, y) => println!("First is 0, y = {}", y),
        (x, 0) => println!("Second is 0, x = {}", x),
        _ => println!("Other"),
    }

    // Ref patterns
    println!("\n=== Ref Patterns ===");
    let reference = &42;
    match reference {
        &val => println!("Destructured: {}", val),
    }

    // matches! macro
    println!("\n=== matches! Macro ===");
    let foo = 'f';
    println!("matches!('f', 'A'..='Z' | 'a'..='z'): {}", matches!(foo, 'A'..='Z' | 'a'..='z'));
    println!("matches!('5', '0'..='9'): {}", matches!('5', '0'..='9'));

    // Exhaustiveness
    println!("\n=== Exhaustiveness ===");
    let boolean = true;
    let binary = match boolean {
        false => 0,
        true => 1,
    };
    println!("true as binary: {}", binary);
}
