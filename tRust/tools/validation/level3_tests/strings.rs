// Level 3 Test: String operations
// Tests: String creation, manipulation, formatting, Unicode

fn main() {
    // Basic strings
    let s1 = "Hello, World!";
    let s2 = String::from("Rust is awesome");
    println!("str literal: {}", s1);
    println!("String: {}", s2);

    // String operations
    println!("len: {}", s2.len());
    println!("is_empty: {}", s2.is_empty());
    println!("to_uppercase: {}", s2.to_uppercase());
    println!("to_lowercase: {}", s2.to_lowercase());

    // Concatenation
    let s3 = format!("{} - {}", s1, s2);
    println!("concat: {}", s3);

    // Slicing
    let slice = &s1[0..5];
    println!("slice [0..5]: {}", slice);

    // Searching
    println!("contains 'World': {}", s1.contains("World"));
    println!("starts_with 'Hello': {}", s1.starts_with("Hello"));
    println!("ends_with '!': {}", s1.ends_with("!"));
    println!("find 'W': {:?}", s1.find('W'));

    // Splitting
    print!("split by ' ': ");
    for word in s1.split(' ') {
        print!("[{}] ", word);
    }
    println!();

    // Trimming
    let padded = "   trim me   ";
    println!("trim: '{}'", padded.trim());
    println!("trim_start: '{}'", padded.trim_start());
    println!("trim_end: '{}'", padded.trim_end());

    // Replacement
    let replaced = s1.replace("World", "Rust");
    println!("replace: {}", replaced);

    // Unicode
    let unicode = "こんにちは世界! 🦀";
    println!("unicode: {}", unicode);
    println!("unicode len (bytes): {}", unicode.len());
    println!("unicode chars count: {}", unicode.chars().count());

    // Chars iteration
    print!("chars: ");
    for c in "Rust🦀".chars() {
        print!("[{}] ", c);
    }
    println!();

    // Bytes
    print!("bytes of 'ABC': ");
    for b in "ABC".bytes() {
        print!("{} ", b);
    }
    println!();

    // Parsing
    let num_str = "42";
    let parsed: i32 = num_str.parse().unwrap();
    println!("parsed '42': {}", parsed);

    // Formatting
    println!("format int: {:05}", 42);
    println!("format hex: {:x}", 255);
    println!("format bin: {:b}", 255);
    println!("format float: {:.3}", 3.14159);
    println!("format debug: {:?}", vec![1, 2, 3]);
}
