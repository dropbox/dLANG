// Level 4.1: Unsafe Code
// Tests unsafe blocks, raw pointers, and unsafe functions

use std::mem;

// Unsafe function
unsafe fn dangerous() -> i32 {
    42
}

// Function using unsafe internally
fn safe_wrapper() -> i32 {
    unsafe { dangerous() }
}

// Raw pointer operations
fn raw_pointer_demo() {
    let mut x = 10;

    // Create raw pointers
    let ptr = &mut x as *mut i32;
    let const_ptr = &x as *const i32;

    unsafe {
        // Dereference raw pointer
        *ptr = 20;
        println!("Via raw ptr: {}", *ptr);
        println!("Via const ptr: {}", *const_ptr);
    }

    println!("x is now: {}", x);
}

// Unsafe trait
unsafe trait UnsafeTrait {
    fn do_unsafe(&self) -> i32;
}

struct UnsafeImpl;

unsafe impl UnsafeTrait for UnsafeImpl {
    fn do_unsafe(&self) -> i32 {
        100
    }
}

// Mutable static
static mut COUNTER: i32 = 0;

fn increment_counter() {
    unsafe {
        COUNTER += 1;
    }
}

fn get_counter() -> i32 {
    unsafe { COUNTER }
}

// Union types
#[repr(C)]
union IntOrFloat {
    i: i32,
    f: f32,
}

fn union_demo() {
    let u = IntOrFloat { i: 42 };
    unsafe {
        println!("As int: {}", u.i);
        // Note: accessing u.f would be UB if not properly initialized
    }

    let u2 = IntOrFloat { f: 3.14 };
    unsafe {
        println!("As float: {}", u2.f);
    }
}

// Transmute
#[allow(unnecessary_transmutes)]
fn transmute_demo() {
    // Transmute between compatible types
    let x: i32 = 42;
    let y: u32 = unsafe { mem::transmute(x) };
    println!("Transmuted: {} -> {}", x, y);

    // Transmute array
    let arr: [u8; 4] = [1, 2, 3, 4];
    let val: u32 = unsafe { mem::transmute(arr) };
    println!("Array as u32: {}", val);
}

// Pointer arithmetic
fn pointer_arithmetic() {
    let arr = [10, 20, 30, 40, 50];
    let ptr = arr.as_ptr();

    unsafe {
        println!("arr[0] via ptr: {}", *ptr);
        println!("arr[2] via ptr.add(2): {}", *ptr.add(2));
        println!("arr[4] via ptr.add(4): {}", *ptr.add(4));
    }
}

// Slice from raw parts
fn slice_from_raw() {
    let arr = [1, 2, 3, 4, 5];
    let ptr = arr.as_ptr();
    let len = arr.len();

    let slice: &[i32] = unsafe {
        std::slice::from_raw_parts(ptr, len)
    };
    println!("Slice: {:?}", slice);
}

// Extern block (linking)
extern "C" {
    fn abs(x: i32) -> i32;
}

fn extern_demo() {
    let x = -42;
    let y = unsafe { abs(x) };
    println!("abs({}) = {}", x, y);
}

fn main() {
    // Unsafe function
    println!("Safe wrapper: {}", safe_wrapper());

    // Raw pointers
    raw_pointer_demo();

    // Unsafe trait
    let u = UnsafeImpl;
    println!("Unsafe trait: {}", u.do_unsafe());

    // Mutable static
    increment_counter();
    increment_counter();
    println!("Counter: {}", get_counter());

    // Union
    union_demo();

    // Transmute
    transmute_demo();

    // Pointer arithmetic
    pointer_arithmetic();

    // Slice from raw
    slice_from_raw();

    // Extern
    extern_demo();

    println!("All unsafe tests passed!");
}
