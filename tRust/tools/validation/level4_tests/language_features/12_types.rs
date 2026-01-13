// Level 4.1: Type System Features
// Tests type aliases, newtypes, PhantomData, variance

use std::marker::PhantomData;

// Type alias
type Kilometers = i32;
type StringResult = Result<String, String>;
type Callback = fn(i32) -> i32;

// Generic type alias
type VecOf<T> = Vec<T>;

// Newtype pattern
struct Meters(f64);

impl Meters {
    fn to_feet(&self) -> f64 {
        self.0 * 3.28084
    }
}

impl std::fmt::Display for Meters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}m", self.0)
    }
}

// PhantomData for unused type parameters
struct TypedId<T> {
    id: u64,
    _marker: PhantomData<T>,
}

impl<T> TypedId<T> {
    fn new(id: u64) -> Self {
        TypedId { id, _marker: PhantomData }
    }

    fn value(&self) -> u64 {
        self.id
    }
}

struct User;
struct Order;

// Never type (!) in diverging functions
#[allow(dead_code)]
fn diverge() -> ! {
    panic!("This function never returns")
}

fn maybe_diverge(should: bool) -> i32 {
    if should {
        42
    } else {
        // diverge() // Would compile, returns !
        0
    }
}

// Sized and ?Sized
fn take_sized<T>(t: T) {
    std::mem::drop(t);
}

fn take_unsized<T: ?Sized>(t: &T)
where
    T: std::fmt::Debug,
{
    println!("{:?}", t);
}

// dyn Trait
trait Animal {
    fn speak(&self);
}

struct Dog;
struct Cat;

impl Animal for Dog {
    fn speak(&self) { println!("Woof!"); }
}

impl Animal for Cat {
    fn speak(&self) { println!("Meow!"); }
}

fn animal_speak(animal: &dyn Animal) {
    animal.speak();
}

// Inference with turbofish
fn generic_fn<T>() -> Vec<T> {
    Vec::new()
}

// Associated type bounds
trait Collection {
    type Item;
    fn get(&self, index: usize) -> Option<&Self::Item>;
}

impl<T> Collection for Vec<T> {
    type Item = T;
    fn get(&self, index: usize) -> Option<&T> {
        self.as_slice().get(index)
    }
}

fn get_first<C: Collection>(c: &C) -> Option<&C::Item> {
    c.get(0)
}

// Higher-ranked trait bounds (HRTB)
fn apply_to_str<F>(f: F)
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    let s = "hello";
    let result = f(s);
    println!("HRTB result: {}", result);
}

// Coercion examples
fn coercion_demo() {
    // &mut to &
    let mut x = 5;
    let r: &i32 = &mut x;
    println!("Coerced: {}", r);

    // Array to slice
    let arr = [1, 2, 3];
    let slice: &[i32] = &arr;
    println!("Slice: {:?}", slice);

    // Box to reference
    let boxed = Box::new(42);
    let r: &i32 = &boxed;
    println!("Boxed ref: {}", r);

    // Deref coercion
    let s = String::from("hello");
    let len = s.len(); // String -> &str via Deref
    println!("Len: {}", len);
}

fn main() {
    // Type aliases
    let distance: Kilometers = 100;
    println!("Distance: {}km", distance);

    let ok: StringResult = Ok("success".to_string());
    println!("Result: {:?}", ok);

    let cb: Callback = |x| x * 2;
    println!("Callback: {}", cb(5));

    let v: VecOf<i32> = vec![1, 2, 3];
    println!("VecOf: {:?}", v);

    // Newtype
    let m = Meters(100.0);
    println!("{} = {} feet", m, m.to_feet());

    // PhantomData
    let user_id: TypedId<User> = TypedId::new(1);
    let order_id: TypedId<Order> = TypedId::new(100);
    println!("User ID: {}, Order ID: {}", user_id.value(), order_id.value());
    // These are different types - can't mix them

    // Maybe diverge
    println!("Maybe: {}", maybe_diverge(true));

    // Sized
    take_sized(42);
    take_unsized(&[1, 2, 3]);
    take_unsized("hello"); // str is !Sized

    // dyn Trait
    let dog = Dog;
    let cat = Cat;
    animal_speak(&dog);
    animal_speak(&cat);

    // Turbofish
    let v = generic_fn::<i32>();
    println!("Turbofish vec: {:?}", v);

    // Collection
    let v = vec![1, 2, 3];
    println!("First: {:?}", get_first(&v));

    // HRTB
    apply_to_str(|s| s);

    // Coercion
    coercion_demo();

    println!("All type tests passed!");
}
