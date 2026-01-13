// Type recursion stress test
trait DeepTrait<T> {
    type Assoc;
}

struct Level0;
struct Level1<T>(T);
struct Level2<T>(T);
struct Level3<T>(T);
struct Level4<T>(T);
struct Level5<T>(T);

impl DeepTrait<Level0> for Level1<Level0> { type Assoc = Level0; }
impl<T> DeepTrait<Level1<T>> for Level2<Level1<T>> where Level1<T>: DeepTrait<T> { type Assoc = Level1<T>; }
impl<T> DeepTrait<Level2<T>> for Level3<Level2<T>> where Level2<T>: DeepTrait<T> { type Assoc = Level2<T>; }
impl<T> DeepTrait<Level3<T>> for Level4<Level3<T>> where Level3<T>: DeepTrait<T> { type Assoc = Level3<T>; }
impl<T> DeepTrait<Level4<T>> for Level5<Level4<T>> where Level4<T>: DeepTrait<T> { type Assoc = Level4<T>; }

// Recursive type with lifetime
enum List<'a, T> {
    Nil,
    Cons(T, &'a List<'a, T>),
}

impl<'a, T: Copy> List<'a, T> {
    fn len(&self) -> usize {
        match self {
            List::Nil => 0,
            List::Cons(_, tail) => 1 + tail.len(),
        }
    }
}

fn main() {
    let nil: List<i32> = List::Nil;
    let cons = List::Cons(1, &nil);
    let cons2 = List::Cons(2, &cons);
    println!("List length: {}", cons2.len());
    println!("Type stress test passed");
}
