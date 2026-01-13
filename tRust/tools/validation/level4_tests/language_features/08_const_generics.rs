// Level 4.1: Const Generics
// Tests const generic parameters

// Array wrapper with const generic size
#[derive(Debug)]
struct Array<T, const N: usize> {
    data: [T; N],
}

impl<T: Default + Copy, const N: usize> Array<T, N> {
    fn new() -> Self {
        Array {
            data: [T::default(); N],
        }
    }

    fn len(&self) -> usize {
        N
    }
}

impl<T: Copy, const N: usize> Array<T, N> {
    fn from_array(data: [T; N]) -> Self {
        Array { data }
    }

    fn get(&self, index: usize) -> Option<&T> {
        if index < N {
            Some(&self.data[index])
        } else {
            None
        }
    }
}

// Const generic with default
struct WithDefault<const N: usize = 10>;

impl<const N: usize> WithDefault<N> {
    fn size() -> usize {
        N
    }
}

// Multiple const generics
#[allow(dead_code)]
struct Matrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Default + Copy, const ROWS: usize, const COLS: usize> Matrix<T, ROWS, COLS> {
    fn new() -> Self {
        Matrix {
            data: [[T::default(); COLS]; ROWS],
        }
    }

    fn dimensions(&self) -> (usize, usize) {
        (ROWS, COLS)
    }
}

// Const generic in function
fn create_array<const N: usize>() -> [i32; N] {
    [0; N]
}

// Const generic with expression
fn double_sized<const N: usize>() -> usize {
    N * 2
}

// Simple const generic function
fn print_const_size<const N: usize>() {
    println!("N = {}", N);
}

// Const generic in trait
trait FixedSize<const N: usize> {
    fn capacity() -> usize {
        N
    }
}

struct Buffer<const SIZE: usize> {
    _data: [u8; SIZE],
}

impl<const SIZE: usize> FixedSize<SIZE> for Buffer<SIZE> {}

// Const generic with associated types
trait ArrayLike {
    type Element;
    const SIZE: usize;

    fn as_slice(&self) -> &[Self::Element];
}

impl<T, const N: usize> ArrayLike for Array<T, N> {
    type Element = T;
    const SIZE: usize = N;

    fn as_slice(&self) -> &[T] {
        &self.data
    }
}

fn main() {
    // Basic const generic struct
    let arr: Array<i32, 5> = Array::from_array([1, 2, 3, 4, 5]);
    println!("Array len: {}", arr.len());
    println!("Array[2]: {:?}", arr.get(2));
    println!("Array: {:?}", arr);

    // Default const generic
    let arr_default: Array<i32, 3> = Array::new();
    println!("Default array: {:?}", arr_default);

    // With default size
    println!("Default size: {}", WithDefault::<10>::size());
    println!("Custom size: {}", WithDefault::<5>::size());

    // Matrix (multiple const generics)
    let matrix: Matrix<i32, 2, 3> = Matrix::new();
    println!("Matrix dimensions: {:?}", matrix.dimensions());

    // Const generic function
    let zeros: [i32; 4] = create_array();
    println!("Zeros: {:?}", zeros);

    // Const expression
    println!("Double 5: {}", double_sized::<5>());
    println!("Double 10: {}", double_sized::<10>());

    // Simple const function call
    print_const_size::<3>();
    print_const_size::<100>();

    // Trait with const generic
    println!("Buffer<64> capacity: {}", Buffer::<64>::capacity());
    println!("Buffer<256> capacity: {}", Buffer::<256>::capacity());

    // Associated const
    let arr5: Array<i32, 5> = Array::from_array([1, 2, 3, 4, 5]);
    println!("ArrayLike SIZE: {}", <Array<i32, 5> as ArrayLike>::SIZE);
    println!("ArrayLike slice: {:?}", arr5.as_slice());

    println!("All const generic tests passed!");
}
