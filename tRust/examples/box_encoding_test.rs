// Box/Heap Encoding Test
//
// STATUS: EXPECTED_VERIFY - Box::new semantics now modeled
//
// SOUNDNESS FIX (2026-01-05):
// Box::new(v) now establishes the constraint *result == v in WP calculus.
// The heap allocation correctly tracks the relationship between the box
// pointer and its contents.
//
// Previous bug: Box::new was treated as opaque function call, heap semantics
// were not modeled, causing verification to fail for correct code.
//
// Current behavior: For dest = Box::new(arg), we generate the constraint
// (*dest == arg), which allows verification of box-related postconditions.
//
// See: docs/design/NUCLEAR_GRADE_ROADMAP.md Phase N1.2

// EXPECTED: VERIFY - Box::new(42) creates box containing 42
// Now correctly generates constraint (*result == 42)
#[ensures("*result == 42")]
fn make_box() -> Box<i32> {
    Box::new(42)
}

// Integer control: this should VERIFY (no heap operations)
#[ensures("result == 42")]
fn make_int() -> i32 {
    42
}

fn main() {}
