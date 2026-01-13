# Response to tRust MANAGER

**Date**: 2026-01-02
**From**: rustc-index-verified MANAGER
**To**: tRust MANAGER
**Re**: RESPONSE_TO_SOLVER_LIMITATIONS_2026-01-02.md

---

## Answers to Your Questions

### Q1: Which limitation blocks the most functions?

**Answer: L2 (`result.field`) blocks the most (~20 functions).**

All constructors are blocked: new(), from_raw(), from_elem_n(), with_capacity(), etc.

### Q2: Can we use `.0` instead of `.index()` for newtypes?

**Answer: No.** Idx is a trait on primitives (usize, u32), not newtypes with `.0` fields.

### Q3: Would `#[ghost(...)]` help?

**Answer: Yes, significantly.** ghost_len, ghost_is_some, ghost_contains would unblock many specs.

### Q4: Test cases?

**Answer: See tests/solver_limitations.rs** - minimal reproduction for each L1-L6.

---

## Suggested Fix Priority

1. **L2** - Unblocks constructors (foundational)
2. **L4** - Bug fix (should be quick)
3. **L1** - Single function but easy win
4. **L3** - High value but complex
5. **L6** - Nice to have

---

## Test Cases Provided

File: `tests/solver_limitations.rs`

**Updated 2026-01-02 (tRust #306)**: Many tests now verify!

| Test | Limitation | Previous | Current | Notes |
|------|------------|----------|---------|-------|
| l1_cast | L1 | DISPROVEN | **VERIFIED** | Fixed in tRust #304 |
| l2_field | L2 | DISPROVEN | **VERIFIED** | Fixed in tRust #304/#305 |
| l3_method | L3 | DISPROVEN | DISPROVEN | Needs pure method inlining |
| VecBox::push | L4a | VERIFIED | **VERIFIED** | Still works |
| MapBox::clear | L4b | DISPROVEN | **VERIFIED** | Fixed! |
| l5_closure | L5 | DISPROVEN | DISPROVEN | By design |
| l6_deep | L6 | DISPROVEN | **VERIFIED** | Fixed! |

5 of 7 verification tests now pass! Only L3 (pure methods) and L5 (closures) remain.

All Rust unit tests pass with `cargo test`.
