# PHASE 5: Real-World Verification

**Date**: 2024-12-31
**Priority**: CRITICAL - Prove the system works on real code
**Status**: COMPLETE (22/22 verified - stack + binary search)

## STOP ADDING FEATURES

The verification infrastructure is **complete enough**. We have:
- ✅ Basic postconditions
- ✅ Struct field access
- ✅ Array indexing
- ✅ Modular verification
- ✅ Loop invariants
- ✅ Termination proofs
- ✅ Mutual recursion
- ✅ Refinement types

**It's time to verify REAL CODE.**

## Goals

1. Pick a small, real Rust crate
2. Add specifications to it
3. Verify it with cargo-trust
4. Document what works and what breaks

## Target: A Simple Data Structure Crate

Choose ONE of these to verify:

### Option A: Vec operations (from std)
```rust
// Verify push, pop, len, is_empty
// Test: vec.len() after push increases by 1
// Test: pop on non-empty returns Some
```

### Option B: Simple stack implementation
```rust
struct Stack<T> { data: Vec<T> }

// #[ensures(result == old(self.data.len()) + 1)]
fn push(&mut self, x: T) { self.data.push(x); }

// #[requires(self.data.len() > 0)]
// #[ensures(result.is_some())]
fn pop(&mut self) -> Option<T> { self.data.pop() }
```

### Option C: Binary search
```rust
// #[requires(arr.is_sorted())]
// #[ensures(result.is_none() || arr[result.unwrap()] == target)]
fn binary_search(arr: &[i32], target: i32) -> Option<usize>
```

## Success Criteria

1. At least 5 functions with specs verified
2. At least 1 function with loop + invariant verified
3. At least 1 function calling another (modular verification)
4. Document any feature gaps discovered

## Implementation Plan

### Step 1: Create examples/real_world/ directory

```bash
mkdir -p examples/real_world
```

### Step 2: Implement a simple verified stack

```rust
// examples/real_world/verified_stack.rs

struct Stack {
    data: Vec<i32>,
    capacity: usize,
}

// #[ensures(result.data.len() == 0)]
// #[ensures(result.capacity == cap)]
fn new(cap: usize) -> Stack {
    Stack { data: Vec::new(), capacity: cap }
}

// #[requires(self.data.len() < self.capacity)]
// #[ensures(self.data.len() == old(self.data.len()) + 1)]
fn push(&mut self, x: i32) {
    self.data.push(x);
}

// #[ensures(old(self.data.len()) == 0 ==> result.is_none())]
// #[ensures(old(self.data.len()) > 0 ==> result.is_some())]
fn pop(&mut self) -> Option<i32> {
    self.data.pop()
}

// #[ensures(result == self.data.len() == 0)]
fn is_empty(&self) -> bool {
    self.data.is_empty()
}

// #[ensures(result == self.data.len())]
fn len(&self) -> usize {
    self.data.len()
}
```

### Step 3: Run verification

```bash
cargo trust verify examples/real_world/verified_stack.rs
```

### Step 4: Document results

Create `reports/real_world_verification_YYYY-MM-DD.md` with:
- Which specs verified
- Which specs failed (and why)
- Feature gaps discovered
- Suggested improvements

## DO NOT

- Do not add more verification features
- Do not refactor existing code
- Do not add more unit tests

**FOCUS: Verify real code, find gaps, document results.**

## After This

Once we've verified real code:
1. Fix any critical gaps discovered
2. Improve error messages based on real usage
3. Then consider Phase 5 (Effects) or Phase 6 (Temporal)
