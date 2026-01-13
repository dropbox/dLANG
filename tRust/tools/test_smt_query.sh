#!/bin/bash
# Test script to verify SMT query generation for nested_guards
# Created: #99 - Demonstrates the tuple field operand fix

echo "=== Testing SMT Query for nested_guards ==="
echo ""
echo "Test case: nested_guards(x: u8, y: u8, z: u8) -> u8"
echo "  if x < 50 { if y < 50 { if z < 50 { x + y + z } } }"
echo ""
echo "MIR representation:"
echo "  _10 = AddWithOverflow(_1, _2)  // x + y"
echo "  _12 = AddWithOverflow((_10.0), _3)  // (x+y) + z"
echo ""

# Test 1: First addition (x + y) with all path conditions
echo "--- Test 1: First addition (x + y) ---"
cat <<'EOF' | z3 -smt2 -in 2>&1
; Check first addition: _1 + _2 (x + y)
; Declarations
(declare-const _1 Int)
(assert (and (>= _1 0) (<= _1 255)))
(declare-const _2 Int)
(assert (and (>= _2 0) (<= _2 255)))
(declare-const _3 Int)
(assert (and (>= _3 0) (<= _3 255)))

; Path conditions (all three guards)
(assert (< _1 50))
(assert (< _2 50))
(assert (< _3 50))

; Check overflow: (+ _1 _2) > 255 OR < 0
(assert (or (> (+ _1 _2) 255) (< (+ _1 _2) 0)))
(check-sat)
EOF
echo ""

# Test 2: Second addition WITHOUT intermediate definition (should be SAT - overflow possible)
echo "--- Test 2: Second addition WITHOUT intermediate definition (EXPECTED: sat) ---"
cat <<'EOF' | z3 -smt2 -in 2>&1
; Check second addition: _9 + _3 WITHOUT definition for _9
(declare-const _1 Int)
(assert (and (>= _1 0) (<= _1 255)))
(declare-const _2 Int)
(assert (and (>= _2 0) (<= _2 255)))
(declare-const _3 Int)
(assert (and (>= _3 0) (<= _3 255)))
(declare-const _9 Int)
(assert (and (>= _9 0) (<= _9 255)))

; Path conditions
(assert (< _1 50))
(assert (< _2 50))
(assert (< _3 50))

; NO intermediate definition for _9!
; Check overflow: (+ _9 _3) > 255 OR < 0
(assert (or (> (+ _9 _3) 255) (< (+ _9 _3) 0)))
(check-sat)
(get-model)
EOF
echo ""

# Test 3: Second addition WITH intermediate definition (should be UNSAT - no overflow)
echo "--- Test 3: Second addition WITH intermediate definition (EXPECTED: unsat) ---"
cat <<'EOF' | z3 -smt2 -in 2>&1
; Check second addition: _9 + _3 WITH definition for _9
(declare-const _1 Int)
(assert (and (>= _1 0) (<= _1 255)))
(declare-const _2 Int)
(assert (and (>= _2 0) (<= _2 255)))
(declare-const _3 Int)
(assert (and (>= _3 0) (<= _3 255)))
(declare-const _9 Int)
(assert (and (>= _9 0) (<= _9 255)))

; Intermediate definition: _9 = _1 + _2
(assert (= _9 (+ _1 _2)))

; Path conditions
(assert (< _1 50))
(assert (< _2 50))
(assert (< _3 50))

; Check overflow: (+ _9 _3) > 255 OR < 0
(assert (or (> (+ _9 _3) 255) (< (+ _9 _3) 0)))
(check-sat)
EOF
echo ""

echo "=== Analysis ==="
echo "If Test 2 is 'sat' and Test 3 is 'unsat', then the intermediate definition is REQUIRED."
echo "The bug must be that intermediate definitions are NOT being included in the query."
