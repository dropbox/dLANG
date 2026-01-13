/-
  MIR Semantics Formalization for tRust
  Phase N2.1: Foundational MIR semantics in Lean5

  This formalizes the subset of Rust MIR that tRust uses for verification.
-/

namespace TRust

/-!
  ## Basic Type Aliases
-/
abbrev Local := Nat
abbrev BasicBlock := Nat
abbrev Location := Nat  -- Heap location

/-!
  ## MIR Type System
-/

-- Integer type tags
inductive IntTy where
  | i8 | i16 | i32 | i64 | isize
  | u8 | u16 | u32 | u64 | usize
  deriving DecidableEq, Repr, Inhabited

-- Mutability for references
inductive Mutability where
  | shared  -- &T (immutable borrow)
  | mutable -- &mut T (mutable borrow)
  deriving DecidableEq, Repr, Inhabited

-- MIR Types (simplified)
inductive MirTy where
  | bool
  | int (ty : IntTy)
  | unit
  | ref (m : Mutability) (pointee : MirTy)  -- &T or &mut T
  | box_ (inner : MirTy)                     -- Box<T>
  | rawPtr (m : Mutability) (pointee : MirTy) -- *const T or *mut T
  | array (elem : MirTy) (len : Nat)        -- [T; N]
  | tuple (elems : List MirTy)              -- (T1, T2, ...)
  | opaque (name : String)                  -- Opaque/abstract types
  deriving Repr, Inhabited

/-!
  ## Values
-/

-- Values in the MIR semantics
-- Extended with references, boxes, and aggregates
inductive Value where
  | bool (b : Bool)
  | int (ty : IntTy) (v : Int)
  | unit
  | fn_ (name : String)           -- Function value (simplified)
  | ref (loc : Location)            -- Reference value (points to heap location)
  | box_ (loc : Location)           -- Box value (owns heap location)
  | rawPtr (loc : Option Location)  -- Raw pointer (can be null)
  | array (elems : List Value)      -- Array value
  | tuple (elems : List Value)      -- Tuple value
  deriving Repr, Inhabited

/-!
  ## Memory Model
-/

-- Heap: maps locations to values
-- nextLoc tracks the next free location
structure Heap where
  mem : Location → Option Value
  nextLoc : Location

def Heap.empty : Heap :=
  { mem := fun _ => none, nextLoc := 0 }

def Heap.read (h : Heap) (loc : Location) : Option Value :=
  h.mem loc

def Heap.write (h : Heap) (loc : Location) (v : Value) : Heap :=
  { h with mem := fun l => if l = loc then some v else h.mem l }

def Heap.alloc (h : Heap) (v : Value) : Heap × Location :=
  let loc := h.nextLoc
  let h' := { mem := fun l => if l = loc then some v else h.mem l,
              nextLoc := loc + 1 }
  (h', loc)

def Heap.dealloc (h : Heap) (loc : Location) : Heap :=
  { h with mem := fun l => if l = loc then none else h.mem l }

/-!
  ## State
-/

-- State: locals + heap
structure State where
  alive : Local → Bool
  locals : Local → Option Value
  heap : Heap

def State.empty : State :=
  { alive := fun _ => false, locals := fun _ => none, heap := Heap.empty }

def State.isAlive (s : State) (l : Local) : Bool :=
  s.alive l

def State.readLocal (s : State) (l : Local) : Option Value :=
  if s.isAlive l then s.locals l else none

def State.writeLocal (s : State) (l : Local) (v : Value) : Option State :=
  if s.isAlive l then
    some { s with locals := fun l' => if l' = l then some v else s.locals l' }
  else
    none

def State.storageLive (s : State) (l : Local) : State :=
  { alive := fun l' => if l' = l then true else s.alive l',
    locals := s.locals,
    heap := s.heap }

def State.storageDead (s : State) (l : Local) : State :=
  { alive := fun l' => if l' = l then false else s.alive l',
    locals := fun l' => if l' = l then none else s.locals l',
    heap := s.heap }

-- Heap operations on state
def State.heapRead (s : State) (loc : Location) : Option Value :=
  s.heap.read loc

def State.heapWrite (s : State) (loc : Location) (v : Value) : State :=
  { s with heap := s.heap.write loc v }

def State.heapAlloc (s : State) (v : Value) : State × Location :=
  let (h', loc) := s.heap.alloc v
  ({ s with heap := h' }, loc)

def State.heapDealloc (s : State) (loc : Location) : State :=
  { s with heap := s.heap.dealloc loc }

/-
  LEMMA 1: Reading a dead local returns none
-/
@[simp]
theorem State.readLocal_dead (s : State) (l : Local) :
    (s.storageDead l).readLocal l = none := by
  simp [State.readLocal, State.storageDead, State.isAlive]

/-
  LEMMA 2: Writing to a live local succeeds
-/
theorem State.writeLocal_live (s : State) (l : Local) (v : Value) (h : s.isAlive l = true) :
    (s.writeLocal l v).isSome := by
  simp [State.writeLocal, h]

/-
  LEMMA 3: StorageLive makes a local alive
-/
@[simp]
theorem State.isAlive_storageLive (s : State) (l : Local) :
    (s.storageLive l).isAlive l = true := by
  simp [State.storageLive, State.isAlive]

/-!
  ## Places
-/

-- Projection elements for navigating into aggregates
inductive PlaceElem where
  | deref                    -- *place (dereference)
  | field (idx : Nat)        -- place.field
  | index (indexLocal : Local)    -- place[local]
  | constIndex (idx : Nat)   -- place[const]
  deriving Repr, Inhabited

-- Places (where values are stored)
-- A place is a base (local variable) followed by projections
inductive Place where
  | local (l : Local)
  | project (base : Place) (elem : PlaceElem)
  deriving Inhabited

-- Operands (sources of values)
inductive Operand where
  | const (v : Value)
  | copy (p : Place)    -- Copy value from place
  | move (p : Place)    -- Move value from place
  deriving Inhabited

-- Binary operations
inductive BinOp where
  | add | sub | mul | div | rem
  | eq | ne | lt | le | gt | ge  -- Comparison operators
  | bitAnd | bitOr | bitXor | shl | shr  -- Bitwise operators
  -- Checked arithmetic (returns (result, overflow) pair in Rvalue.CheckedBinOp)
  | addChecked | subChecked | mulChecked
  deriving DecidableEq, Repr, Inhabited

-- Unary operations
inductive UnOp where
  | neg  -- Arithmetic negation
  | not  -- Logical/bitwise not
  deriving DecidableEq, Repr, Inhabited

-- Bitwise operations on Int (abstract specification)
-- These model the behavior, concrete implementation uses native ops
opaque intBitAnd : Int → Int → Int
opaque intBitOr : Int → Int → Int
opaque intBitXor : Int → Int → Int
opaque intShl : Int → Nat → Int
opaque intShr : Int → Nat → Int
opaque intComplement : Int → Int

-- Borrow kind for reference creation
inductive BorrowKind where
  | shared   -- &T
  | mutable  -- &mut T
  | shallow  -- Shallow borrow (for two-phase borrows)
  deriving DecidableEq, Repr, Inhabited
/-!
  ## Integer Bounds and Overflow Detection
-/

-- Get the bit width of an integer type
def IntTy.bits : IntTy → Nat
  | .i8 | .u8 => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 => 32
  | .i64 | .u64 | .isize | .usize => 64

-- Is this a signed type?
def IntTy.isSigned : IntTy → Bool
  | .i8 | .i16 | .i32 | .i64 | .isize => true
  | .u8 | .u16 | .u32 | .u64 | .usize => false

-- Minimum value for an integer type
def IntTy.minVal (ty : IntTy) : Int :=
  if ty.isSigned then
    -(2 ^ (ty.bits - 1))
  else
    0

-- Maximum value for an integer type
def IntTy.maxVal (ty : IntTy) : Int :=
  if ty.isSigned then
    2 ^ (ty.bits - 1) - 1
  else
    2 ^ ty.bits - 1

-- Check if a value is in range for a type
def IntTy.inRange (ty : IntTy) (v : Int) : Bool :=
  ty.minVal ≤ v && v ≤ ty.maxVal

-- Checked addition: returns (result, overflowed)
def checkedAdd (ty : IntTy) (a b : Int) : Int × Bool :=
  let result := a + b
  (result, !ty.inRange result)

-- Checked subtraction: returns (result, overflowed)
def checkedSub (ty : IntTy) (a b : Int) : Int × Bool :=
  let result := a - b
  (result, !ty.inRange result)

-- Checked multiplication: returns (result, overflowed)
def checkedMul (ty : IntTy) (a b : Int) : Int × Bool :=
  let result := a * b
  (result, !ty.inRange result)

-- Rvalues (right-hand side of assignments)
inductive Rvalue where
  | use (op : Operand)
  | binOp (op : BinOp) (lhs rhs : Operand)
  | unOp (op : UnOp) (operand : Operand)
  | checkedBinOp (op : BinOp) (lhs rhs : Operand)  -- Returns (result, overflow) tuple
  | ref (bk : BorrowKind) (place : Place)   -- &place or &mut place
  | addressOf (mutbl : Mutability) (place : Place)  -- &raw const/mut place
  | aggregate (kind : AggregateKind) (ops : List Operand)
  | len (place : Place)                     -- array.len()
  | cast (op : Operand)                     -- Type cast (abstract)
  | repeat (op : Operand) (count : Nat)     -- [op; count]
  | discriminant (place : Place)            -- discriminant of enum
  deriving Inhabited

-- Aggregate kinds
inductive AggregateKind where
  | array
  | tuple
  | closure
  deriving Repr, Inhabited

-- MIR Statements
inductive MirStmt where
  | Assign (dst : Place) (src : Rvalue)
  | StorageLive (l : Local)
  | StorageDead (l : Local)
  | Nop
  deriving Inhabited
-- Assert condition (for assert terminator)
structure AssertMsg where
  cond : Operand
  expected : Bool
  target : BasicBlock
  cleanup : Option BasicBlock  -- Cleanup block for panics

-- MIR Terminators
inductive MirTerminator where
  | Return
  | Goto (bb : BasicBlock)
  | SwitchInt (discr : Operand) (targets : List (Int × BasicBlock)) (otherwise : BasicBlock)
  | Call (func : Operand) (args : List Operand) (dest : Place) (target : BasicBlock)
  | Assert (msg : AssertMsg)
  | Drop (place : Place) (target : BasicBlock) (unwind : Option BasicBlock)
  | Unreachable
  deriving Inhabited

-- Extended control flow for panic/unwind
inductive Control where
  | return_
  | goto (bb : BasicBlock)
  | panic             -- Assertion failed
  | unwind (bb : BasicBlock)  -- Unwinding to cleanup block
  deriving Repr, Inhabited
/-
  Basic Block structure
-/
structure BasicBlockData where
  stmts : List MirStmt
  terminator : MirTerminator
  deriving Inhabited

/-!
  ## Function Body Structure
-/

/-
  MIR function body containing all basic blocks
-/
structure MirBody where
  -- Number of local variables
  localCount : Nat
  -- Basic blocks (indexed by BasicBlock = Nat)
  blocks : List BasicBlockData
  -- Entry block (usually 0)
  entryBlock : BasicBlock
  deriving Inhabited

-- Get a basic block by index
def MirBody.getBlock (body : MirBody) (bb : BasicBlock) : Option BasicBlockData :=
  body.blocks[bb]?

-- Execution trace element
structure TraceStep where
  block : BasicBlock
  state : State
  control : Control

structure MirProgram where
  funs : String → Option MirBody

def MirProgram.getFun (p : MirProgram) (name : String) : Option MirBody :=
  p.funs name

end TRust
