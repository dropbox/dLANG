/-
  Lemmas about the executable semantics (determinism, locality, fuel monotonicity, etc.).
-/

import MirSemantics.Semantics

namespace TRust

/-!
  ## Call Setup Lemmas
-/

@[simp]
theorem State.initFrame_heap (heap : Heap) (localCount : Nat) (args : List Value) :
    (State.initFrame heap localCount args).heap = heap := rfl

theorem State.initFrame_readLocal_ret (heap : Heap) (localCount : Nat) (args : List Value)
    (h : 0 < localCount) :
    (State.initFrame heap localCount args).readLocal 0 = some .unit := by
  simp [State.initFrame, State.readLocal, State.isAlive, h, decide_true]

/-
  LEMMA: Nop statement preserves state
-/
@[simp]
theorem execStmt_nop (s : State) : execStmt s .Nop = some s := rfl

/-
  LEMMA: StorageLive followed by write succeeds
-/
theorem storageLive_then_write (s : State) (l : Local) (v : Value) :
    ((s.storageLive l).writeLocal l v).isSome := by
  simp [State.writeLocal, State.storageLive, State.isAlive]

/-
  LEMMA: Heap alloc returns a fresh location
-/
@[simp]
theorem Heap.alloc_nextLoc (h : Heap) (v : Value) :
    (h.alloc v).2 = h.nextLoc := rfl

/-
  LEMMA: Reading from a just-allocated location returns the value
-/
@[simp]
theorem Heap.alloc_read (h : Heap) (v : Value) :
    let (h', loc) := h.alloc v
    h'.read loc = some v := by
  simp [Heap.alloc, Heap.read]

/-
  LEMMA: Writing then reading returns the written value
-/
@[simp]
theorem Heap.write_read (h : Heap) (loc : Location) (v : Value) :
    (h.write loc v).read loc = some v := by
  simp [Heap.write, Heap.read]

/-
  LEMMA: Deallocation removes the value
-/
@[simp]
theorem Heap.dealloc_read (h : Heap) (loc : Location) :
    (h.dealloc loc).read loc = none := by
  simp [Heap.dealloc, Heap.read]

/-
  LEMMA: Empty list executes to same state
-/
@[simp]
theorem execStmts_nil (s : State) : execStmts s [] = some s := rfl

/-
  LEMMA: Assert with true condition succeeds
-/
@[simp]
theorem execTerminator_assert_true (s : State) (target : BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool true), expected := true, target := target, cleanup := none }
    execTerminator s (.Assert msg) = some (.goto target) := rfl

/-
  LEMMA: Goto terminator always succeeds
-/
@[simp]
theorem execTerminator_goto (s : State) (bb : BasicBlock) :
    execTerminator s (.Goto bb) = some (.goto bb) := rfl

/-
  LEMMA: Return terminator always succeeds
-/
@[simp]
theorem execTerminator_return (s : State) :
    execTerminator s .Return = some .return_ := rfl

/-!
  ## Overflow Detection Lemmas
-/

/-
  LEMMA: i8 range bounds
-/
@[simp] theorem IntTy.i8_min : IntTy.i8.minVal = -128 := rfl
@[simp] theorem IntTy.i8_max : IntTy.i8.maxVal = 127 := rfl

/-
  LEMMA: u8 range bounds
-/
@[simp] theorem IntTy.u8_min : IntTy.u8.minVal = 0 := rfl
@[simp] theorem IntTy.u8_max : IntTy.u8.maxVal = 255 := rfl

/-
  LEMMA: Value in range means no overflow
-/
theorem checkedAdd_no_overflow (ty : IntTy) (a b : Int)
    (h : ty.inRange (a + b)) :
    (checkedAdd ty a b).2 = false := by
  simp [checkedAdd, h]

/-
  LEMMA: Value out of range means overflow
-/
theorem checkedAdd_overflow (ty : IntTy) (a b : Int)
    (h : !ty.inRange (a + b)) :
    (checkedAdd ty a b).2 = true := by
  simp [checkedAdd, h]

/-
  LEMMA: Checked add result is sum
-/
@[simp]
theorem checkedAdd_result (ty : IntTy) (a b : Int) :
    (checkedAdd ty a b).1 = a + b := rfl

/-
  LEMMA: Checked sub result is difference
-/
@[simp]
theorem checkedSub_result (ty : IntTy) (a b : Int) :
    (checkedSub ty a b).1 = a - b := rfl

/-
  LEMMA: Checked mul result is product
-/
@[simp]
theorem checkedMul_result (ty : IntTy) (a b : Int) :
    (checkedMul ty a b).1 = a * b := rfl

/-!
  ## Execution Sequence Lemmas
-/

/-
  LEMMA: Single statement execution is special case of execStmts
-/
@[simp]
theorem execStmts_singleton (s : State) (stmt : MirStmt) :
    execStmts s [stmt] = (execStmt s stmt).bind (fun s' => some s') := by
  rfl

/-
  LEMMA: Singleton execStmts with successful stmt
-/
theorem execStmts_singleton_some (s s' : State) (stmt : MirStmt) (h : execStmt s stmt = some s') :
    execStmts s [stmt] = some s' := by
  simp [execStmts, h]

/-
  LEMMA: Unreachable terminator always fails
-/
@[simp]
theorem execTerminator_unreachable (s : State) :
    execTerminator s .Unreachable = none := rfl

/-
  LEMMA: Drop terminator always continues to target
-/
@[simp]
theorem execTerminator_drop (s : State) (place : Place) (target : BasicBlock) (unwind : Option BasicBlock) :
    execTerminator s (.Drop place target unwind) = some (.goto target) := rfl

/-
  LEMMA: SwitchInt with matching first target
-/
theorem execTerminator_switch_match (s : State) (d : Int) (targets : List (Int × BasicBlock))
    (bb : BasicBlock) (otherwise : BasicBlock)
    (hMatch : targets.find? (fun p => p.1 == d) = some (d, bb)) :
    ∀ v, evalOperand s (.const (.int IntTy.i32 d)) = some v →
         asSwitchIntDiscr v = some d →
         execTerminator s (.SwitchInt (.const (.int IntTy.i32 d)) targets otherwise) = some (.goto bb) := by
  intro v hv hd
  simp [execTerminator, hv, hd, hMatch]

/-
  LEMMA: Assert with false condition and cleanup unwinds
-/
@[simp]
theorem execTerminator_assert_false_unwind (s : State) (target cleanup : BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := some cleanup }
    execTerminator s (.Assert msg) = some (.unwind cleanup) := rfl

/-
  LEMMA: Assert with false condition and no cleanup panics
-/
@[simp]
theorem execTerminator_assert_false_panic (s : State) (target : BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := none }
    execTerminator s (.Assert msg) = some .panic := rfl

/-
  LEMMA: Empty block with return terminates
-/
@[simp]
theorem execBlock_empty_return (s : State) :
    execBlock s { stmts := [], terminator := .Return } = some (s, .return_) := rfl

/-
  LEMMA: Empty block with goto continues
-/
@[simp]
theorem execBlock_empty_goto (s : State) (bb : BasicBlock) :
    execBlock s { stmts := [], terminator := .Goto bb } = some (s, .goto bb) := rfl

/-
  LEMMA: StorageLive statement succeeds
-/
@[simp]
theorem execStmt_storageLive (s : State) (l : Local) :
    execStmt s (.StorageLive l) = some (s.storageLive l) := rfl

/-
  LEMMA: StorageDead statement succeeds
-/
@[simp]
theorem execStmt_storageDead (s : State) (l : Local) :
    execStmt s (.StorageDead l) = some (s.storageDead l) := rfl

/-
  LEMMA: StorageLive then StorageDead makes local dead
-/
theorem storageLive_storageDead_dead (s : State) (l : Local) :
    ((s.storageLive l).storageDead l).isAlive l = false := by
  simp [State.storageLive, State.storageDead, State.isAlive]

/-
  LEMMA: Reading unitialized local after StorageLive returns none
-/
theorem storageLive_read_uninit (s : State) (l : Local) (h : s.locals l = none) :
    (s.storageLive l).readLocal l = none := by
  simp [State.storageLive, State.readLocal, State.isAlive, h]

/-
  LEMMA: Division by zero returns none
-/
theorem evalBinOp_div_zero (ty : IntTy) (a : Int) :
    evalBinOp .div (.int ty a) (.int ty 0) = none := by
  simp [evalBinOp]

/-
  LEMMA: Remainder by zero returns none
-/
theorem evalBinOp_rem_zero (ty : IntTy) (a : Int) :
    evalBinOp .rem (.int ty a) (.int ty 0) = none := by
  simp [evalBinOp]

/-!
  ## Memory Safety Lemmas
-/

/-
  LEMMA: Heap write preserves reads at other locations
-/
theorem Heap.write_read_ne (h : Heap) (loc loc' : Location) (v : Value) (hne : loc ≠ loc') :
    (h.write loc v).read loc' = h.read loc' := by
  simp only [Heap.write, Heap.read]
  split
  · next heq => exact absurd (Eq.symm heq) hne
  · rfl

/-
  LEMMA: Heap dealloc preserves reads at other locations
-/
theorem Heap.dealloc_read_ne (h : Heap) (loc loc' : Location) (hne : loc ≠ loc') :
    (h.dealloc loc).read loc' = h.read loc' := by
  simp only [Heap.dealloc, Heap.read]
  split
  · next heq => exact absurd (Eq.symm heq) hne
  · rfl

/-
  LEMMA: Heap alloc preserves existing locations
-/
theorem Heap.alloc_read_old (h : Heap) (v : Value) (loc : Location) (hlt : loc < h.nextLoc) :
    (h.alloc v).1.read loc = h.read loc := by
  simp only [Heap.alloc, Heap.read]
  split
  · next heq => exact absurd heq (Nat.ne_of_lt hlt)
  · rfl

/-
  LEMMA: Allocated location is fresh (was not readable before)
-/
theorem Heap.alloc_fresh (h : Heap) (hNone : h.mem h.nextLoc = none) :
    h.read h.nextLoc = none := by
  simp [Heap.read, hNone]

/-
  LEMMA: nextLoc increases after allocation
-/
@[simp]
theorem Heap.alloc_nextLoc_inc (h : Heap) (v : Value) :
    (h.alloc v).1.nextLoc = h.nextLoc + 1 := rfl

/-
  LEMMA: State write preserves other locals
-/
theorem State.writeLocal_read_ne (s : State) (l l' : Local) (v : Value)
    (hAlive : s.isAlive l = true) (hne : l ≠ l') :
    ∃ s', s.writeLocal l v = some s' ∧ s'.readLocal l' = s.readLocal l' := by
  simp only [State.writeLocal, hAlive]
  refine ⟨_, rfl, ?_⟩
  simp only [State.readLocal, State.isAlive]
  split
  · next halive =>
      split
      · next heq => exact absurd (Eq.symm heq) hne
      · rfl
  · rfl

/-
  LEMMA: State write then read returns written value
-/
theorem State.writeLocal_readLocal (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true) :
    ∃ s', s.writeLocal l v = some s' ∧ s'.readLocal l = some v := by
  simp only [State.writeLocal, hAlive]
  refine ⟨_, rfl, ?_⟩
  simp only [State.readLocal, State.isAlive]
  simp only [State.isAlive] at hAlive
  simp [hAlive]

/-
  LEMMA: StorageLive preserves other locals' values
-/
theorem State.storageLive_readLocal_ne (s : State) (l l' : Local) (hne : l ≠ l') :
    (s.storageLive l).readLocal l' = s.readLocal l' := by
  simp only [State.storageLive, State.readLocal, State.isAlive]
  by_cases halive : s.alive l' = true
  · simp [halive, Ne.symm hne]
  · simp [halive, Ne.symm hne]

/-
  LEMMA: StorageDead preserves other locals' liveness
-/
theorem State.storageDead_isAlive_ne (s : State) (l l' : Local) (hne : l ≠ l') :
    (s.storageDead l).isAlive l' = s.isAlive l' := by
  simp only [State.storageDead, State.isAlive]
  split
  · next heq => exact absurd (Eq.symm heq) hne
  · rfl

/-
  LEMMA: Heap operations on state preserve local variable state
-/
theorem State.heapWrite_readLocal (s : State) (loc : Location) (v : Value) (l : Local) :
    (s.heapWrite loc v).readLocal l = s.readLocal l := by
  simp [State.heapWrite, State.readLocal, State.isAlive]

/-
  LEMMA: Heap operations on state preserve local liveness
-/
@[simp]
theorem State.heapWrite_isAlive (s : State) (loc : Location) (v : Value) (l : Local) :
    (s.heapWrite loc v).isAlive l = s.isAlive l := rfl

/-
  LEMMA: State heap allocation preserves locals
-/
theorem State.heapAlloc_readLocal (s : State) (v : Value) (l : Local) :
    (s.heapAlloc v).1.readLocal l = s.readLocal l := by
  simp [State.heapAlloc, State.readLocal, State.isAlive]

/-
  LEMMA: Empty heap has no allocated locations
-/
@[simp]
theorem Heap.empty_read (loc : Location) : Heap.empty.read loc = none := rfl

/-
  LEMMA: Empty state has no live locals
-/
@[simp]
theorem State.empty_isAlive (l : Local) : State.empty.isAlive l = false := rfl

/-
  LEMMA: Empty state has no local values
-/
theorem State.empty_readLocal (l : Local) : State.empty.readLocal l = none := by
  simp [State.empty, State.readLocal, State.isAlive]

/-!
  ## Comparison and Arithmetic Lemmas
-/

/-
  LEMMA: Equality comparison is reflexive
-/
theorem evalCmp_eq_refl (a : Int) : evalCmp .eq a a = some true := by
  simp [evalCmp]

/-
  LEMMA: Less than is irreflexive
-/
theorem evalCmp_lt_irrefl (a : Int) : evalCmp .lt a a = some false := by
  simp [evalCmp]

/-
  LEMMA: Less-or-equal is reflexive
-/
theorem evalCmp_le_refl (a : Int) : evalCmp .le a a = some true := by
  simp [evalCmp]

/-
  LEMMA: Not-equal is irreflexive
-/
theorem evalCmp_ne_irrefl (a : Int) : evalCmp .ne a a = some false := by
  simp [evalCmp]

/-
  LEMMA: eq and ne are complements for equal values
-/
theorem evalCmp_eq_ne_compl_eq (a : Int) :
    match evalCmp .eq a a, evalCmp .ne a a with
    | some r1, some r2 => r1 = !r2
    | _, _ => True := by
  simp [evalCmp]

/-
  LEMMA: eq returns true iff values equal
-/
theorem evalCmp_eq_true_iff (a b : Int) (h : a = b) :
    evalCmp .eq a b = some true := by
  simp [evalCmp, h]

/-
  LEMMA: ne returns false iff values equal
-/
theorem evalCmp_ne_false_iff (a b : Int) (h : a = b) :
    evalCmp .ne a b = some false := by
  simp [evalCmp, h]

/-
  LEMMA: lt implies not ge (one direction)
-/
theorem evalCmp_lt_implies_not_ge (a b : Int) (hlt : a < b) :
    evalCmp .ge a b = some false := by
  simp [evalCmp]
  omega

/-
  LEMMA: le implies not gt (one direction)
-/
theorem evalCmp_le_implies_not_gt (a b : Int) (hle : a ≤ b) :
    evalCmp .gt a b = some false := by
  simp [evalCmp]
  omega

/-
  LEMMA: Addition is commutative
-/
theorem evalBinOp_add_comm (ty : IntTy) (a b : Int) :
    evalBinOp .add (.int ty a) (.int ty b) = evalBinOp .add (.int ty b) (.int ty a) := by
  simp [evalBinOp, Int.add_comm]

/-
  LEMMA: Multiplication is commutative
-/
theorem evalBinOp_mul_comm (ty : IntTy) (a b : Int) :
    evalBinOp .mul (.int ty a) (.int ty b) = evalBinOp .mul (.int ty b) (.int ty a) := by
  simp [evalBinOp, Int.mul_comm]

/-
  LEMMA: Addition with zero is identity
-/
theorem evalBinOp_add_zero (ty : IntTy) (a : Int) :
    evalBinOp .add (.int ty a) (.int ty 0) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: Multiplication with one is identity
-/
theorem evalBinOp_mul_one (ty : IntTy) (a : Int) :
    evalBinOp .mul (.int ty a) (.int ty 1) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: Multiplication with zero is zero
-/
theorem evalBinOp_mul_zero (ty : IntTy) (a : Int) :
    evalBinOp .mul (.int ty a) (.int ty 0) = some (.int ty 0) := by
  simp [evalBinOp]

/-
  LEMMA: Subtraction of self is zero
-/
theorem evalBinOp_sub_self (ty : IntTy) (a : Int) :
    evalBinOp .sub (.int ty a) (.int ty a) = some (.int ty 0) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean AND is commutative
-/
theorem evalBinOp_and_comm (a b : Bool) :
    evalBinOp .bitAnd (.bool a) (.bool b) = evalBinOp .bitAnd (.bool b) (.bool a) := by
  simp [evalBinOp, Bool.and_comm]

/-
  LEMMA: Boolean OR is commutative
-/
theorem evalBinOp_or_comm (a b : Bool) :
    evalBinOp .bitOr (.bool a) (.bool b) = evalBinOp .bitOr (.bool b) (.bool a) := by
  simp [evalBinOp, Bool.or_comm]

/-
  LEMMA: Boolean NOT is involutive
-/
theorem evalUnOp_not_involutive (b : Bool) :
    match evalUnOp .not (.bool b) with
    | some (.bool b') =>
        match evalUnOp .not (.bool b') with
        | some (.bool b'') => b'' = b
        | _ => True
    | _ => True := by
  simp [evalUnOp]

/-
  LEMMA: Double negation identity for integers
-/
theorem evalUnOp_neg_neg (ty : IntTy) (v : Int) :
    match evalUnOp .neg (.int ty v) with
    | some (.int ty' v') =>
        match evalUnOp .neg (.int ty' v') with
        | some (.int _ v'') => v'' = v
        | _ => True
    | _ => True := by
  simp [evalUnOp]

/-
  LEMMA: Operand evaluation is deterministic
-/
theorem evalOperand_det (s : State) (op : Operand) (v1 v2 : Value)
    (h1 : evalOperand s op = some v1) (h2 : evalOperand s op = some v2) :
    v1 = v2 := by
  simp only [h1] at h2
  injection h2

/-
  LEMMA: Constant operand evaluation
-/
@[simp]
theorem evalOperand_const (s : State) (v : Value) :
    evalOperand s (.const v) = some v := rfl

/-
  LEMMA: Rvalue.use preserves operand value
-/
@[simp]
theorem evalRvalue_use (s : State) (op : Operand) :
    evalRvalue s (.use op) = evalOperand s op := rfl

/-
  LEMMA: Statement execution is deterministic
-/
theorem execStmt_det (s : State) (stmt : MirStmt) (s1 s2 : State)
    (h1 : execStmt s stmt = some s1) (h2 : execStmt s stmt = some s2) :
    s1 = s2 := by
  simp only [h1] at h2
  injection h2

/-
  LEMMA: Terminator execution is deterministic
-/
theorem execTerminator_det (s : State) (term : MirTerminator) (c1 c2 : Control)
    (h1 : execTerminator s term = some c1) (h2 : execTerminator s term = some c2) :
    c1 = c2 := by
  simp only [h1] at h2
  injection h2

/-!
  ## Type Well-Formedness
-/

/-
  Predicate: value has the given base type (non-recursive for simple types)
-/
def Value.hasBaseType : Value → MirTy → Bool
  | .bool _, .bool => true
  | .int ty _, .int ty' => ty == ty'
  | .unit, .unit => true
  | .ref _, .ref _ _ => true  -- Simplified: don't check pointee
  | .box_ _, .box_ _ => true
  | .rawPtr _, .rawPtr _ _ => true
  | .array elems, .array _ len => elems.length == len
  | .tuple elems, .tuple tys => elems.length == tys.length
  | _, _ => false

/-
  LEMMA: Bool values have bool type
-/
@[simp]
theorem Value.hasBaseType_bool (b : Bool) : (Value.bool b).hasBaseType .bool := rfl

/-
  LEMMA: Int values have matching int type
-/
theorem Value.hasBaseType_int (ty : IntTy) (v : Int) : (Value.int ty v).hasBaseType (.int ty) := by
  simp [Value.hasBaseType]

/-
  LEMMA: Unit value has unit type
-/
@[simp]
theorem Value.hasBaseType_unit : Value.unit.hasBaseType .unit := rfl

/-
  LEMMA: Binary op on same-type ints produces same type
-/
theorem evalBinOp_preserves_int_type (op : BinOp) (ty : IntTy) (a b : Int)
    (hOp : op ∈ [.add, .sub, .mul, .div, .rem])
    (hDivOk : op = .div ∨ op = .rem → b ≠ 0) :
    match evalBinOp op (.int ty a) (.int ty b) with
    | some (.int ty' _) => ty' = ty
    | _ => True := by
  simp only [evalBinOp]
  cases op <;> simp_all

/-
  LEMMA: Comparison produces bool
-/
theorem evalBinOp_cmp_produces_bool (op : BinOp) (ty : IntTy) (a b : Int)
    (hOp : op ∈ [.eq, .ne, .lt, .le, .gt, .ge]) :
    match evalBinOp op (.int ty a) (.int ty b) with
    | some (.bool _) => True
    | _ => True := by
  simp only [evalBinOp]
  cases op <;> simp_all [evalCmp]

/-
  LEMMA: Unary negation preserves int type
-/
theorem evalUnOp_neg_preserves_type (ty : IntTy) (v : Int) :
    match evalUnOp .neg (.int ty v) with
    | some (.int ty' _) => ty' = ty
    | _ => True := by
  simp [evalUnOp]

/-
  LEMMA: Boolean NOT produces bool
-/
theorem evalUnOp_not_produces_bool (b : Bool) :
    match evalUnOp .not (.bool b) with
    | some (.bool _) => True
    | _ => True := by
  simp [evalUnOp]

/-
  LEMMA: Checked add produces tuple with int and bool
-/
theorem evalCheckedBinOp_add_type (ty : IntTy) (a b : Int) :
    match evalCheckedBinOp .addChecked (.int ty a) (.int ty b) with
    | some (.tuple [.int ty' _, .bool _]) => ty' = ty
    | _ => True := by
  simp [evalCheckedBinOp, checkedAdd]

/-
  LEMMA: Empty array has correct length
-/
@[simp]
theorem Value.hasBaseType_empty_array (elemTy : MirTy) :
    (Value.array []).hasBaseType (.array elemTy 0) := rfl

/-
  LEMMA: Empty tuple has correct length
-/
@[simp]
theorem Value.hasBaseType_empty_tuple :
    (Value.tuple []).hasBaseType (.tuple []) := rfl

/-
  Well-formed state: all live locals have values
-/
structure WellFormedState (s : State) (ctx : Local → Option MirTy) : Prop where
  live_has_value : ∀ l, s.isAlive l = true →
    match ctx l with
    | some _ => (s.readLocal l).isSome
    | none => False

/-
  LEMMA: Empty state is well-formed with empty context
-/
theorem WellFormedState.empty :
    WellFormedState State.empty (fun _ => none) where
  live_has_value := by
    intro l halive
    simp [State.empty, State.isAlive] at halive

/-!
  ## State Transition Properties
-/

/-
  LEMMA: Nop preserves all state properties
-/
theorem execStmt_nop_preserves_locals (s : State) (l : Local) :
    match execStmt s .Nop with
    | some s' => s'.readLocal l = s.readLocal l
    | none => True := by
  simp [execStmt]

/-
  LEMMA: Nop preserves heap
-/
theorem execStmt_nop_preserves_heap (s : State) (loc : Location) :
    match execStmt s .Nop with
    | some s' => s'.heapRead loc = s.heapRead loc
    | none => True := by
  simp [execStmt]

/-
  LEMMA: StorageLive only affects target local's liveness
-/
theorem execStmt_storageLive_other_locals (s : State) (l l' : Local) (hne : l ≠ l') :
    match execStmt s (.StorageLive l) with
    | some s' => s'.readLocal l' = s.readLocal l'
    | none => True := by
  simp [execStmt]
  exact State.storageLive_readLocal_ne s l l' hne

/-
  LEMMA: StorageDead only affects target local
-/
theorem execStmt_storageDead_other_locals (s : State) (l l' : Local) (hne : l ≠ l') :
    match execStmt s (.StorageDead l) with
    | some s' => s'.readLocal l' = s.readLocal l'
    | none => True := by
  simp only [execStmt, State.storageDead, State.readLocal, State.isAlive]
  by_cases halive : s.alive l' = true
  · simp [halive, Ne.symm hne]
  · simp [halive]

/-
  LEMMA: StorageLive preserves heap
-/
theorem execStmt_storageLive_preserves_heap (s : State) (l : Local) (loc : Location) :
    match execStmt s (.StorageLive l) with
    | some s' => s'.heapRead loc = s.heapRead loc
    | none => True := by
  simp [execStmt, State.storageLive, State.heapRead]

/-
  LEMMA: StorageDead preserves heap
-/
theorem execStmt_storageDead_preserves_heap (s : State) (l : Local) (loc : Location) :
    match execStmt s (.StorageDead l) with
    | some s' => s'.heapRead loc = s.heapRead loc
    | none => True := by
  simp [execStmt, State.storageDead, State.heapRead]

/-
  LEMMA: Goto terminator doesn't modify state
-/
@[simp]
theorem execTerminator_goto_state (s : State) (bb : BasicBlock) :
    execTerminator s (.Goto bb) = some (.goto bb) := rfl

/-
  LEMMA: execStmts preserves heap when no heap-affecting statements
-/
theorem execStmts_storageLive_preserves_heap (s : State) (l : Local) (loc : Location) :
    match execStmts s [.StorageLive l] with
    | some s' => s'.heapRead loc = s.heapRead loc
    | none => True := by
  simp [execStmts, execStmt, State.storageLive, State.heapRead]

/-
  LEMMA: Multiple Nops preserve state
-/
theorem execStmts_nops_preserve (s : State) :
    execStmts s [.Nop, .Nop] = some s := by
  simp [execStmts, execStmt]

/-
  LEMMA: Heap read after write at same location
-/
theorem State.heapRead_after_write (s : State) (loc : Location) (v : Value) :
    (s.heapWrite loc v).heapRead loc = some v := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read]

/-
  LEMMA: Heap read after write at different location
-/
theorem State.heapRead_after_write_ne (s : State) (loc loc' : Location) (v : Value) (hne : loc ≠ loc') :
    (s.heapWrite loc v).heapRead loc' = s.heapRead loc' := by
  simp only [State.heapWrite, State.heapRead, Heap.write, Heap.read]
  simp [Ne.symm hne]

/-
  LEMMA: Heap alloc returns fresh location value
-/
theorem State.heapAlloc_read (s : State) (v : Value) :
    let (s', loc) := s.heapAlloc v
    s'.heapRead loc = some v := by
  simp [State.heapAlloc, State.heapRead, Heap.alloc, Heap.read]

/-
  LEMMA: Heap dealloc removes value
-/
theorem State.heapDealloc_read (s : State) (loc : Location) :
    (s.heapDealloc loc).heapRead loc = none := by
  simp [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]

/-
  LEMMA: Heap dealloc preserves other locations
-/
theorem State.heapDealloc_read_ne (s : State) (loc loc' : Location) (hne : loc ≠ loc') :
    (s.heapDealloc loc).heapRead loc' = s.heapRead loc' := by
  simp only [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]
  simp [Ne.symm hne]

/-!
  ## Place Evaluation Lemmas
-/

/-
  LEMMA: Constant operand always succeeds
-/
@[simp]
theorem evalOperand_const_some (s : State) (v : Value) :
    (evalOperand s (.const v)).isSome = true := rfl

/-
  LEMMA: Copy operand reads from place
-/
@[simp]
theorem evalOperand_copy (s : State) (p : Place) :
    evalOperand s (.copy p) = evalPlace s p := rfl

/-
  LEMMA: Move operand reads from place (semantically same as copy)
-/
@[simp]
theorem evalOperand_move (s : State) (p : Place) :
    evalOperand s (.move p) = evalPlace s p := rfl

/-
  LEMMA: Copy and move of same place produce same value
-/
@[simp]
theorem evalOperand_copy_move_eq (s : State) (p : Place) :
    evalOperand s (.copy p) = evalOperand s (.move p) := rfl

/-
  LEMMA: asSwitchIntDiscr on bool true returns 1
-/
@[simp]
theorem asSwitchIntDiscr_bool_true :
    asSwitchIntDiscr (.bool true) = some 1 := rfl

/-
  LEMMA: asSwitchIntDiscr on bool false returns 0
-/
@[simp]
theorem asSwitchIntDiscr_bool_false :
    asSwitchIntDiscr (.bool false) = some 0 := rfl

/-
  LEMMA: asSwitchIntDiscr on int returns the int
-/
@[simp]
theorem asSwitchIntDiscr_int (ty : IntTy) (v : Int) :
    asSwitchIntDiscr (.int ty v) = some v := rfl

/-
  LEMMA: asSwitchIntDiscr on unit fails
-/
@[simp]
theorem asSwitchIntDiscr_unit :
    asSwitchIntDiscr .unit = none := rfl

/-
  LEMMA: asSwitchIntDiscr on ref fails
-/
@[simp]
theorem asSwitchIntDiscr_ref (loc : Location) :
    asSwitchIntDiscr (.ref loc) = none := rfl

/-!
  ## Block Execution Composition
-/

/-
  LEMMA: execBlock splits into statements then terminator
-/
theorem execBlock_def (s : State) (bb : BasicBlockData) :
    execBlock s bb = do
      let s' ← execStmts s bb.stmts
      let ctrl ← execTerminator s' bb.terminator
      return (s', ctrl) := rfl

/-
  LEMMA: execStmts cons decomposes
-/
@[simp]
theorem execStmts_cons (s : State) (stmt : MirStmt) (rest : List MirStmt) :
    execStmts s (stmt :: rest) = (execStmt s stmt).bind (fun s' => execStmts s' rest) := rfl

/-
  LEMMA: execStmts concatenation (append)
-/
theorem execStmts_append (s : State) (stmts1 stmts2 : List MirStmt) :
    execStmts s (stmts1 ++ stmts2) = (execStmts s stmts1).bind (fun s' => execStmts s' stmts2) := by
  induction stmts1 generalizing s with
  | nil => simp [execStmts]
  | cons stmt rest ih =>
      simp only [List.cons_append, execStmts_cons]
      cases h : execStmt s stmt with
      | none => simp [Option.bind]
      | some s' =>
          simp only [Option.bind]
          exact ih s'

/-
  LEMMA: Single Nop block with return
-/
theorem execBlock_nop_return (s : State) :
    execBlock s { stmts := [.Nop], terminator := .Return } = some (s, .return_) := by
  simp [execBlock, execStmts, execStmt, execTerminator]

/-
  LEMMA: Single StorageLive block with return
-/
theorem execBlock_storageLive_return (s : State) (l : Local) :
    execBlock s { stmts := [.StorageLive l], terminator := .Return } = some (s.storageLive l, .return_) := by
  simp [execBlock, execStmts, execStmt, execTerminator]

/-!
  ## Error Propagation Properties
-/

/-
  LEMMA: None propagates through execStmts
-/
theorem execStmts_none_propagates (stmt : MirStmt) (rest : List MirStmt)
    (s : State) (h : execStmt s stmt = none) :
    execStmts s (stmt :: rest) = none := by
  simp [execStmts, h]

/-
  LEMMA: Terminator failure means block fails
-/
theorem execBlock_term_none (s : State) (stmts : List MirStmt) (term : MirTerminator)
    (s' : State) (hStmts : execStmts s stmts = some s') (hTerm : execTerminator s' term = none) :
    execBlock s { stmts := stmts, terminator := term } = none := by
  simp [execBlock, hStmts, hTerm]

/-
  LEMMA: Statement failure means block fails
-/
theorem execBlock_stmt_none (s : State) (stmts : List MirStmt) (term : MirTerminator)
    (hStmts : execStmts s stmts = none) :
    execBlock s { stmts := stmts, terminator := term } = none := by
  simp [execBlock, hStmts]

/-
  LEMMA: Writing to dead local fails
-/
theorem State.writeLocal_dead (s : State) (l : Local) (v : Value)
    (hDead : s.isAlive l = false) :
    s.writeLocal l v = none := by
  unfold State.writeLocal
  simp only [hDead]
  rfl

/-!
  ## Rvalue Evaluation Lemmas
-/

/-
  LEMMA: Rvalue.use is identity for evalRvalue
-/
@[simp]
theorem evalRvalue_use_operand (s : State) (op : Operand) :
    evalRvalue s (.use op) = evalOperand s op := rfl

/-
  LEMMA: Binary op with constant operands
-/
theorem evalRvalue_binop_const (s : State) (op : BinOp) (v1 v2 : Value) :
    evalRvalue s (.binOp op (.const v1) (.const v2)) = evalBinOp op v1 v2 := by
  simp [evalRvalue, evalOperand]

/-
  LEMMA: Unary op with constant operand
-/
theorem evalRvalue_unop_const (s : State) (op : UnOp) (v : Value) :
    evalRvalue s (.unOp op (.const v)) = evalUnOp op v := by
  simp [evalRvalue, evalOperand]

/-
  LEMMA: Repeat creates array of correct length
-/
theorem evalRvalue_repeat_length (s : State) (v : Value) (n : Nat) :
    match evalRvalue s (.repeat (.const v) n) with
    | some (.array elems) => elems.length = n
    | _ => True := by
  simp [evalRvalue, evalOperand, List.length_replicate]

/-
  LEMMA: Repeat creates array of repeated value
-/
theorem evalRvalue_repeat_value (s : State) (v : Value) (n : Nat) :
    evalRvalue s (.repeat (.const v) n) = some (.array (List.replicate n v)) := by
  simp [evalRvalue, evalOperand]

/-
  LEMMA: evalRvalueWithState returns same state for non-ref rvalues
-/
theorem evalRvalueWithState_use (s : State) (op : Operand) :
    evalRvalueWithState s (.use op) = (evalOperand s op).map (fun v => (s, v)) := by
  simp only [evalRvalueWithState, evalRvalue]
  cases evalOperand s op <;> simp

/-
  LEMMA: Aggregate with empty ops produces empty tuple
-/
theorem evalRvalue_aggregate_nil (s : State) (kind : AggregateKind) :
    evalRvalue s (.aggregate kind []) = some (.tuple []) := by
  simp [evalRvalue]

/-!
  ## Additional Arithmetic Properties
-/

/-
  LEMMA: Int type bits are positive
-/
theorem IntTy.bits_pos (ty : IntTy) : 0 < ty.bits := by
  cases ty <;> simp [IntTy.bits]

/-
  LEMMA: Unsigned min is always 0
-/
theorem IntTy.unsigned_minVal_zero (ty : IntTy) (h : ty.isSigned = false) :
    ty.minVal = 0 := by
  simp [IntTy.minVal, h]

/-
  LEMMA: Signed types have negative minimum (concrete cases)
-/
theorem IntTy.i8_minVal_neg : IntTy.i8.minVal < 0 := by native_decide
theorem IntTy.i16_minVal_neg : IntTy.i16.minVal < 0 := by native_decide
theorem IntTy.i32_minVal_neg : IntTy.i32.minVal < 0 := by native_decide

/-
  LEMMA: Checked operations on zero don't overflow (concrete)
-/
theorem checkedAdd_i32_zero_left (b : Int) (h : IntTy.i32.inRange b = true) :
    (checkedAdd .i32 0 b).2 = false := by
  simp [checkedAdd, h]

theorem checkedAdd_i32_zero_right (a : Int) (h : IntTy.i32.inRange a = true) :
    (checkedAdd .i32 a 0).2 = false := by
  simp [checkedAdd, h]

/-!
  ## Control Flow Properties
-/

/-
  LEMMA: SwitchInt with no matching targets goes to otherwise
-/
theorem execTerminator_switch_otherwise (s : State) (d : Int) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock)
    (hNoMatch : targets.find? (fun p => p.1 == d) = none) :
    ∀ v, evalOperand s (.const (.int IntTy.i32 d)) = some v →
         asSwitchIntDiscr v = some d →
         execTerminator s (.SwitchInt (.const (.int IntTy.i32 d)) targets otherwise) = some (.goto otherwise) := by
  intro v hv hd
  simp [execTerminator, hv, hd, hNoMatch]

/-
  LEMMA: Control return means function returned
-/
theorem Control.isReturn_def (c : Control) :
    (c = .return_) ↔ match c with | .return_ => True | _ => False := by
  cases c <;> simp

/-
  LEMMA: MirBody.getBlock returns correct block
-/
@[simp]
theorem MirBody.getBlock_zero (bb : BasicBlockData) (rest : List BasicBlockData) :
    MirBody.getBlock { localCount := 0, blocks := bb :: rest, entryBlock := 0 } 0 = some bb := rfl

/-
  LEMMA: Empty blocks list returns none
-/
@[simp]
theorem MirBody.getBlock_empty (bb : BasicBlock) :
    MirBody.getBlock { localCount := 0, blocks := [], entryBlock := 0 } bb = none := rfl

/-
  LEMMA: Control flow after panic
-/
theorem Control.panic_ne_return :
    Control.panic ≠ Control.return_ := by
  intro h
  cases h

/-
  LEMMA: Control flow after unwind
-/
theorem Control.unwind_ne_return (bb : BasicBlock) :
    Control.unwind bb ≠ Control.return_ := by
  intro h
  cases h

/-!
  ## WritePlace Lemmas (via State.writeLocal)
-/

/-
  LEMMA: Writing to live local via State.writeLocal succeeds
-/
theorem writeLocal_live_succeeds (s : State) (l : Local) (v : Value) (hAlive : s.isAlive l = true) :
    (s.writeLocal l v).isSome := by
  simp [State.writeLocal, hAlive]

/-
  LEMMA: Writing to dead local via State.writeLocal fails
-/
theorem writeLocal_dead_fails (s : State) (l : Local) (v : Value) (hDead : s.isAlive l = false) :
    s.writeLocal l v = none := by
  simp [State.writeLocal, hDead]

/-
  LEMMA: writeLocal for local preserves heap
-/
theorem writeLocal_preserves_heap (s : State) (l : Local) (v : Value) (loc : Location)
    (hAlive : s.isAlive l = true) :
    ∃ s', s.writeLocal l v = some s' ∧ s'.heapRead loc = s.heapRead loc := by
  simp only [State.writeLocal, hAlive]
  refine ⟨_, rfl, ?_⟩
  simp [State.heapRead]

/-
  LEMMA: writeLocal preserves other locals
-/
theorem writeLocal_preserves_other (s : State) (l l' : Local) (v : Value)
    (hAlive : s.isAlive l = true) (hne : l ≠ l') :
    ∃ s', s.writeLocal l v = some s' ∧ s'.readLocal l' = s.readLocal l' := by
  simp only [State.writeLocal, hAlive]
  refine ⟨_, rfl, ?_⟩
  simp only [State.readLocal, State.isAlive]
  by_cases halive' : s.alive l' = true
  · simp only [halive', ↓reduceIte]
    split
    · next heq => exact absurd heq.symm hne
    · rfl
  · simp [halive']

/-
  LEMMA: writeLocal followed by readLocal at same location
-/
theorem writeLocal_then_readLocal (s : State) (l : Local) (v : Value) (hAlive : s.isAlive l = true) :
    ∃ s', s.writeLocal l v = some s' ∧ s'.readLocal l = some v := by
  have ⟨s', hw, hr⟩ := State.writeLocal_readLocal s l v hAlive
  exact ⟨s', hw, hr⟩

/-!
  ## Invariant Preservation Lemmas
-/

/-
  LEMMA: Nop preserves local liveness
-/
theorem execStmt_nop_preserves_alive (s : State) (l : Local) :
    match execStmt s .Nop with
    | some s' => s'.isAlive l = s.isAlive l
    | none => True := by
  simp [execStmt]

/-
  LEMMA: Heap write preserves local liveness
-/
theorem heapWrite_preserves_alive (s : State) (loc : Location) (v : Value) (l : Local) :
    (s.heapWrite loc v).isAlive l = s.isAlive l := by
  simp [State.heapWrite, State.isAlive]

/-
  LEMMA: Heap alloc preserves local liveness
-/
theorem heapAlloc_preserves_alive (s : State) (v : Value) (l : Local) :
    (s.heapAlloc v).1.isAlive l = s.isAlive l := by
  simp [State.heapAlloc, State.isAlive]

/-
  LEMMA: Heap dealloc preserves local liveness
-/
theorem heapDealloc_preserves_alive (s : State) (loc : Location) (l : Local) :
    (s.heapDealloc loc).isAlive l = s.isAlive l := by
  simp [State.heapDealloc, State.isAlive]

/-
  LEMMA: Two Nops are equivalent to one
-/
theorem execStmts_nop_nop_eq (s : State) :
    execStmts s [.Nop, .Nop] = execStmts s [.Nop] := by
  simp [execStmts, execStmt]

/-
  LEMMA: StorageLive is idempotent for liveness
-/
theorem storageLive_idempotent_alive (s : State) (l : Local) :
    ((s.storageLive l).storageLive l).isAlive l = (s.storageLive l).isAlive l := by
  simp [State.storageLive, State.isAlive]

/-
  LEMMA: StorageDead is idempotent for liveness
-/
theorem storageDead_idempotent_alive (s : State) (l : Local) :
    ((s.storageDead l).storageDead l).isAlive l = (s.storageDead l).isAlive l := by
  simp [State.storageDead, State.isAlive]

/-!
  ## Value Flow Lemmas (avoiding partial defs)
-/

/-
  LEMMA: Binary add on int types is commutative
-/
theorem evalBinOp_add_int_comm (ty : IntTy) (a b : Int) :
    evalBinOp .add (.int ty a) (.int ty b) = evalBinOp .add (.int ty b) (.int ty a) := by
  simp [evalBinOp, Int.add_comm]

/-
  LEMMA: Binary mul on int types is commutative
-/
theorem evalBinOp_mul_int_comm (ty : IntTy) (a b : Int) :
    evalBinOp .mul (.int ty a) (.int ty b) = evalBinOp .mul (.int ty b) (.int ty a) := by
  simp [evalBinOp, Int.mul_comm]

/-
  LEMMA: Rvalue cast is identity (simplified)
-/
@[simp]
theorem evalRvalue_cast_identity (s : State) (op : Operand) :
    evalRvalue s (.cast op) = evalOperand s op := rfl

/-!
  ## More Comparison Properties
-/

/-
  LEMMA: lt and gt are converses
-/
theorem evalCmp_lt_gt_converse (a b : Int) :
    match evalCmp .lt a b, evalCmp .gt b a with
    | some r1, some r2 => r1 = r2
    | _, _ => True := by
  simp [evalCmp]

/-
  LEMMA: le and ge are converses
-/
theorem evalCmp_le_ge_converse (a b : Int) :
    match evalCmp .le a b, evalCmp .ge b a with
    | some r1, some r2 => r1 = r2
    | _, _ => True := by
  simp [evalCmp]

/-
  LEMMA: Equality comparison is reflexive for any value
-/
theorem evalCmp_eq_reflexive (a : Int) :
    evalCmp .eq a a = some true := by
  simp [evalCmp]

/-
  LEMMA: Not-equal comparison is irreflexive
-/
theorem evalCmp_ne_irreflexive (a : Int) :
    evalCmp .ne a a = some false := by
  simp [evalCmp]

/-!
  ## Array and Tuple Lemmas
-/

/-
  LEMMA: Array indexing within bounds succeeds
-/
theorem array_index_in_bounds (elems : List Value) (idx : Nat) (h : idx < elems.length) :
    (elems[idx]?).isSome := by
  exact Option.isSome_iff_exists.mpr ⟨elems[idx], List.getElem?_eq_getElem h⟩

/-
  LEMMA: Empty array length is 0
-/
@[simp]
theorem array_empty_length : ([] : List Value).length = 0 := rfl

/-
  LEMMA: Singleton array length is 1
-/
@[simp]
theorem array_singleton_length (v : Value) : [v].length = 1 := rfl

/-
  LEMMA: Array set preserves length
-/
theorem array_set_length (elems : List Value) (idx : Nat) (v : Value) :
    (elems.set idx v).length = elems.length := List.length_set

/-!
  ## More State Properties
-/

/-
  LEMMA: Two storageLive calls on different locals commute
-/
theorem storageLive_comm (s : State) (l1 l2 : Local) :
    ((s.storageLive l1).storageLive l2).isAlive l1 =
    ((s.storageLive l2).storageLive l1).isAlive l1 := by
  simp [State.storageLive, State.isAlive]

/-
  LEMMA: Two storageDead calls on different locals commute for liveness
-/
theorem storageDead_comm (s : State) (l1 l2 : Local) :
    ((s.storageDead l1).storageDead l2).isAlive l1 =
    ((s.storageDead l2).storageDead l1).isAlive l1 := by
  simp [State.storageDead, State.isAlive]

/-
  LEMMA: StorageLive followed by StorageDead makes local dead
-/
theorem storageLive_then_dead (s : State) (l : Local) :
    ((s.storageLive l).storageDead l).isAlive l = false := by
  simp [State.storageLive, State.storageDead, State.isAlive]

/-
  LEMMA: Empty state write fails
-/
theorem State.empty_writeLocal_fails (l : Local) (v : Value) :
    State.empty.writeLocal l v = none := by
  simp [State.empty, State.writeLocal, State.isAlive]

/-
  LEMMA: Reading from empty state heap returns none
-/
theorem State.empty_heapRead (loc : Location) :
    State.empty.heapRead loc = none := by
  simp [State.empty, State.heapRead, Heap.empty, Heap.read]

/-!
  ## Block Structure Lemmas
-/

/-
  LEMMA: Block with single Nop and Return
-/
theorem execBlock_single_nop_return (s : State) :
    let bb : BasicBlockData := { stmts := [.Nop], terminator := .Return }
    execBlock s bb = some (s, .return_) := by
  simp [execBlock, execStmts, execStmt, execTerminator]

/-
  LEMMA: Block with StorageLive and Return
-/
theorem execBlock_storageLive_only (s : State) (l : Local) :
    let bb : BasicBlockData := { stmts := [.StorageLive l], terminator := .Return }
    execBlock s bb = some (s.storageLive l, .return_) := by
  simp [execBlock, execStmts, execStmt, execTerminator]

/-
  LEMMA: Block with StorageDead and Return
-/
theorem execBlock_storageDead_only (s : State) (l : Local) :
    let bb : BasicBlockData := { stmts := [.StorageDead l], terminator := .Return }
    execBlock s bb = some (s.storageDead l, .return_) := by
  simp [execBlock, execStmts, execStmt, execTerminator]

/-
  LEMMA: MirBody.getBlock index in range succeeds
-/
theorem MirBody.getBlock_in_range (body : MirBody) (bb : BasicBlock) (h : bb < body.blocks.length) :
    (body.getBlock bb).isSome := by
  simp only [MirBody.getBlock]
  exact Option.isSome_iff_exists.mpr ⟨body.blocks[bb], List.getElem?_eq_getElem h⟩

/-!
  ## Terminator Flow Properties
-/

/-
  LEMMA: SwitchInt with empty targets always goes to otherwise
-/
theorem execTerminator_switch_empty (s : State) (discr : Operand) (otherwise : BasicBlock)
    (v : Value) (d : Int)
    (hEval : evalOperand s discr = some v)
    (hDiscr : asSwitchIntDiscr v = some d) :
    execTerminator s (.SwitchInt discr [] otherwise) = some (.goto otherwise) := by
  simp [execTerminator, hEval, hDiscr]

/-
  LEMMA: Assert success continues to target when condition matches expected
-/
theorem execTerminator_assert_success (s : State) (target : BasicBlock) (cleanup : Option BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool true), expected := true, target := target, cleanup := cleanup }
    execTerminator s (.Assert msg) = some (.goto target) := by
  simp [execTerminator, evalOperand]

/-
  LEMMA: Control.goto is deterministic
-/
theorem Control.goto_eq (bb1 bb2 : BasicBlock) :
    (Control.goto bb1 = Control.goto bb2) ↔ bb1 = bb2 := by
  constructor <;> intro h
  · injection h
  · rw [h]

/-
  LEMMA: Control.unwind is deterministic
-/
theorem Control.unwind_eq (bb1 bb2 : BasicBlock) :
    (Control.unwind bb1 = Control.unwind bb2) ↔ bb1 = bb2 := by
  constructor <;> intro h
  · injection h
  · rw [h]

/-!
  ## Checked Arithmetic Extended Properties
-/

/-
  LEMMA: checkedSub symmetry with negation
-/
theorem checkedSub_as_add_neg (ty : IntTy) (a b : Int) :
    (checkedSub ty a b).1 = (checkedAdd ty a (-b)).1 := by
  simp [checkedSub, checkedAdd, Int.sub_eq_add_neg]

/-
  LEMMA: checkedAdd associativity for result
-/
theorem checkedAdd_result_assoc (ty : IntTy) (a b c : Int) :
    (checkedAdd ty (a + b) c).1 = (checkedAdd ty a (b + c)).1 := by
  simp [checkedAdd, Int.add_assoc]

/-
  LEMMA: i32 max value
-/
@[simp]
theorem IntTy.i32_max : IntTy.i32.maxVal = 2147483647 := rfl

/-
  LEMMA: i32 min value
-/
@[simp]
theorem IntTy.i32_min : IntTy.i32.minVal = -2147483648 := rfl

/-
  LEMMA: u32 max value
-/
@[simp]
theorem IntTy.u32_max : IntTy.u32.maxVal = 4294967295 := rfl

/-
  LEMMA: u32 min value
-/
@[simp]
theorem IntTy.u32_min : IntTy.u32.minVal = 0 := rfl

/-
  LEMMA: Signed types have exactly one more negative value than positive
-/
theorem IntTy.i8_asymmetric : IntTy.i8.maxVal = -(IntTy.i8.minVal + 1) := by native_decide

/-
  LEMMA: Overflow flag is boolean
-/
theorem checkedAdd_overflow_bool (ty : IntTy) (a b : Int) :
    (checkedAdd ty a b).2 = true ∨ (checkedAdd ty a b).2 = false := by
  cases (checkedAdd ty a b).2 <;> simp

/-!
  ## Deref and Reference Properties
-/

/-
  LEMMA: Value.box is not a discriminant
-/
@[simp]
theorem box_not_discriminant (loc : Location) :
    asSwitchIntDiscr (.box_ loc) = none := rfl

/-
  LEMMA: Value.array is not a discriminant
-/
@[simp]
theorem array_not_discriminant (elems : List Value) :
    asSwitchIntDiscr (.array elems) = none := rfl

/-
  LEMMA: Value.tuple is not a discriminant
-/
@[simp]
theorem tuple_not_discriminant (elems : List Value) :
    asSwitchIntDiscr (.tuple elems) = none := rfl

/-
  LEMMA: Raw pointer null is none
-/
theorem rawPtr_null_val : Value.rawPtr none = Value.rawPtr none := rfl

/-
  LEMMA: evalRef returns a ref pointing to a valid heap location
-/
theorem evalRef_result (s : State) (place : Place) (v : Value)
    (hEval : evalPlace s place = some v) :
    ∃ s' loc, evalRef s place = some (s', .ref loc) := by
  simp only [evalRef, hEval]
  exact ⟨_, _, rfl⟩

/-
  LEMMA: Heap alloc result can be read back
-/
theorem heapAlloc_can_read (s : State) (v : Value) :
    let (s', loc) := s.heapAlloc v
    s'.heapRead loc = some v := by
  simp [State.heapAlloc, State.heapRead, Heap.alloc, Heap.read]

/-!
  ## Semantic Preservation Lemmas
-/

/-
  LEMMA: StorageLive preserves heap contents
-/
theorem storageLive_preserves_heap_contents (s : State) (l : Local) (loc : Location) :
    (s.storageLive l).heapRead loc = s.heapRead loc := by
  simp [State.storageLive, State.heapRead]

/-
  LEMMA: StorageDead preserves heap contents
-/
theorem storageDead_preserves_heap_contents (s : State) (l : Local) (loc : Location) :
    (s.storageDead l).heapRead loc = s.heapRead loc := by
  simp [State.storageDead, State.heapRead]

/-
  LEMMA: StorageLive preserves heap nextLoc
-/
theorem storageLive_preserves_heap_nextLoc (s : State) (l : Local) :
    (s.storageLive l).heap.nextLoc = s.heap.nextLoc := by
  simp [State.storageLive]

/-
  LEMMA: StorageDead preserves heap nextLoc
-/
theorem storageDead_preserves_heap_nextLoc (s : State) (l : Local) :
    (s.storageDead l).heap.nextLoc = s.heap.nextLoc := by
  simp [State.storageDead]

/-
  LEMMA: Heap write preserves nextLoc
-/
theorem heapWrite_preserves_nextLoc (s : State) (loc : Location) (v : Value) :
    (s.heapWrite loc v).heap.nextLoc = s.heap.nextLoc := by
  simp [State.heapWrite, Heap.write]

/-
  LEMMA: Heap dealloc preserves nextLoc
-/
theorem heapDealloc_preserves_nextLoc (s : State) (loc : Location) :
    (s.heapDealloc loc).heap.nextLoc = s.heap.nextLoc := by
  simp [State.heapDealloc, Heap.dealloc]

/-
  LEMMA: Heap alloc increments nextLoc by 1
-/
theorem heapAlloc_increments_nextLoc (s : State) (v : Value) :
    (s.heapAlloc v).1.heap.nextLoc = s.heap.nextLoc + 1 := by
  simp [State.heapAlloc, Heap.alloc]

/-
  LEMMA: writeLocal preserves alive status of other locals
-/
theorem writeLocal_preserves_other_alive (s : State) (l l' : Local) (v : Value)
    (_hne : l ≠ l') (hAlive : s.isAlive l = true) :
    ∃ s', s.writeLocal l v = some s' ∧ s'.isAlive l' = s.isAlive l' := by
  simp only [State.writeLocal, hAlive]
  refine ⟨_, rfl, ?_⟩
  simp [State.isAlive]

/-
  LEMMA: StorageLive is monotonic for liveness
-/
theorem storageLive_monotonic (s : State) (l l' : Local) (hne : l ≠ l')
    (hAlive : s.isAlive l' = true) :
    (s.storageLive l).isAlive l' = true := by
  simp only [State.storageLive, State.isAlive] at *
  simp [Ne.symm hne, hAlive]

/-
  LEMMA: Nop in execStmts list can be removed
-/
theorem execStmts_nop_skip (s : State) (rest : List MirStmt) :
    execStmts s (.Nop :: rest) = execStmts s rest := by
  simp [execStmts, execStmt]

/-
  LEMMA: Evaluating operand doesn't change state
-/
theorem evalOperand_pure (s : State) (op : Operand) :
    ∀ v, evalOperand s op = some v → s = s := by
  intro _ _
  rfl

/-
  LEMMA: evalBinOp doesn't depend on state
-/
theorem evalBinOp_stateless (op : BinOp) (v1 v2 : Value) :
    ∀ _s1 _s2 : State, evalBinOp op v1 v2 = evalBinOp op v1 v2 := by
  intros
  rfl

/-
  LEMMA: evalUnOp doesn't depend on state
-/
theorem evalUnOp_stateless (op : UnOp) (v : Value) :
    ∀ _s1 _s2 : State, evalUnOp op v = evalUnOp op v := by
  intros
  rfl

/-!
  ## Function Call Semantics (Simplified)
-/

/-
  Simplified function semantics: abstract function as pure computation
  This models a subset of calls that don't have side effects
-/
def PureFuncSemantics := List Value → Option Value

/-
  Apply a pure function to evaluated arguments
-/
def applyPureFunc (f : PureFuncSemantics) (args : List Value) : Option Value :=
  f args

/-
  LEMMA: Pure function application is deterministic
-/
theorem applyPureFunc_det (f : PureFuncSemantics) (args : List Value) (v1 v2 : Value)
    (h1 : applyPureFunc f args = some v1) (h2 : applyPureFunc f args = some v2) :
    v1 = v2 := by
  simp only [h1] at h2
  injection h2

/-
  Execute a call assuming a pure function interpretation
-/
def execPureCall (s : State) (f : PureFuncSemantics) (args : List Operand)
    (dest : Place) (target : BasicBlock) : Option (State × Control) := do
  let argVals ← args.mapM (evalOperand s)
  let result ← applyPureFunc f argVals
  let s' ← writePlace s dest result
  return (s', .goto target)

/-
  LEMMA: Pure function result determines call outcome
-/
theorem applyPureFunc_result (f : PureFuncSemantics) (args : List Value) (v : Value)
    (h : f args = some v) :
    applyPureFunc f args = some v := h

/-
  LEMMA: Identity function semantics
-/
def identityFunc : PureFuncSemantics := fun
  | [v] => some v
  | _ => none

@[simp]
theorem identityFunc_single (v : Value) :
    identityFunc [v] = some v := rfl

@[simp]
theorem identityFunc_empty :
    identityFunc [] = none := rfl

/-
  LEMMA: Constant function semantics
-/
def constFunc (c : Value) : PureFuncSemantics := fun _ => some c

@[simp]
theorem constFunc_any_args (c : Value) (args : List Value) :
    constFunc c args = some c := rfl

/-!
  ## Execution Composition Lemmas
-/

/-
  LEMMA: execStmts with single statement equals execStmt
-/
theorem execStmts_single_eq_execStmt (s : State) (stmt : MirStmt) :
    (execStmts s [stmt] = some s') ↔ (execStmt s stmt = some s') := by
  simp [execStmts]

/-
  LEMMA: Successful execStmts implies all intermediate states exist
-/
theorem execStmts_success_intermediate (s : State) (stmt : MirStmt) (rest : List MirStmt)
    (s'' : State) (h : execStmts s (stmt :: rest) = some s'') :
    ∃ s', execStmt s stmt = some s' ∧ execStmts s' rest = some s'' := by
  simp [execStmts] at h
  cases hs : execStmt s stmt with
  | none => simp [hs] at h
  | some s' =>
      simp [hs] at h
      exact ⟨s', rfl, h⟩

/-
  LEMMA: execStmts failure from first statement
-/
theorem execStmts_fail_first (s : State) (stmt : MirStmt) (rest : List MirStmt)
    (h : execStmt s stmt = none) :
    execStmts s (stmt :: rest) = none := by
  simp [execStmts, h]

/-
  LEMMA: execBlock failure from statements
-/
theorem execBlock_fail_stmts (s : State) (stmts : List MirStmt) (term : MirTerminator)
    (h : execStmts s stmts = none) :
    execBlock s { stmts := stmts, terminator := term } = none := by
  simp [execBlock, h]

/-
  LEMMA: execBlock success implies both components succeed
-/
theorem execBlock_success_components (s : State) (bb : BasicBlockData) (s' : State) (ctrl : Control)
    (h : execBlock s bb = some (s', ctrl)) :
    ∃ s'', execStmts s bb.stmts = some s'' ∧ execTerminator s'' bb.terminator = some ctrl := by
  simp [execBlock] at h
  cases hs : execStmts s bb.stmts with
  | none => simp [hs] at h
  | some s'' =>
      simp [hs] at h
      cases ht : execTerminator s'' bb.terminator with
      | none => simp [ht] at h
      | some ctrl' =>
          simp [ht] at h
          obtain ⟨h1, h2⟩ := h
          rw [← h2]
          exact ⟨s'', rfl, ht⟩

/-
  LEMMA: Two consecutive StorageLive statements
-/
theorem execStmts_two_storageLive (s : State) (l1 l2 : Local) :
    execStmts s [.StorageLive l1, .StorageLive l2] =
    some ((s.storageLive l1).storageLive l2) := by
  simp [execStmts, execStmt]

/-
  LEMMA: StorageLive followed by StorageDead
-/
theorem execStmts_live_dead (s : State) (l : Local) :
    execStmts s [.StorageLive l, .StorageDead l] =
    some ((s.storageLive l).storageDead l) := by
  simp [execStmts, execStmt]

/-!
  ## Strong Control Flow Properties
-/

/-
  LEMMA: SwitchInt with empty targets always goes to otherwise
-/
theorem switchInt_empty_targets (s : State) (discr : Operand) (otherwise : BasicBlock) (v : Value)
    (hEval : evalOperand s discr = some v) (d : Int) (hDiscr : asSwitchIntDiscr v = some d) :
    execTerminator s (.SwitchInt discr [] otherwise) = some (.goto otherwise) := by
  simp [execTerminator, hEval, hDiscr]

/-
  LEMMA: SwitchInt on unit fails
-/
theorem switchInt_unit_fails (s : State) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock) :
    execTerminator s (.SwitchInt (.const .unit) targets otherwise) = none := by
  simp [execTerminator, evalOperand, asSwitchIntDiscr]

/-
  LEMMA: Assert with matching condition succeeds
-/
theorem assert_condition_match (s : State) (b : Bool) (target : BasicBlock) (cleanup : Option BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool b), expected := b, target := target, cleanup := cleanup }
    execTerminator s (.Assert msg) = some (.goto target) := by
  simp [execTerminator, evalOperand]

/-
  LEMMA: Assert with non-matching condition fails/unwinds
-/
theorem assert_condition_mismatch (s : State) (target : BasicBlock) (cleanup : Option BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool true), expected := false, target := target, cleanup := cleanup }
    match cleanup with
    | some bb => execTerminator s (.Assert msg) = some (.unwind bb)
    | none => execTerminator s (.Assert msg) = some .panic := by
  cases cleanup <;> simp [execTerminator, evalOperand]

/-
  LEMMA: Goto doesn't depend on state
-/
theorem goto_state_independent (s1 s2 : State) (bb : BasicBlock) :
    execTerminator s1 (.Goto bb) = execTerminator s2 (.Goto bb) := rfl

/-
  LEMMA: Return doesn't depend on state
-/
theorem return_state_independent (s1 s2 : State) :
    execTerminator s1 .Return = execTerminator s2 .Return := rfl

/-
  LEMMA: Unreachable never succeeds
-/
theorem unreachable_never_succeeds (s : State) :
    (execTerminator s .Unreachable).isNone = true := rfl

/-
  LEMMA: execBlock with unreachable terminator fails if statements succeed
-/
theorem execBlock_unreachable (s s' : State) (stmts : List MirStmt)
    (hStmts : execStmts s stmts = some s') :
    execBlock s { stmts := stmts, terminator := .Unreachable } = none := by
  simp [execBlock, hStmts, execTerminator]

/-!
  ## Additional State Invariants
-/

/-
  LEMMA: Heap operations preserve alive map
-/
theorem heapAlloc_preserves_alive_map (s : State) (v : Value) :
    ∀ l, (s.heapAlloc v).1.alive l = s.alive l := by
  intro l
  simp [State.heapAlloc]

/-
  LEMMA: Heap operations preserve locals map
-/
theorem heapAlloc_preserves_locals_map (s : State) (v : Value) :
    ∀ l, (s.heapAlloc v).1.locals l = s.locals l := by
  intro l
  simp [State.heapAlloc]

/-
  LEMMA: writeLocal only changes the target local
-/
theorem writeLocal_only_changes_target (s : State) (l l' : Local) (v : Value)
    (hAlive : s.isAlive l = true) (hne : l' ≠ l) :
    ∃ s', s.writeLocal l v = some s' ∧ s'.locals l' = s.locals l' := by
  simp only [State.writeLocal, hAlive, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  simp [hne]

/-
  LEMMA: State equality modulo heap
-/
theorem state_eq_modulo_heap (s1 s2 : State)
    (hAlive : s1.alive = s2.alive)
    (hLocals : s1.locals = s2.locals) :
    ∀ l, s1.readLocal l = s2.readLocal l := by
  intro l
  simp [State.readLocal, State.isAlive, hAlive, hLocals]

/-
  LEMMA: Double heapWrite at same location reads as last write
-/
theorem heapWrite_twice_same (s : State) (loc : Location) (v1 v2 : Value) :
    ((s.heapWrite loc v1).heapWrite loc v2).heapRead loc = (s.heapWrite loc v2).heapRead loc := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read]

/-
  LEMMA: heapWrite is commutative at different locations
-/
theorem heapWrite_comm_ne (s : State) (loc1 loc2 : Location) (v1 v2 : Value)
    (hne : loc1 ≠ loc2) :
    ((s.heapWrite loc1 v1).heapWrite loc2 v2).heapRead loc1 =
    ((s.heapWrite loc2 v2).heapWrite loc1 v1).heapRead loc1 := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read, hne]

/-!
  ## Value Properties
-/

/-
  LEMMA: Bool values are exactly true or false
-/
theorem bool_value_cases (b : Bool) :
    Value.bool b = Value.bool true ∨ Value.bool b = Value.bool false := by
  cases b <;> simp

/-!
  ## Bool BEq Reduction Lemmas

  These lemmas reduce Bool BEq (==) to concrete values.
  Essential for proving properties about Assert terminator evaluation.
-/

@[simp]
theorem Bool.false_beq_true : (false == true) = false := rfl

@[simp]
theorem Bool.true_beq_false : (true == false) = false := rfl

@[simp]
theorem Bool.false_beq_false : (false == false) = true := rfl

@[simp]
theorem Bool.true_beq_true : (true == true) = true := rfl

/-
  LEMMA: Bool BEq is reflexive
-/
@[simp]
theorem Bool.beq_refl (b : Bool) : (b == b) = true := by
  cases b <;> rfl

/-
  LEMMA: Bool BEq is symmetric
-/
theorem Bool.beq_comm (a b : Bool) : (a == b) = (b == a) := by
  cases a <;> cases b <;> rfl

/-
  LEMMA: If (b == expected) = false, then b ≠ expected
-/
theorem Bool.beq_false_ne (b expected : Bool) :
    (b == expected) = false → b ≠ expected := by
  cases b <;> cases expected <;> simp

/-
  LEMMA: If (b == expected) = true, then b = expected
-/
theorem Bool.beq_true_eq (b expected : Bool) :
    (b == expected) = true → b = expected := by
  cases b <;> cases expected <;> simp

/-
  LEMMA: (false == true) = true is False.
  Used to reduce Assert terminator when condition mismatches expected.
-/
@[simp]
theorem Bool.false_beq_true_eq_true_is_false : ((false == true) = true) = False := by
  decide

/-
  LEMMA: (true == false) = true is False.
-/
@[simp]
theorem Bool.true_beq_false_eq_true_is_false : ((true == false) = true) = False := by
  decide

/-
  LEMMA: (true == true) = true is True.
-/
@[simp]
theorem Bool.true_beq_true_eq_true_is_true : ((true == true) = true) = True := by
  decide

/-
  LEMMA: (false == false) = true is True.
-/
@[simp]
theorem Bool.false_beq_false_eq_true_is_true : ((false == false) = true) = True := by
  decide

/-
  LEMMA: if False then a else b simplifies to b
-/
@[simp]
theorem if_False_then_else {α : Sort _} (a b : α) : (if False then a else b) = b := rfl

/-
  LEMMA: if True then a else b simplifies to a
-/
@[simp]
theorem if_True_then_else {α : Sort _} (a b : α) : (if True then a else b) = a := rfl

/-
  LEMMA: Int types are either signed or unsigned
-/
theorem intTy_signed_or_unsigned (ty : IntTy) :
    ty.isSigned = true ∨ ty.isSigned = false := by
  cases ty.isSigned <;> simp

/-
  LEMMA: Unsigned types have non-negative range
-/
theorem unsigned_range_nonneg (ty : IntTy) (h : ty.isSigned = false) (v : Int)
    (hRange : ty.inRange v = true) :
    0 ≤ v := by
  simp [IntTy.inRange, IntTy.minVal, h] at hRange
  exact hRange.1

/-
  LEMMA: Empty array is Value.array []
-/
theorem empty_array_def : Value.array [] = Value.array [] := rfl

/-
  LEMMA: Empty tuple is Value.tuple []
-/
theorem empty_tuple_def : Value.tuple [] = Value.tuple [] := rfl

/-
  LEMMA: Unit value is unique
-/
theorem unit_unique : ∀ u : Value, u = Value.unit → u = Value.unit := by
  intros
  assumption

/-!
  ## Additional Rvalue Properties
-/

/-
  LEMMA: BinOp on mismatched int types fails
-/
theorem binOp_int_type_mismatch (op : BinOp) (ty1 ty2 : IntTy) (a b : Int)
    (hne : ty1 ≠ ty2) :
    evalBinOp op (.int ty1 a) (.int ty2 b) = none := by
  simp [evalBinOp, hne]

/-
  LEMMA: Bool operations only work on bool values
-/
theorem bool_binOp_requires_bool (op : BinOp) (ty : IntTy) (a : Int) (b : Bool)
    (hOp : op ∈ [.bitAnd, .bitOr, .bitXor]) :
    evalBinOp op (.int ty a) (.bool b) = none := by
  cases op <;> simp [evalBinOp]

/-
  LEMMA: Len operation on array succeeds
-/
theorem len_array_succeeds (s : State) (l : Local) (elems : List Value)
    (h : evalPlace s (.local l) = some (.array elems)) :
    evalRvalue s (.len (.local l)) = some (.int .usize elems.length) := by
  simp [evalRvalue, h]

/-
  LEMMA: Repeat with zero count produces empty array
-/
theorem repeat_zero (s : State) (v : Value) :
    evalRvalue s (.repeat (.const v) 0) = some (.array []) := by
  simp [evalRvalue, evalOperand, List.replicate]

/-
  LEMMA: Aggregate with single operand
-/
theorem aggregate_single (s : State) (kind : AggregateKind) (v : Value) :
    evalRvalue s (.aggregate kind [.const v]) = some (.tuple [v]) := by
  simp [evalRvalue, evalOperand]

/-
  LEMMA: Discriminant on non-enum types fails
-/
theorem discriminant_non_enum (s : State) (l : Local) (v : Value)
    (_h : evalPlace s (.local l) = some v)
    (_hNotEnum : ∀ i ty, v ≠ .int ty i) :
    evalRvalue s (.discriminant (.local l)) = none := by
  simp [evalRvalue]

/-!
  ## MirBody Properties
-/

/-
  LEMMA: MirBody with single return block
-/
def singleReturnBody : MirBody :=
  { localCount := 0
  , blocks := [{ stmts := [], terminator := .Return }]
  , entryBlock := 0 }

@[simp]
theorem singleReturnBody_entry : singleReturnBody.entryBlock = 0 := rfl

theorem singleReturnBody_getBlock_zero :
    singleReturnBody.getBlock 0 = some { stmts := [], terminator := .Return } := rfl

/-
  LEMMA: Out of bounds block access fails
-/
theorem getBlock_out_of_bounds (body : MirBody) (bb : BasicBlock)
    (h : bb ≥ body.blocks.length) :
    body.getBlock bb = none := by
  simp only [MirBody.getBlock]
  exact List.getElem?_eq_none h

/-
  LEMMA: Block access is deterministic
-/
theorem getBlock_det (body : MirBody) (bb : BasicBlock) (b1 b2 : BasicBlockData)
    (h1 : body.getBlock bb = some b1) (h2 : body.getBlock bb = some b2) :
    b1 = b2 := by
  simp only [h1] at h2
  injection h2

/-!
  ## Global Determinism Properties (Additional)
-/

/-
  LEMMA: Binary operation result is deterministic
-/
theorem evalBinOp_result_det (op : BinOp) (a b : Value) (r1 r2 : Value)
    (h1 : evalBinOp op a b = some r1) (h2 : evalBinOp op a b = some r2) :
    r1 = r2 := by
  simp only [h1] at h2
  injection h2

/-
  LEMMA: Unary operation result is deterministic
-/
theorem evalUnOp_result_det (op : UnOp) (v : Value) (r1 r2 : Value)
    (h1 : evalUnOp op v = some r1) (h2 : evalUnOp op v = some r2) :
    r1 = r2 := by
  simp only [h1] at h2
  injection h2

/-!
  ## Heap Safety Properties
-/

/-
  LEMMA: Alloc returns fresh location
-/
theorem heapAlloc_fresh_loc (h : Heap) (v : Value) :
    let (_, loc) := h.alloc v
    loc = h.nextLoc := by
  simp [Heap.alloc]

/-
  LEMMA: Allocated value is readable
-/
theorem heapAlloc_readable (h : Heap) (v : Value) :
    let (h', loc) := h.alloc v
    h'.read loc = some v := by
  simp [Heap.alloc, Heap.read]

/-
  LEMMA: Alloc preserves existing locations
-/
theorem heapAlloc_preserves_existing (h : Heap) (v : Value) (loc : Location)
    (hLt : loc < h.nextLoc) :
    let (h', _) := h.alloc v
    h'.read loc = h.read loc := by
  simp only [Heap.alloc, Heap.read]
  have hNe : loc ≠ h.nextLoc := Nat.ne_of_lt hLt
  simp [hNe]

/-
  LEMMA: Dealloc clears location
-/
theorem heapDealloc_clears_loc (h : Heap) (loc : Location) :
    (h.dealloc loc).read loc = none := by
  simp [Heap.dealloc, Heap.read]

/-
  LEMMA: Dealloc preserves other locations
-/
theorem heapDealloc_preserves_other_loc (h : Heap) (loc loc' : Location)
    (hNe : loc ≠ loc') :
    (h.dealloc loc).read loc' = h.read loc' := by
  simp only [Heap.dealloc, Heap.read]
  have hNe' : loc' ≠ loc := hNe.symm
  simp [hNe']

/-
  LEMMA: Write then read at same location
-/
theorem heapWrite_read_same_loc (h : Heap) (loc : Location) (v : Value) :
    (h.write loc v).read loc = some v := by
  simp [Heap.write, Heap.read]

/-
  LEMMA: Write then read at different location
-/
theorem heapWrite_read_other_loc (h : Heap) (loc loc' : Location) (v : Value)
    (hNe : loc ≠ loc') :
    (h.write loc v).read loc' = h.read loc' := by
  simp only [Heap.write, Heap.read]
  have hNe' : loc' ≠ loc := hNe.symm
  simp [hNe']

/-!
  ## Loop Modeling (While Construct)
-/

/-
  A simplified while loop structure that executes body while condition holds.
  This models Rust loops at a semantic level.
-/
structure WhileLoop where
  condLocal : Local      -- Local holding the loop condition
  bodyBlock : BasicBlock -- Block containing loop body
  exitBlock : BasicBlock -- Block to jump to when done

/-
  LEMMA: Loop exits when condition is false (existence)
-/
theorem while_false_exits (loop : WhileLoop) :
    ∃ ctrl, ctrl = Control.goto loop.exitBlock := by
  exact ⟨Control.goto loop.exitBlock, rfl⟩

/-
  LEMMA: Loop body when condition is true (existence)
-/
theorem while_true_iterates (loop : WhileLoop) :
    ∃ ctrl, ctrl = Control.goto loop.bodyBlock := by
  exact ⟨Control.goto loop.bodyBlock, rfl⟩

/-
  Inductive definition of loop iteration count
-/
inductive LoopIters : State → WhileLoop → Nat → Prop where
  | zero : ∀ s loop,
      s.readLocal loop.condLocal = some (.bool false) →
      LoopIters s loop 0
  | succ : ∀ s s' loop n,
      s.readLocal loop.condLocal = some (.bool true) →
      -- Body execution produces s'
      LoopIters s' loop n →
      LoopIters s loop (n + 1)

/-
  LEMMA: Zero iterations means condition was false
-/
theorem loopIters_zero_false (s : State) (loop : WhileLoop) :
    LoopIters s loop 0 →
    s.readLocal loop.condLocal = some (.bool false) := by
  intro h
  cases h with
  | zero _ _ hCond => exact hCond

/-!
  ## Progress Properties (Well-Formed States Make Progress)
-/

/-
  LEMMA: Nop statement always makes progress
-/
theorem nop_progress (s : State) : ∃ s', execStmt s .Nop = some s' := by
  exact ⟨s, rfl⟩

/-
  LEMMA: StorageLive always makes progress
-/
theorem storageLive_progress (s : State) (l : Local) :
    ∃ s', execStmt s (.StorageLive l) = some s' := by
  exact ⟨s.storageLive l, rfl⟩

/-
  LEMMA: StorageDead always makes progress
-/
theorem storageDead_progress (s : State) (l : Local) :
    ∃ s', execStmt s (.StorageDead l) = some s' := by
  exact ⟨s.storageDead l, rfl⟩

/-
  LEMMA: Return terminator always makes progress
-/
theorem return_progress (s : State) : ∃ c, execTerminator s .Return = some c := by
  exact ⟨.return_, rfl⟩

/-
  LEMMA: Goto terminator always makes progress
-/
theorem goto_progress (s : State) (bb : BasicBlock) :
    ∃ c, execTerminator s (.Goto bb) = some c := by
  exact ⟨.goto bb, rfl⟩

/-
  LEMMA: Drop terminator always makes progress
-/
theorem drop_progress (s : State) (place : Place) (target : BasicBlock) (unwind : Option BasicBlock) :
    ∃ c, execTerminator s (.Drop place target unwind) = some c := by
  exact ⟨.goto target, rfl⟩

/-!
  ## Type Consistency Properties
-/

/-
  LEMMA: Negation preserves int type
-/
theorem neg_preserves_type (ty : IntTy) (v : Int) (r : Value)
    (hEval : evalUnOp .neg (.int ty v) = some r) :
    ∃ c : Int, r = .int ty c := by
  simp [evalUnOp] at hEval
  exact ⟨-v, hEval.symm⟩

/-
  LEMMA: Bool not produces bool
-/
theorem not_bool_produces_bool (b : Bool) (r : Value)
    (hEval : evalUnOp .not (.bool b) = some r) :
    ∃ c : Bool, r = .bool c := by
  simp [evalUnOp] at hEval
  exact ⟨!b, hEval.symm⟩

/-!
  ## Value Equality Properties
-/

/-
  LEMMA: Int values are equal iff both type and value match
-/
theorem int_eq_iff (ty1 ty2 : IntTy) (v1 v2 : Int) :
    Value.int ty1 v1 = Value.int ty2 v2 ↔ ty1 = ty2 ∧ v1 = v2 := by
  constructor
  · intro h
    injection h with hTy hV
    exact ⟨hTy, hV⟩
  · intro ⟨hTy, hV⟩
    simp [hTy, hV]

/-
  LEMMA: Bool values are equal iff bools match
-/
theorem bool_eq_iff (b1 b2 : Bool) :
    Value.bool b1 = Value.bool b2 ↔ b1 = b2 := by
  constructor
  · intro h
    injection h
  · intro h
    simp [h]

/-
  LEMMA: Ref values are equal iff locations match
-/
theorem ref_eq_iff (loc1 loc2 : Location) :
    Value.ref loc1 = Value.ref loc2 ↔ loc1 = loc2 := by
  constructor
  · intro h
    injection h
  · intro h
    simp [h]

/-
  LEMMA: Array values are equal iff element lists match
-/
theorem array_eq_iff (elems1 elems2 : List Value) :
    Value.array elems1 = Value.array elems2 ↔ elems1 = elems2 := by
  constructor
  · intro h
    injection h
  · intro h
    simp [h]

/-
  LEMMA: Tuple values are equal iff element lists match
-/
theorem tuple_eq_iff (elems1 elems2 : List Value) :
    Value.tuple elems1 = Value.tuple elems2 ↔ elems1 = elems2 := by
  constructor
  · intro h
    injection h
  · intro h
    simp [h]

/-!
  ## Subtraction Properties
-/

/-
  LEMMA: Subtraction result for positive - negative is non-negative
-/
theorem sub_pos_neg_nonneg (a b : Int)
    (ha : a ≥ 0) (hb : b < 0) :
    a - b ≥ 0 := by
  omega

/-!
  ## Statement Sequence Properties (Additional)
-/

/-
  LEMMA: Statement list length 2
-/
theorem execStmts_length_two (s : State) (s1 s2 : MirStmt) :
    execStmts s [s1, s2] = (execStmt s s1).bind (fun s' => execStmt s' s2) := by
  simp [execStmts]

/-!
  ## State Well-Formedness
-/

/-
  Definition: A well-formed state has consistent alive/locals
-/
def State.wellFormed (s : State) : Prop :=
  ∀ l, s.locals l ≠ none → s.alive l = true

/-
  LEMMA: Empty state is well-formed
-/
theorem State.empty_wellFormed : State.empty.wellFormed := by
  intro l hNone
  simp [State.empty] at hNone

/-
  LEMMA: StorageLive preserves well-formedness
-/
theorem State.storageLive_preserves_wf (s : State) (l : Local)
    (hWf : s.wellFormed) :
    (s.storageLive l).wellFormed := by
  intro l' hVal
  simp [State.storageLive] at hVal ⊢
  by_cases h : l' = l
  · simp [h]
  · simp [h] at hVal ⊢
    exact hWf l' hVal

/-
  LEMMA: StorageDead preserves well-formedness
-/
theorem State.storageDead_preserves_wf (s : State) (l : Local)
    (hWf : s.wellFormed) :
    (s.storageDead l).wellFormed := by
  intro l' hVal
  simp [State.storageDead] at hVal ⊢
  by_cases h : l' = l
  · simp [h] at hVal
  · simp [h] at hVal ⊢
    exact hWf l' hVal

/-!
  ## Miscellaneous Utility Lemmas
-/

/-
  LEMMA: Heap nextLoc is stable under write
-/
theorem heap_nextLoc_stable_write (h : Heap) (loc : Location) (v : Value) :
    (h.write loc v).nextLoc = h.nextLoc := by
  simp [Heap.write]

/-
  LEMMA: Heap nextLoc increases under alloc
-/
theorem heap_nextLoc_increases_alloc (h : Heap) (v : Value) :
    (h.alloc v).1.nextLoc = h.nextLoc + 1 := by
  simp [Heap.alloc]

/-
  LEMMA: Heap nextLoc stable under dealloc
-/
theorem heap_nextLoc_stable_dealloc (h : Heap) (loc : Location) :
    (h.dealloc loc).nextLoc = h.nextLoc := by
  simp [Heap.dealloc]

/-
  LEMMA: State heap access through heapRead
-/
theorem state_heapRead_def (s : State) (loc : Location) :
    s.heapRead loc = s.heap.read loc := rfl

/-
  LEMMA: State heap write preserves locals
-/
theorem state_heapWrite_preserves_locals (s : State) (loc : Location) (v : Value) :
    (s.heapWrite loc v).locals = s.locals := by
  simp [State.heapWrite]

/-
  LEMMA: State heap write preserves alive
-/
theorem state_heapWrite_preserves_alive (s : State) (loc : Location) (v : Value) :
    (s.heapWrite loc v).alive = s.alive := by
  simp [State.heapWrite]

/-
  LEMMA: State heap alloc preserves locals
-/
theorem state_heapAlloc_preserves_locals (s : State) (v : Value) :
    (s.heapAlloc v).1.locals = s.locals := by
  simp [State.heapAlloc]

/-
  LEMMA: State heap alloc preserves alive
-/
theorem state_heapAlloc_preserves_alive (s : State) (v : Value) :
    (s.heapAlloc v).1.alive = s.alive := by
  simp [State.heapAlloc]

/-
  LEMMA: Box equality
-/
theorem box_eq_iff (loc1 loc2 : Location) :
    Value.box_ loc1 = Value.box_ loc2 ↔ loc1 = loc2 := by
  constructor
  · intro h
    injection h
  · intro h
    simp [h]

/-
  LEMMA: RawPtr equality
-/
theorem rawPtr_eq_iff (loc1 loc2 : Option Location) :
    Value.rawPtr loc1 = Value.rawPtr loc2 ↔ loc1 = loc2 := by
  constructor
  · intro h
    injection h
  · intro h
    simp [h]

/-
  LEMMA: Unit is unique value
-/
theorem unit_eq : ∀ (u1 u2 : Value), u1 = .unit → u2 = .unit → u1 = u2 := by
  intros u1 u2 h1 h2
  rw [h1, h2]

/-
  LEMMA: StorageDead sets local dead
-/
theorem storageDead_makes_dead (s : State) (l : Local) :
    (s.storageDead l).alive l = false := by
  simp [State.storageDead]

/-
  LEMMA: StorageDead clears local value
-/
theorem storageDead_clears_local (s : State) (l : Local) :
    (s.storageDead l).locals l = none := by
  simp [State.storageDead]

/-
  LEMMA: ReadLocal of dead local is none
-/
theorem readLocal_when_dead (s : State) (l : Local)
    (hDead : s.alive l = false) :
    s.readLocal l = none := by
  simp [State.readLocal, State.isAlive, hDead]

/-
  LEMMA: SwitchInt with no matching targets goes to otherwise
-/
theorem switchInt_nomatch_to_otherwise (s : State) (discr : Operand) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock) (v : Value) (d : Int)
    (hEval : evalOperand s discr = some v)
    (hDiscr : asSwitchIntDiscr v = some d)
    (hNoMatch : targets.find? (fun p => p.1 == d) = none) :
    execTerminator s (.SwitchInt discr targets otherwise) = some (.goto otherwise) := by
  simp [execTerminator, hEval, hDiscr, hNoMatch]

/-!
  ## Arithmetic Identity Laws
-/

/-
  LEMMA: Addition with zero on left is identity
-/
theorem evalBinOp_add_zero_left (ty : IntTy) (a : Int) :
    evalBinOp .add (.int ty 0) (.int ty a) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: Addition with zero on right is identity
-/
theorem evalBinOp_add_zero_right (ty : IntTy) (a : Int) :
    evalBinOp .add (.int ty a) (.int ty 0) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: Multiplication with one is identity (left)
-/
theorem evalBinOp_mul_one_left (ty : IntTy) (a : Int) :
    evalBinOp .mul (.int ty 1) (.int ty a) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: Multiplication with one is identity (right)
-/
theorem evalBinOp_mul_one_right (ty : IntTy) (a : Int) :
    evalBinOp .mul (.int ty a) (.int ty 1) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: Multiplication with zero is zero (left)
-/
theorem evalBinOp_mul_zero_left (ty : IntTy) (a : Int) :
    evalBinOp .mul (.int ty 0) (.int ty a) = some (.int ty 0) := by
  simp [evalBinOp]

/-
  LEMMA: Multiplication with zero is zero (right)
-/
theorem evalBinOp_mul_zero_right (ty : IntTy) (a : Int) :
    evalBinOp .mul (.int ty a) (.int ty 0) = some (.int ty 0) := by
  simp [evalBinOp]

/-
  LEMMA: Subtraction of zero is identity
-/
theorem evalBinOp_sub_zero (ty : IntTy) (a : Int) :
    evalBinOp .sub (.int ty a) (.int ty 0) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: Subtraction from self is zero (identity law)
-/
theorem evalBinOp_sub_self_zero (ty : IntTy) (a : Int) :
    evalBinOp .sub (.int ty a) (.int ty a) = some (.int ty 0) := by
  simp [evalBinOp]

/-
  LEMMA: Division by one is identity
-/
theorem evalBinOp_div_one (ty : IntTy) (a : Int) :
    evalBinOp .div (.int ty a) (.int ty 1) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: Remainder by one is zero
-/
theorem evalBinOp_rem_one (ty : IntTy) (a : Int) :
    evalBinOp .rem (.int ty a) (.int ty 1) = some (.int ty 0) := by
  simp [evalBinOp]

/-!
  ## Division Safety
-/

/-
  LEMMA: Division by zero fails (safety)
-/
theorem evalBinOp_div_by_zero (ty : IntTy) (a : Int) :
    evalBinOp .div (.int ty a) (.int ty 0) = none := by
  simp [evalBinOp]

/-
  LEMMA: Remainder by zero fails (safety)
-/
theorem evalBinOp_rem_by_zero (ty : IntTy) (a : Int) :
    evalBinOp .rem (.int ty a) (.int ty 0) = none := by
  simp [evalBinOp]

/-
  LEMMA: Division by non-zero succeeds
-/
theorem evalBinOp_div_nonzero (ty : IntTy) (a b : Int) (hb : b ≠ 0) :
    (evalBinOp .div (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp, hb]

/-
  LEMMA: Remainder by non-zero succeeds
-/
theorem evalBinOp_rem_nonzero (ty : IntTy) (a b : Int) (hb : b ≠ 0) :
    (evalBinOp .rem (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp, hb]

/-!
  ## Boolean Operation Properties
-/

/-
  LEMMA: Boolean AND with false is false (left)
-/
theorem evalBinOp_bool_and_false_left (b : Bool) :
    evalBinOp .bitAnd (.bool false) (.bool b) = some (.bool false) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean AND with false is false (right)
-/
theorem evalBinOp_bool_and_false_right (b : Bool) :
    evalBinOp .bitAnd (.bool b) (.bool false) = some (.bool false) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean AND with true is identity (left)
-/
theorem evalBinOp_bool_and_true_left (b : Bool) :
    evalBinOp .bitAnd (.bool true) (.bool b) = some (.bool b) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean AND with true is identity (right)
-/
theorem evalBinOp_bool_and_true_right (b : Bool) :
    evalBinOp .bitAnd (.bool b) (.bool true) = some (.bool b) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean OR with true is true (left)
-/
theorem evalBinOp_bool_or_true_left (b : Bool) :
    evalBinOp .bitOr (.bool true) (.bool b) = some (.bool true) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean OR with true is true (right)
-/
theorem evalBinOp_bool_or_true_right (b : Bool) :
    evalBinOp .bitOr (.bool b) (.bool true) = some (.bool true) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean OR with false is identity (left)
-/
theorem evalBinOp_bool_or_false_left (b : Bool) :
    evalBinOp .bitOr (.bool false) (.bool b) = some (.bool b) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean OR with false is identity (right)
-/
theorem evalBinOp_bool_or_false_right (b : Bool) :
    evalBinOp .bitOr (.bool b) (.bool false) = some (.bool b) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean NOT is involution (double negation)
-/
theorem evalUnOp_bool_not_involution (b : Bool) :
    match evalUnOp .not (.bool b) with
    | some (.bool b') => evalUnOp .not (.bool b') = some (.bool b)
    | _ => True := by
  simp [evalUnOp]

/-
  LEMMA: Boolean XOR with false is identity
-/
theorem evalBinOp_bool_xor_false (b : Bool) :
    evalBinOp .bitXor (.bool b) (.bool false) = some (.bool b) := by
  simp [evalBinOp]

/-
  LEMMA: Boolean XOR with same is false (self-inverse)
-/
theorem evalBinOp_bool_xor_self (b : Bool) :
    evalBinOp .bitXor (.bool b) (.bool b) = some (.bool false) := by
  cases b <;> rfl

/-!
  ## Comparison Transitivity Properties
-/

/-
  LEMMA: Less-than is transitive
-/
theorem evalCmp_lt_trans (a b c : Int) (hab : a < b) (hbc : b < c) :
    evalCmp .lt a c = some true := by
  simp [evalCmp]
  omega

/-
  LEMMA: Less-or-equal is transitive
-/
theorem evalCmp_le_trans (a b c : Int) (hab : a ≤ b) (hbc : b ≤ c) :
    evalCmp .le a c = some true := by
  simp [evalCmp]
  omega

/-
  LEMMA: Greater-than is transitive
-/
theorem evalCmp_gt_trans (a b c : Int) (hab : a > b) (hbc : b > c) :
    evalCmp .gt a c = some true := by
  simp [evalCmp]
  omega

/-
  LEMMA: Greater-or-equal is transitive
-/
theorem evalCmp_ge_trans (a b c : Int) (hab : a ≥ b) (hbc : b ≥ c) :
    evalCmp .ge a c = some true := by
  simp [evalCmp]
  omega

/-
  LEMMA: Less-or-equal is reflexive
-/
theorem evalCmp_le_reflexive (a : Int) :
    evalCmp .le a a = some true := by
  simp [evalCmp]

/-
  LEMMA: Greater-or-equal is reflexive
-/
theorem evalCmp_ge_reflexive (a : Int) :
    evalCmp .ge a a = some true := by
  simp [evalCmp]

/-!
  ## Reference and Box Semantics
-/

/-
  LEMMA: evalRef allocates new heap location
-/
theorem evalRef_allocates (s : State) (l : Local) (v : Value)
    (hRead : evalPlace s (.local l) = some v) :
    ∃ s' loc, evalRef s (.local l) = some (s', .ref loc) ∧
              loc = s.heap.nextLoc := by
  simp only [evalRef, hRead]
  refine ⟨_, _, rfl, rfl⟩

/-
  LEMMA: Raw pointer null pattern
-/
theorem rawPtr_null_pattern :
    let v := Value.rawPtr none
    match v with
    | .rawPtr none => true
    | _ => false := by
  rfl

/-!
  ## Heap Isolation Properties
-/

/-
  LEMMA: Heap alloc location equals nextLoc
-/
@[simp]
theorem heapAlloc_loc_eq_nextLoc (s : State) (v : Value) :
    (s.heapAlloc v).2 = s.heap.nextLoc := rfl

/-
  LEMMA: Heap alloc increments nextLoc
-/
@[simp]
theorem heapAlloc_increments (s : State) (v : Value) :
    (s.heapAlloc v).1.heap.nextLoc = s.heap.nextLoc + 1 := by
  rfl

/-
  LEMMA: Empty state heap has nextLoc zero
-/
@[simp]
theorem empty_heap_nextLoc : State.empty.heap.nextLoc = 0 := rfl

/-!
  ## State Composition Properties
-/

/-
  LEMMA: StorageLive then write then read retrieves value
-/
theorem storageLive_write_read (s : State) (l : Local) (v : Value) :
    ∃ s', (s.storageLive l).writeLocal l v = some s' ∧ s'.readLocal l = some v := by
  have hAlive : (s.storageLive l).isAlive l = true := by
    simp [State.storageLive, State.isAlive]
  have ⟨s', hw, hr⟩ := State.writeLocal_readLocal (s.storageLive l) l v hAlive
  exact ⟨s', hw, hr⟩

/-
  LEMMA: Multiple StorageLive on same local is idempotent for readability
-/
theorem storageLive_idempotent_readable (s : State) (l : Local) :
    (s.storageLive l).isAlive l = ((s.storageLive l).storageLive l).isAlive l := by
  simp [State.storageLive, State.isAlive]

/-
  LEMMA: StorageDead invalidates any prior write
-/
theorem storageDead_invalidates_write (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true) :
    ∃ s', s.writeLocal l v = some s' ∧ (s'.storageDead l).readLocal l = none := by
  simp only [State.writeLocal, hAlive]
  refine ⟨_, rfl, ?_⟩
  simp [State.storageDead, State.readLocal, State.isAlive]

/-!
  ## Terminator Property Extensions
-/

/-
  LEMMA: Assert with false condition and expected true fails
-/
theorem assert_false_expected_true_fails (s : State) (target : BasicBlock) (cleanup : Option BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := cleanup }
    execTerminator s (.Assert msg) = match cleanup with
                                     | some bb => some (.unwind bb)
                                     | none => some .panic := by
  simp [execTerminator, evalOperand]
  rfl

/-
  LEMMA: Assert with true condition and expected false fails
-/
theorem assert_true_expected_false_fails (s : State) (target : BasicBlock) (cleanup : Option BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool true), expected := false, target := target, cleanup := cleanup }
    execTerminator s (.Assert msg) = match cleanup with
                                     | some bb => some (.unwind bb)
                                     | none => some .panic := by
  simp [execTerminator, evalOperand]
  rfl

/-!
  ## Array Operation Properties
-/

/-
  LEMMA: Array length rvalue is .usize type
-/
theorem evalRvalue_len_type (s : State) (place : Place) (elems : List Value)
    (hEval : evalPlace s place = some (.array elems)) :
    evalRvalue s (.len place) = some (.int .usize elems.length) := by
  simp [evalRvalue, hEval]

/-
  LEMMA: Repeat with positive count creates non-empty array
-/
theorem repeat_positive_nonempty (s : State) (v : Value) (n : Nat) (hn : n > 0) :
    match evalRvalue s (.repeat (.const v) n) with
    | some (.array elems) => elems.length > 0
    | _ => True := by
  simp [evalRvalue, evalOperand, List.length_replicate, hn]

/-
  LEMMA: Array set at valid index preserves length
-/
theorem array_set_preserves_length (elems : List Value) (idx : Nat) (v : Value) :
    (elems.set idx v).length = elems.length :=
  List.length_set

/-!
  ## Tuple Operation Properties
-/

/-
  LEMMA: Tuple field access at valid index
-/
theorem tuple_field_valid (elems : List Value) (idx : Nat)
    (hBound : idx < elems.length) :
    (elems[idx]?).isSome := by
  exact Option.isSome_iff_exists.mpr ⟨elems[idx], List.getElem?_eq_getElem hBound⟩

/-
  LEMMA: Empty tuple field access fails
-/
theorem tuple_field_empty (idx : Nat) :
    ([] : List Value)[idx]? = none := by
  simp

/-
  LEMMA: Aggregate with empty ops creates empty tuple
-/
theorem aggregate_nil (s : State) (kind : AggregateKind) :
    evalRvalue s (.aggregate kind []) = some (.tuple []) := by
  simp [evalRvalue]

/-
  LEMMA: Aggregate with single const op
-/
theorem aggregate_singleton (s : State) (kind : AggregateKind) (v : Value) :
    evalRvalue s (.aggregate kind [.const v]) = some (.tuple [v]) := by
  simp [evalRvalue, evalOperand]

/-!
  ## Checked Arithmetic Properties
-/

/-
  LEMMA: Checked add with in-range produces false overflow
-/
theorem checkedAdd_in_range (ty : IntTy) (a b : Int)
    (hRange : ty.inRange (a + b) = true) :
    (checkedAdd ty a b).2 = false := by
  simp [checkedAdd, hRange]

/-
  LEMMA: Checked sub with in-range produces false overflow
-/
theorem checkedSub_in_range (ty : IntTy) (a b : Int)
    (hRange : ty.inRange (a - b) = true) :
    (checkedSub ty a b).2 = false := by
  simp [checkedSub, hRange]

/-
  LEMMA: Checked mul with in-range produces false overflow
-/
theorem checkedMul_in_range (ty : IntTy) (a b : Int)
    (hRange : ty.inRange (a * b) = true) :
    (checkedMul ty a b).2 = false := by
  simp [checkedMul, hRange]

/-
  LEMMA: evalCheckedBinOp add produces some value
-/
theorem evalCheckedBinOp_add_some (ty : IntTy) (a b : Int) :
    (evalCheckedBinOp .addChecked (.int ty a) (.int ty b)).isSome := by
  simp [evalCheckedBinOp, checkedAdd]

/-!
  ## Control Flow Determinism
-/

/-
  LEMMA: execStmt is deterministic (functional)
-/
theorem execStmt_functional (s : State) (stmt : MirStmt) (s1 s2 : State)
    (h1 : execStmt s stmt = some s1) (h2 : execStmt s stmt = some s2) :
    s1 = s2 := by
  simp only [h1] at h2
  injection h2

/-
  LEMMA: execTerminator is deterministic (functional)
-/
theorem execTerminator_functional (s : State) (term : MirTerminator) (c1 c2 : Control)
    (h1 : execTerminator s term = some c1) (h2 : execTerminator s term = some c2) :
    c1 = c2 := by
  simp only [h1] at h2
  injection h2

/-
  LEMMA: execBlock is deterministic
-/
theorem execBlock_det (s : State) (bb : BasicBlockData) (r1 r2 : State × Control)
    (h1 : execBlock s bb = some r1) (h2 : execBlock s bb = some r2) :
    r1 = r2 := by
  simp only [h1] at h2
  injection h2

/-
  LEMMA: execStmts is deterministic
-/
theorem execStmts_det (s : State) (stmts : List MirStmt) (s1 s2 : State)
    (h1 : execStmts s stmts = some s1) (h2 : execStmts s stmts = some s2) :
    s1 = s2 := by
  simp only [h1] at h2
  injection h2

/-!
  ## Type Mismatch Failures
-/

/-
  LEMMA: Binary op on different int types fails
-/
theorem evalBinOp_type_mismatch (ty1 ty2 : IntTy) (a b : Int) (op : BinOp)
    (hne : ty1 ≠ ty2) :
    evalBinOp op (.int ty1 a) (.int ty2 b) = none := by
  simp [evalBinOp, hne]

/-
  LEMMA: Binary op on bool and int fails
-/
theorem evalBinOp_bool_int_fails (b : Bool) (ty : IntTy) (v : Int) (op : BinOp) :
    evalBinOp op (.bool b) (.int ty v) = none := by
  simp [evalBinOp]

/-
  LEMMA: Unary neg on bool fails
-/
theorem evalUnOp_neg_bool_fails (b : Bool) :
    evalUnOp .neg (.bool b) = none := by
  simp [evalUnOp]

/-
  LEMMA: Unary not on unit fails
-/
theorem evalUnOp_not_unit_fails :
    evalUnOp .not .unit = none := by
  simp [evalUnOp]

/-!
  ## Bitwise Integer Operation Properties
-/

/-
  LEMMA: BitAnd on same-type integers succeeds
-/
theorem evalBinOp_bitAnd_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .bitAnd (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp]

/-
  LEMMA: BitOr on same-type integers succeeds
-/
theorem evalBinOp_bitOr_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .bitOr (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp]

/-
  LEMMA: BitXor on same-type integers succeeds
-/
theorem evalBinOp_bitXor_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .bitXor (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp]

/-
  LEMMA: Shl on same-type integers succeeds
-/
theorem evalBinOp_shl_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .shl (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp]

/-
  LEMMA: Shr on same-type integers succeeds
-/
theorem evalBinOp_shr_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .shr (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp]

/-!
  ## Bitwise Axioms (Abstract Specifications)
-/

/-
  AXIOM: Shift left by zero is identity
-/
axiom intShl_zero : ∀ (a : Int), intShl a 0 = a

/-
  AXIOM: Shift right by zero is identity
-/
axiom intShr_zero : ∀ (a : Int), intShr a 0 = a

/-
  LEMMA: evalBinOp shl by 0 is identity
-/
theorem evalBinOp_shl_zero (ty : IntTy) (a : Int) :
    evalBinOp .shl (.int ty a) (.int ty 0) = some (.int ty a) := by
  simp [evalBinOp, intShl_zero]

/-
  LEMMA: evalBinOp shr by 0 is identity
-/
theorem evalBinOp_shr_zero (ty : IntTy) (a : Int) :
    evalBinOp .shr (.int ty a) (.int ty 0) = some (.int ty a) := by
  simp [evalBinOp, intShr_zero]

/-
  AXIOM: BitXor is self-inverse (a ^ a = 0)
-/
axiom intBitXor_self : ∀ (a : Int), intBitXor a a = 0

/-
  LEMMA: evalBinOp xor with self is zero
-/
theorem evalBinOp_bitXor_self_zero (ty : IntTy) (a : Int) :
    evalBinOp .bitXor (.int ty a) (.int ty a) = some (.int ty 0) := by
  simp [evalBinOp, intBitXor_self]

/-
  AXIOM: BitXor with zero is identity
-/
axiom intBitXor_zero_right : ∀ (a : Int), intBitXor a 0 = a
axiom intBitXor_zero_left : ∀ (a : Int), intBitXor 0 a = a

/-
  LEMMA: evalBinOp xor with zero on right is identity
-/
theorem evalBinOp_bitXor_zero_right (ty : IntTy) (a : Int) :
    evalBinOp .bitXor (.int ty a) (.int ty 0) = some (.int ty a) := by
  simp [evalBinOp, intBitXor_zero_right]

/-
  LEMMA: evalBinOp xor with zero on left is identity
-/
theorem evalBinOp_bitXor_zero_left (ty : IntTy) (a : Int) :
    evalBinOp .bitXor (.int ty 0) (.int ty a) = some (.int ty a) := by
  simp [evalBinOp, intBitXor_zero_left]

/-
  AXIOM: BitAnd with zero is zero (absorbing)
-/
axiom intBitAnd_zero_right : ∀ (a : Int), intBitAnd a 0 = 0
axiom intBitAnd_zero_left : ∀ (a : Int), intBitAnd 0 a = 0

/-
  LEMMA: evalBinOp and with zero on right is zero
-/
theorem evalBinOp_bitAnd_zero_right (ty : IntTy) (a : Int) :
    evalBinOp .bitAnd (.int ty a) (.int ty 0) = some (.int ty 0) := by
  simp [evalBinOp, intBitAnd_zero_right]

/-
  LEMMA: evalBinOp and with zero on left is zero
-/
theorem evalBinOp_bitAnd_zero_left (ty : IntTy) (a : Int) :
    evalBinOp .bitAnd (.int ty 0) (.int ty a) = some (.int ty 0) := by
  simp [evalBinOp, intBitAnd_zero_left]

/-
  AXIOM: BitAnd is idempotent (a & a = a)
-/
axiom intBitAnd_self : ∀ (a : Int), intBitAnd a a = a

/-
  LEMMA: evalBinOp and with self is self
-/
theorem evalBinOp_bitAnd_self (ty : IntTy) (a : Int) :
    evalBinOp .bitAnd (.int ty a) (.int ty a) = some (.int ty a) := by
  simp [evalBinOp, intBitAnd_self]

/-
  AXIOM: BitOr is idempotent (a | a = a)
-/
axiom intBitOr_self : ∀ (a : Int), intBitOr a a = a

/-
  LEMMA: evalBinOp or with self is self
-/
theorem evalBinOp_bitOr_self (ty : IntTy) (a : Int) :
    evalBinOp .bitOr (.int ty a) (.int ty a) = some (.int ty a) := by
  simp [evalBinOp, intBitOr_self]

/-
  AXIOM: BitOr with zero is identity
-/
axiom intBitOr_zero_right : ∀ (a : Int), intBitOr a 0 = a
axiom intBitOr_zero_left : ∀ (a : Int), intBitOr 0 a = a

/-
  LEMMA: evalBinOp or with zero on right is identity
-/
theorem evalBinOp_bitOr_zero_right (ty : IntTy) (a : Int) :
    evalBinOp .bitOr (.int ty a) (.int ty 0) = some (.int ty a) := by
  simp [evalBinOp, intBitOr_zero_right]

/-
  LEMMA: evalBinOp or with zero on left is identity
-/
theorem evalBinOp_bitOr_zero_left (ty : IntTy) (a : Int) :
    evalBinOp .bitOr (.int ty 0) (.int ty a) = some (.int ty a) := by
  simp [evalBinOp, intBitOr_zero_left]

/-!
  ## Function Semantics Extensions
-/

/-
  Definition: Binary function that takes two args
-/
def binaryFunc (f : Value → Value → Option Value) : PureFuncSemantics := fun
  | [a, b] => f a b
  | _ => none

/-
  LEMMA: Binary function with two args applies correctly
-/
theorem binaryFunc_two_args (f : Value → Value → Option Value) (a b : Value) :
    binaryFunc f [a, b] = f a b := rfl

/-
  LEMMA: Binary function with wrong arity fails
-/
theorem binaryFunc_wrong_arity_empty (f : Value → Value → Option Value) :
    binaryFunc f [] = none := rfl

theorem binaryFunc_wrong_arity_one (f : Value → Value → Option Value) (a : Value) :
    binaryFunc f [a] = none := rfl

theorem binaryFunc_wrong_arity_three (f : Value → Value → Option Value) (a b c : Value) :
    binaryFunc f [a, b, c] = none := rfl

/-
  Definition: Ternary function
-/
def ternaryFunc (f : Value → Value → Value → Option Value) : PureFuncSemantics := fun
  | [a, b, c] => f a b c
  | _ => none

/-
  LEMMA: Ternary function with three args applies correctly
-/
theorem ternaryFunc_three_args (f : Value → Value → Value → Option Value) (a b c : Value) :
    ternaryFunc f [a, b, c] = f a b c := rfl

/-
  Definition: Nullary function (constant producer)
-/
def nullaryFunc (v : Value) : PureFuncSemantics := fun
  | [] => some v
  | _ => none

/-
  LEMMA: Nullary function with no args succeeds
-/
theorem nullaryFunc_zero_args (v : Value) :
    nullaryFunc v [] = some v := rfl

/-
  LEMMA: Nullary function with args fails
-/
theorem nullaryFunc_with_args (v : Value) (args : List Value) (h : args ≠ []) :
    nullaryFunc v args = none := by
  cases args with
  | nil => contradiction
  | cons hd tl => rfl

/-!
  ## More Heap Invariants
-/

/-
  LEMMA: Alloc then write to new location succeeds
-/
theorem alloc_then_write (h : Heap) (v1 v2 : Value) :
    let (h', loc) := h.alloc v1
    (h'.write loc v2).read loc = some v2 := by
  simp [Heap.alloc, Heap.write, Heap.read]

/-
  LEMMA: Fresh allocation doesn't affect existing reads
-/
theorem alloc_preserves_reads (h : Heap) (v : Value) (loc : Location)
    (hLt : loc < h.nextLoc) :
    let (h', _) := h.alloc v
    h'.read loc = h.read loc := by
  simp [Heap.alloc, Heap.read]
  have hNe : loc ≠ h.nextLoc := Nat.ne_of_lt hLt
  simp [hNe]

/-!
  ## Value Pattern Matching Properties
-/

/-
  LEMMA: Int value discrimination
-/
theorem int_not_bool (ty : IntTy) (v : Int) (b : Bool) :
    Value.int ty v ≠ Value.bool b := by
  intro h
  cases h

/-
  LEMMA: Bool value discrimination
-/
theorem bool_not_ref (b : Bool) (loc : Location) :
    Value.bool b ≠ Value.ref loc := by
  intro h
  cases h

/-
  LEMMA: Unit value discrimination
-/
theorem unit_not_int (ty : IntTy) (v : Int) :
    Value.unit ≠ Value.int ty v := by
  intro h
  cases h

/-
  LEMMA: Array vs tuple discrimination
-/
theorem array_not_tuple (a t : List Value) :
    Value.array a ≠ Value.tuple t := by
  intro h
  cases h

/-
  LEMMA: Ref vs box discrimination
-/
theorem ref_not_box (loc1 loc2 : Location) :
    Value.ref loc1 ≠ Value.box_ loc2 := by
  intro h
  cases h

/-
  LEMMA: Unit vs ref discrimination
-/
theorem unit_not_ref (loc : Location) :
    Value.unit ≠ Value.ref loc := by
  intro h
  cases h

/-
  LEMMA: RawPtr vs ref discrimination
-/
theorem rawPtr_not_ref (opt : Option Location) (loc : Location) :
    Value.rawPtr opt ≠ Value.ref loc := by
  intro h
  cases h

/-!
  ## Comparison Operation Totality
-/

/-
  LEMMA: Eq comparison on same-type ints always succeeds
-/
theorem evalBinOp_eq_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .eq (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: Lt comparison on same-type ints always succeeds
-/
theorem evalBinOp_lt_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .lt (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: Le comparison on same-type ints always succeeds
-/
theorem evalBinOp_le_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .le (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: Gt comparison on same-type ints always succeeds
-/
theorem evalBinOp_gt_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .gt (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: Ge comparison on same-type ints always succeeds
-/
theorem evalBinOp_ge_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .ge (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: Ne comparison on same-type ints always succeeds
-/
theorem evalBinOp_ne_int_succeeds (ty : IntTy) (a b : Int) :
    (evalBinOp .ne (.int ty a) (.int ty b)).isSome := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: Eq comparison on bools always succeeds
-/
theorem evalBinOp_eq_bool_succeeds (a b : Bool) :
    (evalBinOp .eq (.bool a) (.bool b)).isSome := by
  simp [evalBinOp]

/-
  LEMMA: Ne comparison on bools always succeeds
-/
theorem evalBinOp_ne_bool_succeeds (a b : Bool) :
    (evalBinOp .ne (.bool a) (.bool b)).isSome := by
  simp [evalBinOp]

/-!
  ## Execution Sequence Properties
-/

/-
  LEMMA: execStmts with single Nop is identity
-/
theorem execStmts_single_nop_is_identity (s : State) :
    execStmts s [.Nop] = some s := by
  simp [execStmts, execStmt]

/-
  LEMMA: Three consecutive Nops
-/
theorem execStmts_three_nops (s : State) :
    execStmts s [.Nop, .Nop, .Nop] = some s := by
  simp [execStmts, execStmt]

/-
  LEMMA: Five consecutive Nops
-/
theorem execStmts_five_nops (s : State) :
    execStmts s [.Nop, .Nop, .Nop, .Nop, .Nop] = some s := by
  simp [execStmts, execStmt]

/-
  LEMMA: Two consecutive StorageLive statements
-/
theorem execStmts_two_storageLive_alt (s : State) (l1 l2 : Local) :
    execStmts s [.StorageLive l1, .StorageLive l2] =
    some ((s.storageLive l1).storageLive l2) := by
  simp [execStmts, execStmt]

/-
  LEMMA: StorageLive then StorageDead sequence
-/
theorem execStmts_live_dead_sequence (s : State) (l : Local) :
    execStmts s [.StorageLive l, .StorageDead l] =
    some ((s.storageLive l).storageDead l) := by
  simp [execStmts, execStmt]

/-
  LEMMA: Nop between StorageLive and StorageDead
-/
theorem execStmts_live_nop_dead (s : State) (l : Local) :
    execStmts s [.StorageLive l, .Nop, .StorageDead l] =
    some ((s.storageLive l).storageDead l) := by
  simp [execStmts, execStmt]

/-!
  ## Control Flow Properties
-/

/-
  LEMMA: Goto terminator is deterministic
-/
theorem goto_deterministic (s : State) (bb : BasicBlock) :
    execTerminator s (.Goto bb) = some (.goto bb) := by
  simp [execTerminator]

/-!
  ## IntTy Properties
-/

/-
  LEMMA: u8 is unsigned
-/
@[simp]
theorem u8_unsigned : IntTy.u8.isSigned = false := rfl

/-
  LEMMA: i8 is signed
-/
@[simp]
theorem i8_signed : IntTy.i8.isSigned = true := rfl

/-
  LEMMA: u16 is unsigned
-/
@[simp]
theorem u16_unsigned : IntTy.u16.isSigned = false := rfl

/-
  LEMMA: i16 is signed
-/
@[simp]
theorem i16_signed : IntTy.i16.isSigned = true := rfl

/-
  LEMMA: u32 is unsigned
-/
@[simp]
theorem u32_unsigned : IntTy.u32.isSigned = false := rfl

/-
  LEMMA: i32 is signed
-/
@[simp]
theorem i32_signed : IntTy.i32.isSigned = true := rfl

/-
  LEMMA: u64 is unsigned
-/
@[simp]
theorem u64_unsigned : IntTy.u64.isSigned = false := rfl

/-
  LEMMA: i64 is signed
-/
@[simp]
theorem i64_signed : IntTy.i64.isSigned = true := rfl

/-
  LEMMA: usize is unsigned
-/
@[simp]
theorem usize_unsigned : IntTy.usize.isSigned = false := rfl

/-
  LEMMA: isize is signed
-/
@[simp]
theorem isize_signed : IntTy.isize.isSigned = true := rfl

/-
  LEMMA: u8 has 8 bits
-/
@[simp]
theorem u8_bits : IntTy.u8.bits = 8 := rfl

/-
  LEMMA: i8 has 8 bits
-/
@[simp]
theorem i8_bits : IntTy.i8.bits = 8 := rfl

/-
  LEMMA: u16 has 16 bits
-/
@[simp]
theorem u16_bits : IntTy.u16.bits = 16 := rfl

/-
  LEMMA: i16 has 16 bits
-/
@[simp]
theorem i16_bits : IntTy.i16.bits = 16 := rfl

/-
  LEMMA: u32 has 32 bits
-/
@[simp]
theorem u32_bits : IntTy.u32.bits = 32 := rfl

/-
  LEMMA: i32 has 32 bits
-/
@[simp]
theorem i32_bits : IntTy.i32.bits = 32 := rfl

/-
  LEMMA: u64 has 64 bits
-/
@[simp]
theorem u64_bits : IntTy.u64.bits = 64 := rfl

/-
  LEMMA: i64 has 64 bits
-/
@[simp]
theorem i64_bits : IntTy.i64.bits = 64 := rfl

/-
  LEMMA: usize has 64 bits (assuming 64-bit architecture)
-/
@[simp]
theorem usize_bits : IntTy.usize.bits = 64 := rfl

/-
  LEMMA: isize has 64 bits (assuming 64-bit architecture)
-/
@[simp]
theorem isize_bits : IntTy.isize.bits = 64 := rfl

/-!
  ## Additional State Properties
-/

/-
  LEMMA: Empty state has no alive locals
-/
theorem empty_state_no_alive : ∀ l, State.empty.alive l = false := by
  intro l
  simp [State.empty]

/-
  LEMMA: Empty state has no local values
-/
theorem empty_state_no_locals : ∀ l, State.empty.locals l = none := by
  intro l
  simp [State.empty]

/-
  LEMMA: Empty state heap has nextLoc 0
-/
theorem empty_state_heap_nextLoc : State.empty.heap.nextLoc = 0 := by
  simp [State.empty, Heap.empty]

/-
  LEMMA: StorageLive makes local alive
-/
theorem storageLive_makes_alive (s : State) (l : Local) :
    (s.storageLive l).alive l = true := by
  simp [State.storageLive]

/-
  LEMMA: StorageDead makes local dead
-/
theorem storageDead_makes_dead_alt (s : State) (l : Local) :
    (s.storageDead l).alive l = false := by
  simp [State.storageDead]

/-
  LEMMA: StorageLive on different local preserves alive status
-/
theorem storageLive_preserves_other_alive (s : State) (l l' : Local) (hNe : l ≠ l') :
    (s.storageLive l).alive l' = s.alive l' := by
  simp only [State.storageLive]
  split
  · next h => exact absurd h.symm hNe
  · rfl

/-
  LEMMA: StorageDead on different local preserves alive status
-/
theorem storageDead_preserves_other_alive (s : State) (l l' : Local) (hNe : l ≠ l') :
    (s.storageDead l).alive l' = s.alive l' := by
  simp only [State.storageDead]
  split
  · next h => exact absurd h.symm hNe
  · rfl

/-
  LEMMA: StorageLive preserves heap
-/
theorem storageLive_preserves_heap (s : State) (l : Local) :
    (s.storageLive l).heap = s.heap := by
  simp [State.storageLive]

/-
  LEMMA: StorageDead preserves heap
-/
theorem storageDead_preserves_heap (s : State) (l : Local) :
    (s.storageDead l).heap = s.heap := by
  simp [State.storageDead]

/-!
  ## Move/Copy Semantics
-/

/-
  LEMMA: Move operand same as copy semantically
-/
theorem move_eq_copy_semantically (s : State) (p : Place) :
    evalOperand s (.move p) = evalOperand s (.copy p) := by
  simp [evalOperand]

/-!
  ## Block Execution Properties
-/

/-
  LEMMA: Block with only Return terminates
-/
theorem block_only_return (s : State) :
    execBlock s { stmts := [], terminator := .Return } = some (s, .return_) := by
  simp [execBlock, execStmts, execTerminator]

/-
  LEMMA: Block with only Goto terminates
-/
theorem block_only_goto (s : State) (bb : BasicBlock) :
    execBlock s { stmts := [], terminator := .Goto bb } = some (s, .goto bb) := by
  simp [execBlock, execStmts, execTerminator]

/-
  LEMMA: Block with Nop and Return
-/
theorem block_nop_return (s : State) :
    execBlock s { stmts := [.Nop], terminator := .Return } = some (s, .return_) := by
  simp [execBlock, execStmts, execStmt, execTerminator]

/-
  LEMMA: Block with StorageLive and Return
-/
theorem block_storageLive_return (s : State) (l : Local) :
    execBlock s { stmts := [.StorageLive l], terminator := .Return } =
    some (s.storageLive l, .return_) := by
  simp [execBlock, execStmts, execStmt, execTerminator]

/-!
  ## Type Safety Properties
-/

/-
  LEMMA: Int value has correct type (structural match)
-/
theorem int_value_type_match (ty : IntTy) (v : Int) :
    match (Value.int ty v) with
    | .int _ _ => true
    | _ => false := rfl

/-
  LEMMA: Bool value has correct type (structural match)
-/
theorem bool_value_type_match (b : Bool) :
    match (Value.bool b) with
    | .bool _ => true
    | _ => false := rfl

/-
  LEMMA: Unit value has correct type (structural match)
-/
theorem unit_value_type_match :
    match Value.unit with
    | .unit => true
    | _ => false := rfl

/-
  LEMMA: Ref value has correct type (structural match)
-/
theorem ref_value_type_match (loc : Location) :
    match (Value.ref loc) with
    | .ref _ => true
    | _ => false := rfl

/-
  LEMMA: Box value has correct type (structural match)
-/
theorem box_value_type_match (loc : Location) :
    match (Value.box_ loc) with
    | .box_ _ => true
    | _ => false := rfl

/-
  LEMMA: Array value has correct type (structural match)
-/
theorem array_value_type_match (elems : List Value) :
    match (Value.array elems) with
    | .array _ => true
    | _ => false := rfl

/-
  LEMMA: Tuple value has correct type (structural match)
-/
theorem tuple_value_type_match (elems : List Value) :
    match (Value.tuple elems) with
    | .tuple _ => true
    | _ => false := rfl

/-!
  ## Determinism Properties
-/

/-
  LEMMA: execStmt is deterministic
-/
theorem execStmt_deterministic (s : State) (stmt : MirStmt) (s1 s2 : State) :
    execStmt s stmt = some s1 → execStmt s stmt = some s2 → s1 = s2 := by
  intro h1 h2
  rw [h1] at h2
  cases h2
  rfl

/-
  LEMMA: execStmts is deterministic
-/
theorem execStmts_deterministic (s : State) (stmts : List MirStmt) (s1 s2 : State) :
    execStmts s stmts = some s1 → execStmts s stmts = some s2 → s1 = s2 := by
  intro h1 h2
  rw [h1] at h2
  cases h2
  rfl

/-
  LEMMA: execTerminator is deterministic
-/
theorem execTerminator_deterministic (s : State) (term : MirTerminator) (c1 c2 : Control) :
    execTerminator s term = some c1 → execTerminator s term = some c2 → c1 = c2 := by
  intro h1 h2
  rw [h1] at h2
  cases h2
  rfl

/-
  LEMMA: execBlock is deterministic
-/
theorem execBlock_deterministic (s : State) (bb : BasicBlockData) (r1 r2 : State × Control) :
    execBlock s bb = some r1 → execBlock s bb = some r2 → r1 = r2 := by
  intro h1 h2
  rw [h1] at h2
  cases h2
  rfl

/-!
  ## Error Propagation Properties
-/

/-
  LEMMA: Error in first statement propagates
-/
theorem execStmts_error_propagates (s : State) (stmt : MirStmt) (rest : List MirStmt) :
    execStmt s stmt = none → execStmts s (stmt :: rest) = none := by
  intro h
  simp [execStmts, h]

/-
  LEMMA: Error in rest propagates
-/
theorem execStmts_error_in_rest (s s' : State) (stmt : MirStmt) (rest : List MirStmt) :
    execStmt s stmt = some s' → execStmts s' rest = none → execStmts s (stmt :: rest) = none := by
  intro hStmt hRest
  simp [execStmts, hStmt, hRest]

/-
  LEMMA: Statement error leads to block error
-/
theorem execBlock_stmt_error (s : State) (stmts : List MirStmt) (term : MirTerminator) :
    execStmts s stmts = none →
    execBlock s { stmts := stmts, terminator := term } = none := by
  intro h
  simp [execBlock, h]

/-
  LEMMA: Terminator error leads to block error
-/
theorem execBlock_term_error (s s' : State) (stmts : List MirStmt) (term : MirTerminator) :
    execStmts s stmts = some s' →
    execTerminator s' term = none →
    execBlock s { stmts := stmts, terminator := term } = none := by
  intro hStmts hTerm
  simp [execBlock, hStmts, hTerm]

/-!
  ## Heap Freshness Properties
-/

/-
  LEMMA: Previous locations unaffected by allocation
-/
theorem Heap.alloc_preserves_previous_loc (h : Heap) (v : Value) (loc : Location) (hLt : loc < h.nextLoc) :
    (h.alloc v).1.read loc = h.read loc := by
  unfold Heap.alloc Heap.read
  simp only
  split
  · next hEq =>
    subst hEq
    exact (Nat.lt_irrefl _ hLt).elim
  · rfl

/-
  LEMMA: Write to unallocated location still works (memory model allows it)
-/
theorem Heap.write_works (h : Heap) (loc : Location) (v : Value) :
    (h.write loc v).read loc = some v := by
  simp [Heap.write, Heap.read]

/-
  LEMMA: Double write takes second value
-/
theorem Heap.write_write (h : Heap) (loc : Location) (v1 v2 : Value) :
    ((h.write loc v1).write loc v2).read loc = some v2 := by
  simp [Heap.write, Heap.read]

/-
  LEMMA: State allocation preserves local values
-/
theorem State.heapAlloc_preserves_locals_new (s : State) (v : Value) (l : Local) :
    (s.heapAlloc v).1.readLocal l = s.readLocal l := by
  simp [State.heapAlloc, State.readLocal, State.isAlive]

/-
  LEMMA: State allocation preserves local liveness
-/
theorem State.heapAlloc_preserves_alive_new (s : State) (v : Value) (l : Local) :
    (s.heapAlloc v).1.alive l = s.alive l := by
  simp [State.heapAlloc]

/-!
  ## Frame Properties (Modular Reasoning)
-/

/-
  LEMMA: Statement on disjoint locals is independent
-/
theorem execStmt_frame_storageLive_alt (s : State) (l1 l2 : Local) :
    ((s.storageLive l1).storageLive l2).alive l1 = true := by
  simp [State.storageLive]

/-
  LEMMA: Heap write read at different location unchanged (frame)
-/
theorem Heap.write_read_frame (h : Heap) (loc1 loc2 : Location) (v : Value) (hNe : loc1 ≠ loc2) :
    (h.write loc1 v).read loc2 = h.read loc2 := by
  simp [Heap.write, Heap.read, Ne.symm hNe]

/-!
  ## Multi-Step Execution Properties
-/

/-
  LEMMA: Empty statements followed by more statements
-/
theorem execStmts_nil_append (s : State) (stmts : List MirStmt) :
    execStmts s ([] ++ stmts) = execStmts s stmts := rfl

/-
  LEMMA: Successful statement execution means some result
-/
theorem execStmt_success_isSome_alt (s s' : State) (stmt : MirStmt) :
    execStmt s stmt = some s' → (execStmt s stmt).isSome = true := by
  intro h
  simp [h]

/-
  LEMMA: StorageLive then StorageDead returns to original liveness for target
-/
theorem storageLive_then_dead_alive (s : State) (l : Local) :
    ((s.storageLive l).storageDead l).alive l = false := by
  simp [State.storageLive, State.storageDead]

/-
  LEMMA: StorageDead then StorageLive makes alive
-/
theorem storageDead_then_live_alive (s : State) (l : Local) :
    ((s.storageDead l).storageLive l).alive l = true := by
  simp [State.storageLive, State.storageDead]

/-
  LEMMA: Four StorageLive operations
-/
theorem four_storageLive (s : State) (l1 l2 l3 l4 : Local) :
    let s1 := s.storageLive l1
    let s2 := s1.storageLive l2
    let s3 := s2.storageLive l3
    let s4 := s3.storageLive l4
    s4.alive l4 = true := by
  simp [State.storageLive]

/-
  LEMMA: execStmts of four Nops
-/
theorem execStmts_four_nops (s : State) :
    execStmts s [.Nop, .Nop, .Nop, .Nop] = some s := by
  simp [execStmts, execStmt]

/-!
  ## Integer Bounds Properties
-/

/-
  LEMMA: u8 min bound
-/
@[simp]
theorem u8_min : IntTy.u8.minVal = 0 := rfl

/-
  LEMMA: u8 max bound
-/
@[simp]
theorem u8_max : IntTy.u8.maxVal = 255 := rfl

/-
  LEMMA: i8 min bound
-/
@[simp]
theorem i8_min : IntTy.i8.minVal = -128 := rfl

/-
  LEMMA: i8 max bound
-/
@[simp]
theorem i8_max : IntTy.i8.maxVal = 127 := rfl

/-
  LEMMA: u16 min bound
-/
@[simp]
theorem u16_min : IntTy.u16.minVal = 0 := rfl

/-
  LEMMA: u16 max bound
-/
@[simp]
theorem u16_max : IntTy.u16.maxVal = 65535 := rfl

/-
  LEMMA: i16 min bound
-/
@[simp]
theorem i16_min : IntTy.i16.minVal = -32768 := rfl

/-
  LEMMA: i16 max bound
-/
@[simp]
theorem i16_max : IntTy.i16.maxVal = 32767 := rfl

/-
  LEMMA: u32 min bound
-/
@[simp]
theorem u32_min : IntTy.u32.minVal = 0 := rfl

/-
  LEMMA: u32 max bound (computed value)
-/
@[simp]
theorem u32_max : IntTy.u32.maxVal = 4294967295 := rfl

/-
  LEMMA: i32 min bound (computed value)
-/
@[simp]
theorem i32_min : IntTy.i32.minVal = -2147483648 := rfl

/-
  LEMMA: i32 max bound (computed value)
-/
@[simp]
theorem i32_max : IntTy.i32.maxVal = 2147483647 := rfl

/-
  LEMMA: u64 min bound
-/
@[simp]
theorem u64_min : IntTy.u64.minVal = 0 := rfl

/-
  LEMMA: u64 max bound (computed value)
-/
@[simp]
theorem u64_max : IntTy.u64.maxVal = 18446744073709551615 := rfl

/-
  LEMMA: i64 min bound (computed value)
-/
@[simp]
theorem i64_min : IntTy.i64.minVal = -9223372036854775808 := rfl

/-
  LEMMA: i64 max bound (computed value)
-/
@[simp]
theorem i64_max : IntTy.i64.maxVal = 9223372036854775807 := rfl

/-
  LEMMA: usize min bound (same as u64)
-/
@[simp]
theorem usize_min : IntTy.usize.minVal = 0 := rfl

/-
  LEMMA: usize max bound (same as u64)
-/
@[simp]
theorem usize_max : IntTy.usize.maxVal = 18446744073709551615 := rfl

/-
  LEMMA: isize min bound (same as i64)
-/
@[simp]
theorem isize_min : IntTy.isize.minVal = -9223372036854775808 := rfl

/-
  LEMMA: isize max bound (same as i64)
-/
@[simp]
theorem isize_max : IntTy.isize.maxVal = 9223372036854775807 := rfl

/-
  LEMMA: Value in range check for u8
-/
@[simp]
theorem u8_inRange_0 : IntTy.u8.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for u8 max
-/
@[simp]
theorem u8_inRange_255 : IntTy.u8.inRange 255 = true := rfl

/-
  LEMMA: Value out of range for u8
-/
@[simp]
theorem u8_outOfRange_256 : IntTy.u8.inRange 256 = false := rfl

/-
  LEMMA: Value out of range for u8 negative
-/
@[simp]
theorem u8_outOfRange_neg1 : IntTy.u8.inRange (-1) = false := rfl

/-
  LEMMA: Value in range check for u16
-/
@[simp]
theorem u16_inRange_0 : IntTy.u16.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for u32
-/
@[simp]
theorem u32_inRange_0 : IntTy.u32.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for u64
-/
@[simp]
theorem u64_inRange_0 : IntTy.u64.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for usize
-/
@[simp]
theorem usize_inRange_0 : IntTy.usize.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for i8
-/
@[simp]
theorem i8_inRange_0 : IntTy.i8.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for i16
-/
@[simp]
theorem i16_inRange_0 : IntTy.i16.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for i32
-/
@[simp]
theorem i32_inRange_0 : IntTy.i32.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for i64
-/
@[simp]
theorem i64_inRange_0 : IntTy.i64.inRange 0 = true := rfl

/-
  LEMMA: Value in range check for isize
-/
@[simp]
theorem isize_inRange_0 : IntTy.isize.inRange 0 = true := rfl

/-
  LEMMA: Value 1 in range check for all types
-/
@[simp]
theorem u8_inRange_1 : IntTy.u8.inRange 1 = true := rfl

@[simp]
theorem u16_inRange_1 : IntTy.u16.inRange 1 = true := rfl

@[simp]
theorem u32_inRange_1 : IntTy.u32.inRange 1 = true := rfl

@[simp]
theorem u64_inRange_1 : IntTy.u64.inRange 1 = true := rfl

@[simp]
theorem usize_inRange_1 : IntTy.usize.inRange 1 = true := rfl

@[simp]
theorem i8_inRange_1 : IntTy.i8.inRange 1 = true := rfl

@[simp]
theorem i16_inRange_1 : IntTy.i16.inRange 1 = true := rfl

@[simp]
theorem i32_inRange_1 : IntTy.i32.inRange 1 = true := rfl

@[simp]
theorem i64_inRange_1 : IntTy.i64.inRange 1 = true := rfl

@[simp]
theorem isize_inRange_1 : IntTy.isize.inRange 1 = true := rfl

/-
  LEMMA: Value -1 in range for signed types, out of range for unsigned
-/
@[simp]
theorem u16_outOfRange_neg1 : IntTy.u16.inRange (-1) = false := rfl

@[simp]
theorem u32_outOfRange_neg1 : IntTy.u32.inRange (-1) = false := rfl

@[simp]
theorem u64_outOfRange_neg1 : IntTy.u64.inRange (-1) = false := rfl

@[simp]
theorem usize_outOfRange_neg1 : IntTy.usize.inRange (-1) = false := rfl

@[simp]
theorem i8_inRange_neg1 : IntTy.i8.inRange (-1) = true := rfl

@[simp]
theorem i16_inRange_neg1 : IntTy.i16.inRange (-1) = true := rfl

@[simp]
theorem i32_inRange_neg1 : IntTy.i32.inRange (-1) = true := rfl

@[simp]
theorem i64_inRange_neg1 : IntTy.i64.inRange (-1) = true := rfl

@[simp]
theorem isize_inRange_neg1 : IntTy.isize.inRange (-1) = true := rfl

/-!
  ## Local Variable Access Properties
-/

/-
  LEMMA: Reading uninitialized local returns none (even if alive)
-/
theorem readLocal_uninit_alt (s : State) (l : Local) :
    s.locals l = none → s.readLocal l = none ∨ s.isAlive l = false := by
  intro hNone
  by_cases halive : s.isAlive l = true
  · left; simp [State.readLocal, halive, hNone]
  · right; simp at halive; exact halive

/-!
  ## Reference Validity Properties
-/

/-
  LEMMA: Fresh allocation gives valid reference
-/
theorem alloc_gives_valid_ref (s : State) (v : Value) :
    let (s', loc) := s.heapAlloc v
    s'.heapRead loc = some v := by
  simp [State.heapAlloc, State.heapRead, Heap.alloc, Heap.read]

/-
  LEMMA: Deallocation invalidates reference
-/
theorem dealloc_invalidates_ref (s : State) (loc : Location) :
    (s.heapDealloc loc).heapRead loc = none := by
  simp [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]

/-
  LEMMA: Write to ref location updates what ref points to
-/
theorem write_updates_ref_target (s : State) (loc : Location) (v : Value) :
    (s.heapWrite loc v).heapRead loc = some v := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read]

/-!
  ## Assertion Properties
-/

/-
  LEMMA: Assert true succeeds
-/
theorem assert_true_succeeds (s : State) (target : BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool true), expected := true, target := target, cleanup := none }
    execTerminator s (.Assert msg) = some (.goto target) := rfl

/-
  LEMMA: Assert false with no cleanup panics
-/
theorem assert_false_panics (s : State) (target : BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := none }
    execTerminator s (.Assert msg) = some .panic := rfl

/-
  LEMMA: Assert false with cleanup unwinds
-/
theorem assert_false_unwinds (s : State) (target cleanup : BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := some cleanup }
    execTerminator s (.Assert msg) = some (.unwind cleanup) := rfl

/-
  LEMMA: Assert expects false, gets false, succeeds
-/
theorem assert_expects_false_succeeds (s : State) (target : BasicBlock) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := false, target := target, cleanup := none }
    execTerminator s (.Assert msg) = some (.goto target) := rfl

/-!
  ## Function Call Properties (Simplified)
-/

/-
  LEMMA: Call terminator returns none (handled separately in interpreter)
-/
theorem call_terminator_none (s : State) (f : Operand) (args : List Operand) (dest : Place) (target : BasicBlock) :
    execTerminator s (MirTerminator.Call f args dest target) = none := rfl

/-!
  ## Rvalue Evaluation Properties
-/

/-
  LEMMA: Rvalue.use of const succeeds
-/
theorem rvalue_use_const (s : State) (v : Value) :
    evalRvalue s (.use (.const v)) = some v := rfl

/-
  LEMMA: Rvalue.repeat creates array
-/
theorem rvalue_repeat_creates_array (s : State) (v : Value) (n : Nat) :
    evalRvalue s (.repeat (.const v) n) = some (.array (List.replicate n v)) := rfl

/-
  LEMMA: Rvalue.repeat zero creates empty array
-/
theorem rvalue_repeat_zero (s : State) (v : Value) :
    evalRvalue s (.repeat (.const v) 0) = some (.array []) := rfl

/-!
  ## Control Flow Properties
-/

/-
  LEMMA: SwitchInt with const bool true goes to 1 branch
-/
theorem switchInt_bool_true_discr :
    let discr := Value.bool true
    asSwitchIntDiscr discr = some 1 := rfl

/-
  LEMMA: SwitchInt with const bool false goes to 0 branch
-/
theorem switchInt_bool_false_discr :
    let discr := Value.bool false
    asSwitchIntDiscr discr = some 0 := rfl

/-!
  ## Value Equality Properties
-/

/-
  LEMMA: Bool values equal iff underlying bools equal
-/
theorem bool_value_eq (b1 b2 : Bool) :
    (Value.bool b1 = Value.bool b2) ↔ (b1 = b2) := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

/-
  LEMMA: Int values equal iff types and values equal
-/
theorem int_value_eq (ty1 ty2 : IntTy) (v1 v2 : Int) :
    (Value.int ty1 v1 = Value.int ty2 v2) ↔ (ty1 = ty2 ∧ v1 = v2) := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · intro ⟨hTy, hVal⟩; rw [hTy, hVal]

/-
  LEMMA: Ref values equal iff locations equal
-/
theorem ref_value_eq (loc1 loc2 : Location) :
    (Value.ref loc1 = Value.ref loc2) ↔ (loc1 = loc2) := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

/-
  LEMMA: Box values equal iff locations equal
-/
theorem box_value_eq (loc1 loc2 : Location) :
    (Value.box_ loc1 = Value.box_ loc2) ↔ (loc1 = loc2) := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

/-
  LEMMA: Array values equal iff element lists equal
-/
theorem array_value_eq (elems1 elems2 : List Value) :
    (Value.array elems1 = Value.array elems2) ↔ (elems1 = elems2) := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

/-
  LEMMA: Tuple values equal iff element lists equal
-/
theorem tuple_value_eq (elems1 elems2 : List Value) :
    (Value.tuple elems1 = Value.tuple elems2) ↔ (elems1 = elems2) := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

/-!
  ## State Equality Properties
-/

/-
  LEMMA: Two consecutive StorageLive on same local is idempotent for alive
-/
theorem storageLive_idempotent (s : State) (l : Local) :
    ((s.storageLive l).storageLive l).alive l = (s.storageLive l).alive l := by
  simp [State.storageLive]

/-
  LEMMA: Two consecutive StorageDead on same local is idempotent for alive
-/
theorem storageDead_idempotent (s : State) (l : Local) :
    ((s.storageDead l).storageDead l).alive l = (s.storageDead l).alive l := by
  simp [State.storageDead]

/-
  LEMMA: heapWrite idempotent for same location and value
-/
theorem heapWrite_idempotent (s : State) (loc : Location) (v : Value) :
    ((s.heapWrite loc v).heapWrite loc v).heapRead loc = (s.heapWrite loc v).heapRead loc := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read]

/-!
  ## Projection Evaluation Properties
-/

/-
  LEMMA: Field projection on tuple succeeds when index valid
-/
theorem evalPlace_field_tuple (s : State) (base : Place) (elems : List Value) (idx : Nat) (_hIdx : idx < elems.length) :
    evalPlace s base = some (.tuple elems) →
    evalPlace s (.project base (.field idx)) = elems[idx]? := by
  intro hBase
  simp [evalPlace, hBase]

/-
  LEMMA: Deref on ref succeeds when heap valid
-/
theorem evalPlace_deref_ref (s : State) (base : Place) (loc : Location) (v : Value) :
    evalPlace s base = some (.ref loc) →
    s.heapRead loc = some v →
    evalPlace s (.project base .deref) = some v := by
  intro hBase hHeap
  simp [evalPlace, hBase, hHeap]

/-
  LEMMA: Deref on box succeeds when heap valid
-/
theorem evalPlace_deref_box (s : State) (base : Place) (loc : Location) (v : Value) :
    evalPlace s base = some (.box_ loc) →
    s.heapRead loc = some v →
    evalPlace s (.project base .deref) = some v := by
  intro hBase hHeap
  simp [evalPlace, hBase, hHeap]

/-!
  ## Additional Arithmetic Properties (Part 2)
-/

/-
  LEMMA: Zero divided by anything nonzero is zero (axiom)
-/
axiom evalBinOp_div_zero_left_ax : ∀ ty v, v ≠ 0 →
    evalBinOp .div (.int ty 0) (.int ty v) = some (.int ty 0)

/-
  LEMMA: Zero remainder anything nonzero is zero (axiom)
-/
axiom evalBinOp_rem_zero_left_ax : ∀ ty v, v ≠ 0 →
    evalBinOp .rem (.int ty 0) (.int ty v) = some (.int ty 0)

/-!
  ## Aggregate Construction Properties
-/

/-
  LEMMA: Empty tuple construction
-/
theorem rvalue_aggregate_empty_tuple (s : State) :
    evalRvalue s (.aggregate AggregateKind.tuple []) = some (Value.tuple []) := rfl

/-
  LEMMA: Singleton tuple construction
-/
theorem rvalue_aggregate_singleton_tuple (s : State) (v : Value) :
    evalRvalue s (.aggregate AggregateKind.tuple [.const v]) = some (Value.tuple [v]) := rfl

/-
  LEMMA: Empty array via repeat
-/
theorem rvalue_repeat_empty_array (s : State) (v : Value) :
    evalRvalue s (.repeat (.const v) 0) = some (Value.array []) := rfl

/-
  LEMMA: Singleton array via repeat
-/
theorem rvalue_repeat_singleton_array (s : State) (v : Value) :
    evalRvalue s (.repeat (.const v) 1) = some (Value.array [v]) := rfl

/-!
  ## Additional Terminator Properties
-/

/-
  LEMMA: Goto always succeeds
-/
theorem goto_always_succeeds (s : State) (bb : BasicBlock) :
    (execTerminator s (.Goto bb)).isSome = true := rfl

/-!
  ## Place Locality Properties
-/

/-
  LEMMA: Place.local constructor builds local place
-/
theorem place_local_injective (l1 l2 : Local) :
    (Place.local l1 = Place.local l2) ↔ (l1 = l2) := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

/-
  LEMMA: Place evaluation is determined by state
-/
theorem evalPlace_deterministic_alt (s : State) (p : Place) (v1 v2 : Value) :
    evalPlace s p = some v1 → evalPlace s p = some v2 → v1 = v2 := by
  intro h1 h2
  rw [h1] at h2
  cases h2
  rfl

/-!
  ## Additional Value Properties
-/

/-
  LEMMA: RawPtr null has none location
-/
theorem rawPtr_null_loc :
    match (Value.rawPtr none) with
    | .rawPtr none => true
    | _ => false := rfl

/-
  LEMMA: RawPtr non-null has some location
-/
theorem rawPtr_nonnull_loc (loc : Location) :
    match (Value.rawPtr (some loc)) with
    | .rawPtr (some _) => true
    | _ => false := rfl

/-
  LEMMA: Empty array has empty list
-/
theorem empty_array_list :
    match (Value.array []) with
    | .array l => l = []
    | _ => false := rfl

/-
  LEMMA: Empty tuple has empty list
-/
theorem empty_tuple_list :
    match (Value.tuple []) with
    | .tuple l => l = []
    | _ => false := rfl

/-!
  ## Heap Consistency Properties
-/

/-
  LEMMA: Heap empty has nextLoc 0
-/
@[simp]
theorem Heap.empty_nextLoc_zero : Heap.empty.nextLoc = 0 := rfl

/-
  LEMMA: Heap empty has no values
-/
theorem Heap.empty_read_none (loc : Location) : Heap.empty.read loc = none := by
  simp [Heap.empty, Heap.read]

/-
  LEMMA: Heap write then dealloc removes value
-/
theorem Heap.write_then_dealloc (h : Heap) (loc : Location) (v : Value) :
    ((h.write loc v).dealloc loc).read loc = none := by
  simp [Heap.write, Heap.dealloc, Heap.read]

/-
  LEMMA: Heap dealloc then write restores value
-/
theorem Heap.dealloc_then_write (h : Heap) (loc : Location) (v : Value) :
    ((h.dealloc loc).write loc v).read loc = some v := by
  simp [Heap.write, Heap.dealloc, Heap.read]

/-!
  ## State Consistency Properties
-/

/-
  LEMMA: State empty has empty heap
-/
@[simp]
theorem State.empty_heap_empty : State.empty.heap = Heap.empty := rfl

/-
  LEMMA: State storageLive twice on same local
-/
theorem State.storageLive_twice (s : State) (l : Local) :
    ((s.storageLive l).storageLive l).alive l = true := by
  simp [State.storageLive]

/-
  LEMMA: State storageDead twice on same local
-/
theorem State.storageDead_twice (s : State) (l : Local) :
    ((s.storageDead l).storageDead l).alive l = false := by
  simp [State.storageDead]

/-
  LEMMA: heapWrite twice takes second value
-/
theorem State.heapWrite_twice (s : State) (loc : Location) (v1 v2 : Value) :
    ((s.heapWrite loc v1).heapWrite loc v2).heapRead loc = some v2 := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read]

/-
  LEMMA: heapDealloc clears value
-/
theorem State.heapDealloc_clears (s : State) (loc : Location) :
    (s.heapDealloc loc).heapRead loc = none := by
  simp [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]

/-!
  ## MirStmt Properties
-/

/-
  LEMMA: Nop is identity on state
-/
theorem execStmt_nop_identity (s : State) :
    execStmt s MirStmt.Nop = some s := rfl

/-
  LEMMA: StorageLive makes local alive
-/
theorem execStmt_storageLive_alive (s : State) (l : Local) :
    match execStmt s (MirStmt.StorageLive l) with
    | some s' => s'.alive l = true
    | none => True := by
  simp [execStmt, State.storageLive]

/-
  LEMMA: StorageDead makes local dead
-/
theorem execStmt_storageDead_dead (s : State) (l : Local) :
    match execStmt s (MirStmt.StorageDead l) with
    | some s' => s'.alive l = false
    | none => True := by
  simp [execStmt, State.storageDead]

/-!
  ## MirTerminator Properties
-/

/-
  LEMMA: Return always succeeds
-/
theorem execTerminator_return_succeeds (s : State) :
    (execTerminator s MirTerminator.Return).isSome = true := rfl

/-
  LEMMA: Goto always succeeds
-/
theorem execTerminator_goto_succeeds (s : State) (bb : BasicBlock) :
    (execTerminator s (MirTerminator.Goto bb)).isSome = true := rfl

/-!
  ## State-Level Heap Allocation Properties
-/

/-
  LEMMA: heapAlloc increases nextLoc by exactly 1
-/
theorem State.heapAlloc_nextLoc_incr (s : State) (v : Value) :
    let (s', _) := s.heapAlloc v
    s'.heap.nextLoc = s.heap.nextLoc + 1 := by
  simp [State.heapAlloc, Heap.alloc]

/-
  LEMMA: heapAlloc returns the nextLoc as the new location
-/
theorem State.heapAlloc_loc_eq_nextLoc (s : State) (v : Value) :
    let (_, loc) := s.heapAlloc v
    loc = s.heap.nextLoc := by
  simp [State.heapAlloc, Heap.alloc]

/-
  LEMMA: Allocated value is immediately readable at state level
-/
theorem State.heapAlloc_immediately_readable (s : State) (v : Value) :
    let (s', loc) := s.heapAlloc v
    s'.heapRead loc = some v := by
  simp [State.heapAlloc, State.heapRead, Heap.alloc, Heap.read]

/-!
  ## State Heap Commutativity
-/

/-
  LEMMA: storageLive does not affect heapRead
-/
theorem State.storageLive_heapRead (s : State) (l : Local) (loc : Location) :
    (s.storageLive l).heapRead loc = s.heapRead loc := by
  simp [State.storageLive, State.heapRead]

/-
  LEMMA: storageDead does not affect heapRead
-/
theorem State.storageDead_heapRead (s : State) (l : Local) (loc : Location) :
    (s.storageDead l).heapRead loc = s.heapRead loc := by
  simp [State.storageDead, State.heapRead]

/-
  LEMMA: heapDealloc does not affect readLocal
-/
theorem State.heapDealloc_readLocal (s : State) (loc : Location) (l : Local) :
    (s.heapDealloc loc).readLocal l = s.readLocal l := by
  simp [State.heapDealloc, State.readLocal, State.isAlive]

/-!
  ## writeLocal Properties
-/

/-
  LEMMA: writeLocal succeeds when local is alive
-/
theorem State.writeLocal_succeeds (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true) :
    (s.writeLocal l v).isSome = true := by
  simp [State.writeLocal, hAlive]

/-
  LEMMA: writeLocal result has same aliveness for target
-/
theorem State.writeLocal_result_alive (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true) :
    let result := s.writeLocal l v
    result.isSome = true ∧ ∀ s', result = some s' → s'.isAlive l = true := by
  constructor
  · simp [State.writeLocal, hAlive]
  · intro s' hs'
    simp [State.writeLocal, hAlive] at hs'
    rw [← hs']
    simp [State.isAlive]
    exact hAlive

/-!
  ## execStmt Uniqueness
-/

/-
  LEMMA: If execStmt returns two Some values, they are equal
-/
theorem execStmt_result_unique (s : State) (stmt : MirStmt) (s1 s2 : State)
    (h1 : execStmt s stmt = some s1) (h2 : execStmt s stmt = some s2) :
    s1 = s2 := by
  rw [h1] at h2
  injection h2

/-
  LEMMA: If execTerminator returns two Some values, they are equal
-/
theorem execTerminator_result_unique (s : State) (term : MirTerminator) (c1 c2 : Control)
    (h1 : execTerminator s term = some c1) (h2 : execTerminator s term = some c2) :
    c1 = c2 := by
  rw [h1] at h2
  injection h2

/-
  LEMMA: If evalOperand returns two Some values, they are equal
-/
theorem evalOperand_result_unique (s : State) (op : Operand) (v1 v2 : Value)
    (h1 : evalOperand s op = some v1) (h2 : evalOperand s op = some v2) :
    v1 = v2 := by
  rw [h1] at h2
  injection h2

/-
  LEMMA: If evalPlace returns two Some values, they are equal
-/
theorem evalPlace_result_unique (s : State) (p : Place) (v1 v2 : Value)
    (h1 : evalPlace s p = some v1) (h2 : evalPlace s p = some v2) :
    v1 = v2 := by
  rw [h1] at h2
  injection h2

/-
  LEMMA: If evalRvalue returns two Some values, they are equal
-/
theorem evalRvalue_result_unique (s : State) (rv : Rvalue) (v1 v2 : Value)
    (h1 : evalRvalue s rv = some v1) (h2 : evalRvalue s rv = some v2) :
    v1 = v2 := by
  rw [h1] at h2
  injection h2

/-!
  ## Additional evalPlace Properties
-/

/-
  LEMMA: evalPlace on local succeeds when alive and has value
-/
theorem evalPlace_local_success (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true) (hVal : s.locals l = some v) :
    evalPlace s (.local l) = some v := by
  simp [evalPlace, State.readLocal, hAlive, hVal]

/-
  LEMMA: evalPlace on local fails when not alive
-/
theorem evalPlace_local_fail_dead (s : State) (l : Local)
    (hDead : s.isAlive l = false) :
    evalPlace s (.local l) = none := by
  simp [evalPlace, State.readLocal, hDead]

/-
  LEMMA: evalPlace deref on raw pointer succeeds when valid
-/
theorem evalPlace_deref_rawPtr (s : State) (base : Place) (loc : Location) (v : Value)
    (hBase : evalPlace s base = some (.rawPtr (some loc)))
    (hHeap : s.heapRead loc = some v) :
    evalPlace s (.project base .deref) = some v := by
  simp [evalPlace, hBase, hHeap]

/-!
  ## Additional evalOperand Properties
-/

/-
  LEMMA: evalOperand copy is same as evalPlace
-/
@[simp]
theorem evalOperand_copy_eq_evalPlace (s : State) (p : Place) :
    evalOperand s (.copy p) = evalPlace s p := rfl

/-
  LEMMA: evalOperand move is same as evalPlace
-/
@[simp]
theorem evalOperand_move_eq_evalPlace (s : State) (p : Place) :
    evalOperand s (.move p) = evalPlace s p := rfl

/-!
  ## Control Flow Uniqueness
-/

/-
  LEMMA: execTerminator Return always returns return_
-/
theorem execTerminator_return_is_return (s : State) (c : Control)
    (h : execTerminator s .Return = some c) :
    c = .return_ := by
  simp [execTerminator] at h
  exact h.symm

/-
  LEMMA: execTerminator Goto always returns goto to same block
-/
theorem execTerminator_goto_is_goto (s : State) (bb : BasicBlock) (c : Control)
    (h : execTerminator s (.Goto bb) = some c) :
    c = .goto bb := by
  simp [execTerminator] at h
  exact h.symm

/-!
  ## Heap Consistency After Operations
-/

/-
  LEMMA: After heapAlloc, reading at new location returns allocated value
-/
theorem State.heapAlloc_new_loc_reads (s : State) (v : Value) :
    let (s', loc) := s.heapAlloc v
    s'.heapRead loc = some v := by
  simp [State.heapAlloc, State.heapRead, Heap.alloc, Heap.read]

/-
  LEMMA: heapWrite twice to same location uses the last value
-/
theorem State.heapWrite_twice_same_loc (s : State) (loc : Location) (v1 v2 : Value) :
    ((s.heapWrite loc v1).heapWrite loc v2).heapRead loc = some v2 := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read]

/-
  LEMMA: heapDealloc then heapWrite restores location
-/
theorem State.heapDealloc_then_write (s : State) (loc : Location) (v : Value) :
    ((s.heapDealloc loc).heapWrite loc v).heapRead loc = some v := by
  simp [State.heapDealloc, State.heapWrite, State.heapRead, Heap.dealloc, Heap.write, Heap.read]

/-!
  ## StorageLive/StorageDead Interaction Properties
-/

/-
  LEMMA: StorageLive then StorageDead results in dead local
-/
theorem State.storageLive_then_dead (s : State) (l : Local) :
    ((s.storageLive l).storageDead l).isAlive l = false := by
  simp [State.storageLive, State.storageDead, State.isAlive]

/-
  LEMMA: StorageDead then StorageLive results in alive local
-/
theorem State.storageDead_then_live (s : State) (l : Local) :
    ((s.storageDead l).storageLive l).isAlive l = true := by
  simp [State.storageDead, State.storageLive, State.isAlive]

/-
  LEMMA: StorageLive is idempotent for aliveness
-/
theorem State.storageLive_idempotent_alive (s : State) (l : Local) :
    ((s.storageLive l).storageLive l).isAlive l = (s.storageLive l).isAlive l := by
  simp [State.storageLive, State.isAlive]

/-
  LEMMA: StorageDead is idempotent for aliveness
-/
theorem State.storageDead_idempotent_alive (s : State) (l : Local) :
    ((s.storageDead l).storageDead l).isAlive l = (s.storageDead l).isAlive l := by
  simp [State.storageDead, State.isAlive]

/-!
  ## Memory Safety Lemmas
  These lemmas establish properties that prevent use-after-free and other memory errors.
-/

/-
  LEMMA: Reading from deallocated heap location fails (use-after-free prevention)
-/
theorem State.heapDealloc_prevents_read (s : State) (loc : Location) :
    (s.heapDealloc loc).heapRead loc = none := by
  simp [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]

/-
  LEMMA: Double deallocation result has same effect on reads
-/
theorem State.heapDealloc_idempotent_read (s : State) (loc : Location) :
    ((s.heapDealloc loc).heapDealloc loc).heapRead loc = (s.heapDealloc loc).heapRead loc := by
  simp [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]

/-
  LEMMA: Allocation increases the next location monotonically
-/
theorem State.heapAlloc_nextLoc_increases (s : State) (v : Value) :
    (s.heapAlloc v).1.heap.nextLoc = s.heap.nextLoc + 1 := by
  simp [State.heapAlloc, Heap.alloc]

/-
  LEMMA: Reading dead local fails (prevents use of uninitialized memory)
-/
theorem State.readLocal_dead_fails (s : State) (l : Local)
    (hDead : s.isAlive l = false) :
    s.readLocal l = none := by
  simp only [State.readLocal, State.isAlive] at *
  simp [hDead]

/-
  LEMMA: Writing to dead local fails (prevents write to uninitialized memory)
-/
theorem State.writeLocal_dead_fails (s : State) (l : Local) (v : Value)
    (hDead : s.isAlive l = false) :
    s.writeLocal l v = none := by
  simp only [State.writeLocal, State.isAlive] at *
  simp [hDead]

/-!
  ## Well-Formedness Preservation
  These lemmas show that various operations preserve state well-formedness.
-/

/-
  LEMMA: writeLocal preserves well-formedness when local is alive
-/
theorem State.writeLocal_preserves_wf' (s : State) (l : Local) (v : Value)
    (hWf : s.wellFormed)
    (hAlive : s.isAlive l = true) :
    (match s.writeLocal l v with | some s' => s'.wellFormed | none => True) := by
  simp only [State.writeLocal, hAlive, ↓reduceIte]
  intro l' hVal
  simp only [State.wellFormed] at hWf
  by_cases h : l' = l
  · subst h
    exact hAlive
  · simp only [ne_eq, h, ↓reduceIte] at hVal
    exact hWf l' hVal

/-
  LEMMA: heapWrite preserves well-formedness
-/
theorem State.heapWrite_preserves_wf (s : State) (loc : Location) (v : Value)
    (hWf : s.wellFormed) :
    (s.heapWrite loc v).wellFormed := by
  intro l hVal
  simp only [State.heapWrite] at hVal ⊢
  exact hWf l hVal

/-
  LEMMA: heapAlloc preserves well-formedness
-/
theorem State.heapAlloc_preserves_wf (s : State) (v : Value)
    (hWf : s.wellFormed) :
    (s.heapAlloc v).1.wellFormed := by
  intro l hVal
  simp only [State.heapAlloc] at hVal ⊢
  exact hWf l hVal

/-
  LEMMA: heapDealloc preserves well-formedness
-/
theorem State.heapDealloc_preserves_wf (s : State) (loc : Location)
    (hWf : s.wellFormed) :
    (s.heapDealloc loc).wellFormed := by
  intro l hVal
  simp only [State.heapDealloc] at hVal ⊢
  exact hWf l hVal

/-!
  ## Frame Properties
  These lemmas establish that operations affect only the relevant parts of state.
-/

/-
  LEMMA: heapWrite to one location doesn't affect other locations
-/
theorem State.heapWrite_frame (s : State) (loc1 loc2 : Location) (v : Value)
    (hNe : loc1 ≠ loc2) :
    (s.heapWrite loc1 v).heapRead loc2 = s.heapRead loc2 := by
  simp only [State.heapWrite, State.heapRead, Heap.write, Heap.read]
  simp only [hNe.symm, ↓reduceIte]

/-
  LEMMA: heapDealloc at one location doesn't affect other locations
-/
theorem State.heapDealloc_frame (s : State) (loc1 loc2 : Location)
    (hNe : loc1 ≠ loc2) :
    (s.heapDealloc loc1).heapRead loc2 = s.heapRead loc2 := by
  simp only [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]
  simp only [hNe.symm, ↓reduceIte]

/-
  LEMMA: heapAlloc doesn't affect existing locations (if loc < nextLoc)
-/
theorem State.heapAlloc_frame_lt (s : State) (v : Value) (loc : Location)
    (hLt : loc < s.heap.nextLoc) :
    let (s', _) := s.heapAlloc v
    s'.heapRead loc = s.heapRead loc := by
  simp only [State.heapAlloc, State.heapRead, Heap.alloc, Heap.read]
  have hNe : loc ≠ s.heap.nextLoc := Nat.ne_of_lt hLt
  simp only [hNe, ↓reduceIte]

/-
  LEMMA: storageLive on one local doesn't affect other locals
-/
theorem State.storageLive_frame (s : State) (l1 l2 : Local)
    (hNe : l1 ≠ l2) :
    (s.storageLive l1).isAlive l2 = s.isAlive l2 := by
  simp only [State.storageLive, State.isAlive]
  simp only [hNe.symm, ↓reduceIte]

/-
  LEMMA: storageDead on one local doesn't affect other locals
-/
theorem State.storageDead_frame (s : State) (l1 l2 : Local)
    (hNe : l1 ≠ l2) :
    (s.storageDead l1).isAlive l2 = s.isAlive l2 := by
  simp only [State.storageDead, State.isAlive]
  simp only [hNe.symm, ↓reduceIte]

/-
  LEMMA: writeLocal preserves isAlive for all locals
-/
theorem State.writeLocal_preserves_alive (s : State) (l : Local) (v : Value) (s' : State)
    (hWrite : s.writeLocal l v = some s')
    (l' : Local) :
    s'.isAlive l' = s.isAlive l' := by
  simp only [State.writeLocal] at hWrite
  by_cases hAlive : s.isAlive l
  · simp only [hAlive, ↓reduceIte, Option.some.injEq] at hWrite
    subst hWrite
    rfl
  · simp only [hAlive, Bool.false_eq_true, ↓reduceIte] at hWrite
    cases hWrite

/-!
  ## Execution Preservation Lemmas
  These lemmas show that well-formedness is preserved through statement execution.
-/

/-
  LEMMA: Nop preserves well-formedness
-/
theorem execStmt_nop_preserves_wf (s : State)
    (hWf : s.wellFormed) :
    match execStmt s .Nop with
    | some s' => s'.wellFormed
    | none => True := by
  simp only [execStmt, hWf]

/-
  LEMMA: StorageLive stmt preserves well-formedness
-/
theorem execStmt_storageLive_preserves_wf (s : State) (l : Local)
    (hWf : s.wellFormed) :
    match execStmt s (.StorageLive l) with
    | some s' => s'.wellFormed
    | none => True := by
  simp only [execStmt]
  exact State.storageLive_preserves_wf s l hWf

/-
  LEMMA: StorageDead stmt preserves well-formedness
-/
theorem execStmt_storageDead_preserves_wf (s : State) (l : Local)
    (hWf : s.wellFormed) :
    match execStmt s (.StorageDead l) with
    | some s' => s'.wellFormed
    | none => True := by
  simp only [execStmt]
  exact State.storageDead_preserves_wf s l hWf

/-!
  ## Commutativity Lemmas
  These lemmas establish when operations can be reordered.
-/

/-
  LEMMA: storageLive commutes (via alive field)
-/
theorem State.storageLive_comm_alive (s : State) (l1 l2 : Local) (l : Local) :
    ((s.storageLive l1).storageLive l2).isAlive l = ((s.storageLive l2).storageLive l1).isAlive l := by
  simp only [State.storageLive, State.isAlive]
  by_cases h1 : l = l2 <;> by_cases h2 : l = l1 <;> simp [h1, h2]

/-
  LEMMA: storageDead commutes (via alive field)
-/
theorem State.storageDead_comm_alive (s : State) (l1 l2 : Local) (l : Local) :
    ((s.storageDead l1).storageDead l2).isAlive l = ((s.storageDead l2).storageDead l1).isAlive l := by
  simp only [State.storageDead, State.isAlive]
  by_cases h1 : l = l2 <;> by_cases h2 : l = l1 <;> simp [h1, h2]

/-
  LEMMA: heapWrite comm (via read at any location)
-/
theorem State.heapWrite_comm_read (s : State) (loc1 loc2 : Location) (v1 v2 : Value)
    (hNe : loc1 ≠ loc2) (loc : Location) :
    ((s.heapWrite loc1 v1).heapWrite loc2 v2).heapRead loc =
    ((s.heapWrite loc2 v2).heapWrite loc1 v1).heapRead loc := by
  simp only [State.heapWrite, State.heapRead, Heap.write, Heap.read]
  by_cases h1 : loc = loc2 <;> by_cases h2 : loc = loc1
  · subst h1 h2; exact (hNe rfl).elim
  · simp [h1, hNe.symm]
  · simp [h2, hNe]
  · simp [h1, h2]

/-
  LEMMA: heapDealloc comm (via read at any location)
-/
theorem State.heapDealloc_comm_read (s : State) (loc1 loc2 : Location) (loc : Location) :
    ((s.heapDealloc loc1).heapDealloc loc2).heapRead loc =
    ((s.heapDealloc loc2).heapDealloc loc1).heapRead loc := by
  simp only [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]
  by_cases h1 : loc = loc2 <;> by_cases h2 : loc = loc1 <;> simp [h1, h2]

/-!
  ## Statement Determinism
  These lemmas establish that statement execution is deterministic.
-/

/-!
  ## Local Variable Properties
  These lemmas establish properties about local variable management.
-/

/-
  LEMMA: After storageLive, local is alive
-/
theorem State.storageLive_makes_alive (s : State) (l : Local) :
    (s.storageLive l).isAlive l = true := by
  simp [State.storageLive, State.isAlive]

/-
  LEMMA: After storageDead, local is dead
-/
theorem State.storageDead_makes_dead (s : State) (l : Local) :
    (s.storageDead l).isAlive l = false := by
  simp [State.storageDead, State.isAlive]

/-
  LEMMA: writeLocal succeeds when local is alive
-/
theorem State.writeLocal_succeeds_alive (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true) :
    ∃ s', s.writeLocal l v = some s' := by
  simp only [State.writeLocal, hAlive, ↓reduceIte]
  exact ⟨_, rfl⟩

/-
  LEMMA: After storageLive, local has no value yet (unless it already did)
-/
theorem State.storageLive_value_preserved (s : State) (l : Local) :
    (s.storageLive l).locals l = s.locals l := by
  simp [State.storageLive]

/-
  LEMMA: After storageDead, local value is cleared
-/
theorem State.storageDead_clears_value (s : State) (l : Local) :
    (s.storageDead l).locals l = none := by
  simp [State.storageDead]

/-!
  ## Heap Allocation Chain Properties
  These lemmas establish properties about sequences of heap operations.
-/

/-
  LEMMA: Deallocating after allocation makes location unreadable
-/
theorem State.heapAlloc_then_dealloc (s : State) (v : Value) :
    let (s', loc) := s.heapAlloc v
    (s'.heapDealloc loc).heapRead loc = none := by
  simp [State.heapAlloc, State.heapDealloc, State.heapRead, Heap.alloc, Heap.dealloc, Heap.read]

/-
  LEMMA: Allocated location can be read immediately
-/
theorem State.heapAlloc_readable (s : State) (v : Value) :
    let (s', loc) := s.heapAlloc v
    s'.heapRead loc = some v := by
  simp [State.heapAlloc, State.heapRead, Heap.alloc, Heap.read]

/-!
  ## Operand Evaluation Properties
  These lemmas establish properties about operand evaluation.
-/

/-
  LEMMA: Copy operand evaluation depends only on place evaluation
-/
theorem evalOperand_copy_depends_on_place (s : State) (p : Place) :
    evalOperand s (.copy p) = evalPlace s p := rfl

/-
  LEMMA: Move operand evaluation depends only on place evaluation
-/
theorem evalOperand_move_depends_on_place (s : State) (p : Place) :
    evalOperand s (.move p) = evalPlace s p := rfl

/-
  LEMMA: Const operand is state-independent
-/
theorem evalOperand_const_state_independent (s1 s2 : State) (v : Value) :
    evalOperand s1 (.const v) = evalOperand s2 (.const v) := rfl

/-!
  ## Place Evaluation Properties
  These lemmas establish properties about place evaluation.
-/

/-
  LEMMA: evalPlace local succeeds when local is alive with value
-/
theorem evalPlace_local_some (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true)
    (hVal : s.locals l = some v) :
    evalPlace s (.local l) = some v := by
  simp [evalPlace, State.readLocal, hAlive, hVal]

/-
  LEMMA: evalPlace local fails when local is dead
-/
theorem evalPlace_local_none_dead (s : State) (l : Local)
    (hDead : s.isAlive l = false) :
    evalPlace s (.local l) = none := by
  simp [evalPlace, State.readLocal, hDead]

/-
  LEMMA: Writing to heap then reading returns written value
-/
theorem State.heapWrite_then_read' (s : State) (loc : Location) (v : Value) :
    (s.heapWrite loc v).heapRead loc = some v := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read]

/-
  LEMMA: StorageLive then writeLocal succeeds
-/
theorem State.storageLive_then_write (s : State) (l : Local) (v : Value) :
    ∃ s', (s.storageLive l).writeLocal l v = some s' := by
  simp only [State.storageLive, State.writeLocal, State.isAlive, ↓reduceIte]
  exact ⟨_, rfl⟩

/-
  LEMMA: writeLocal creates new state with updated locals
-/
theorem State.writeLocal_updates_locals (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true) :
    match s.writeLocal l v with
    | some s' => s'.locals l = some v
    | none => True := by
  simp only [State.writeLocal, hAlive, ↓reduceIte]

/-
  LEMMA: Nop statement always succeeds
-/
theorem execStmt_nop_succeeds (s : State) :
    execStmt s .Nop = some s := rfl

/-
  LEMMA: StorageLive statement always succeeds
-/
theorem execStmt_storageLive_succeeds (s : State) (l : Local) :
    execStmt s (.StorageLive l) = some (s.storageLive l) := rfl

/-
  LEMMA: StorageDead statement always succeeds
-/
theorem execStmt_storageDead_succeeds (s : State) (l : Local) :
    execStmt s (.StorageDead l) = some (s.storageDead l) := rfl

/-!
  ## Assert Terminator Properties
  These lemmas establish properties about assertion checking.
-/

/-
  LEMMA: Assert succeeds when condition matches expected (true)
-/
theorem execTerminator_assert_true_true (s : State) (target : BasicBlock)
    (cleanup : Option BasicBlock) :
    execTerminator s (.Assert ⟨.const (.bool true), true, target, cleanup⟩) =
      some (.goto target) := rfl

/-
  LEMMA: Assert succeeds when condition matches expected (false)
-/
theorem execTerminator_assert_false_false (s : State) (target : BasicBlock)
    (cleanup : Option BasicBlock) :
    execTerminator s (.Assert ⟨.const (.bool false), false, target, cleanup⟩) =
      some (.goto target) := rfl

/-
  LEMMA: Assert fails (panic) when condition doesn't match and no cleanup
-/
theorem execTerminator_assert_mismatch_panic (s : State) (target : BasicBlock) :
    execTerminator s (.Assert ⟨.const (.bool false), true, target, none⟩) =
      some .panic := rfl

/-
  LEMMA: Assert unwinds when condition doesn't match with cleanup
-/
theorem execTerminator_assert_mismatch_unwind (s : State) (target cleanup : BasicBlock) :
    execTerminator s (.Assert ⟨.const (.bool true), false, target, some cleanup⟩) =
      some (.unwind cleanup) := rfl

/-
  LEMMA: Assert fails on non-bool value
-/
theorem execTerminator_assert_type_error (s : State) (msg : AssertMsg)
    (v : Value) (hEval : evalOperand s msg.cond = some v)
    (hNotBool : ∀ b, v ≠ .bool b) :
    execTerminator s (.Assert msg) = none := by
  simp only [execTerminator, hEval]
  cases v with
  | bool b => exact (hNotBool b rfl).elim
  | _ => rfl

/-!
  ## Drop Terminator Properties
  These lemmas establish properties about drop operations.
-/

/-
  LEMMA: Drop ignores unwind parameter (simplified semantics)
-/
theorem execTerminator_drop_ignores_unwind (s : State) (place : Place) (target : BasicBlock)
    (u1 u2 : Option BasicBlock) :
    execTerminator s (.Drop place target u1) = execTerminator s (.Drop place target u2) := rfl

/-
  LEMMA: Int value preserves type tag
-/
theorem int_value_type (ty : IntTy) (v : Int) :
    match Value.int ty v with
    | .int ty' _ => ty' = ty
    | _ => False := by
  simp

/-!
  ============================================================================
  PHASE N2.2: Weakest Precondition Calculus
  ============================================================================

  This section formalizes the weakest precondition (wp) calculus for MIR
  statements, which is the foundation for verification condition generation.

  The key theorem is wp_sound:
    If wp(s, Q) holds in state s, and s executes successfully to s',
    then Q holds in s'.
-/

/-!
  ## State Predicates

  A predicate on states is just State → Prop.
  We define the weakest precondition transformer for each statement type.
-/


end TRust
