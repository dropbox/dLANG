/-
  Operational semantics and evaluators for the MIR subset modeled in `MirSemantics`.
-/

import MirSemantics.Syntax

namespace TRust

-- Read a value from a place (without projection, for simplicity)
-- Full implementation would handle all projections
def evalPlace (s : State) : Place → Option Value
  | .local l => s.readLocal l
  | .project base .deref => do
      let v ← evalPlace s base
      match v with
      | .ref loc | .box_ loc => s.heapRead loc
      | .rawPtr (some loc) => s.heapRead loc
      | _ => none
  | .project base (.field idx) => do
      let v ← evalPlace s base
      match v with
      | .tuple elems => elems[idx]?
      | _ => none
  | .project base (.index idxLocal) => do
      let v ← evalPlace s base
      let idxVal ← s.readLocal idxLocal
      match v, idxVal with
      | .array elems, .int _ idx => elems[idx.toNat]?
      | _, _ => none
  | .project base (.constIndex idx) => do
      let v ← evalPlace s base
      match v with
      | .array elems => elems[idx]?
      | _ => none
termination_by p => sizeOf p
decreasing_by
  all_goals
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hb1 : sizeOf base < 1 + sizeOf base :=
      Nat.lt_add_of_pos_left (n := sizeOf base) (k := 1) (by decide)
    have hb2 : 1 + sizeOf base < 1 + (1 + sizeOf base) :=
      Nat.lt_add_of_pos_left (n := 1 + sizeOf base) (k := 1) (by decide)
    have hb : sizeOf base < 1 + (1 + sizeOf base) :=
      Nat.lt_trans hb1 hb2
    refine Nat.lt_of_lt_of_le hb ?_
    simp <;> exact Nat.le_add_left _ _

def evalOperand (s : State) : Operand → Option Value
  | .const v => some v
  | .copy p => evalPlace s p
  | .move p => evalPlace s p  -- In semantics, move = copy (ownership is checked statically)

-- Evaluate comparison operators
def evalCmp (op : BinOp) (a b : Int) : Option Bool :=
  match op with
  | .eq => some (a == b)
  | .ne => some (a != b)
  | .lt => some (a < b)
  | .le => some (a <= b)
  | .gt => some (a > b)
  | .ge => some (a >= b)
  | _ => none

-- Evaluate binary operations
def evalBinOp (op : BinOp) : Value → Value → Option Value
  | .int ty a, .int ty' b =>
      if ty = ty' then
        match op with
        | .add | .addChecked => some (.int ty (a + b))  -- Overflow handled separately
        | .sub | .subChecked => some (.int ty (a - b))
        | .mul | .mulChecked => some (.int ty (a * b))
        | .div => if b = 0 then none else some (.int ty (a / b))
        | .rem => if b = 0 then none else some (.int ty (a % b))
        | .eq | .ne | .lt | .le | .gt | .ge =>
            match evalCmp op a b with
            | some r => some (.bool r)
            | none => none
        | .bitAnd => some (.int ty (intBitAnd a b))
        | .bitOr => some (.int ty (intBitOr a b))
        | .bitXor => some (.int ty (intBitXor a b))
        | .shl => some (.int ty (intShl a b.toNat))
        | .shr => some (.int ty (intShr a b.toNat))
      else
        none
  | .bool a, .bool b =>
      match op with
      | .bitAnd => some (.bool (a && b))  -- Logical AND
      | .bitOr => some (.bool (a || b))   -- Logical OR
      | .bitXor => some (.bool (xor a b)) -- Logical XOR
      | .eq => some (.bool (a == b))
      | .ne => some (.bool (a != b))
      | _ => none
  | _, _ => none

-- Evaluate unary operations
def evalUnOp (op : UnOp) : Value → Option Value
  | .int ty v =>
      match op with
      | .neg => some (.int ty (-v))
      | .not => some (.int ty (intComplement v))
  | .bool b =>
      match op with
      | .not => some (.bool (!b))
      | _ => none
  | _ => none
-- Evaluate checked binary operation - returns (result, overflow) tuple
def evalCheckedBinOp (op : BinOp) : Value → Value → Option Value
  | .int ty a, .int ty' b =>
      if ty = ty' then
        match op with
        | .addChecked =>
            let (result, overflow) := checkedAdd ty a b
            some (.tuple [.int ty result, .bool overflow])
        | .subChecked =>
            let (result, overflow) := checkedSub ty a b
            some (.tuple [.int ty result, .bool overflow])
        | .mulChecked =>
            let (result, overflow) := checkedMul ty a b
            some (.tuple [.int ty result, .bool overflow])
        | _ => none  -- Non-checked ops don't use this
      else
        none
  | _, _ => none
-- Evaluate reference creation (returns location in heap)
-- Note: In a real implementation, we'd track where the place is stored
-- For simplification, we just create a heap location for the value
def evalRef (s : State) (place : Place) : Option (State × Value) := do
  let v ← evalPlace s place
  let (s', loc) := s.heapAlloc v
  return (s', .ref loc)

def evalRvalue (s : State) : Rvalue → Option Value
  | .use op => evalOperand s op
  | .binOp op lhs rhs => do
      let lv ← evalOperand s lhs
      let rv ← evalOperand s rhs
      evalBinOp op lv rv
  | .unOp op operand => do
      let v ← evalOperand s operand
      evalUnOp op v
  | .checkedBinOp op lhs rhs => do
      let lv ← evalOperand s lhs
      let rv ← evalOperand s rhs
      evalCheckedBinOp op lv rv
  | .ref _bk _place => none  -- Ref needs state update, handled specially
  | .addressOf _mutbl _place => none  -- Similarly needs state
  | .aggregate _kind ops => do
      let vals ← ops.mapM (evalOperand s)
      some (.tuple vals)  -- Simplified: all aggregates as tuples
  | .len place => do
      let v ← evalPlace s place
      match v with
      | .array elems => some (.int .usize elems.length)
      | _ => none
  | .cast op => evalOperand s op  -- Simplified: cast = identity
  | .repeat op count => do
      let v ← evalOperand s op
      some (.array (List.replicate count v))
  | .discriminant _place => none  -- Would need enum type info

-- Evaluate rvalue with state update (for Ref)
def evalRvalueWithState (s : State) (rv : Rvalue) : Option (State × Value) :=
  match rv with
  | .ref _bk place => evalRef s place
  | .addressOf _mutbl place => do
      let v ← evalPlace s place
      let (s', loc) := s.heapAlloc v
      return (s', .rawPtr (some loc))
  | _ => do
      let v ← evalRvalue s rv
      return (s, v)

-- Write to a place (simplified - only handles local writes)
partial def writePlace (s : State) (p : Place) (v : Value) : Option State :=
  match p with
  | .local l => s.writeLocal l v
  | .project base .deref => do
      let baseVal ← evalPlace s base
      match baseVal with
      | .ref loc | .box_ loc => some (s.heapWrite loc v)
      | .rawPtr (some loc) => some (s.heapWrite loc v)
      | _ => none
  | .project base (.field idx) => do
      let baseVal ← evalPlace s base
      match baseVal with
      | .tuple elems =>
          if idx < elems.length then
            let elems' := elems.set idx v
            writePlace s base (.tuple elems')
          else
            none
      | _ => none
  | .project base (.index idxLocal) => do
      let baseVal ← evalPlace s base
      let idxVal ← s.readLocal idxLocal
      match baseVal, idxVal with
      | .array elems, .int _ idx =>
          if idx.toNat < elems.length then
            let elems' := elems.set idx.toNat v
            writePlace s base (.array elems')
          else
            none
      | _, _ => none
  | .project base (.constIndex idx) => do
      let baseVal ← evalPlace s base
      match baseVal with
      | .array elems =>
          if idx < elems.length then
            let elems' := elems.set idx v
            writePlace s base (.array elems')
          else
            none
      | _ => none

def execStmt (s : State) : MirStmt → Option State
  | .Assign place rv => do
      let (s', v) ← evalRvalueWithState s rv
      writePlace s' place v
  | .StorageLive l => some (s.storageLive l)
  | .StorageDead l => some (s.storageDead l)
  | .Nop => some s

-- Convert a value to an integer for switch discrimination
def asSwitchIntDiscr : Value → Option Int
  | .bool b => some (if b then 1 else 0)
  | .int _ i => some i
  | .unit => none
  | .fn_ _ => none
  | .ref _ => none      -- References can't be switch discriminants
  | .box_ _ => none     -- Boxes can't be switch discriminants
  | .rawPtr _ => none   -- Raw pointers can't be switch discriminants
  | .array _ => none    -- Arrays can't be switch discriminants
  | .tuple _ => none    -- Tuples can't be switch discriminants
def execTerminator (s : State) : MirTerminator → Option Control
  | .Return => some .return_
  | .Goto bb => some (.goto bb)
  | .SwitchInt discr targets otherwise => do
      let v ← evalOperand s discr
      let d ← asSwitchIntDiscr v
      match targets.find? (fun (p : Int × BasicBlock) => p.1 == d) with
      | some (_, bb) => some (.goto bb)
      | none => some (.goto otherwise)
  | .Call .. => none  -- Function calls handled separately
  | .Assert msg => do
      let v ← evalOperand s msg.cond
      match v with
      | .bool b =>
          if b == msg.expected then
            some (.goto msg.target)
          else
            match msg.cleanup with
            | some bb => some (.unwind bb)
            | none => some .panic
      | _ => none  -- Type error
  | .Drop _place target _unwind => some (.goto target)  -- Simplified: drop just continues
  | .Unreachable => none  -- UB if reached
/-!
  ## Block and Statement Execution
-/

/-
  Execute all statements in a basic block
-/
def execStmts (s : State) : List MirStmt → Option State
  | [] => some s
  | stmt :: rest => do
      let s' ← execStmt s stmt
      execStmts s' rest

/-
  Execute a basic block (statements then terminator)
-/
def execBlock (s : State) (bb : BasicBlockData) : Option (State × Control) := do
  let s' ← execStmts s bb.stmts
  let ctrl ← execTerminator s' bb.terminator
  return (s', ctrl)

/-
  Execute a function body from a given state, returning final state
  Uses fuel to ensure termination
-/
partial def execBody (body : MirBody) (s : State) (fuel : Nat) : Option State :=
  go body.entryBlock s fuel
where
  go (bb : BasicBlock) (s : State) (fuel : Nat) : Option State :=
    match fuel with
    | 0 => none  -- Out of fuel
    | fuel' + 1 => do
        let blockData ← body.getBlock bb
        let (s', ctrl) ← execBlock s blockData
        match ctrl with
        | .return_ => some s'
        | .goto nextBb => go nextBb s' fuel'
        | .panic => none  -- Assertion failure
        | .unwind _ => none  -- Unwinding (simplified)

/-!
  ## Programs and Function Calls

  The base `execTerminator` above is pure (returns only `Control`) and treats `Call` as `none`.
  For Phase N2.1 we additionally provide an executable semantics that supports `Call`, modeled as:

  - A program maps function names to MIR bodies.
  - Calls evaluate arguments in the caller, run the callee with a fresh local frame but shared heap,
    then write the callee return value (local 0) into the caller destination place.
-/
-- Initialize a fresh local frame for a callee body (shared heap with caller).
def State.initFrame (heap : Heap) (localCount : Nat) (args : List Value) : State :=
  { alive := fun l => decide (l < localCount)
    locals := fun
      | 0 => some .unit
      | l + 1 => args[l]?
    heap := heap }

mutual
  /-
    Terminator execution with program context.
    Returns an updated state (to model `Call`) and the resulting control flow.
  -/
  partial def execTerminatorP (p : MirProgram) (s : State) (term : MirTerminator) (fuel : Nat) :
      Option (State × Control) :=
    match term with
    | .Call func args dest target =>
        match fuel with
        | 0 => none
        | fuel' + 1 => do
            let fnVal ← evalOperand s func
            let name ← match fnVal with
              | .fn_ n => some n
              | _ => none
            let body ← p.getFun name
            let argVals ← args.mapM (evalOperand s)
            let calleeInit := State.initFrame s.heap body.localCount argVals
            let calleeFinal ← execFromBlockP p body body.entryBlock calleeInit fuel'
            let retVal ← calleeFinal.readLocal 0
            let callerWithHeap : State := { s with heap := calleeFinal.heap }
            let callerFinal ← writePlace callerWithHeap dest retVal
            return (callerFinal, .goto target)
    | _ => do
        let ctrl ← execTerminator s term
        return (s, ctrl)

  /-
    Execute a MIR body starting at a given basic block (fuel-bounded).
  -/
  partial def execFromBlockP (p : MirProgram) (body : MirBody) (bb : BasicBlock) (s : State) (fuel : Nat) :
      Option State :=
    match fuel with
    | 0 => none
    | fuel' + 1 => do
        let blockData ← body.getBlock bb
        let s' ← execStmts s blockData.stmts
        let (s'', ctrl) ← execTerminatorP p s' blockData.terminator fuel'
        match ctrl with
        | .return_ => some s''
        | .goto nextBb => execFromBlockP p body nextBb s'' fuel'
        | .panic => none
        | .unwind _ => none

end

/- Execute a function body from a given state, returning final state (fuel-bounded). -/
def execBodyP (p : MirProgram) (body : MirBody) (s : State) (fuel : Nat) : Option State :=
  execFromBlockP p body body.entryBlock s fuel

end TRust
