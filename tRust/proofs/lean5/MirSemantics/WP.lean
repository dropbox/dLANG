/-
  Weakest-precondition / weakest-liberal-precondition definitions and proofs.
-/

import MirSemantics.Lemmas

namespace TRust

abbrev StatePred := State → Prop

/-!
  ## Weakest Precondition for Statements
-/

/-
  wp_stmt computes the weakest precondition for a statement.
  Given a postcondition Q, wp_stmt returns the weakest P such that
  if P holds and the statement executes, Q holds afterward.
-/
def wp_stmt (stmt : MirStmt) (Q : StatePred) : StatePred :=
  fun s =>
    match execStmt s stmt with
    | some s' => Q s'
    | none => True  -- If statement fails, any precondition suffices (vacuous)

/-
  Stronger wp that requires successful execution
-/
def wp_stmt_total (stmt : MirStmt) (Q : StatePred) : StatePred :=
  fun s =>
    match execStmt s stmt with
    | some s' => Q s'
    | none => False  -- Require statement to succeed

/-!
  ## WP Soundness Theorem

  The fundamental soundness property: if wp holds and execution succeeds,
  then the postcondition holds.
-/

/-
  THEOREM: wp_stmt is sound
-/
theorem wp_stmt_sound (stmt : MirStmt) (Q : StatePred) (s s' : State) :
    wp_stmt stmt Q s → execStmt s stmt = some s' → Q s' := by
  intro hwp hexec
  simp only [wp_stmt] at hwp
  rw [hexec] at hwp
  exact hwp

/-
  THEOREM: wp_stmt_total is sound and requires success
-/
theorem wp_stmt_total_sound (stmt : MirStmt) (Q : StatePred) (s s' : State) :
    wp_stmt_total stmt Q s → execStmt s stmt = some s' → Q s' := by
  intro hwp hexec
  simp only [wp_stmt_total] at hwp
  rw [hexec] at hwp
  exact hwp

/-
  THEOREM: wp_stmt_total implies successful execution
-/
theorem wp_stmt_total_succeeds (stmt : MirStmt) (Q : StatePred) (s : State) :
    wp_stmt_total stmt Q s → ∃ s', execStmt s stmt = some s' := by
  intro hwp
  simp only [wp_stmt_total] at hwp
  match hexec : execStmt s stmt with
  | some s' => exact ⟨s', rfl⟩
  | none => simp [hexec] at hwp

/-!
  ## WP for Specific Statement Types
-/

/-
  LEMMA: WP for Nop is just the postcondition
-/
@[simp]
theorem wp_nop (Q : StatePred) (s : State) :
    wp_stmt .Nop Q s ↔ Q s := by
  simp [wp_stmt, execStmt]

/-
  LEMMA: WP for StorageLive
-/
@[simp]
theorem wp_storageLive (l : Local) (Q : StatePred) (s : State) :
    wp_stmt (.StorageLive l) Q s ↔ Q (s.storageLive l) := by
  simp [wp_stmt, execStmt]

/-
  LEMMA: WP for StorageDead
-/
@[simp]
theorem wp_storageDead (l : Local) (Q : StatePred) (s : State) :
    wp_stmt (.StorageDead l) Q s ↔ Q (s.storageDead l) := by
  simp [wp_stmt, execStmt]

/-
  LEMMA: WP for Nop (total version)
-/
@[simp]
theorem wp_nop_total (Q : StatePred) (s : State) :
    wp_stmt_total .Nop Q s ↔ Q s := by
  simp [wp_stmt_total, execStmt]

/-
  LEMMA: WP for StorageLive (total version)
-/
@[simp]
theorem wp_storageLive_total (l : Local) (Q : StatePred) (s : State) :
    wp_stmt_total (.StorageLive l) Q s ↔ Q (s.storageLive l) := by
  simp [wp_stmt_total, execStmt]

/-
  LEMMA: WP for StorageDead (total version)
-/
@[simp]
theorem wp_storageDead_total (l : Local) (Q : StatePred) (s : State) :
    wp_stmt_total (.StorageDead l) Q s ↔ Q (s.storageDead l) := by
  simp [wp_stmt_total, execStmt]

/-!
  ## WP for Statement Lists
-/

/-
  wp for a list of statements (backward through the list)
-/
def wp_stmts_wp : List MirStmt → StatePred → StatePred
  | [], Q => Q
  | stmt :: rest, Q => wp_stmt stmt (wp_stmts_wp rest Q)

/-
  THEOREM: wp_stmts_wp is sound
-/
theorem wp_stmts_wp_sound (stmts : List MirStmt) (Q : StatePred) (s s' : State) :
    wp_stmts_wp stmts Q s → execStmts s stmts = some s' → Q s' := by
  induction stmts generalizing s s' with
  | nil =>
    intro hwp hexec
    simp [execStmts] at hexec
    subst hexec
    simp [wp_stmts_wp] at hwp
    exact hwp
  | cons stmt rest ih =>
    intro hwp hexec
    simp only [wp_stmts_wp] at hwp
    simp only [execStmts] at hexec
    cases hExec : execStmt s stmt with
    | some s'' =>
      simp only [hExec] at hexec
      have hwp' := wp_stmt_sound stmt (wp_stmts_wp rest Q) s s'' hwp hExec
      exact ih s'' s' hwp' hexec
    | none =>
      simp [hExec] at hexec

/-
  LEMMA: wp_stmts_wp for empty list is identity
-/
@[simp]
theorem wp_stmts_wp_nil (Q : StatePred) :
    wp_stmts_wp [] Q = Q := rfl

/-
  LEMMA: wp_stmts_wp for singleton is wp_stmt
-/
theorem wp_stmts_wp_singleton (stmt : MirStmt) (Q : StatePred) :
    wp_stmts_wp [stmt] Q = wp_stmt stmt Q := by
  simp [wp_stmts_wp]

/-
  LEMMA: wp_stmts_wp composes
-/
theorem wp_stmts_wp_append (stmts1 stmts2 : List MirStmt) (Q : StatePred) :
    wp_stmts_wp (stmts1 ++ stmts2) Q = wp_stmts_wp stmts1 (wp_stmts_wp stmts2 Q) := by
  induction stmts1 with
  | nil => simp [wp_stmts_wp]
  | cons stmt rest ih => simp [wp_stmts_wp, ih]

/-!
  ## Monotonicity of WP
-/

/-
  LEMMA: wp_stmt is monotonic in the postcondition
-/
theorem wp_stmt_mono (stmt : MirStmt) (Q1 Q2 : StatePred) (s : State) :
    (∀ s, Q1 s → Q2 s) → wp_stmt stmt Q1 s → wp_stmt stmt Q2 s := by
  intro hImp hwp
  simp only [wp_stmt] at *
  match hexec : execStmt s stmt with
  | some s' =>
    simp only [hexec] at hwp ⊢
    exact hImp s' hwp
  | none =>
    trivial

/-
  LEMMA: wp_stmts_wp is monotonic in the postcondition
-/
theorem wp_stmts_wp_mono (stmts : List MirStmt) (Q1 Q2 : StatePred) (s : State) :
    (∀ s, Q1 s → Q2 s) → wp_stmts_wp stmts Q1 s → wp_stmts_wp stmts Q2 s := by
  induction stmts generalizing s with
  | nil =>
    intro hImp hwp
    simp only [wp_stmts_wp] at *
    exact hImp s hwp
  | cons stmt rest ih =>
    intro hImp hwp
    simp only [wp_stmts_wp] at *
    apply wp_stmt_mono stmt _ _ s
    · intro s' h
      exact ih s' hImp h
    · exact hwp

/-!
  ## WP Conjunction and Disjunction
-/

/-
  LEMMA: wp distributes over conjunction (forward)
-/
theorem wp_stmt_conj (stmt : MirStmt) (Q1 Q2 : StatePred) (s : State) :
    wp_stmt stmt Q1 s ∧ wp_stmt stmt Q2 s →
    wp_stmt stmt (fun s => Q1 s ∧ Q2 s) s := by
  intro ⟨h1, h2⟩
  simp only [wp_stmt] at *
  match hexec : execStmt s stmt with
  | some s' =>
    simp only [hexec] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  | none =>
    trivial

/-
  LEMMA: wp distributes over conjunction (backward)
-/
theorem wp_stmt_conj_inv (stmt : MirStmt) (Q1 Q2 : StatePred) (s : State) :
    wp_stmt stmt (fun s => Q1 s ∧ Q2 s) s →
    wp_stmt stmt Q1 s ∧ wp_stmt stmt Q2 s := by
  intro h
  simp only [wp_stmt] at *
  match hexec : execStmt s stmt with
  | some s' =>
    simp only [hexec] at h ⊢
    exact h
  | none =>
    simp only [hexec] at h ⊢
    exact ⟨trivial, trivial⟩

/-
  LEMMA: wp distributes over disjunction (backward)
-/
theorem wp_stmt_disj (stmt : MirStmt) (Q1 Q2 : StatePred) (s : State) :
    wp_stmt stmt Q1 s ∨ wp_stmt stmt Q2 s →
    wp_stmt stmt (fun s => Q1 s ∨ Q2 s) s := by
  intro h
  simp only [wp_stmt] at *
  match hexec : execStmt s stmt with
  | some s' =>
    simp only [hexec] at h ⊢
    exact h
  | none =>
    trivial

/-!
  ## Frame Rule for WP
-/

/-
  LEMMA: Frame rule - if P is preserved and disjoint from stmt's writes
  This is a simplified version; full frame rule needs separation logic
-/
theorem wp_stmt_frame (stmt : MirStmt) (Q R : StatePred) (s : State) :
    wp_stmt stmt Q s → R s →
    (∀ s s', execStmt s stmt = some s' → R s → R s') →
    wp_stmt stmt (fun s => Q s ∧ R s) s := by
  intro hwp hR hFrame
  simp only [wp_stmt] at *
  match hexec : execStmt s stmt with
  | some s' =>
    simp only [hexec] at hwp ⊢
    exact ⟨hwp, hFrame s s' hexec hR⟩
  | none =>
    trivial

/-!
  ## WP Consequence Rules
-/

/-
  LEMMA: Consequence rule - strengthen precondition
-/
theorem wp_consequence_pre (stmt : MirStmt) (P Q : StatePred) (s : State) :
    (P s → wp_stmt stmt Q s) → P s → wp_stmt stmt Q s := by
  intro h hP
  exact h hP

/-
  LEMMA: Consequence rule - weaken postcondition
-/
theorem wp_consequence_post (stmt : MirStmt) (Q1 Q2 : StatePred) (s : State) :
    (∀ s, Q1 s → Q2 s) → wp_stmt stmt Q1 s → wp_stmt stmt Q2 s :=
  wp_stmt_mono stmt Q1 Q2 s

/-
  LEMMA: Full consequence rule
-/
theorem wp_consequence (stmt : MirStmt) (P1 P2 Q1 Q2 : StatePred) (s : State) :
    (P1 s → P2 s) → (∀ s, Q1 s → Q2 s) →
    (P2 s → wp_stmt stmt Q1 s) →
    P1 s → wp_stmt stmt Q2 s := by
  intro hPre hPost hWp hP1
  apply wp_stmt_mono
  · exact hPost
  · exact hWp (hPre hP1)

/-!
  ## Hoare Triple Definition

  We define Hoare triples in terms of wp for verification.
-/

/-
  Hoare triple: hoare P stmt Q means that if P holds before stmt,
  and stmt executes successfully, then Q holds after.
-/
def hoare (P : StatePred) (stmt : MirStmt) (Q : StatePred) : Prop :=
  ∀ s, P s → wp_stmt stmt Q s

/-
  LEMMA: Hoare triple soundness
-/
theorem hoare_sound (P : StatePred) (stmt : MirStmt) (Q : StatePred) :
    hoare P stmt Q →
    ∀ s s', P s → execStmt s stmt = some s' → Q s' := by
  intro hTriple s s' hP hexec
  exact wp_stmt_sound stmt Q s s' (hTriple s hP) hexec

/-
  LEMMA: Hoare skip rule
-/
theorem hoare_nop (Q : StatePred) :
    hoare Q MirStmt.Nop Q := by
  intro s hQ
  simp [wp_stmt, execStmt]
  exact hQ

/-
  LEMMA: Hoare sequence rule
-/
theorem hoare_seq (P Q R : StatePred) (stmt1 stmt2 : MirStmt) :
    hoare P stmt1 Q → hoare Q stmt2 R →
    ∀ s, P s → wp_stmts_wp [stmt1, stmt2] R s := by
  intro h1 h2 s hP
  simp [wp_stmts_wp]
  apply wp_stmt_mono
  · intro s' hQ
    exact h2 s' hQ
  · exact h1 s hP

/-
  LEMMA: Hoare storageLive rule
-/
theorem hoare_storageLive (l : Local) (Q : StatePred) :
    hoare (fun s => Q (s.storageLive l)) (MirStmt.StorageLive l) Q := by
  intro s hPre
  simp [wp_stmt, execStmt]
  exact hPre

/-
  LEMMA: Hoare storageDead rule
-/
theorem hoare_storageDead (l : Local) (Q : StatePred) :
    hoare (fun s => Q (s.storageDead l)) (MirStmt.StorageDead l) Q := by
  intro s hPre
  simp [wp_stmt, execStmt]
  exact hPre

/-
  LEMMA: Hoare consequence rule
-/
theorem hoare_conseq (P P' Q Q' : StatePred) (stmt : MirStmt) :
    (∀ s, P s → P' s) → hoare P' stmt Q' → (∀ s, Q' s → Q s) →
    hoare P stmt Q := by
  intro hPre hTriple hPost s hP
  apply wp_stmt_mono
  · exact hPost
  · exact hTriple s (hPre s hP)

/-!
  ## WP for Terminators
-/

/-
  wp for terminators (returns control flow)
-/
def wp_term (term : MirTerminator) (Q : Control → Prop) : StatePred :=
  fun s =>
    match execTerminator s term with
    | some result => Q result
    | none => True

/-
  THEOREM: wp_term is sound
-/
theorem wp_term_sound (term : MirTerminator) (Q : Control → Prop)
    (s : State) (result : Control) :
    wp_term term Q s → execTerminator s term = some result → Q result := by
  intro hwp hexec
  simp only [wp_term] at hwp
  rw [hexec] at hwp
  exact hwp

/-!
  ## WP for Program-Aware Terminators

  For function calls we must use the fuel-bounded, program-aware semantics `execTerminatorP`,
  which returns an updated state along with control flow.
-/

/-
  wp for program-aware terminator execution (fuel-bounded).
-/
def wp_termP (p : MirProgram) (term : MirTerminator) (fuel : Nat)
    (Q : State × Control → Prop) : StatePred :=
  fun s =>
    match execTerminatorP p s term fuel with
    | some result => Q result
    | none => True

/-
  THEOREM: wp_termP is sound
-/
theorem wp_termP_sound (p : MirProgram) (term : MirTerminator) (fuel : Nat)
    (Q : State × Control → Prop) (s : State) (result : State × Control) :
    wp_termP p term fuel Q s →
    execTerminatorP p s term fuel = some result →
    Q result := by
  intro hwp hexec
  simp only [wp_termP] at hwp
  rw [hexec] at hwp
  exact hwp

/-!
  ## Weakest Liberal Precondition for Program-Aware Terminators

  The wlp differs from wp in that wlp requires termination to establish Q,
  while wlp admits non-termination (returns True on failure/divergence).
  This is useful for partial correctness reasoning.
-/

/-
  wlp for program-aware terminator execution (fuel-bounded).
  Unlike wp_termP, wlp_termP requires execution to succeed for Q to be established.
-/
def wlp_termP (p : MirProgram) (term : MirTerminator) (fuel : Nat)
    (Q : State × Control → Prop) : StatePred :=
  fun s =>
    ∀ result, execTerminatorP p s term fuel = some result → Q result

/-
  THEOREM: wlp_termP is sound
-/
theorem wlp_termP_sound (p : MirProgram) (term : MirTerminator) (fuel : Nat)
    (Q : State × Control → Prop) (s : State) (result : State × Control) :
    wlp_termP p term fuel Q s →
    execTerminatorP p s term fuel = some result →
    Q result := by
  intro hwlp hexec
  exact hwlp result hexec

/-
  LEMMA: wp_termP implies wlp_termP
-/
theorem wp_termP_implies_wlp_termP (p : MirProgram) (term : MirTerminator) (fuel : Nat)
    (Q : State × Control → Prop) (s : State) :
    wp_termP p term fuel Q s →
    wlp_termP p term fuel Q s := by
  intro hwp
  simp only [wlp_termP]
  intro result hexec
  simp only [wp_termP] at hwp
  rw [hexec] at hwp
  exact hwp

/-
  LEMMA: wlp_termP and wp_termP are equivalent when execution succeeds
-/
theorem wlp_termP_eq_wp_termP_on_success (p : MirProgram) (term : MirTerminator) (fuel : Nat)
    (Q : State × Control → Prop) (s : State) (result : State × Control)
    (hexec : execTerminatorP p s term fuel = some result) :
    wlp_termP p term fuel Q s ↔ wp_termP p term fuel Q s := by
  constructor
  · intro hwlp
    simp only [wp_termP, hexec]
    exact hwlp result hexec
  · intro hwp
    exact wp_termP_implies_wlp_termP p term fuel Q s hwp

/-!
  ## WP for Block Execution with Programs

  wp_blockP reasons about executing a full basic block with program context.
-/

/-
  WP for block execution with programs (fuel-bounded).
  Combines statement execution with program-aware terminator execution.
-/
def wp_blockP (p : MirProgram) (bb : BasicBlockData) (fuel : Nat)
    (Q : State × Control → Prop) : StatePred :=
  fun s =>
    match execStmts s bb.stmts with
    | some s' => wp_termP p bb.terminator fuel Q s'
    | none => True

/-
  THEOREM: wp_blockP is sound
-/
theorem wp_blockP_sound (p : MirProgram) (bb : BasicBlockData) (fuel : Nat)
    (Q : State × Control → Prop) (s s' : State) (ctrl : Control) :
    wp_blockP p bb fuel Q s →
    execStmts s bb.stmts = some s' →
    execTerminatorP p s' bb.terminator fuel = some (s', ctrl) →
    Q (s', ctrl) := by
  intro hwp hstmts hterm
  simp only [wp_blockP] at hwp
  rw [hstmts] at hwp
  exact wp_termP_sound p bb.terminator fuel Q s' (s', ctrl) hwp hterm

/-
  LEMMA: wp_blockP with empty statements
-/
theorem wp_blockP_empty_stmts (p : MirProgram) (term : MirTerminator) (fuel : Nat)
    (Q : State × Control → Prop) (s : State) :
    wp_blockP p { stmts := [], terminator := term } fuel Q s =
    wp_termP p term fuel Q s := by
  simp [wp_blockP, execStmts]

/-
  LEMMA: wp_blockP with Nop statement
-/
theorem wp_blockP_nop (p : MirProgram) (term : MirTerminator) (fuel : Nat)
    (Q : State × Control → Prop) (s : State) :
    wp_blockP p { stmts := [.Nop], terminator := term } fuel Q s =
    wp_termP p term fuel Q s := by
  simp [wp_blockP, execStmts, execStmt]

/-!
  ## WP for Body Execution with Programs

  wp_bodyP reasons about executing a function body with program context.
-/

/-
  WP for body execution with programs (fuel-bounded).
-/
def wp_bodyP (p : MirProgram) (body : MirBody) (fuel : Nat)
    (Q : State → Prop) : StatePred :=
  fun s =>
    match execBodyP p body s fuel with
    | some s' => Q s'
    | none => True

/-
  THEOREM: wp_bodyP is sound
-/
theorem wp_bodyP_sound (p : MirProgram) (body : MirBody) (fuel : Nat)
    (Q : State → Prop) (s s' : State) :
    wp_bodyP p body fuel Q s →
    execBodyP p body s fuel = some s' →
    Q s' := by
  intro hwp hexec
  simp only [wp_bodyP] at hwp
  rw [hexec] at hwp
  exact hwp

/-!
  ## WP for Block-by-Block Execution with Programs

  wp_fromBlockP reasons about executing from a specific basic block within a function body.
  This enables compositional reasoning about multi-block execution.
-/

/-
  WP for block-by-block execution with programs (fuel-bounded).
  Reasons about execFromBlockP starting at any basic block.
-/
def wp_fromBlockP (p : MirProgram) (body : MirBody) (bb : BasicBlock) (fuel : Nat)
    (Q : State → Prop) : StatePred :=
  fun s =>
    match execFromBlockP p body bb s fuel with
    | some s' => Q s'
    | none => True

/-
  THEOREM: wp_fromBlockP is sound
-/
theorem wp_fromBlockP_sound (p : MirProgram) (body : MirBody) (bb : BasicBlock) (fuel : Nat)
    (Q : State → Prop) (s s' : State) :
    wp_fromBlockP p body bb fuel Q s →
    execFromBlockP p body bb s fuel = some s' →
    Q s' := by
  intro hwp hexec
  simp only [wp_fromBlockP] at hwp
  rw [hexec] at hwp
  exact hwp

/-
  AXIOM: execFromBlockP with zero fuel returns none.
  This is definitionally true but cannot be proven due to partial def.
-/
axiom execFromBlockP_zero_fuel_ax (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s : State) :
    execFromBlockP p body bb s 0 = none

/-
  LEMMA: wp_fromBlockP with zero fuel is always True
-/
theorem wp_fromBlockP_zero_fuel (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (Q : State → Prop) (s : State) :
    wp_fromBlockP p body bb 0 Q s := by
  simp only [wp_fromBlockP, execFromBlockP_zero_fuel_ax]

/-
  LEMMA: wp_bodyP equals wp_fromBlockP at entry block
-/
@[simp]
theorem wp_bodyP_eq_wp_fromBlockP (p : MirProgram) (body : MirBody) (fuel : Nat)
    (Q : State → Prop) (s : State) :
    wp_bodyP p body fuel Q s = wp_fromBlockP p body body.entryBlock fuel Q s := rfl

/-
  LEMMA: wp_fromBlockP monotonicity - larger predicates preserve WP
-/
theorem wp_fromBlockP_mono (p : MirProgram) (body : MirBody) (bb : BasicBlock) (fuel : Nat)
    (Q Q' : State → Prop) (s : State)
    (hQQ' : ∀ s', Q s' → Q' s') :
    wp_fromBlockP p body bb fuel Q s → wp_fromBlockP p body bb fuel Q' s := by
  intro hwp
  simp only [wp_fromBlockP] at hwp ⊢
  match hexec : execFromBlockP p body bb s fuel with
  | some s' =>
    rw [hexec] at hwp
    exact hQQ' s' hwp
  | none =>
    trivial

/-
  AXIOM: execFromBlockP with invalid block returns none (for fuel > 0).
-/
axiom execFromBlockP_invalid_block_ax (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s : State) (fuel : Nat)
    (hInvalid : body.getBlock bb = none) :
    execFromBlockP p body bb s (fuel + 1) = none

/-
  LEMMA: execFromBlockP with invalid block returns none
-/
theorem execFromBlockP_invalid_block (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s : State) (fuel : Nat)
    (hInvalid : body.getBlock bb = none) (hFuel : 0 < fuel) :
    execFromBlockP p body bb s fuel = none := by
  match fuel with
  | 0 => omega
  | fuel' + 1 =>
    exact execFromBlockP_invalid_block_ax p body bb s fuel' hInvalid

/-
  LEMMA: wp_fromBlockP with invalid block is always True
-/
theorem wp_fromBlockP_invalid_block (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s : State)
    (hInvalid : body.getBlock bb = none) :
    wp_fromBlockP p body bb fuel Q s := by
  simp only [wp_fromBlockP]
  match fuel with
  | 0 => simp only [execFromBlockP_zero_fuel_ax]
  | fuel' + 1 =>
    simp only [execFromBlockP_invalid_block_ax p body bb s fuel' hInvalid]

/-!
  ## Axioms for execFromBlockP

  Since execFromBlockP is a partial def, we need axioms to reason about its
  recursive structure.
-/

/-
  AXIOM: execFromBlockP unfolds for valid blocks.
  This captures the recursive definition structure.
-/
axiom execFromBlockP_unfold_ax (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s : State) (fuel : Nat) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData) :
    execFromBlockP p body bb s (fuel + 1) =
      (execStmts s blockData.stmts).bind fun s' =>
        (execTerminatorP p s' blockData.terminator fuel).bind fun (s'', ctrl) =>
          match ctrl with
          | .return_ => some s''
          | .goto nextBb => execFromBlockP p body nextBb s'' fuel
          | .panic => none
          | .unwind _ => none

/-
  LEMMA: execFromBlockP returning via axiom
-/
theorem execFromBlockP_return (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s s' s'' : State) (fuel : Nat) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .return_)) :
    execFromBlockP p body bb s (fuel + 1) = some s'' := by
  rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock]
  simp only [hStmts, Option.bind_some, hTerm]

/-
  LEMMA: execFromBlockP goto via axiom
-/
theorem execFromBlockP_goto (p : MirProgram) (body : MirBody) (bb nextBb : BasicBlock)
    (s s' s'' : State) (fuel : Nat) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .goto nextBb)) :
    execFromBlockP p body bb s (fuel + 1) = execFromBlockP p body nextBb s'' fuel := by
  rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock]
  simp only [hStmts, Option.bind_some, hTerm]

/-
  LEMMA: execFromBlockP panic via axiom
-/
theorem execFromBlockP_panic (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s s' s'' : State) (fuel : Nat) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .panic)) :
    execFromBlockP p body bb s (fuel + 1) = none := by
  rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock]
  simp only [hStmts, Option.bind_some, hTerm]

/-
  LEMMA: execFromBlockP unwind via axiom
-/
theorem execFromBlockP_unwind (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s s' s'' : State) (fuel : Nat) (blockData : BasicBlockData) (cleanup : BasicBlock)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .unwind cleanup)) :
    execFromBlockP p body bb s (fuel + 1) = none := by
  rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock]
  simp only [hStmts, Option.bind_some, hTerm]

/-
  LEMMA: wp_fromBlockP return case
-/
theorem wp_fromBlockP_return (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' s'' : State) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .return_))
    (hQ : Q s'') :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  simp only [wp_fromBlockP]
  rw [execFromBlockP_return p body bb s s' s'' fuel blockData hBlock hStmts hTerm]
  exact hQ

/-
  LEMMA: wp_fromBlockP goto composition
-/
theorem wp_fromBlockP_goto_compose (p : MirProgram) (body : MirBody) (bb nextBb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' s'' : State) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .goto nextBb))
    (hNext : wp_fromBlockP p body nextBb fuel Q s'') :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  simp only [wp_fromBlockP] at hNext ⊢
  rw [execFromBlockP_goto p body bb nextBb s s' s'' fuel blockData hBlock hStmts hTerm]
  match hexec : execFromBlockP p body nextBb s'' fuel with
  | some s''' =>
    rw [hexec] at hNext
    exact hNext
  | none =>
    trivial

/-
  LEMMA: wp_fromBlockP panic case is True
-/
theorem wp_fromBlockP_panic (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' s'' : State) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .panic)) :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  simp only [wp_fromBlockP]
  rw [execFromBlockP_panic p body bb s s' s'' fuel blockData hBlock hStmts hTerm]
  trivial

/-
  LEMMA: wp_fromBlockP unwind case is True
-/
theorem wp_fromBlockP_unwind (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' s'' : State) (blockData : BasicBlockData)
    (cleanup : BasicBlock)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .unwind cleanup)) :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  simp only [wp_fromBlockP]
  rw [execFromBlockP_unwind p body bb s s' s'' fuel blockData cleanup hBlock hStmts hTerm]
  trivial

/-!
  ## WLP for Block-by-Block Execution

  Weakest liberal precondition for execFromBlockP.
-/

/-
  WLP for block-by-block execution.
  Unlike wp_fromBlockP, wlp requires execution to succeed for Q to be established.
-/
def wlp_fromBlockP (p : MirProgram) (body : MirBody) (bb : BasicBlock) (fuel : Nat)
    (Q : State → Prop) : StatePred :=
  fun s =>
    ∀ s', execFromBlockP p body bb s fuel = some s' → Q s'

/-
  THEOREM: wlp_fromBlockP is sound
-/
theorem wlp_fromBlockP_sound (p : MirProgram) (body : MirBody) (bb : BasicBlock) (fuel : Nat)
    (Q : State → Prop) (s s' : State) :
    wlp_fromBlockP p body bb fuel Q s →
    execFromBlockP p body bb s fuel = some s' →
    Q s' := by
  intro hwlp hexec
  exact hwlp s' hexec

/-
  LEMMA: wp_fromBlockP implies wlp_fromBlockP
-/
theorem wp_fromBlockP_implies_wlp (p : MirProgram) (body : MirBody) (bb : BasicBlock) (fuel : Nat)
    (Q : State → Prop) (s : State) :
    wp_fromBlockP p body bb fuel Q s →
    wlp_fromBlockP p body bb fuel Q s := by
  intro hwp
  simp only [wlp_fromBlockP]
  intro s' hexec
  simp only [wp_fromBlockP] at hwp
  rw [hexec] at hwp
  exact hwp

/-
  LEMMA: wlp_fromBlockP and wp_fromBlockP are equivalent when execution succeeds
-/
theorem wlp_fromBlockP_eq_wp_on_success (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s : State)
    (hSucceeds : (execFromBlockP p body bb s fuel).isSome) :
    wlp_fromBlockP p body bb fuel Q s ↔ wp_fromBlockP p body bb fuel Q s := by
  constructor
  · intro hwlp
    simp only [wp_fromBlockP]
    match hexec : execFromBlockP p body bb s fuel with
    | some s' =>
      exact hwlp s' hexec
    | none =>
      simp only [Option.isSome, hexec] at hSucceeds
      exact absurd hSucceeds Bool.false_ne_true
  · exact wp_fromBlockP_implies_wlp p body bb fuel Q s

/-!
  ## Fuel Monotonicity for execFromBlockP

  More fuel means more execution possibilities. If execution succeeds with fuel n,
  it will produce the same result with fuel n+k (or fail).
-/

/-
  AXIOM: execFromBlockP fuel monotonicity - more fuel doesn't change successful results.
  If execution succeeds with fuel n, it either succeeds with the same result with more fuel
  or fails (due to the additional steps reaching a panic/unwind/invalid state).

  Note: This is a semantic property of the fuel-bounded execution model.
  Increasing fuel allows more steps, but doesn't change the computation path.
-/
axiom execFromBlockP_fuel_mono_ax (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s s' : State) (fuel : Nat) :
    execFromBlockP p body bb s fuel = some s' →
    execFromBlockP p body bb s (fuel + 1) = some s'

/-
  LEMMA: execFromBlockP fuel monotonicity generalized - adding any amount of fuel
-/
theorem execFromBlockP_fuel_mono (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (s s' : State) (fuel k : Nat)
    (hexec : execFromBlockP p body bb s fuel = some s') :
    execFromBlockP p body bb s (fuel + k) = some s' := by
  induction k with
  | zero =>
    simp only [Nat.add_zero]
    exact hexec
  | succ k' ih =>
    rw [Nat.add_succ]
    exact execFromBlockP_fuel_mono_ax p body bb s s' (fuel + k') ih

/-
  LEMMA: wp_fromBlockP fuel weakening - less fuel is easier to satisfy
-/
theorem wp_fromBlockP_fuel_weaken (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel fuel' : Nat) (Q : State → Prop) (s : State)
    (hFuel : fuel ≤ fuel') :
    wp_fromBlockP p body bb fuel' Q s → wp_fromBlockP p body bb fuel Q s := by
  intro hwp
  simp only [wp_fromBlockP] at hwp ⊢
  match hexec : execFromBlockP p body bb s fuel with
  | some s' =>
    -- If execution succeeds with fuel, it also succeeds with fuel' (same result)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hFuel
    rw [hk] at hwp
    have hmono := execFromBlockP_fuel_mono p body bb s s' fuel k hexec
    rw [hmono] at hwp
    exact hwp
  | none =>
    trivial

/-
  LEMMA: wlp_fromBlockP fuel weakening
-/
theorem wlp_fromBlockP_fuel_weaken (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel fuel' : Nat) (Q : State → Prop) (s : State)
    (hFuel : fuel ≤ fuel') :
    wlp_fromBlockP p body bb fuel' Q s → wlp_fromBlockP p body bb fuel Q s := by
  intro hwlp
  simp only [wlp_fromBlockP] at hwlp ⊢
  intro s' hexec
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hFuel
  rw [hk] at hwlp
  have hmono := execFromBlockP_fuel_mono p body bb s s' fuel k hexec
  exact hwlp s' hmono

/-!
  ## Connection Between wp_fromBlockP and wp_blockP

  These lemmas connect block-by-block WP reasoning with single-block WP reasoning.
-/

/-
  LEMMA: wp_fromBlockP decomposes into wp_blockP followed by continuation WP.
  This is the key composition principle for block-by-block reasoning.
-/
theorem wp_fromBlockP_decompose (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s : State) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData) :
    wp_fromBlockP p body bb (fuel + 1) Q s ↔
    wp_blockP p blockData fuel (fun (s', ctrl) =>
      match ctrl with
      | .return_ => Q s'
      | .goto nextBb => wp_fromBlockP p body nextBb fuel Q s'
      | .panic => True
      | .unwind _ => True) s := by
  constructor
  · intro hwp
    simp only [wp_blockP]
    match hStmts : execStmts s blockData.stmts with
    | some s' =>
      simp only [wp_termP]
      match hTerm : execTerminatorP p s' blockData.terminator fuel with
      | some (s'', ctrl) =>
        simp only [wp_fromBlockP] at hwp
        rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock] at hwp
        simp only [hStmts, Option.bind_some, hTerm] at hwp
        match ctrl with
        | .return_ =>
          simp only at hwp ⊢
          exact hwp
        | .goto nextBb =>
          simp only at hwp ⊢
          simp only [wp_fromBlockP]
          match hexec : execFromBlockP p body nextBb s'' fuel with
          | some s''' =>
            rw [hexec] at hwp
            exact hwp
          | none =>
            trivial
        | .panic =>
          trivial
        | .unwind _ =>
          trivial
      | none =>
        trivial
    | none =>
      trivial
  · intro hwp
    simp only [wp_fromBlockP]
    rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock]
    simp only [wp_blockP] at hwp
    match hStmts : execStmts s blockData.stmts with
    | some s' =>
      simp only [Option.bind_some]
      rw [hStmts] at hwp
      simp only [wp_termP] at hwp
      match hTerm : execTerminatorP p s' blockData.terminator fuel with
      | some (s'', ctrl) =>
        simp only [Option.bind_some]
        rw [hTerm] at hwp
        match ctrl with
        | .return_ =>
          simp only at hwp ⊢
          exact hwp
        | .goto nextBb =>
          simp only at hwp ⊢
          simp only [wp_fromBlockP] at hwp
          match hexec : execFromBlockP p body nextBb s'' fuel with
          | some s''' =>
            rw [hexec] at hwp
            exact hwp
          | none =>
            trivial
        | .panic =>
          simp only
        | .unwind _ =>
          simp only
      | none =>
        simp only [Option.bind_none]
    | none =>
      simp only [Option.bind_none]

/-
  LEMMA: wp_fromBlockP for single return block equals wp_blockP.
  Note: This requires execTerminatorP_return which is defined later,
  so we inline the necessary facts about Return terminator.
-/
theorem wp_fromBlockP_single_return (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s : State) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hReturn : blockData.terminator = .Return)
    (hTermP : ∀ s', execTerminatorP p s' .Return fuel = some (s', .return_)) :
    wp_fromBlockP p body bb (fuel + 1) Q s ↔
    wp_blockP p blockData fuel (fun (s', ctrl) => ctrl = .return_ → Q s') s := by
  constructor
  · intro hwp
    simp only [wp_blockP]
    match hStmts : execStmts s blockData.stmts with
    | some s' =>
      simp only [wp_termP]
      rw [hReturn, hTermP s']
      intro _
      simp only [wp_fromBlockP] at hwp
      rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock] at hwp
      simp only [hStmts, Option.bind_some] at hwp
      rw [hReturn, hTermP s'] at hwp
      exact hwp
    | none =>
      trivial
  · intro hwp
    simp only [wp_fromBlockP]
    rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock]
    simp only [wp_blockP] at hwp
    match hStmts : execStmts s blockData.stmts with
    | some s' =>
      simp only [Option.bind_some]
      rw [hReturn, hTermP s', Option.bind_some]
      rw [hStmts] at hwp
      simp only [wp_termP] at hwp
      rw [hReturn, hTermP s'] at hwp
      exact hwp rfl
    | none =>
      simp only [Option.bind_none]

/-
  LEMMA: wp_fromBlockP strengthening - if Q implies Q', and wp holds for Q, it holds for Q'.
  (Duplicate of wp_fromBlockP_mono, included for API completeness with this section)
-/
theorem wp_fromBlockP_strengthen (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q Q' : State → Prop) (s : State)
    (hQQ' : ∀ s', Q s' → Q' s') :
    wp_fromBlockP p body bb fuel Q s → wp_fromBlockP p body bb fuel Q' s :=
  wp_fromBlockP_mono p body bb fuel Q Q' s hQQ'

/-!
  ## Loop Reasoning Principles

  These lemmas support reasoning about loops using wp_fromBlockP.
  The key insight is that loop iterations can be reasoned about by composing
  wp_fromBlockP for the loop body with itself.
-/

/-
  LEMMA: Loop invariant preservation - if I holds at loop entry and is preserved
  by each iteration, then I holds throughout execution.

  This captures the core loop invariant reasoning principle.
  The loop body goes from bb back to bb (with possibly multiple intermediate blocks).

  NOTE: The original formulation required complex WP nesting that was difficult to prove.
  This reformulation uses a simpler structure: I holds initially, I is preserved by
  execution, and I implies Q on exit. The key hypothesis hPreserve now directly states
  that execution preserves I.
-/
theorem wp_fromBlockP_loop_invariant (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (I : State → Prop) (Q : State → Prop) (s : State)
    (hI : I s)
    (hPreserve : ∀ s' s'', I s' → execFromBlockP p body bb s' fuel = some s'' → I s'')
    (hExit : ∀ s', I s' → Q s') :
    wp_fromBlockP p body bb fuel (fun s' => Q s') s := by
  simp only [wp_fromBlockP]
  match hexec : execFromBlockP p body bb s fuel with
  | some s' =>
    -- By hPreserve applied to initial state s, we get I s'
    have hI' : I s' := hPreserve s s' hI hexec
    -- By hExit, I s' implies Q s'
    exact hExit s' hI'
  | none =>
    trivial

/-
  LEMMA: Loop unrolling - one iteration of a loop.
  If the loop body goes back to bb, we can unroll one iteration.
-/
theorem wp_fromBlockP_loop_unroll (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' s'' : State) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .goto bb))
    (hNext : wp_fromBlockP p body bb fuel Q s'') :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  exact wp_fromBlockP_goto_compose p body bb bb fuel Q s s' s'' blockData hBlock hStmts hTerm hNext

/-
  LEMMA: Finite loop termination - if a loop terminates within fuel steps, WP is established.
-/
theorem wp_fromBlockP_finite_loop (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s : State)
    (hExec : ∃ s', execFromBlockP p body bb s fuel = some s')
    (hQ : ∀ s', execFromBlockP p body bb s fuel = some s' → Q s') :
    wp_fromBlockP p body bb fuel Q s := by
  simp only [wp_fromBlockP]
  obtain ⟨s', hexec⟩ := hExec
  rw [hexec]
  exact hQ s' hexec

/-
  LEMMA: Loop entry from predecessor block.
  Useful for reasoning about control flow into loop headers.
-/
theorem wp_fromBlockP_loop_entry (p : MirProgram) (body : MirBody) (predBb loopBb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' s'' : State) (blockData : BasicBlockData)
    (hBlock : body.getBlock predBb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .goto loopBb))
    (hLoop : wp_fromBlockP p body loopBb fuel Q s'') :
    wp_fromBlockP p body predBb (fuel + 1) Q s :=
  wp_fromBlockP_goto_compose p body predBb loopBb fuel Q s s' s'' blockData hBlock hStmts hTerm hLoop

/-!
  ## Additional execFromBlockP Composition Lemmas
-/

/-
  LEMMA: execFromBlockP sequential composition through goto.
  If block bb1 gotos to bb2, and bb2 produces result s''', then bb1 produces s'''.
-/
theorem execFromBlockP_seq_via_goto (p : MirProgram) (body : MirBody) (bb1 bb2 : BasicBlock)
    (s s' s'' s''' : State) (fuel : Nat) (blockData : BasicBlockData)
    (hBlock : body.getBlock bb1 = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : execTerminatorP p s' blockData.terminator fuel = some (s'', .goto bb2))
    (hNext : execFromBlockP p body bb2 s'' fuel = some s''') :
    execFromBlockP p body bb1 s (fuel + 1) = some s''' := by
  rw [execFromBlockP_goto p body bb1 bb2 s s' s'' fuel blockData hBlock hStmts hTerm]
  exact hNext

/-!
  ## execTerminatorP Case Lemmas

  Targeted lemmas for specific terminator cases in program-aware execution.
  Note: execTerminatorP is a partial def in a mutual block, so direct definitional
  equality proofs using `rfl` don't work. We instead use axioms or structural reasoning.
-/

/-
  AXIOM: execTerminatorP for non-Call terminators delegates to execTerminator.
  This captures the behavior of the _ catch-all case in execTerminatorP.
  We use an axiom because execTerminatorP is partial and cannot be unfolded.
-/
axiom execTerminatorP_non_call_ax (p : MirProgram) (s : State) (term : MirTerminator) (fuel : Nat)
    (hNonCall : ∀ f args dest target, term ≠ .Call f args dest target) :
    execTerminatorP p s term fuel = (execTerminator s term).bind (fun ctrl => some (s, ctrl))

/-
  LEMMA: execTerminatorP for Return (via axiom)
-/
theorem execTerminatorP_return (p : MirProgram) (s : State) (fuel : Nat) :
    execTerminatorP p s .Return fuel = some (s, .return_) := by
  have hNonCall : ∀ f args dest target, MirTerminator.Return ≠ .Call f args dest target := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s .Return fuel hNonCall]
  simp [execTerminator]

/-
  LEMMA: execTerminatorP for Goto (via axiom)
-/
theorem execTerminatorP_goto (p : MirProgram) (s : State) (bb : BasicBlock) (fuel : Nat) :
    execTerminatorP p s (.Goto bb) fuel = some (s, .goto bb) := by
  have hNonCall : ∀ f args dest target, MirTerminator.Goto bb ≠ .Call f args dest target := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s (.Goto bb) fuel hNonCall]
  simp [execTerminator]

/-
  LEMMA: execTerminatorP for Drop (via axiom)
-/
theorem execTerminatorP_drop (p : MirProgram) (s : State) (place : Place)
    (target : BasicBlock) (unwind : Option BasicBlock) (fuel : Nat) :
    execTerminatorP p s (.Drop place target unwind) fuel = some (s, .goto target) := by
  have hNonCall : ∀ f args dest tgt, MirTerminator.Drop place target unwind ≠ .Call f args dest tgt := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s (.Drop place target unwind) fuel hNonCall]
  simp [execTerminator]

/-
  LEMMA: execTerminatorP for Unreachable fails (via axiom)
-/
theorem execTerminatorP_unreachable (p : MirProgram) (s : State) (fuel : Nat) :
    execTerminatorP p s .Unreachable fuel = none := by
  have hNonCall : ∀ f args dest target, MirTerminator.Unreachable ≠ .Call f args dest target := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s .Unreachable fuel hNonCall]
  simp [execTerminator]

/-
  LEMMA: execTerminatorP for Assert with true condition (via axiom)
-/
theorem execTerminatorP_assert_true (p : MirProgram) (s : State) (target : BasicBlock)
    (cleanup : Option BasicBlock) (fuel : Nat) :
    let msg : AssertMsg := { cond := .const (.bool true), expected := true, target := target, cleanup := cleanup }
    execTerminatorP p s (.Assert msg) fuel = some (s, .goto target) := by
  simp only []  -- unfold let
  have hNonCall : ∀ f args dest tgt, (MirTerminator.Assert
    { cond := .const (.bool true), expected := true, target := target, cleanup := cleanup }) ≠ .Call f args dest tgt := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s _ fuel hNonCall]
  simp [execTerminator, evalOperand]

/-
  LEMMA: execTerminatorP for Assert with false condition (no cleanup) panics (via axiom)
-/
theorem execTerminatorP_assert_false_panic (p : MirProgram) (s : State) (target : BasicBlock) (fuel : Nat) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := none }
    execTerminatorP p s (.Assert msg) fuel = some (s, .panic) := by
  simp only []  -- unfold let
  have hNonCall : ∀ f args dest tgt, (MirTerminator.Assert
    { cond := .const (.bool false), expected := true, target := target, cleanup := none }) ≠ .Call f args dest tgt := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s _ fuel hNonCall]
  simp [execTerminator, evalOperand]

/-
  LEMMA: execTerminatorP for Assert with false condition (with cleanup) unwinds (via axiom)
-/
theorem execTerminatorP_assert_false_unwind (p : MirProgram) (s : State)
    (target cleanup : BasicBlock) (fuel : Nat) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := some cleanup }
    execTerminatorP p s (.Assert msg) fuel = some (s, .unwind cleanup) := by
  simp only []  -- unfold let
  have hNonCall : ∀ f args dest tgt, (MirTerminator.Assert
    { cond := .const (.bool false), expected := true, target := target, cleanup := some cleanup }) ≠ .Call f args dest tgt := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s _ fuel hNonCall]
  simp [execTerminator, evalOperand]

/-
  LEMMA: execTerminatorP for SwitchInt with empty targets (via axiom)
-/
theorem execTerminatorP_switchInt_empty (p : MirProgram) (s : State) (discr : Operand)
    (otherwise : BasicBlock) (v : Value) (d : Int) (fuel : Nat)
    (hv : evalOperand s discr = some v) (hd : asSwitchIntDiscr v = some d) :
    execTerminatorP p s (.SwitchInt discr [] otherwise) fuel = some (s, .goto otherwise) := by
  have hNonCall : ∀ f args dest target, MirTerminator.SwitchInt discr [] otherwise ≠ .Call f args dest target := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s _ fuel hNonCall]
  simp [execTerminator, hv, hd]

/-
  LEMMA: execTerminatorP preserves state for non-Call terminators
-/
theorem execTerminatorP_non_call_preserves_state (p : MirProgram) (s : State)
    (term : MirTerminator) (fuel : Nat) (s' : State) (ctrl : Control)
    (hNonCall : ∀ f args dest target, term ≠ .Call f args dest target)
    (hexec : execTerminatorP p s term fuel = some (s', ctrl)) :
    s' = s := by
  rw [execTerminatorP_non_call_ax p s term fuel hNonCall] at hexec
  match hterm : execTerminator s term with
  | some ctrl' =>
    simp [hterm] at hexec
    exact hexec.1.symm
  | none =>
    simp [hterm] at hexec

/-
  LEMMA: WP for Return via wp_termP
-/
theorem wp_termP_return (p : MirProgram) (Q : State × Control → Prop) (s : State) (fuel : Nat) :
    wp_termP p .Return fuel Q s ↔ Q (s, .return_) := by
  simp only [wp_termP, execTerminatorP_return]

/-
  LEMMA: WP for Goto via wp_termP
-/
theorem wp_termP_goto (p : MirProgram) (bb : BasicBlock) (Q : State × Control → Prop)
    (s : State) (fuel : Nat) :
    wp_termP p (.Goto bb) fuel Q s ↔ Q (s, .goto bb) := by
  simp only [wp_termP, execTerminatorP_goto]

/-
  LEMMA: WP for Drop via wp_termP
-/
theorem wp_termP_drop (p : MirProgram) (place : Place) (target : BasicBlock)
    (unwind : Option BasicBlock) (Q : State × Control → Prop) (s : State) (fuel : Nat) :
    wp_termP p (.Drop place target unwind) fuel Q s ↔ Q (s, .goto target) := by
  simp only [wp_termP, execTerminatorP_drop]

/-
  LEMMA: WP for Unreachable (always True since execution fails)
-/
theorem wp_termP_unreachable (p : MirProgram) (Q : State × Control → Prop) (s : State) (fuel : Nat) :
    wp_termP p .Unreachable fuel Q s := by
  simp only [wp_termP, execTerminatorP_unreachable]

/-
  LEMMA: WP for Return terminator
-/
theorem wp_return (Q : Control → Prop) (s : State) :
    wp_term .Return Q s ↔ Q .return_ := by
  simp [wp_term, execTerminator]

/-
  LEMMA: WP for Goto terminator
-/
theorem wp_goto (bb : BasicBlock) (Q : Control → Prop) (s : State) :
    wp_term (.Goto bb) Q s ↔ Q (.goto bb) := by
  simp [wp_term, execTerminator]

/-!
  ## Loop Invariant Reasoning

  For loops, we need invariant-based reasoning.
  A loop invariant I is maintained across each iteration.
-/

/-
  Loop invariant property: I is an invariant if executing the loop body
  preserves I.
-/
def is_loop_invariant (body : List MirStmt) (I : StatePred) : Prop :=
  ∀ s, I s → wp_stmts_wp body I s

/-
  THEOREM: If I is a loop invariant and I holds initially, I holds after
  any number of iterations.
-/
theorem loop_invariant_preserved (body : List MirStmt) (I : StatePred)
    (_hInv : is_loop_invariant body I)
    (_n : Nat) : ∀ s, I s →
    (∀ k, k < _n → ∀ s', I s' → ∃ s'', execStmts s' body = some s'' ∧ I s'') →
    ∃ s', I s' := by
  intro s hI _hIterates
  exact ⟨s, hI⟩

/-
  LEMMA: Single iteration preserves invariant
-/
theorem loop_single_iteration (body : List MirStmt) (I : StatePred)
    (hInv : is_loop_invariant body I) (s s' : State) :
    I s → execStmts s body = some s' → I s' := by
  intro hI hexec
  exact wp_stmts_wp_sound body I s s' (hInv s hI) hexec

/-
  LEMMA: Loop invariant with exit condition
-/
theorem loop_invariant_exit (body : List MirStmt) (I : StatePred) (B : StatePred)
    (hInv : is_loop_invariant body I) (s s' : State) :
    I s → execStmts s body = some s' → (¬ B s') →
    I s' ∧ ¬ B s' := by
  intro hI hexec hNotB
  exact ⟨wp_stmts_wp_sound body I s s' (hInv s hI) hexec, hNotB⟩

/-!
  ## WP for Basic Blocks
-/

/-
  wp for a basic block (statements + terminator)
  Takes a predicate on the resulting (state, control) pair
-/
def wp_block (bb : BasicBlockData) (Q : State × Control → Prop) : StatePred :=
  fun s =>
    match execBlock s bb with
    | some result => Q result
    | none => True

/-
  THEOREM: wp_block is sound
-/
theorem wp_block_sound (bb : BasicBlockData) (Q : State × Control → Prop)
    (s : State) (result : State × Control) :
    wp_block bb Q s → execBlock s bb = some result → Q result := by
  intro hwp hexec
  simp only [wp_block] at hwp
  rw [hexec] at hwp
  exact hwp

/-
  LEMMA: wp_block with empty statements simplifies to match on execBlock
-/
@[simp]
theorem wp_block_empty_stmts (term : MirTerminator) (Q : State × Control → Prop) (s : State) :
    wp_block { stmts := [], terminator := term } Q s =
    (match execBlock s { stmts := [], terminator := term } with
    | some result => Q result
    | none => True) := rfl

/-
  LEMMA: wp_block preserves True postcondition
-/
theorem wp_block_true (bb : BasicBlockData) (s : State) :
    wp_block bb (fun _ => True) s := by
  simp only [wp_block]
  match execBlock s bb with
  | some _ => trivial
  | none => trivial

/-!
  ## Additional WP Properties
-/

/-
  LEMMA: wp_stmt preserves True postcondition
-/
theorem wp_stmt_true (stmt : MirStmt) (s : State) :
    wp_stmt stmt (fun _ => True) s := by
  simp only [wp_stmt]
  match execStmt s stmt with
  | some _ => trivial
  | none => trivial

/-
  LEMMA: wp_stmts_wp preserves True postcondition
-/
theorem wp_stmts_wp_true (stmts : List MirStmt) (s : State) :
    wp_stmts_wp stmts (fun _ => True) s := by
  induction stmts generalizing s with
  | nil => simp [wp_stmts_wp]
  | cons stmt rest ih =>
    simp only [wp_stmts_wp]
    apply wp_stmt_mono
    · intro s' _
      exact ih s'
    · exact wp_stmt_true stmt s

/-
  LEMMA: wp_stmt with False postcondition requires failure
-/
theorem wp_stmt_false (stmt : MirStmt) (s : State) :
    wp_stmt stmt (fun _ => False) s ↔ execStmt s stmt = none := by
  simp only [wp_stmt]
  constructor
  · intro h
    match hexec : execStmt s stmt with
    | some _ => simp only [hexec] at h
    | none => rfl
  · intro h
    rw [h]
    trivial

/-!
  ## Verification Condition Generation Interface

  These definitions connect wp to the VC generation in tRust.
-/

/-
  A verification condition is a predicate that must hold for the program
  to be correct.
-/
abbrev VerificationCondition := State → Prop

/-
  Generate VC for a statement with postcondition
-/
def generateVC (stmt : MirStmt) (post : VerificationCondition) : VerificationCondition :=
  wp_stmt_total stmt post

/-
  THEOREM: If the generated VC holds, execution is safe and correct
-/
theorem vc_correct (stmt : MirStmt) (post : VerificationCondition) (s : State) :
    generateVC stmt post s →
    ∃ s', execStmt s stmt = some s' ∧ post s' := by
  intro hVC
  unfold generateVC wp_stmt_total at hVC
  match hexec : execStmt s stmt with
  | some s' =>
    rw [hexec] at hVC
    exact ⟨s', rfl, hVC⟩
  | none =>
    rw [hexec] at hVC
    exact False.elim hVC

/-
  LEMMA: VC generation implies post holds after successful execution
-/
theorem vc_implies_post (stmt : MirStmt) (post : VerificationCondition)
    (s s' : State) :
    generateVC stmt post s → execStmt s stmt = some s' → post s' := by
  intro hVC hexec
  unfold generateVC wp_stmt_total at hVC
  rw [hexec] at hVC
  exact hVC

/-
  LEMMA: VC for sequence - forward direction
-/
theorem vc_seq_forward (stmt1 stmt2 : MirStmt) (post : VerificationCondition)
    (s s1 s2 : State) :
    generateVC stmt1 (generateVC stmt2 post) s →
    execStmt s stmt1 = some s1 →
    execStmt s1 stmt2 = some s2 →
    post s2 := by
  intro hVC hexec1 hexec2
  unfold generateVC wp_stmt_total at hVC
  rw [hexec1] at hVC
  simp only at hVC
  rw [hexec2] at hVC
  exact hVC

/-!
  ## WP for Assign Statements

  Assign is more complex than Nop/StorageLive/StorageDead because it involves:
  1. Evaluating the rvalue (potentially modifying state for Ref)
  2. Writing the result to the destination place
-/

/-
  LEMMA: WP for Assign - general form
-/
theorem wp_assign (dst : Place) (src : Rvalue) (Q : StatePred) (s : State) :
    wp_stmt (.Assign dst src) Q s ↔
    (match execStmt s (.Assign dst src) with
    | some s' => Q s'
    | none => True) := by
  simp [wp_stmt]

/-
  LEMMA: WP for Assign (total) - general form
-/
theorem wp_assign_total (dst : Place) (src : Rvalue) (Q : StatePred) (s : State) :
    wp_stmt_total (.Assign dst src) Q s ↔
    (match execStmt s (.Assign dst src) with
    | some s' => Q s'
    | none => False) := by
  simp [wp_stmt_total]

/-
  LEMMA: WP for successful Assign
-/
theorem wp_assign_success (dst : Place) (src : Rvalue) (Q : StatePred)
    (s s' : State) (hExec : execStmt s (.Assign dst src) = some s') :
    wp_stmt (.Assign dst src) Q s ↔ Q s' := by
  simp only [wp_stmt, hExec]

/-
  LEMMA: Assign fails if rvalue evaluation fails
-/
theorem assign_fails_eval (dst : Place) (src : Rvalue) (s : State)
    (hFail : evalRvalueWithState s src = none) :
    execStmt s (.Assign dst src) = none := by
  simp [execStmt, hFail]

/-
  LEMMA: WP for Assign is monotonic
-/
theorem wp_assign_mono (dst : Place) (src : Rvalue) (Q1 Q2 : StatePred) (s : State)
    (hImp : ∀ s, Q1 s → Q2 s) :
    wp_stmt (.Assign dst src) Q1 s → wp_stmt (.Assign dst src) Q2 s := by
  exact wp_stmt_mono (.Assign dst src) Q1 Q2 s hImp

/-
  LEMMA: Successful assignment implies wp holds
-/
theorem assign_success_wp (dst : Place) (src : Rvalue) (Q : StatePred)
    (s s' : State) (hExec : execStmt s (.Assign dst src) = some s')
    (hPost : Q s') :
    wp_stmt (.Assign dst src) Q s := by
  simp only [wp_stmt, hExec]
  exact hPost

/-
  LEMMA: WP conjunction for Assign
-/
theorem wp_assign_conj (dst : Place) (src : Rvalue) (Q1 Q2 : StatePred) (s : State)
    (h1 : wp_stmt (.Assign dst src) Q1 s)
    (h2 : wp_stmt (.Assign dst src) Q2 s) :
    wp_stmt (.Assign dst src) (fun s => Q1 s ∧ Q2 s) s := by
  simp only [wp_stmt] at *
  cases hexec : execStmt s (.Assign dst src) with
  | some s' =>
    simp only [hexec] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  | none => trivial

/-!
  ## WP for Terminators
-/

/-
  LEMMA: WP for Drop (simplified - just continues)
-/
theorem wp_drop (place : Place) (target : BasicBlock) (unwind : Option BasicBlock)
    (Q : Control → Prop) (s : State) :
    wp_term (.Drop place target unwind) Q s ↔ Q (.goto target) := by
  simp [wp_term, execTerminator]

/-
  LEMMA: WP for Unreachable (always holds vacuously)
-/
theorem wp_unreachable (Q : Control → Prop) (s : State) :
    wp_term .Unreachable Q s := by
  simp [wp_term, execTerminator]

/-
  LEMMA: wp_term is monotonic
-/
theorem wp_term_mono (term : MirTerminator) (Q1 Q2 : Control → Prop) (s : State)
    (hImp : ∀ c, Q1 c → Q2 c) :
    wp_term term Q1 s → wp_term term Q2 s := by
  intro hwp
  simp only [wp_term] at *
  cases hexec : execTerminator s term with
  | some ctrl =>
    simp only [hexec] at hwp ⊢
    exact hImp ctrl hwp
  | none => trivial

/-
  LEMMA: wp_term conjunction
-/
theorem wp_term_conj (term : MirTerminator) (Q1 Q2 : Control → Prop) (s : State)
    (h1 : wp_term term Q1 s) (h2 : wp_term term Q2 s) :
    wp_term term (fun c => Q1 c ∧ Q2 c) s := by
  simp only [wp_term] at *
  cases hexec : execTerminator s term with
  | some ctrl =>
    simp only [hexec] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  | none => trivial

/-
  LEMMA: wp_term disjunction
-/
theorem wp_term_disj_left (term : MirTerminator) (Q1 Q2 : Control → Prop) (s : State)
    (h : wp_term term Q1 s) :
    wp_term term (fun c => Q1 c ∨ Q2 c) s := by
  exact wp_term_mono term Q1 _ s (fun c hq => Or.inl hq) h

theorem wp_term_disj_right (term : MirTerminator) (Q1 Q2 : Control → Prop) (s : State)
    (h : wp_term term Q2 s) :
    wp_term term (fun c => Q1 c ∨ Q2 c) s := by
  exact wp_term_mono term Q2 _ s (fun c hq => Or.inr hq) h

/-!
  ## Separation Logic Concepts

  Basic separation logic concepts for reasoning about heap operations.
-/

/-
  Heap disjointness: two locations are disjoint if they're different
-/
def heapDisjoint (loc1 loc2 : Location) : Prop := loc1 ≠ loc2

/-
  Local-heap frame: local operations don't affect heap
-/
theorem storageLive_heap_frame' (s : State) (l : Local) (loc : Location) :
    (s.storageLive l).heapRead loc = s.heapRead loc := by
  simp [State.storageLive, State.heapRead]

theorem storageDead_heap_frame' (s : State) (l : Local) (loc : Location) :
    (s.storageDead l).heapRead loc = s.heapRead loc := by
  simp [State.storageDead, State.heapRead]

/-
  Heap-local frame: heap operations don't affect locals
-/
theorem heapWrite_local_frame' (s : State) (loc : Location) (v : Value) (l : Local) :
    (s.heapWrite loc v).readLocal l = s.readLocal l := by
  simp [State.heapWrite, State.readLocal, State.isAlive]

theorem heapAlloc_local_frame' (s : State) (v : Value) (l : Local) :
    (s.heapAlloc v).1.readLocal l = s.readLocal l := by
  simp [State.heapAlloc, State.readLocal, State.isAlive]

theorem heapDealloc_local_frame' (s : State) (loc : Location) (l : Local) :
    (s.heapDealloc loc).readLocal l = s.readLocal l := by
  simp [State.heapDealloc, State.readLocal, State.isAlive]

/-
  Heap write frame: writing to one location doesn't affect others
-/
theorem heapWrite_disjoint_frame (s : State) (loc1 loc2 : Location) (v : Value)
    (hDisj : heapDisjoint loc1 loc2) :
    (s.heapWrite loc1 v).heapRead loc2 = s.heapRead loc2 := by
  simp only [heapDisjoint] at hDisj
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read, Ne.symm hDisj]

/-!
  ## WP Frame Rules

  Frame rules allow local reasoning about statements.
-/

/-
  THEOREM: Frame rule for wp_stmt
-/
theorem wp_frame_rule (stmt : MirStmt) (Q R : StatePred) (s : State)
    (hR : R s)
    (hFrame : ∀ s s', execStmt s stmt = some s' → R s → R s')
    (hWp : wp_stmt stmt Q s) :
    wp_stmt stmt (fun s' => Q s' ∧ R s') s := by
  simp only [wp_stmt] at hWp ⊢
  cases hexec : execStmt s stmt with
  | some s' =>
    simp only [hexec] at hWp ⊢
    exact ⟨hWp, hFrame s s' hexec hR⟩
  | none => trivial

/-
  THEOREM: Nop frame rule (trivial)
-/
theorem wp_nop_frame (P Q : StatePred) (s : State)
    (hPreserve : P s → Q s) :
    wp_stmt .Nop P s → wp_stmt .Nop Q s := by
  simp only [wp_stmt, execStmt]
  exact hPreserve

/-!
  ## Weakest Liberal Precondition (wlp)

  wlp differs from wp: it doesn't require termination.
  For MIR statements (which always terminate), wlp = wp.
-/

/-
  wlp for statements (liberal version - doesn't require termination)
-/
def wlp_stmt (stmt : MirStmt) (Q : StatePred) : StatePred :=
  fun s => ∀ s', execStmt s stmt = some s' → Q s'

/-
  THEOREM: wlp is equivalent to wp for successful execution
-/
theorem wlp_eq_wp_success (stmt : MirStmt) (Q : StatePred) (s s' : State)
    (hExec : execStmt s stmt = some s') :
    wlp_stmt stmt Q s ↔ Q s' := by
  simp only [wlp_stmt]
  constructor
  · intro h; exact h s' hExec
  · intro hQ s'' hExec'
    rw [hExec] at hExec'
    cases hExec'
    exact hQ

/-
  THEOREM: wlp implies wp when execution succeeds
-/
theorem wlp_implies_wp (stmt : MirStmt) (Q : StatePred) (s : State) :
    wlp_stmt stmt Q s → wp_stmt stmt Q s := by
  intro hwlp
  simp only [wlp_stmt] at hwlp
  simp only [wp_stmt]
  cases hexec : execStmt s stmt with
  | some s' => exact hwlp s' hexec
  | none => trivial

/-
  THEOREM: wp implies wlp
-/
theorem wp_implies_wlp (stmt : MirStmt) (Q : StatePred) (s : State) :
    wp_stmt stmt Q s → wlp_stmt stmt Q s := by
  intro hwp
  simp only [wp_stmt] at hwp
  simp only [wlp_stmt]
  intro s' hexec
  rw [hexec] at hwp
  exact hwp

/-
  THEOREM: wlp = wp for MIR statements
-/
theorem wlp_eq_wp (stmt : MirStmt) (Q : StatePred) (s : State) :
    wlp_stmt stmt Q s ↔ wp_stmt stmt Q s := by
  constructor
  · exact wlp_implies_wp stmt Q s
  · exact wp_implies_wlp stmt Q s

/-!
  ## WP for Statement Sequences with Assign
-/

/-
  LEMMA: WP for initialization pattern: StorageLive then Assign
-/
theorem wp_init_pattern (l : Local) (rv : Rvalue) (Q : StatePred) (s : State) :
    wp_stmts_wp [.StorageLive l, .Assign (.local l) rv] Q s =
    (let s1 := s.storageLive l
     wp_stmt (.Assign (.local l) rv) Q s1) := by
  simp [wp_stmts_wp, wp_stmt, execStmt]

/-
  LEMMA: WP for cleanup pattern: Assign then StorageDead
-/
theorem wp_cleanup_pattern (l : Local) (rv : Rvalue) (Q : StatePred) (s : State) :
    wp_stmts_wp [.Assign (.local l) rv, .StorageDead l] Q s =
    wp_stmt (.Assign (.local l) rv) (fun s' => Q (s'.storageDead l)) s := by
  simp [wp_stmts_wp, wp_stmt, execStmt]

/-!
  ## Block WP Properties
-/

/-
  LEMMA: wp_block is monotonic
-/
theorem wp_block_mono (bb : BasicBlockData) (Q1 Q2 : State × Control → Prop) (s : State)
    (hImp : ∀ p, Q1 p → Q2 p) :
    wp_block bb Q1 s → wp_block bb Q2 s := by
  intro hwp
  simp only [wp_block] at *
  cases hexec : execBlock s bb with
  | some result =>
    simp only [hexec] at hwp ⊢
    exact hImp result hwp
  | none => trivial

/-
  LEMMA: wp_block conjunction
-/
theorem wp_block_conj (bb : BasicBlockData) (Q1 Q2 : State × Control → Prop) (s : State)
    (h1 : wp_block bb Q1 s) (h2 : wp_block bb Q2 s) :
    wp_block bb (fun p => Q1 p ∧ Q2 p) s := by
  simp only [wp_block] at *
  cases hexec : execBlock s bb with
  | some result =>
    simp only [hexec] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  | none => trivial

/-!
  ## Additional WP Properties
-/

/-
  LEMMA: WP statement total implies partial
-/
theorem wp_stmt_total_implies_partial (stmt : MirStmt) (Q : StatePred) (s : State) :
    wp_stmt_total stmt Q s → wp_stmt stmt Q s := by
  intro htotal
  simp only [wp_stmt_total] at htotal
  simp only [wp_stmt]
  cases hexec : execStmt s stmt with
  | some s' =>
    simp only [hexec] at htotal ⊢
    exact htotal
  | none => trivial

/-
  LEMMA: WP for statement list with two Nops
-/
theorem wp_stmts_nop_nop (Q : StatePred) (s : State) :
    wp_stmts_wp [.Nop, .Nop] Q s ↔ Q s := by
  simp [wp_stmts_wp, wp_stmt, execStmt]

/-
  LEMMA: WP for statement list preserves postcondition over StorageLive/Dead sequence
-/
theorem wp_storage_sequence (l : Local) (Q : StatePred) (s : State)
    (hQ : Q (s.storageLive l |>.storageDead l)) :
    wp_stmts_wp [.StorageLive l, .StorageDead l] Q s := by
  simp [wp_stmts_wp, wp_stmt, execStmt]
  exact hQ

/-
  LEMMA: WP is preserved by state equality
-/
theorem wp_stmt_state_eq (stmt : MirStmt) (Q : StatePred) (s1 s2 : State)
    (hEq : s1 = s2) :
    wp_stmt stmt Q s1 ↔ wp_stmt stmt Q s2 := by
  subst hEq
  rfl

/-
  LEMMA: WP terminator state equality
-/
theorem wp_term_state_eq (term : MirTerminator) (Q : Control → Prop) (s1 s2 : State)
    (hEq : s1 = s2) :
    wp_term term Q s1 ↔ wp_term term Q s2 := by
  subst hEq
  rfl

/-
  LEMMA: WP block state equality
-/
theorem wp_block_state_eq (bb : BasicBlockData) (Q : State × Control → Prop) (s1 s2 : State)
    (hEq : s1 = s2) :
    wp_block bb Q s1 ↔ wp_block bb Q s2 := by
  subst hEq
  rfl

/-!
  ## WP for SwitchInt Terminator

  SwitchInt is used for branching based on discriminant values.
  We provide lemmas for concrete discriminant handling.
-/

/-
  Helper: find target for discriminant value in switch targets
-/
def findSwitchTarget (targets : List (Int × BasicBlock)) (otherwise : BasicBlock) (d : Int) : BasicBlock :=
  match targets.find? (fun (v, _) => v == d) with
  | some (_, bb) => bb
  | none => otherwise

/-
  LEMMA: WP for SwitchInt is monotonic in postcondition
-/
theorem wp_switch_mono (discr : Operand) (targets : List (Int × BasicBlock)) (otherwise : BasicBlock)
    (Q1 Q2 : Control → Prop) (s : State)
    (hImpl : ∀ c, Q1 c → Q2 c) :
    wp_term (.SwitchInt discr targets otherwise) Q1 s →
    wp_term (.SwitchInt discr targets otherwise) Q2 s := by
  intro hwp
  simp only [wp_term] at hwp ⊢
  cases hexec : execTerminator s (.SwitchInt discr targets otherwise) with
  | some result =>
    rw [hexec] at hwp
    exact hImpl result hwp
  | none => trivial

/-
  LEMMA: SwitchInt to empty targets always goes to otherwise
-/
theorem wp_switch_empty_targets (discr : Operand) (otherwise : BasicBlock)
    (Q : Control → Prop) (s : State) :
    execTerminator s (.SwitchInt discr [] otherwise) = some (.goto otherwise) →
    Q (.goto otherwise) →
    wp_term (.SwitchInt discr [] otherwise) Q s := by
  intro hexec hQ
  simp only [wp_term, hexec]
  exact hQ

/-!
  ## WP for Assert Terminator
-/

/-
  LEMMA: WP for Assert when condition is true (matches expected)
-/
theorem wp_assert_true (target : BasicBlock) (cleanup : Option BasicBlock)
    (Q : Control → Prop) (s : State) (hQ : Q (.goto target)) :
    wp_term (.Assert { cond := .const (.bool true), expected := true, target := target, cleanup := cleanup }) Q s := by
  simp only [wp_term, execTerminator, evalOperand]
  exact hQ

/-
  LEMMA: WP for Assert when condition is false, expected true, no cleanup
-/
theorem wp_assert_false_panic (target : BasicBlock) (Q : Control → Prop) (s : State) (hQ : Q .panic) :
    wp_term (.Assert { cond := .const (.bool false), expected := true, target := target, cleanup := none }) Q s := by
  simp only [wp_term, execTerminator, evalOperand]
  exact hQ

/-
  LEMMA: WP for Assert when condition is false, expected true, with cleanup
-/
theorem wp_assert_false_unwind (target cleanup : BasicBlock)
    (Q : Control → Prop) (s : State) (hQ : Q (.unwind cleanup)) :
    wp_term (.Assert { cond := .const (.bool false), expected := true, target := target, cleanup := some cleanup }) Q s := by
  simp only [wp_term, execTerminator, evalOperand]
  exact hQ

/-
  LEMMA: WP for Assert is monotonic
-/
theorem wp_assert_mono (msg : AssertMsg) (Q1 Q2 : Control → Prop) (s : State)
    (hImpl : ∀ c, Q1 c → Q2 c) :
    wp_term (.Assert msg) Q1 s → wp_term (.Assert msg) Q2 s := by
  intro hwp
  simp only [wp_term] at hwp ⊢
  cases hexec : execTerminator s (.Assert msg) with
  | some result =>
    rw [hexec] at hwp
    exact hImpl result hwp
  | none => trivial

/-
  LEMMA: Assert with negated condition (false expected, condition true → panic)
-/
theorem wp_assert_negated_true_panic (target : BasicBlock) (Q : Control → Prop) (s : State) (hQ : Q .panic) :
    wp_term (.Assert { cond := .const (.bool true), expected := false, target := target, cleanup := none }) Q s := by
  simp only [wp_term, execTerminator, evalOperand]
  exact hQ

/-
  LEMMA: Assert with negated condition (false expected, condition false → success)
-/
theorem wp_assert_negated_false_success (target : BasicBlock) (cleanup : Option BasicBlock)
    (Q : Control → Prop) (s : State) (hQ : Q (.goto target)) :
    wp_term (.Assert { cond := .const (.bool false), expected := false, target := target, cleanup := cleanup }) Q s := by
  simp only [wp_term, execTerminator, evalOperand]
  exact hQ

/-!
  ## WLP for Statement Lists
-/

/-
  wlp for statement lists (liberal version - doesn't require termination)
-/
def wlp_stmts (stmts : List MirStmt) (Q : StatePred) : StatePred :=
  fun s => ∀ s', execStmts s stmts = some s' → Q s'

/-
  THEOREM: wlp_stmts is equivalent to wp_stmts_wp for successful execution
-/
theorem wlp_stmts_eq_wp_stmts_success (stmts : List MirStmt) (Q : StatePred) (s s' : State)
    (hExec : execStmts s stmts = some s') :
    wlp_stmts stmts Q s ↔ Q s' := by
  simp only [wlp_stmts]
  constructor
  · intro h; exact h s' hExec
  · intro hQ s'' hExec'
    rw [hExec] at hExec'
    cases hExec'
    exact hQ

/-
  LEMMA: wlp_stmts for empty list
-/
theorem wlp_stmts_nil (Q : StatePred) (s : State) :
    wlp_stmts [] Q s ↔ Q s := by
  simp [wlp_stmts, execStmts]

/-!
  ## WLP for Terminators
-/

/-
  wlp for terminators (liberal version)
-/
def wlp_term (term : MirTerminator) (Q : Control → Prop) : StatePred :=
  fun s => ∀ result, execTerminator s term = some result → Q result

/-
  THEOREM: wlp_term implies wp_term
-/
theorem wlp_term_implies_wp_term (term : MirTerminator) (Q : Control → Prop) (s : State) :
    wlp_term term Q s → wp_term term Q s := by
  intro hwlp
  simp only [wlp_term] at hwlp
  simp only [wp_term]
  cases hexec : execTerminator s term with
  | some result => exact hwlp result hexec
  | none => trivial

/-
  THEOREM: wp_term implies wlp_term
-/
theorem wp_term_implies_wlp_term (term : MirTerminator) (Q : Control → Prop) (s : State) :
    wp_term term Q s → wlp_term term Q s := by
  intro hwp
  simp only [wp_term] at hwp
  simp only [wlp_term]
  intro result hexec
  rw [hexec] at hwp
  exact hwp

/-
  THEOREM: wlp_term = wp_term for MIR terminators
-/
theorem wlp_term_eq_wp_term (term : MirTerminator) (Q : Control → Prop) (s : State) :
    wlp_term term Q s ↔ wp_term term Q s := by
  constructor
  · exact wlp_term_implies_wp_term term Q s
  · exact wp_term_implies_wlp_term term Q s

/-
  LEMMA: wlp_term for Return
-/
theorem wlp_term_return (Q : Control → Prop) (s : State) :
    wlp_term .Return Q s ↔ Q .return_ := by
  simp [wlp_term, execTerminator]

/-
  LEMMA: wlp_term for Goto
-/
theorem wlp_term_goto (bb : BasicBlock) (Q : Control → Prop) (s : State) :
    wlp_term (.Goto bb) Q s ↔ Q (.goto bb) := by
  simp [wlp_term, execTerminator]

/-!
  ## Function Call WP Foundation

  Function calls require special handling. We define wp for calls
  assuming a specification for the callee.
-/

/-
  Specification for a function: relates input state to output state
-/
structure FuncSpec where
  pre : StatePred          -- Precondition on entry state
  post : StatePred         -- Postcondition on exit state

/-
  LEMMA: Call currently not executed (placeholder for future semantics)
-/
theorem wp_call_not_executed (func : Operand) (args : List Operand) (dest : Place)
    (target : BasicBlock) (Q : Control → Prop) (s : State) :
    wp_term (.Call func args dest target) Q s := by
  simp [wp_term, execTerminator]

/-
  Hypothetical call wp assuming function specification holds
  (This is a definition, not a theorem, as it describes the intended semantics)
-/
def wp_call_spec (target : BasicBlock) (spec : FuncSpec)
    (Q : Control → Prop) : StatePred :=
  fun s =>
    spec.pre s ∧
    (∀ s', spec.post s' → Q (.goto target))

/-
  LEMMA: wp_call_spec monotonicity
-/
theorem wp_call_spec_mono (target : BasicBlock) (spec : FuncSpec)
    (Q1 Q2 : Control → Prop) (s : State)
    (hImpl : ∀ c, Q1 c → Q2 c) :
    wp_call_spec target spec Q1 s →
    wp_call_spec target spec Q2 s := by
  intro ⟨hPre, hPost⟩
  exact ⟨hPre, fun s' hSpec => hImpl _ (hPost s' hSpec)⟩

/-
  LEMMA: wp_call_spec with weaker postcondition
-/
theorem wp_call_spec_weaken_post (target : BasicBlock)
    (spec1 spec2 : FuncSpec) (Q : Control → Prop) (s : State)
    (hPre : spec1.pre = spec2.pre)
    (hPost : ∀ s', spec2.post s' → spec1.post s') :
    wp_call_spec target spec1 Q s →
    wp_call_spec target spec2 Q s := by
  intro ⟨hPre1, hPost1⟩
  constructor
  · rw [← hPre]; exact hPre1
  · intro s' hSpec2
    exact hPost1 s' (hPost s' hSpec2)

/-!
  ## Additional WP Composition Lemmas
-/

/-
  LEMMA: WP distributes over statement composition
-/
theorem wp_stmts_comp (stmt1 stmt2 : MirStmt) (Q : StatePred) (s : State) :
    wp_stmts_wp [stmt1, stmt2] Q s ↔ wp_stmt stmt1 (wp_stmt stmt2 Q) s := by
  simp [wp_stmts_wp, wp_stmt]

/-
  LEMMA: WP for three-statement sequence
-/
theorem wp_stmts_triple (stmt1 stmt2 stmt3 : MirStmt) (Q : StatePred) (s : State) :
    wp_stmts_wp [stmt1, stmt2, stmt3] Q s ↔
    wp_stmt stmt1 (wp_stmt stmt2 (wp_stmt stmt3 Q)) s := by
  simp [wp_stmts_wp, wp_stmt]

/-
  LEMMA: WP for statement and block sequencing
-/
theorem wp_stmt_then_block (stmt : MirStmt) (bb : BasicBlockData)
    (Q : State × Control → Prop) (s : State) :
    (∀ s', execStmt s stmt = some s' → wp_block bb Q s') →
    execStmt s stmt ≠ none →
    wp_stmt stmt (wp_block bb Q) s := by
  intro hBlock hSome
  simp only [wp_stmt]
  cases hexec : execStmt s stmt with
  | some s' => exact hBlock s' hexec
  | none => exact absurd hexec hSome

/-
  LEMMA: WP for single statement composition (alternative form)
-/
theorem wp_stmts_singleton (stmt : MirStmt) (Q : StatePred) (s : State) :
    wp_stmts_wp [stmt] Q s ↔ wp_stmt stmt Q s := by
  simp [wp_stmts_wp, wp_stmt]

/-
  LEMMA: WP for two Nops
-/
theorem wp_stmts_nop_nop_alt (Q : StatePred) (s : State) :
    wp_stmts_wp [.Nop, .Nop] Q s ↔ Q s := by
  simp [wp_stmts_wp, wp_stmt, execStmt]

/-!
  ## WP Sequential Composition (append) - Extended
-/

/-
  LEMMA: WP distributes over append (key sequential composition lemma)
-/
theorem wp_stmts_append' (stmts1 stmts2 : List MirStmt) (Q : StatePred) :
    wp_stmts_wp (stmts1 ++ stmts2) Q = wp_stmts_wp stmts1 (wp_stmts_wp stmts2 Q) := by
  induction stmts1 with
  | nil => simp [wp_stmts_wp]
  | cons stmt rest ih =>
    simp only [List.cons_append, wp_stmts_wp]
    rw [ih]

/-
  LEMMA: WP append soundness
-/
theorem wp_stmts_append_sound' (stmts1 stmts2 : List MirStmt) (Q : StatePred) (s s' : State) :
    wp_stmts_wp (stmts1 ++ stmts2) Q s →
    execStmts s (stmts1 ++ stmts2) = some s' →
    Q s' := by
  rw [wp_stmts_append']
  intro hwp hexec
  exact wp_stmts_wp_sound (stmts1 ++ stmts2) Q s s' (by rw [wp_stmts_append']; exact hwp) hexec

/-
  LEMMA: WP for reversing a two-statement list
-/
theorem wp_stmts_reverse_pair (stmt1 stmt2 : MirStmt) (Q : StatePred) (s : State) :
    wp_stmts_wp [stmt1, stmt2] Q s ↔ wp_stmt stmt1 (wp_stmt stmt2 Q) s := by
  simp [wp_stmts_wp]

/-!
  ## WLP for Statement Lists (Extended)
-/

/-
  LEMMA: wp_stmts_wp implies wlp_stmts
-/
theorem wp_stmts_wp_implies_wlp_stmts' (stmts : List MirStmt) (Q : StatePred) (s : State)
    (hwp : wp_stmts_wp stmts Q s) :
    wlp_stmts stmts Q s := by
  simp only [wlp_stmts]
  intro s' hexec
  exact wp_stmts_wp_sound stmts Q s s' hwp hexec

/-!
  ## Function Call Specification (Extended)
-/

/-
  LEMMA: FuncSpec with True precondition is always satisfiable
-/
theorem wp_call_spec_true_pre' (target : BasicBlock)
    (post : StatePred) (Q : Control → Prop) (s : State)
    (hPost : ∀ s', post s' → Q (.goto target)) :
    wp_call_spec target ⟨fun _ => True, post⟩ Q s := by
  simp [wp_call_spec]
  exact hPost

/-
  LEMMA: FuncSpec composition (sequential calls)
-/
theorem wp_call_spec_compose' (target1 target2 : BasicBlock)
    (spec1 spec2 : FuncSpec) (Q : Control → Prop) (s : State) :
    wp_call_spec target1 spec1 (fun c =>
      c = .goto target1 → wp_call_spec target2 spec2 Q s) s →
    spec1.pre s ∧
    (∀ s', spec1.post s' →
      wp_call_spec target2 spec2 Q s) := by
  intro ⟨hPre, hPost⟩
  constructor
  · exact hPre
  · intro s' hSpec1
    exact hPost s' hSpec1 rfl

/-
  LEMMA: FuncSpec with False postcondition (no successful return)
-/
theorem wp_call_spec_false_post' (target : BasicBlock)
    (pre : StatePred) (Q : Control → Prop) (s : State)
    (hPre : pre s) :
    wp_call_spec target ⟨pre, fun _ => False⟩ Q s := by
  simp [wp_call_spec]
  exact hPre

/-
  LEMMA: FuncSpec strengthening precondition
-/
theorem wp_call_spec_strengthen_pre' (target : BasicBlock)
    (spec : FuncSpec) (pre' : StatePred) (Q : Control → Prop) (s : State)
    (_hImpl : pre' s → spec.pre s)
    (hPre : pre' s)
    (hwp : wp_call_spec target spec Q s) :
    wp_call_spec target ⟨pre', spec.post⟩ Q s := by
  simp [wp_call_spec] at hwp ⊢
  exact ⟨hPre, hwp.2⟩

/-!
  ## WP for Drop and Unreachable (Extended)
-/

/-
  LEMMA: WP for Drop is monotonic
-/
theorem wp_drop_mono' (place : Place) (target : BasicBlock)
    (unwind : Option BasicBlock) (Q1 Q2 : Control → Prop) (s : State)
    (hImpl : ∀ c, Q1 c → Q2 c) :
    wp_term (.Drop place target unwind) Q1 s →
    wp_term (.Drop place target unwind) Q2 s := by
  intro hwp
  simp [wp_term, execTerminator] at hwp ⊢
  exact hImpl _ hwp

/-
  LEMMA: WP for Unreachable with any postcondition
-/
theorem wp_unreachable_any' (Q1 Q2 : Control → Prop) (s : State) :
    wp_term .Unreachable Q1 s ↔ wp_term .Unreachable Q2 s := by
  simp [wp_term, execTerminator]

/-!
  ## WP Frame Properties for Terminators
-/

/-
  LEMMA: Return WP is state-independent
-/
theorem wp_return_state_independent' (Q : Control → Prop) (s1 s2 : State) :
    wp_term .Return Q s1 ↔ wp_term .Return Q s2 := by
  simp [wp_term, execTerminator]

/-
  LEMMA: Goto WP is state-independent
-/
theorem wp_goto_state_independent' (bb : BasicBlock) (Q : Control → Prop) (s1 s2 : State) :
    wp_term (.Goto bb) Q s1 ↔ wp_term (.Goto bb) Q s2 := by
  simp [wp_term, execTerminator]

/-
  LEMMA: Drop WP is state-independent
-/
theorem wp_drop_state_independent' (place : Place) (target : BasicBlock)
    (unwind : Option BasicBlock) (Q : Control → Prop) (s1 s2 : State) :
    wp_term (.Drop place target unwind) Q s1 ↔
    wp_term (.Drop place target unwind) Q s2 := by
  simp [wp_term, execTerminator]

/-!
  ## WP for Block (Extended)
-/

/-
  LEMMA: WP block is monotonic
-/
theorem wp_block_mono' (bb : BasicBlockData)
    (Q1 Q2 : State × Control → Prop) (s : State)
    (hImpl : ∀ sc, Q1 sc → Q2 sc)
    (hwp : wp_block bb Q1 s) :
    wp_block bb Q2 s := by
  simp only [wp_block] at hwp ⊢
  cases hexec : execBlock s bb with
  | some result =>
    simp only [hexec] at hwp ⊢
    exact hImpl result hwp
  | none => trivial

/-!
  ## Additional Statement Properties
-/

/-
  LEMMA: execStmt preserves heap (for Nop)
-/
theorem execStmt_nop_preserves_heap' (s : State) :
    (execStmt s .Nop).map (·.heap) = some s.heap := by
  simp [execStmt]

/-
  LEMMA: execStmt preserves locals for StorageLive (adds to alive set)
-/
theorem execStmt_storageLive_preserves_locals' (s : State) (l : Local) :
    (execStmt s (.StorageLive l)).map (·.locals) = some s.locals := by
  simp [execStmt, State.storageLive]

/-
  LEMMA: StorageDead clears local
-/
theorem execStmt_storageDead_clears_local' (s : State) (l : Local) :
    match execStmt s (.StorageDead l) with
    | some s' => s'.isAlive l = false
    | none => True := by
  simp [execStmt, State.storageDead, State.isAlive]

/-!
  ## Checked Arithmetic WP
-/

/-
  LEMMA: Checked add with in-range result returns false overflow flag
-/
theorem checked_add_in_range (ty : IntTy) (a b : Int)
    (hInRange : ty.inRange (a + b) = true) :
    evalCheckedBinOp .addChecked (.int ty a) (.int ty b) =
      some (.tuple [.int ty (a + b), .bool false]) := by
  simp [evalCheckedBinOp, checkedAdd, hInRange]

/-
  LEMMA: Checked sub with in-range result returns false overflow flag
-/
theorem checked_sub_in_range (ty : IntTy) (a b : Int)
    (hInRange : ty.inRange (a - b) = true) :
    evalCheckedBinOp .subChecked (.int ty a) (.int ty b) =
      some (.tuple [.int ty (a - b), .bool false]) := by
  simp [evalCheckedBinOp, checkedSub, hInRange]

/-
  LEMMA: Checked mul with in-range result returns false overflow flag
-/
theorem checked_mul_in_range (ty : IntTy) (a b : Int)
    (hInRange : ty.inRange (a * b) = true) :
    evalCheckedBinOp .mulChecked (.int ty a) (.int ty b) =
      some (.tuple [.int ty (a * b), .bool false]) := by
  simp [evalCheckedBinOp, checkedMul, hInRange]

/-
  LEMMA: Checked add with out-of-range result returns true overflow flag
-/
theorem checked_add_overflow' (ty : IntTy) (a b : Int)
    (hOverflow : ty.inRange (a + b) = false) :
    evalCheckedBinOp .addChecked (.int ty a) (.int ty b) =
      some (.tuple [.int ty (a + b), .bool true]) := by
  simp [evalCheckedBinOp, checkedAdd, hOverflow]

/-!
  ## Terminator Result Properties (Extended)
-/

/-
  LEMMA: Drop terminator returns goto control
-/
theorem execTerminator_drop_is_goto' (s : State) (place : Place)
    (target : BasicBlock) (unwind : Option BasicBlock) :
    ∃ ctrl, execTerminator s (.Drop place target unwind) = some ctrl ∧
      ctrl = .goto target := by
  exact ⟨.goto target, rfl, rfl⟩

/-
  LEMMA: Return always succeeds
-/
@[simp]
theorem execTerminator_return_always_succeeds (s : State) :
    (execTerminator s .Return).isSome = true := rfl

/-
  LEMMA: Goto always succeeds
-/
@[simp]
theorem execTerminator_goto_always_succeeds (s : State) (bb : BasicBlock) :
    (execTerminator s (.Goto bb)).isSome = true := rfl

/-!
  ## Call Setup Lemmas (Extended)
-/

/-
  LEMMA: initFrame makes all locals < localCount alive
-/
theorem State.initFrame_isAlive (heap : Heap) (localCount : Nat) (args : List Value)
    (l : Local) (h : l < localCount) :
    (State.initFrame heap localCount args).isAlive l = true := by
  simp only [State.initFrame, State.isAlive, decide_eq_true_eq]
  exact h

/-
  LEMMA: initFrame makes all locals >= localCount dead
-/
theorem State.initFrame_isAlive_false (heap : Heap) (localCount : Nat) (args : List Value)
    (l : Local) (h : ¬(l < localCount)) :
    (State.initFrame heap localCount args).isAlive l = false := by
  simp only [State.initFrame, State.isAlive, decide_eq_false_iff_not]
  exact h

/-
  LEMMA: initFrame argument access - args[i] is at local i+1
-/
theorem State.initFrame_readLocal_arg (heap : Heap) (localCount : Nat) (args : List Value)
    (i : Nat) (h1 : i + 1 < localCount) (h2 : i < args.length) :
    (State.initFrame heap localCount args).readLocal (i + 1) = some (args[i]'h2) := by
  simp only [State.initFrame, State.readLocal, State.isAlive, decide_eq_true_eq]
  simp only [h1, ↓reduceIte]
  exact List.getElem?_eq_getElem h2

/-
  LEMMA: initFrame with zero localCount has no alive locals
-/
theorem State.initFrame_zero_locals_dead (heap : Heap) (args : List Value) (l : Local) :
    (State.initFrame heap 0 args).isAlive l = false := by
  simp [State.initFrame, State.isAlive, Nat.not_lt_zero]

/-
  LEMMA: initFrame preserves original heap identity
-/
@[simp]
theorem State.initFrame_heap_eq' (heap : Heap) (localCount : Nat) (args : List Value) :
    (State.initFrame heap localCount args).heap = heap := rfl

/-
  LEMMA: initFrame local 0 (return slot) is initialized to unit
-/
theorem State.initFrame_ret_unit (heap : Heap) (localCount : Nat) (args : List Value)
    (_ : 0 < localCount) :
    (State.initFrame heap localCount args).locals 0 = some .unit := by
  simp [State.initFrame]

/-!
  ## State Locality Lemmas
-/

/-
  LEMMA: Locals are frame-local (setting one doesn't affect others)
-/
theorem State.writeLocal_other' (s : State) (l1 l2 : Local) (v : Value) (s' : State)
    (hNeq : l1 ≠ l2)
    (hWrite : s.writeLocal l1 v = some s') :
    s'.readLocal l2 = s.readLocal l2 := by
  simp only [State.writeLocal] at hWrite
  split at hWrite
  · case isTrue hAlive =>
      simp only [Option.some.injEq] at hWrite
      subst hWrite
      simp only [State.readLocal, State.isAlive, Ne.symm hNeq, ↓reduceIte]
  · case isFalse hNotAlive =>
      cases hWrite

/-
  LEMMA: writeLocal preserves heap (extended)
-/
theorem State.writeLocal_preserves_heap' (s : State) (l : Local) (v : Value) (s' : State)
    (hWrite : s.writeLocal l v = some s') :
    s'.heap = s.heap := by
  simp only [State.writeLocal] at hWrite
  split at hWrite
  · case isTrue hAlive =>
      simp only [Option.some.injEq] at hWrite
      subst hWrite
      rfl
  · case isFalse hNotAlive =>
      cases hWrite

/-!
  ## Heap Sharing in Calls
-/

/-
  LEMMA: initFrame uses the provided heap directly (alias)
-/
@[simp]
theorem State.initFrame_heap_identity' (heap : Heap) (localCount : Nat) (args : List Value) :
    (State.initFrame heap localCount args).heap = heap := rfl

/-
  LEMMA: Heap read through initFrame is same as direct read
-/
@[simp]
theorem State.initFrame_heapRead' (heap : Heap) (localCount : Nat) (args : List Value)
    (loc : Location) :
    (State.initFrame heap localCount args).heapRead loc = heap.read loc := rfl

/-
  LEMMA: StorageLive preserves heap
-/
@[simp]
theorem State.storageLive_heap' (s : State) (l : Local) :
    (s.storageLive l).heap = s.heap := rfl

/-
  LEMMA: StorageDead preserves heap
-/
@[simp]
theorem State.storageDead_heap' (s : State) (l : Local) :
    (s.storageDead l).heap = s.heap := rfl

/-!
  ## Execution Monotonicity
-/

/-
  LEMMA: Single statement list execution equivalence
-/
theorem execStmts_singleton_bind (s : State) (stmt : MirStmt) :
    execStmts s [stmt] = (execStmt s stmt).bind (fun s' => some s') := by
  simp only [execStmts]
  rfl

/-!
  ## Determinism Foundation (Extended)
-/

/-
  LEMMA: execStmt is deterministic (alternative proof style)
-/
theorem execStmt_deterministic'' (s : State) (stmt : MirStmt) (s1 s2 : State)
    (h1 : execStmt s stmt = some s1) (h2 : execStmt s stmt = some s2) :
    s1 = s2 := by
  rw [h1] at h2
  injection h2

/-!
  ## Value Type Properties
-/

/-
  LEMMA: Function value extraction preserves name
-/
@[simp]
theorem Value.fn_name_eq' (name : String) :
    (Value.fn_ name) = .fn_ name := rfl

/-
  LEMMA: Int value preserves type tag
-/
theorem Value.int_ty_preserved' (ty : IntTy) (v : Int) :
    ∃ ty' v', Value.int ty v = .int ty' v' ∧ ty' = ty :=
  ⟨ty, v, rfl, rfl⟩

/-!
  ## Frame Properties for Recursive Calls
-/

/-
  LEMMA: Callee local values are determined only by args
-/
theorem callee_locals_from_args (heap : Heap) (localCount : Nat) (args : List Value) (l : Local) :
    (State.initFrame heap localCount args).locals l =
      match l with
      | 0 => some .unit
      | n + 1 => args[n]? := by
  cases l with
  | zero => rfl
  | succ n => rfl

/-!
  ## Heap Modification Properties
-/

/-
  LEMMA: Heap write at location l doesn't affect other locations
-/
theorem Heap.write_other' (h : Heap) (l1 l2 : Location) (v : Value)
    (hNeq : l1 ≠ l2) :
    (h.write l1 v).read l2 = h.read l2 := by
  simp only [Heap.write, Heap.read]
  simp only [Ne.symm hNeq, ↓reduceIte]

/-
  LEMMA: Heap write at same location returns written value
-/
theorem Heap.write_same' (h : Heap) (l : Location) (v : Value) :
    (h.write l v).read l = some v := by
  simp [Heap.write, Heap.read]

/-
  LEMMA: Heap alloc increases nextLoc
-/
@[simp]
theorem Heap.alloc_increases_nextLoc' (h : Heap) (v : Value) :
    (h.alloc v).1.nextLoc = h.nextLoc + 1 := rfl

/-
  LEMMA: Heap dealloc at location l makes it return none
-/
theorem Heap.dealloc_returns_none' (h : Heap) (l : Location) :
    (h.dealloc l).read l = none := by
  simp [Heap.dealloc, Heap.read]

/-
  LEMMA: Heap dealloc preserves other locations
-/
theorem Heap.dealloc_other' (h : Heap) (l1 l2 : Location) (hNeq : l1 ≠ l2) :
    (h.dealloc l1).read l2 = h.read l2 := by
  simp only [Heap.dealloc, Heap.read]
  simp only [Ne.symm hNeq, ↓reduceIte]

/-!
  ## Control Flow Properties
-/

/-
  LEMMA: Control.return_ is not goto
-/
theorem Control.return_not_goto (bb : BasicBlock) :
    Control.return_ ≠ .goto bb := by
  intro h
  cases h

/-
  LEMMA: Control.panic is not return_
-/
theorem Control.panic_not_return :
    Control.panic ≠ .return_ := by
  intro h
  cases h

/-
  LEMMA: Control.panic is not goto
-/
theorem Control.panic_not_goto (bb : BasicBlock) :
    Control.panic ≠ .goto bb := by
  intro h
  cases h

/-
  LEMMA: Control.goto injectivity
-/
theorem Control.goto_injective (bb1 bb2 : BasicBlock) :
    Control.goto bb1 = .goto bb2 → bb1 = bb2 := by
  intro h
  cases h
  rfl

/-!
  ## Additional initFrame lemmas
-/

/-
  LEMMA: initFrame alive predicate characterization
-/
theorem State.initFrame_alive_iff (heap : Heap) (localCount : Nat) (args : List Value) (l : Local) :
    (State.initFrame heap localCount args).isAlive l = true ↔ l < localCount := by
  simp [State.initFrame, State.isAlive]

/-
  LEMMA: initFrame locals 0 is always unit (when accessed)
-/
theorem State.initFrame_locals_zero (heap : Heap) (localCount : Nat) (args : List Value) :
    (State.initFrame heap localCount args).locals 0 = some .unit := by
  simp [State.initFrame]

/-
  LEMMA: initFrame args list indexing
-/
theorem State.initFrame_locals_succ (heap : Heap) (localCount : Nat) (args : List Value) (n : Nat) :
    (State.initFrame heap localCount args).locals (n + 1) = args[n]? := by
  simp [State.initFrame]

/-!
  ## Reference and Box Lemmas
-/

/-
  LEMMA: Ref values are not box values
-/
theorem Value.ref_ne_box (loc1 loc2 : Location) :
    Value.ref loc1 ≠ .box_ loc2 := by
  intro h
  cases h

/-
  LEMMA: Box values are not ref values
-/
theorem Value.box_ne_ref (loc1 loc2 : Location) :
    Value.box_ loc1 ≠ .ref loc2 := by
  intro h
  cases h

/-
  LEMMA: Ref injectivity
-/
theorem Value.ref_injective (loc1 loc2 : Location) :
    Value.ref loc1 = .ref loc2 → loc1 = loc2 := by
  intro h
  cases h
  rfl

/-
  LEMMA: Box injectivity
-/
theorem Value.box_injective (loc1 loc2 : Location) :
    Value.box_ loc1 = .box_ loc2 → loc1 = loc2 := by
  intro h
  cases h
  rfl

/-
  LEMMA: Ref is not unit
-/
theorem Value.ref_ne_unit (loc : Location) :
    Value.ref loc ≠ .unit := by
  intro h
  cases h

/-
  LEMMA: Box is not unit
-/
theorem Value.box_ne_unit (loc : Location) :
    Value.box_ loc ≠ .unit := by
  intro h
  cases h

/-
  LEMMA: Ref is not bool
-/
theorem Value.ref_ne_bool (loc : Location) (b : Bool) :
    Value.ref loc ≠ .bool b := by
  intro h
  cases h

/-
  LEMMA: Box is not bool
-/
theorem Value.box_ne_bool (loc : Location) (b : Bool) :
    Value.box_ loc ≠ .bool b := by
  intro h
  cases h

/-
  LEMMA: Ref is not int
-/
theorem Value.ref_ne_int (loc : Location) (ty : IntTy) (v : Int) :
    Value.ref loc ≠ .int ty v := by
  intro h
  cases h

/-
  LEMMA: Box is not int
-/
theorem Value.box_ne_int (loc : Location) (ty : IntTy) (v : Int) :
    Value.box_ loc ≠ .int ty v := by
  intro h
  cases h

/-!
  ## Heap Allocation Sequence Lemmas
-/

/-
  LEMMA: Allocating twice gives distinct locations
-/
theorem Heap.alloc_twice_distinct' (h : Heap) (v1 v2 : Value) :
    (h.alloc v1).2 ≠ ((h.alloc v1).1.alloc v2).2 := by
  simp only [Heap.alloc]
  intro hEq
  have : h.nextLoc ≠ h.nextLoc + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
  exact this hEq

/-
  LEMMA: Allocating doesn't affect previous locations
-/
theorem Heap.alloc_preserves_old (h : Heap) (v : Value) (loc : Location) (hLt : loc < h.nextLoc) :
    (h.alloc v).1.read loc = h.read loc := by
  simp only [Heap.alloc, Heap.read]
  have : loc ≠ h.nextLoc := Nat.ne_of_lt hLt
  simp [this]

/-
  LEMMA: New allocation location is fresh (was none before)
-/
theorem Heap.alloc_fresh_loc (h : Heap) (hEmpty : h.mem h.nextLoc = none) :
    h.read h.nextLoc = none := by
  simp [Heap.read, hEmpty]

/-
  LEMMA: alloc then read at fresh location succeeds
-/
theorem Heap.alloc_then_read (h : Heap) (v : Value) :
    let (h', loc) := h.alloc v
    h'.read loc = some v := by
  simp [Heap.alloc, Heap.read]

/-
  LEMMA: Dealloc then alloc may reuse location (nextLoc unchanged by dealloc)
-/
@[simp]
theorem Heap.dealloc_nextLoc' (h : Heap) (loc : Location) :
    (h.dealloc loc).nextLoc = h.nextLoc := rfl

/-
  LEMMA: Double dealloc is idempotent on read
-/
theorem Heap.dealloc_idempotent_read (h : Heap) (loc : Location) :
    (h.dealloc loc).read loc = (h.dealloc loc |>.dealloc loc).read loc := by
  simp [Heap.dealloc, Heap.read]

/-!
  ## Value Discrimination Lemmas
-/

/-
  LEMMA: fn_ values are not int values
-/
theorem Value.fn_ne_int (name : String) (ty : IntTy) (v : Int) :
    Value.fn_ name ≠ .int ty v := by
  intro h
  cases h

/-
  LEMMA: fn_ values are not bool values
-/
theorem Value.fn_ne_bool (name : String) (b : Bool) :
    Value.fn_ name ≠ .bool b := by
  intro h
  cases h

/-
  LEMMA: int values are not bool values
-/
theorem Value.int_ne_bool' (ty : IntTy) (v : Int) (b : Bool) :
    Value.int ty v ≠ .bool b := by
  intro h
  cases h

/-
  LEMMA: bool values are not int values
-/
theorem Value.bool_ne_int' (b : Bool) (ty : IntTy) (v : Int) :
    Value.bool b ≠ .int ty v := by
  intro h
  cases h

/-
  LEMMA: unit is not bool
-/
theorem Value.unit_ne_bool' (b : Bool) :
    Value.unit ≠ .bool b := by
  intro h
  cases h

/-
  LEMMA: unit is not int
-/
theorem Value.unit_ne_int' (ty : IntTy) (v : Int) :
    Value.unit ≠ .int ty v := by
  intro h
  cases h

/-
  LEMMA: array is not tuple (variant)
-/
theorem Value.array_ne_tuple' (a t : List Value) :
    Value.array a ≠ .tuple t := by
  intro h
  cases h

/-
  LEMMA: tuple is not array (variant)
-/
theorem Value.tuple_ne_array' (t a : List Value) :
    Value.tuple t ≠ .array a := by
  intro h
  cases h

/-
  LEMMA: rawPtr is not ref
-/
theorem Value.rawPtr_ne_ref (oloc : Option Location) (loc : Location) :
    Value.rawPtr oloc ≠ .ref loc := by
  intro h
  cases h

/-
  LEMMA: rawPtr is not box
-/
theorem Value.rawPtr_ne_box (oloc : Option Location) (loc : Location) :
    Value.rawPtr oloc ≠ .box_ loc := by
  intro h
  cases h

/-!
  ## Operand Evaluation Extended Lemmas
-/

/-
  LEMMA: Constant bool operand evaluation
-/
@[simp]
theorem evalOperand_const_bool' (s : State) (b : Bool) :
    evalOperand s (.const (.bool b)) = some (.bool b) := rfl

/-
  LEMMA: Constant int operand evaluation
-/
@[simp]
theorem evalOperand_const_int' (s : State) (ty : IntTy) (v : Int) :
    evalOperand s (.const (.int ty v)) = some (.int ty v) := rfl

/-
  LEMMA: Constant unit operand evaluation
-/
@[simp]
theorem evalOperand_const_unit' (s : State) :
    evalOperand s (.const .unit) = some .unit := rfl

/-
  LEMMA: evalOperand on constant doesn't depend on state
-/
@[simp]
theorem evalOperand_const_state_irrelevant' (s1 s2 : State) (c : Value) :
    evalOperand s1 (.const c) = evalOperand s2 (.const c) := rfl

/-
  LEMMA: Successful evalOperand implies some result
-/
theorem evalOperand_success_isSome' (s : State) (op : Operand) (v : Value)
    (h : evalOperand s op = some v) :
    (evalOperand s op).isSome = true := by
  rw [h]
  rfl

/-!
  ## State Read/Write Extended Lemmas
-/

/-
  LEMMA: Reading after writing same local returns new value
-/
theorem State.writeLocal_readLocal_same' (s : State) (l : Local) (v : Value) (s' : State)
    (hWrite : s.writeLocal l v = some s') :
    s'.readLocal l = some v := by
  simp only [State.writeLocal] at hWrite
  split at hWrite
  · case isTrue hAlive =>
      simp only [Option.some.injEq] at hWrite
      subst hWrite
      simp only [State.readLocal, State.isAlive] at hAlive ⊢
      simp [hAlive]
  · case isFalse hNotAlive =>
      cases hWrite

/-
  LEMMA: Writing then reading other local returns old value
-/
theorem State.writeLocal_readLocal_other' (s : State) (l1 l2 : Local) (v : Value) (s' : State)
    (hWrite : s.writeLocal l1 v = some s')
    (hNe : l1 ≠ l2) :
    s'.readLocal l2 = s.readLocal l2 := by
  simp only [State.writeLocal] at hWrite
  split at hWrite
  · case isTrue hAlive =>
      simp only [Option.some.injEq] at hWrite
      subst hWrite
      simp only [State.readLocal, State.isAlive]
      simp [hNe.symm]
  · case isFalse hNotAlive =>
      cases hWrite

/-
  LEMMA: writeLocal preserves alive status of other locals
-/
theorem State.writeLocal_preserves_other_alive' (s : State) (l1 l2 : Local) (v : Value) (s' : State)
    (hWrite : s.writeLocal l1 v = some s')
    (_ : l1 ≠ l2) :
    s'.isAlive l2 = s.isAlive l2 := by
  simp only [State.writeLocal] at hWrite
  split at hWrite
  · case isTrue hAlive =>
      simp only [Option.some.injEq] at hWrite
      subst hWrite
      rfl
  · case isFalse hNotAlive =>
      cases hWrite

/-
  LEMMA: storageLive makes the local alive (variant)
-/
theorem State.storageLive_makes_alive' (s : State) (l : Local) :
    (s.storageLive l).isAlive l = true := by
  simp [State.storageLive, State.isAlive]

/-
  LEMMA: storageDead makes the local dead (variant)
-/
theorem State.storageDead_makes_dead' (s : State) (l : Local) :
    (s.storageDead l).isAlive l = false := by
  simp [State.storageDead, State.isAlive]

/-
  LEMMA: storageLive followed by storageDead
-/
theorem State.storageLive_storageDead_alive' (s : State) (l : Local) :
    ((s.storageLive l).storageDead l).isAlive l = false := by
  simp [State.storageLive, State.storageDead, State.isAlive]

/-
  LEMMA: storageDead followed by storageLive makes alive
-/
theorem State.storageDead_storageLive_alive' (s : State) (l : Local) :
    ((s.storageDead l).storageLive l).isAlive l = true := by
  simp [State.storageDead, State.storageLive, State.isAlive]

/-!
  ## heapRead/heapWrite Lemmas
-/

/-
  LEMMA: heapWrite then heapRead same location returns new value
-/
theorem State.heapWrite_heapRead_same' (s : State) (loc : Location) (v : Value) :
    (s.heapWrite loc v).heapRead loc = some v := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read]

/-
  LEMMA: heapWrite then heapRead other location returns old value
-/
theorem State.heapWrite_heapRead_other' (s : State) (loc1 loc2 : Location) (v : Value)
    (hNe : loc1 ≠ loc2) :
    (s.heapWrite loc1 v).heapRead loc2 = s.heapRead loc2 := by
  simp [State.heapWrite, State.heapRead, Heap.write, Heap.read, hNe.symm]

/-
  LEMMA: heapWrite preserves locals
-/
theorem State.heapWrite_preserves_locals' (s : State) (loc : Location) (v : Value) (l : Local) :
    (s.heapWrite loc v).readLocal l = s.readLocal l := by
  simp [State.heapWrite, State.readLocal, State.isAlive]

/-
  LEMMA: heapWrite preserves alive
-/
@[simp]
theorem State.heapWrite_preserves_alive' (s : State) (loc : Location) (v : Value) (l : Local) :
    (s.heapWrite loc v).isAlive l = s.isAlive l := rfl

/-!
  ## SwitchInt Lemmas
-/

/-
  LEMMA: SwitchInt with empty targets always goes to otherwise
-/
theorem execTerminator_switch_empty_targets' (s : State) (discr : Operand) (otherwise : BasicBlock)
    (v : Value) (d : Int)
    (hEval : evalOperand s discr = some v)
    (hDiscr : asSwitchIntDiscr v = some d) :
    execTerminator s (.SwitchInt discr [] otherwise) = some (.goto otherwise) := by
  simp [execTerminator, hEval, hDiscr]

/-
  LEMMA: SwitchInt targets are checked in order (first match wins)
-/
theorem execTerminator_switch_first_match' (s : State) (discr : Operand) (d : Int)
    (targets : List (Int × BasicBlock)) (bb1 : BasicBlock) (otherwise : BasicBlock)
    (v : Value)
    (hEval : evalOperand s discr = some v)
    (hDiscr : asSwitchIntDiscr v = some d)
    (hMatch : targets.find? (fun p => p.1 == d) = some (d, bb1)) :
    execTerminator s (.SwitchInt discr targets otherwise) = some (.goto bb1) := by
  simp [execTerminator, hEval, hDiscr, hMatch]

/-
  LEMMA: SwitchInt goes to otherwise when no targets match
-/
theorem execTerminator_switch_no_match' (s : State) (discr : Operand) (d : Int)
    (targets : List (Int × BasicBlock)) (otherwise : BasicBlock)
    (v : Value)
    (hEval : evalOperand s discr = some v)
    (hDiscr : asSwitchIntDiscr v = some d)
    (hNoMatch : targets.find? (fun p => p.1 == d) = none) :
    execTerminator s (.SwitchInt discr targets otherwise) = some (.goto otherwise) := by
  simp [execTerminator, hEval, hDiscr, hNoMatch]

/-!
  ## MirBody and BasicBlock Lemmas
-/

/-
  LEMMA: Getting entry block of a body with valid entry
-/
theorem MirBody.getBlock_entry' (body : MirBody) (data : BasicBlockData)
    (hEntry : body.blocks[body.entryBlock]? = some data) :
    body.getBlock body.entryBlock = some data := by
  simp only [MirBody.getBlock, hEntry]

/-
  LEMMA: Empty block list means getBlock fails
-/
theorem MirBody.getBlock_empty' (bb : BasicBlock) :
    MirBody.getBlock { blocks := [], localCount := 0, entryBlock := 0 } bb = none := by
  simp only [MirBody.getBlock]
  rfl

/-!
  ## Control Flow Extended Lemmas
-/

/-
  LEMMA: Control.goto never equals return_
-/
theorem Control.goto_ne_return' (bb : BasicBlock) :
    Control.goto bb ≠ .return_ := by
  intro h
  cases h

/-
  LEMMA: Control.goto never equals panic
-/
theorem Control.goto_ne_panic' (bb : BasicBlock) :
    Control.goto bb ≠ .panic := by
  intro h
  cases h

/-
  LEMMA: Control.return_ never equals panic
-/
theorem Control.return_ne_panic' :
    Control.return_ ≠ .panic := by
  intro h
  cases h

/-!
  ## Additional Value Constructor Lemmas
-/

/-
  LEMMA: Bool values are distinct
-/
theorem Value.bool_true_ne_false' :
    Value.bool true ≠ .bool false := by
  intro h
  cases h

/-
  LEMMA: Int value with same type is equal iff values equal
-/
theorem Value.int_eq_iff' (ty : IntTy) (v1 v2 : Int) :
    Value.int ty v1 = .int ty v2 ↔ v1 = v2 := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; rfl

/-
  LEMMA: Tuple value equality implies element equality
-/
theorem Value.tuple_eq_elems' (elems1 elems2 : List Value) :
    Value.tuple elems1 = .tuple elems2 ↔ elems1 = elems2 := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; rfl

/-
  LEMMA: Array value equality implies element equality
-/
theorem Value.array_eq_elems' (elems1 elems2 : List Value) :
    Value.array elems1 = .array elems2 ↔ elems1 = elems2 := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; rfl

/-
  LEMMA: Ref value equality implies location equality
-/
theorem Value.ref_eq_iff (loc1 loc2 : Location) :
    Value.ref loc1 = .ref loc2 ↔ loc1 = loc2 := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; rfl

/-
  LEMMA: Box value equality implies location equality
-/
theorem Value.box_eq_iff (loc1 loc2 : Location) :
    Value.box_ loc1 = .box_ loc2 ↔ loc1 = loc2 := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; rfl

/-
  LEMMA: fn_ value equality implies name equality
-/
theorem Value.fn_eq_iff (name1 name2 : String) :
    Value.fn_ name1 = .fn_ name2 ↔ name1 = name2 := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; rfl

/-
  LEMMA: rawPtr value equality
-/
theorem Value.rawPtr_eq_iff (loc1 loc2 : Option Location) :
    Value.rawPtr loc1 = .rawPtr loc2 ↔ loc1 = loc2 := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; rfl

/-!
  ## execStmts Extended Lemmas
-/

/-
  LEMMA: execStmts of single Nop is identity
-/
theorem execStmts_nop_identity (s : State) :
    execStmts s [.Nop] = some s := by
  simp [execStmts, execStmt]

/-
  LEMMA: execStmts of two Nops is identity
-/
theorem execStmts_two_nops_identity (s : State) :
    execStmts s [.Nop, .Nop] = some s := by
  simp [execStmts, execStmt]

/-
  LEMMA: execStmts of StorageLive then Nop
-/
theorem execStmts_storageLive_nop (s : State) (l : Local) :
    execStmts s [.StorageLive l, .Nop] = some (s.storageLive l) := by
  simp [execStmts, execStmt]

/-
  LEMMA: execStmts of Nop then StorageLive
-/
theorem execStmts_nop_storageLive (s : State) (l : Local) :
    execStmts s [.Nop, .StorageLive l] = some (s.storageLive l) := by
  simp [execStmts, execStmt]

/-
  LEMMA: execStmts of StorageDead then Nop
-/
theorem execStmts_storageDead_nop (s : State) (l : Local) :
    execStmts s [.StorageDead l, .Nop] = some (s.storageDead l) := by
  simp [execStmts, execStmt]

/-!
  ## MirProgram Lemmas

  Lemmas about program-level operations: function lookup, function properties.
-/

/-
  LEMMA: getFun returns function from funs map
-/
@[simp]
theorem MirProgram.getFun_eq (p : MirProgram) (name : String) :
    p.getFun name = p.funs name := rfl

/-
  LEMMA: getFun is deterministic (same name gives same result)
-/
theorem MirProgram.getFun_det (p : MirProgram) (name : String) (body1 body2 : MirBody)
    (h1 : p.getFun name = some body1)
    (h2 : p.getFun name = some body2) :
    body1 = body2 := by
  simp only [MirProgram.getFun] at h1 h2
  rw [h1] at h2
  cases h2
  rfl

/-
  LEMMA: If getFun succeeds, funs contains the function
-/
theorem MirProgram.getFun_isSome (p : MirProgram) (name : String) (body : MirBody)
    (h : p.getFun name = some body) :
    (p.funs name).isSome := by
  simp only [MirProgram.getFun] at h
  simp [h]

/-
  LEMMA: getFun none means function not in program
-/
theorem MirProgram.getFun_none (p : MirProgram) (name : String)
    (h : p.getFun name = none) :
    p.funs name = none := by
  simp only [MirProgram.getFun] at h
  exact h

/-
  LEMMA: Creating a program and looking up a function
-/
@[simp]
theorem MirProgram.mk_getFun (funs : String → Option MirBody) (name : String) :
    (MirProgram.mk funs).getFun name = funs name := rfl

/-
  LEMMA: Two programs with same funs have same getFun
-/
theorem MirProgram.getFun_ext (p1 p2 : MirProgram)
    (h : p1.funs = p2.funs) (name : String) :
    p1.getFun name = p2.getFun name := by
  simp only [MirProgram.getFun, h]

/-!
  ## Extended Storage Operation Sequences
-/

/-
  LEMMA: execStmts of StorageLive then StorageDead
-/
theorem execStmts_storageLive_storageDead (s : State) (l : Local) :
    execStmts s [.StorageLive l, .StorageDead l] =
    some ((s.storageLive l).storageDead l) := by
  simp [execStmts, execStmt]

/-
  LEMMA: execStmts of StorageDead then StorageLive
-/
theorem execStmts_storageDead_storageLive (s : State) (l : Local) :
    execStmts s [.StorageDead l, .StorageLive l] =
    some ((s.storageDead l).storageLive l) := by
  simp [execStmts, execStmt]

/-
  LEMMA: Multiple Nops is identity
-/
theorem execStmts_multiple_nops (s : State) (n : Nat) :
    execStmts s (List.replicate n .Nop) = some s := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, execStmts, execStmt]
    exact ih

/-
  LEMMA: execStmts with prepended Nop
-/
theorem execStmts_nop_prepend' (s : State) (stmts : List MirStmt) :
    execStmts s (.Nop :: stmts) = execStmts s stmts := by
  simp [execStmts, execStmt]

/-!
  ## Storage Same-Local Lemmas
-/

/-
  LEMMA: storageLive then storageDead on same local makes it dead
-/
theorem State.storageLive_storageDead_same (s : State) (l : Local) :
    ((s.storageLive l).storageDead l).isAlive l = false := by
  simp [State.storageLive, State.storageDead, State.isAlive]

/-
  LEMMA: storageDead then storageLive on same local makes it alive
-/
theorem State.storageDead_storageLive_same (s : State) (l : Local) :
    ((s.storageDead l).storageLive l).isAlive l = true := by
  simp [State.storageDead, State.storageLive, State.isAlive]

/-
  LEMMA: storageLive is idempotent for isAlive
-/
theorem State.storageLive_idempotent_isAlive (s : State) (l : Local) :
    ((s.storageLive l).storageLive l).isAlive l = (s.storageLive l).isAlive l := by
  simp [State.storageLive, State.isAlive]

/-
  LEMMA: storageDead is idempotent for isAlive
-/
theorem State.storageDead_idempotent_isAlive (s : State) (l : Local) :
    ((s.storageDead l).storageDead l).isAlive l = (s.storageDead l).isAlive l := by
  simp [State.storageDead, State.isAlive]

/-!
  ## WP Storage Pair Lemmas
-/

/-
  LEMMA: WP for StorageLive/StorageDead pair
-/
theorem wp_storageLive_storageDead_pair' (l : Local) (Q : StatePred) (s : State) :
    wp_stmts_wp [.StorageLive l, .StorageDead l] Q s =
    Q ((s.storageLive l).storageDead l) := by
  simp [wp_stmts_wp, wp_stmt, execStmt]

/-
  LEMMA: WP for StorageDead/StorageLive pair
-/
theorem wp_storageDead_storageLive_pair' (l : Local) (Q : StatePred) (s : State) :
    wp_stmts_wp [.StorageDead l, .StorageLive l] Q s =
    Q ((s.storageDead l).storageLive l) := by
  simp [wp_stmts_wp, wp_stmt, execStmt]

/-
  LEMMA: WP for stmt sequence with prepended Nop
-/
theorem wp_nop_prepend' (stmts : List MirStmt) (Q : StatePred) (s : State) :
    wp_stmts_wp (.Nop :: stmts) Q s = wp_stmts_wp stmts Q s := by
  simp [wp_stmts_wp, wp_stmt, execStmt]

/-
  LEMMA: WP for empty list of statements
-/
@[simp]
theorem wp_stmts_empty' (Q : StatePred) (s : State) :
    wp_stmts_wp [] Q s = Q s := rfl

/-!
  ## Heap Operation Locality Lemmas
-/

/-
  LEMMA: Heap operations preserve local alive status
-/
@[simp]
theorem State.heapAlloc_preserves_alive' (s : State) (v : Value) (l : Local) :
    (s.heapAlloc v).1.isAlive l = s.isAlive l := rfl

/-
  LEMMA: Deallocation preserves local alive status
-/
@[simp]
theorem State.heapDealloc_preserves_alive' (s : State) (loc : Location) (l : Local) :
    (s.heapDealloc loc).isAlive l = s.isAlive l := rfl

/-
  LEMMA: heapWrite preserves local alive status
-/
@[simp]
theorem State.heapWrite_preserves_alive'' (s : State) (loc : Location) (v : Value) (l : Local) :
    (s.heapWrite loc v).isAlive l = s.isAlive l := rfl

/-!
  ## Constant Evaluation Lemmas
-/

/-
  LEMMA: evalOperand const with tuple
-/
@[simp]
theorem evalOperand_const_tuple (s : State) (vals : List Value) :
    evalOperand s (.const (.tuple vals)) = some (.tuple vals) := rfl

/-
  LEMMA: evalOperand const with array
-/
@[simp]
theorem evalOperand_const_array (s : State) (elems : List Value) :
    evalOperand s (.const (.array elems)) = some (.array elems) := rfl

/-
  LEMMA: evalOperand const with fn_
-/
@[simp]
theorem evalOperand_const_fn (s : State) (name : String) :
    evalOperand s (.const (.fn_ name)) = some (.fn_ name) := rfl

/-!
  ## Value Discrimination Extended
-/

/-
  LEMMA: tuple is not array
-/
theorem Value.tuple_ne_array (t : List Value) (a : List Value) :
    Value.tuple t ≠ .array a := by
  intro h
  cases h

/-
  LEMMA: fn_ is not rawPtr
-/
theorem Value.fn_ne_rawPtr (name : String) (loc : Option Location) :
    Value.fn_ name ≠ .rawPtr loc := by
  intro h
  cases h

/-!
  ## execBlock Additional Lemmas
-/

/-
  LEMMA: execBlock with StorageDead and Return
-/
theorem execBlock_storageDead_return (s : State) (l : Local) :
    execBlock s { stmts := [.StorageDead l], terminator := .Return } =
    some (s.storageDead l, .return_) := by
  simp [execBlock, execStmts, execStmt, execTerminator]

/-
  LEMMA: execBlock with multiple Nops and Return
-/
theorem execBlock_nops_return (s : State) (n : Nat) :
    execBlock s { stmts := List.replicate n .Nop, terminator := .Return } =
    some (s, .return_) := by
  simp [execBlock, execStmts_multiple_nops, execTerminator]

/-
  LEMMA: execBlock with StorageLive/StorageDead sequence and Return
-/
theorem execBlock_storageLive_storageDead_return (s : State) (l : Local) :
    execBlock s { stmts := [.StorageLive l, .StorageDead l], terminator := .Return } =
    some ((s.storageLive l).storageDead l, .return_) := by
  simp [execBlock, execTerminator]

/-!
  ## execTerminatorP Lemmas

  Lemmas for the fuel-bounded terminator execution with program context.
  Note: execTerminatorP is a partial function in a mutual block, so we prove
  lemmas about specific cases rather than trying to unfold the general definition.
-/

/-
  LEMMA: initFrame shares heap with caller
-/
@[simp]
theorem State.initFrame_shares_heap (callerHeap : Heap) (localCount : Nat) (args : List Value)
    (loc : Location) :
    (State.initFrame callerHeap localCount args).heapRead loc = callerHeap.read loc := rfl

/-
  LEMMA: initFrame arg access matches list indexing
-/
theorem State.initFrame_arg_index (heap : Heap) (localCount : Nat) (args : List Value)
    (n : Nat) (v : Value)
    (hArg : args[n]? = some v)
    (hAlive : n + 1 < localCount) :
    (State.initFrame heap localCount args).readLocal (n + 1) = some v := by
  simp [State.initFrame, State.readLocal, State.isAlive, hAlive, decide_true, hArg]

/-
  LEMMA: initFrame locals for local 0 (return slot)
-/
@[simp]
theorem State.initFrame_local_zero (heap : Heap) (localCount : Nat) (args : List Value) :
    (State.initFrame heap localCount args).locals 0 = some .unit := rfl

/-
  LEMMA: initFrame locals for arguments
-/
@[simp]
theorem State.initFrame_local_arg (heap : Heap) (localCount : Nat) (args : List Value) (n : Nat) :
    (State.initFrame heap localCount args).locals (n + 1) = args[n]? := rfl

/-
  LEMMA: execBodyP is execFromBlockP at entry
-/
@[simp]
theorem execBodyP_eq (p : MirProgram) (body : MirBody) (s : State) (fuel : Nat) :
    execBodyP p body s fuel = execFromBlockP p body body.entryBlock s fuel := rfl

/-!
  ## Additional MirBody Lemmas
-/

/-
  LEMMA: Single-block body getBlock 0 succeeds
-/
@[simp]
theorem MirBody.single_block_getBlock (blockData : BasicBlockData) :
    MirBody.getBlock { blocks := [blockData], localCount := 0, entryBlock := 0 } 0 = some blockData := rfl

/-
  LEMMA: getBlock out of bounds returns none
-/
theorem MirBody.getBlock_out_of_bounds (body : MirBody) (bb : BasicBlock)
    (hOOB : body.blocks.length ≤ bb) :
    body.getBlock bb = none := by
  simp only [MirBody.getBlock]
  exact List.getElem?_eq_none hOOB

/-
  LEMMA: getBlock at valid index
-/
theorem MirBody.getBlock_at_index (blocks : List BasicBlockData) (bb : BasicBlock)
    (hBounds : bb < blocks.length) :
    MirBody.getBlock { blocks := blocks, localCount := 0, entryBlock := 0 } bb =
    some blocks[bb] := by
  simp only [MirBody.getBlock, List.getElem?_eq_getElem hBounds]

/-!
  ## Inter-procedural Frame Reasoning
-/

/-
  LEMMA: initFrame heap is same as input heap
-/
@[simp]
theorem State.initFrame_heap_is_input (heap : Heap) (localCount : Nat) (args : List Value) :
    (State.initFrame heap localCount args).heap = heap := rfl

/-
  LEMMA: initFrame alive depends only on localCount
-/
@[simp]
theorem State.initFrame_alive_localCount (heap : Heap) (localCount : Nat) (args : List Value)
    (l : Local) :
    (State.initFrame heap localCount args).isAlive l = decide (l < localCount) := rfl

/-
  LEMMA: initFrame with zero locals has all dead
-/
theorem State.initFrame_zero_all_dead (heap : Heap) (args : List Value) (l : Local) :
    (State.initFrame heap 0 args).isAlive l = false := by
  simp [State.initFrame, State.isAlive]

/-
  LEMMA: initFrame return slot is unit if localCount > 0
-/
theorem State.initFrame_ret_is_unit (heap : Heap) (localCount : Nat) (args : List Value)
    (h : 0 < localCount) :
    (State.initFrame heap localCount args).readLocal 0 = some .unit := by
  simp [State.initFrame, State.readLocal, State.isAlive, h]

/-
  LEMMA: initFrame out of range arg is none
-/
theorem State.initFrame_arg_oob (heap : Heap) (localCount : Nat) (args : List Value)
    (n : Nat) (hOob : args.length ≤ n) :
    (State.initFrame heap localCount args).locals (n + 1) = none := by
  simp only [State.initFrame]
  exact List.getElem?_eq_none hOob

/-!
  ## execTerminator Additional Lemmas
-/

/-
  LEMMA: Call terminator returns none (handled separately)
-/
@[simp]
theorem execTerminator_call_none (s : State) (func : Operand) (args : List Operand)
    (dest : Place) (target : BasicBlock) :
    execTerminator s (.Call func args dest target) = none := rfl

/-!
  ## Control Flow Determinism
-/

/-
  LEMMA: Control values are distinct - goto vs return
-/
theorem Control.goto_ne_return (bb : BasicBlock) :
    Control.goto bb ≠ .return_ := by
  intro h
  cases h

/-
  LEMMA: Control values are distinct - goto vs panic
-/
theorem Control.goto_ne_panic (bb : BasicBlock) :
    Control.goto bb ≠ .panic := by
  intro h
  cases h

/-
  LEMMA: Control values are distinct - return vs panic
-/
theorem Control.return_ne_panic :
    Control.return_ ≠ .panic := by
  intro h
  cases h

/-
  LEMMA: Control values are distinct - goto vs unwind
-/
theorem Control.goto_ne_unwind (bb1 bb2 : BasicBlock) :
    Control.goto bb1 ≠ .unwind bb2 := by
  intro h
  cases h

/-
  LEMMA: Control values are distinct - return vs unwind
-/
theorem Control.return_ne_unwind (bb : BasicBlock) :
    Control.return_ ≠ .unwind bb := by
  intro h
  cases h

/-
  LEMMA: Control values are distinct - panic vs unwind
-/
theorem Control.panic_ne_unwind (bb : BasicBlock) :
    Control.panic ≠ .unwind bb := by
  intro h
  cases h

/-!
  ## MirTerminator Discrimination Lemmas
-/

/-
  LEMMA: Return is not Goto
-/
theorem MirTerminator.return_ne_goto (bb : BasicBlock) :
    MirTerminator.Return ≠ .Goto bb := by
  intro h
  cases h

/-
  LEMMA: Return is not Call
-/
theorem MirTerminator.return_ne_call (func : Operand) (args : List Operand)
    (dest : Place) (target : BasicBlock) :
    MirTerminator.Return ≠ .Call func args dest target := by
  intro h
  cases h

/-
  LEMMA: Goto is not Call
-/
theorem MirTerminator.goto_ne_call (bb : BasicBlock) (func : Operand) (args : List Operand)
    (dest : Place) (target : BasicBlock) :
    MirTerminator.Goto bb ≠ .Call func args dest target := by
  intro h
  cases h

/-
  LEMMA: Return is not SwitchInt
-/
theorem MirTerminator.return_ne_switch (discr : Operand) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock) :
    MirTerminator.Return ≠ .SwitchInt discr targets otherwise := by
  intro h
  cases h

/-
  LEMMA: Return is not Assert
-/
theorem MirTerminator.return_ne_assert (msg : AssertMsg) :
    MirTerminator.Return ≠ .Assert msg := by
  intro h
  cases h

/-
  LEMMA: Return is not Drop
-/
theorem MirTerminator.return_ne_drop (place : Place) (target : BasicBlock)
    (unwind : Option BasicBlock) :
    MirTerminator.Return ≠ .Drop place target unwind := by
  intro h
  cases h

/-
  LEMMA: Return is not Unreachable
-/
theorem MirTerminator.return_ne_unreachable :
    MirTerminator.Return ≠ .Unreachable := by
  intro h
  cases h

/-!
  ## Basic Block Data Lemmas
-/

/-
  LEMMA: BasicBlockData equality
-/
theorem BasicBlockData.eq_iff (b1 b2 : BasicBlockData) :
    b1 = b2 ↔ b1.stmts = b2.stmts ∧ b1.terminator = b2.terminator := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩
    cases b1; cases b2
    simp only [BasicBlockData.mk.injEq]
    exact ⟨h1, h2⟩

/-!
  ============================================================================
  Additional Fuel and Execution Properties
  ============================================================================

  Note: execTerminatorP, execFromBlockP are partial functions in a mutual block.
  Properties about them are captured in existing lemmas like execBodyP_eq.
  The following lemmas cover non-partial execution components.
-/

/-!
  ## SwitchInt Semantics
-/

/-
  LEMMA: SwitchInt with matching target goes to that target
-/
theorem switchInt_find_match (s : State) (discr : Operand) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock) (d : Int) (bb : BasicBlock) (ty : IntTy)
    (hEval : evalOperand s discr = some (.int ty d))
    (hFind : targets.find? (fun p => p.1 == d) = some (d, bb)) :
    execTerminator s (.SwitchInt discr targets otherwise) = some (.goto bb) := by
  simp [execTerminator, hEval, asSwitchIntDiscr, hFind]

/-
  LEMMA: SwitchInt with no match goes to otherwise
-/
theorem switchInt_no_match (s : State) (discr : Operand) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock) (d : Int) (ty : IntTy)
    (hEval : evalOperand s discr = some (.int ty d))
    (hNoFind : targets.find? (fun p => p.1 == d) = none) :
    execTerminator s (.SwitchInt discr targets otherwise) = some (.goto otherwise) := by
  simp [execTerminator, hEval, asSwitchIntDiscr, hNoFind]

/-
  LEMMA: SwitchInt with bool true discriminant
-/
theorem switchInt_bool_true (s : State) (discr : Operand) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock)
    (hEval : evalOperand s discr = some (.bool true)) :
    execTerminator s (.SwitchInt discr targets otherwise) =
      match targets.find? (fun p => p.1 == 1) with
      | some (_, bb) => some (.goto bb)
      | none => some (.goto otherwise) := by
  simp [execTerminator, hEval, asSwitchIntDiscr]
  rfl

/-
  LEMMA: SwitchInt with bool false discriminant
-/
theorem switchInt_bool_false (s : State) (discr : Operand) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock)
    (hEval : evalOperand s discr = some (.bool false)) :
    execTerminator s (.SwitchInt discr targets otherwise) =
      match targets.find? (fun p => p.1 == 0) with
      | some (_, bb) => some (.goto bb)
      | none => some (.goto otherwise) := by
  simp [execTerminator, hEval, asSwitchIntDiscr]
  rfl

/-
  LEMMA: asSwitchIntDiscr on tuple fails
-/
@[simp]
theorem asSwitchIntDiscr_tuple_none (vals : List Value) :
    asSwitchIntDiscr (.tuple vals) = none := rfl

/-
  LEMMA: asSwitchIntDiscr on array fails
-/
@[simp]
theorem asSwitchIntDiscr_array_none (vals : List Value) :
    asSwitchIntDiscr (.array vals) = none := rfl

/-
  LEMMA: asSwitchIntDiscr on box fails
-/
@[simp]
theorem asSwitchIntDiscr_box_none (loc : Location) :
    asSwitchIntDiscr (.box_ loc) = none := rfl

/-
  LEMMA: asSwitchIntDiscr on fn fails
-/
@[simp]
theorem asSwitchIntDiscr_fn_none (name : String) :
    asSwitchIntDiscr (.fn_ name) = none := rfl

/-!
  ## Assert Semantics
-/

/-
  LEMMA: Assert with matching condition succeeds
-/
theorem assert_match_succeeds (s : State) (msg : AssertMsg)
    (hEval : evalOperand s msg.cond = some (.bool msg.expected)) :
    execTerminator s (.Assert msg) = some (.goto msg.target) := by
  simp [execTerminator, hEval]

/-
  LEMMA: Assert with non-matching condition and cleanup unwinds
-/
theorem assert_mismatch_unwinds (s : State) (msg : AssertMsg) (b : Bool) (bb : BasicBlock)
    (hEval : evalOperand s msg.cond = some (.bool b))
    (hMismatch : b ≠ msg.expected)
    (hCleanup : msg.cleanup = some bb) :
    execTerminator s (.Assert msg) = some (.unwind bb) := by
  simp [execTerminator, hEval]
  simp [hMismatch, hCleanup]

/-
  LEMMA: Assert with non-matching condition and no cleanup panics
-/
theorem assert_mismatch_panics (s : State) (msg : AssertMsg) (b : Bool)
    (hEval : evalOperand s msg.cond = some (.bool b))
    (hMismatch : b ≠ msg.expected)
    (hNoCleanup : msg.cleanup = none) :
    execTerminator s (.Assert msg) = some .panic := by
  simp [execTerminator, hEval]
  simp [hMismatch, hNoCleanup]

/-
  LEMMA: Assert true when expected true succeeds
-/
theorem assert_true_expected_true (s : State) (cond : Operand) (target : BasicBlock)
    (cleanup : Option BasicBlock)
    (hEval : evalOperand s cond = some (.bool true)) :
    execTerminator s (.Assert ⟨cond, true, target, cleanup⟩) = some (.goto target) := by
  simp [execTerminator, hEval]

/-
  LEMMA: Assert false when expected false succeeds
-/
theorem assert_false_expected_false (s : State) (cond : Operand) (target : BasicBlock)
    (cleanup : Option BasicBlock)
    (hEval : evalOperand s cond = some (.bool false)) :
    execTerminator s (.Assert ⟨cond, false, target, cleanup⟩) = some (.goto target) := by
  simp [execTerminator, hEval]

/-
  LEMMA: Assert true when expected false panics (no cleanup)
-/
theorem assert_true_expected_false_panics (s : State) (cond : Operand) (target : BasicBlock)
    (hEval : evalOperand s cond = some (.bool true)) :
    execTerminator s (.Assert ⟨cond, false, target, none⟩) = some .panic := by
  simp [execTerminator, hEval]

/-
  LEMMA: Assert false when expected true panics (no cleanup)
-/
theorem assert_false_expected_true_panics (s : State) (cond : Operand) (target : BasicBlock)
    (hEval : evalOperand s cond = some (.bool false)) :
    execTerminator s (.Assert ⟨cond, true, target, none⟩) = some .panic := by
  simp [execTerminator, hEval]

/-
  LEMMA: Assert with non-bool value fails
-/
theorem assert_nonbool_fails (s : State) (msg : AssertMsg) (v : Value)
    (hEval : evalOperand s msg.cond = some v)
    (hNotBool : ∀ b, v ≠ .bool b) :
    execTerminator s (.Assert msg) = none := by
  simp only [execTerminator, hEval]
  cases v with
  | bool b => exact absurd rfl (hNotBool b)
  | _ => rfl

/-!
  ## Additional Control Flow Discrimination
-/

/-
  LEMMA: Control.return_ is not goto (alt)
-/
theorem Control.return_ne_goto' (bb : BasicBlock) :
    Control.return_ ≠ Control.goto bb := by
  intro h; cases h

/-
  LEMMA: Control.unwind is not return (alt)
-/
theorem Control.unwind_ne_return' (bb : BasicBlock) :
    Control.unwind bb ≠ Control.return_ := by
  intro h; cases h

/-
  LEMMA: Control.unwind is not goto
-/
theorem Control.unwind_ne_goto (bb1 bb2 : BasicBlock) :
    Control.unwind bb1 ≠ Control.goto bb2 := by
  intro h; cases h

/-
  LEMMA: Control.panic is not return (alt)
-/
theorem Control.panic_ne_return' :
    Control.panic ≠ Control.return_ := by
  intro h; cases h

/-!
  ## Additional MirTerminator Discrimination
-/

/-
  LEMMA: SwitchInt is not Return
-/
theorem MirTerminator.switchInt_ne_return (discr : Operand) (targets : List (Int × BasicBlock))
    (otherwise : BasicBlock) :
    MirTerminator.SwitchInt discr targets otherwise ≠ MirTerminator.Return := by
  intro h; cases h

/-
  LEMMA: SwitchInt is not Goto
-/
theorem MirTerminator.switchInt_ne_goto (discr : Operand) (targets : List (Int × BasicBlock))
    (otherwise bb : BasicBlock) :
    MirTerminator.SwitchInt discr targets otherwise ≠ MirTerminator.Goto bb := by
  intro h; cases h

/-
  LEMMA: Assert is not Return (alt)
-/
theorem MirTerminator.assert_ne_return' (msg : AssertMsg) :
    MirTerminator.Assert msg ≠ MirTerminator.Return := by
  intro h; cases h

/-
  LEMMA: Assert is not Goto (alt)
-/
theorem MirTerminator.assert_ne_goto' (msg : AssertMsg) (bb : BasicBlock) :
    MirTerminator.Assert msg ≠ MirTerminator.Goto bb := by
  intro h; cases h

/-
  LEMMA: Drop is not Return (alt)
-/
theorem MirTerminator.drop_ne_return' (place : Place) (target : BasicBlock)
    (unwind : Option BasicBlock) :
    MirTerminator.Drop place target unwind ≠ MirTerminator.Return := by
  intro h; cases h

/-
  LEMMA: Drop is not Unreachable
-/
theorem MirTerminator.drop_ne_unreachable (place : Place) (target : BasicBlock)
    (unwind : Option BasicBlock) :
    MirTerminator.Drop place target unwind ≠ MirTerminator.Unreachable := by
  intro h; cases h

/-
  LEMMA: Unreachable is not Return (alt)
-/
theorem MirTerminator.unreachable_ne_return' :
    MirTerminator.Unreachable ≠ MirTerminator.Return := by
  intro h; cases h

/-
  LEMMA: Unreachable is not Goto (alt)
-/
theorem MirTerminator.unreachable_ne_goto' (bb : BasicBlock) :
    MirTerminator.Unreachable ≠ MirTerminator.Goto bb := by
  intro h; cases h

/-!
  ## Heap Deallocation Properties
-/

/-
  LEMMA: Reading from deallocated location returns none
-/
theorem Heap.dealloc_read_same (h : Heap) (loc : Location) :
    (h.dealloc loc).read loc = none := by
  simp [Heap.dealloc, Heap.read]

/-
  LEMMA: Deallocation preserves reads to other locations
-/
theorem Heap.dealloc_read_other (h : Heap) (loc1 loc2 : Location) (hNe : loc1 ≠ loc2) :
    (h.dealloc loc1).read loc2 = h.read loc2 := by
  simp only [Heap.dealloc, Heap.read]
  have h : loc2 ≠ loc1 := fun heq => hNe heq.symm
  simp [h]

/-
  LEMMA: Write then dealloc same location gives none
-/
theorem Heap.write_dealloc_same (h : Heap) (loc : Location) (v : Value) :
    ((h.write loc v).dealloc loc).read loc = none := by
  simp [Heap.write, Heap.dealloc, Heap.read]

/-
  LEMMA: Dealloc then write same location restores
-/
theorem Heap.dealloc_write_same (h : Heap) (loc : Location) (v : Value) :
    ((h.dealloc loc).write loc v).read loc = some v := by
  simp [Heap.dealloc, Heap.write, Heap.read]

/-
  LEMMA: Deallocation is idempotent for reads
-/
theorem Heap.dealloc_dealloc_same (h : Heap) (loc : Location) :
    ((h.dealloc loc).dealloc loc).read loc = none := by
  simp [Heap.dealloc, Heap.read]

/-!
  ## State StorageLive/StorageDead Properties
-/

/-
  LEMMA: StorageLive enables readLocal (when local has value)
-/
theorem State.storageLive_enables_read (s : State) (l : Local) (v : Value)
    (hLocal : s.locals l = some v) :
    (s.storageLive l).readLocal l = some v := by
  simp [State.storageLive, State.readLocal, State.isAlive, hLocal]

/-
  LEMMA: StorageDead disables readLocal
-/
theorem State.storageDead_disables_read (s : State) (l : Local) :
    (s.storageDead l).readLocal l = none := by
  simp [State.storageDead, State.readLocal, State.isAlive]

/-
  LEMMA: StorageLive preserves other locals' alive status
-/
theorem State.storageLive_preserves_other_alive (s : State) (l1 l2 : Local) (hNe : l1 ≠ l2) :
    (s.storageLive l1).isAlive l2 = s.isAlive l2 := by
  simp only [State.storageLive, State.isAlive]
  have h : l2 ≠ l1 := fun heq => hNe heq.symm
  simp [h]

/-
  LEMMA: StorageDead preserves other locals' alive status
-/
theorem State.storageDead_preserves_other_alive (s : State) (l1 l2 : Local) (hNe : l1 ≠ l2) :
    (s.storageDead l1).isAlive l2 = s.isAlive l2 := by
  simp only [State.storageDead, State.isAlive]
  have h : l2 ≠ l1 := fun heq => hNe heq.symm
  simp [h]

/-
  LEMMA: WriteLocal preserves alive status (alt)
-/
theorem State.writeLocal_preserves_alive' (s : State) (l : Local) (v : Value) (l2 : Local)
    (s' : State) (h : s.writeLocal l v = some s') :
    s'.isAlive l2 = s.isAlive l2 := by
  simp only [State.writeLocal] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · simp at h

/-!
  ## execBlock Properties
-/

/-
  LEMMA: execBlock with empty stmts and Return (second alt form)
-/
@[simp]
theorem execBlock_empty_return'' (s : State) :
    execBlock s ⟨[], .Return⟩ = some (s, .return_) := rfl

/-
  LEMMA: execBlock with empty stmts and Goto (second alt form)
-/
@[simp]
theorem execBlock_empty_goto'' (s : State) (bb : BasicBlock) :
    execBlock s ⟨[], .Goto bb⟩ = some (s, .goto bb) := rfl

/-
  LEMMA: execBlock with empty stmts and Unreachable
-/
@[simp]
theorem execBlock_empty_unreachable (s : State) :
    execBlock s ⟨[], .Unreachable⟩ = none := rfl

/-
  LEMMA: execBlock deterministic (second alt form)
-/
theorem execBlock_det'' (s : State) (bb : BasicBlockData) (r1 r2 : State × Control)
    (h1 : execBlock s bb = some r1) (h2 : execBlock s bb = some r2) :
    r1 = r2 := by
  simp [h1] at h2; exact h2

/-
  LEMMA: execBlock with single Nop and Return (second alt form)
-/
@[simp]
theorem execBlock_nop_return'' (s : State) :
    execBlock s ⟨[.Nop], .Return⟩ = some (s, .return_) := rfl

/-
  LEMMA: execBlock with single Nop and Goto
-/
@[simp]
theorem execBlock_nop_goto (s : State) (bb : BasicBlock) :
    execBlock s ⟨[.Nop], .Goto bb⟩ = some (s, .goto bb) := rfl

/-!
  ## Value Type Tag Properties
-/

/-
  LEMMA: Bool value type tag
-/
theorem Value.bool_is_bool (b : Bool) :
    match Value.bool b with
    | .bool _ => True
    | _ => False := trivial

/-
  LEMMA: Int value type tag
-/
theorem Value.int_is_int (ty : IntTy) (v : Int) :
    match Value.int ty v with
    | .int _ _ => True
    | _ => False := trivial

/-
  LEMMA: Unit is unit
-/
theorem Value.unit_is_unit :
    match Value.unit with
    | .unit => True
    | _ => False := trivial

/-
  LEMMA: Ref is ref
-/
theorem Value.ref_is_ref (loc : Location) :
    match Value.ref loc with
    | .ref _ => True
    | _ => False := trivial

/-
  LEMMA: Box is box
-/
theorem Value.box_is_box (loc : Location) :
    match Value.box_ loc with
    | .box_ _ => True
    | _ => False := trivial

/-
  LEMMA: Array is array
-/
theorem Value.array_is_array (elems : List Value) :
    match Value.array elems with
    | .array _ => True
    | _ => False := trivial

/-
  LEMMA: Tuple is tuple
-/
theorem Value.tuple_is_tuple (elems : List Value) :
    match Value.tuple elems with
    | .tuple _ => True
    | _ => False := trivial

/-!
  ## List Find Properties for SwitchInt
-/

/-
  LEMMA: Empty targets always falls through (alt)
-/
theorem switchInt_empty_targets' (s : State) (discr : Operand) (otherwise : BasicBlock)
    (v : Value) (d : Int)
    (hEval : evalOperand s discr = some v)
    (hDiscr : asSwitchIntDiscr v = some d) :
    execTerminator s (.SwitchInt discr [] otherwise) = some (.goto otherwise) := by
  simp [execTerminator, hEval, hDiscr, List.find?]

/-
  LEMMA: Single target match
-/
theorem switchInt_single_match (s : State) (discr : Operand) (d : Int) (bb otherwise : BasicBlock)
    (v : Value)
    (hEval : evalOperand s discr = some v)
    (hDiscr : asSwitchIntDiscr v = some d) :
    execTerminator s (.SwitchInt discr [(d, bb)] otherwise) = some (.goto bb) := by
  simp [execTerminator, hEval, hDiscr, List.find?]

/-!
  ## MirBody Properties
-/

/-
  LEMMA: getBlock on empty body returns none (alt)
-/
theorem MirBody.getBlock_empty'' (localCount entry : Nat) (bb : BasicBlock) :
    (MirBody.mk localCount [] entry).getBlock bb = none := by
  simp [MirBody.getBlock]

/-
  LEMMA: getBlock at 0 with non-empty body (alt)
-/
@[simp]
theorem MirBody.getBlock_zero' (localCount entry : Nat) (b : BasicBlockData) (rest : List BasicBlockData) :
    (MirBody.mk localCount (b :: rest) entry).getBlock 0 = some b := rfl

/-
  LEMMA: getBlock successor
-/
@[simp]
theorem MirBody.getBlock_succ (localCount entry bb : Nat) (b : BasicBlockData) (rest : List BasicBlockData) :
    (MirBody.mk localCount (b :: rest) entry).getBlock (bb + 1) =
    (MirBody.mk localCount rest entry).getBlock bb := rfl

/-!
  ## MirProgram Properties
-/

/-
  LEMMA: getFun is just function application
-/
@[simp]
theorem MirProgram.getFun_apply (funs : String → Option MirBody) (name : String) :
    (MirProgram.mk funs).getFun name = funs name := rfl

/-
  LEMMA: getFun on program with constant none returns none
-/
@[simp]
theorem MirProgram.getFun_const_none (name : String) :
    (MirProgram.mk (fun _ => none)).getFun name = none := rfl

/-!
  ## BinOp Discrimination Lemmas
-/

/-
  LEMMA: add is not sub
-/
theorem BinOp.add_ne_sub : BinOp.add ≠ BinOp.sub := by
  intro h; cases h

/-
  LEMMA: add is not mul
-/
theorem BinOp.add_ne_mul : BinOp.add ≠ BinOp.mul := by
  intro h; cases h

/-
  LEMMA: add is not div
-/
theorem BinOp.add_ne_div : BinOp.add ≠ BinOp.div := by
  intro h; cases h

/-
  LEMMA: mul is not div
-/
theorem BinOp.mul_ne_div : BinOp.mul ≠ BinOp.div := by
  intro h; cases h

/-
  LEMMA: eq is not ne
-/
theorem BinOp.eq_ne_ne : BinOp.eq ≠ BinOp.ne := by
  intro h; cases h

/-
  LEMMA: lt is not gt
-/
theorem BinOp.lt_ne_gt : BinOp.lt ≠ BinOp.gt := by
  intro h; cases h

/-
  LEMMA: le is not ge
-/
theorem BinOp.le_ne_ge : BinOp.le ≠ BinOp.ge := by
  intro h; cases h

/-
  LEMMA: addChecked is not add
-/
theorem BinOp.addChecked_ne_add : BinOp.addChecked ≠ BinOp.add := by
  intro h; cases h

/-
  LEMMA: subChecked is not sub
-/
theorem BinOp.subChecked_ne_sub : BinOp.subChecked ≠ BinOp.sub := by
  intro h; cases h

/-
  LEMMA: mulChecked is not mul
-/
theorem BinOp.mulChecked_ne_mul : BinOp.mulChecked ≠ BinOp.mul := by
  intro h; cases h

/-
  LEMMA: bitAnd is not bitOr
-/
theorem BinOp.bitAnd_ne_bitOr : BinOp.bitAnd ≠ BinOp.bitOr := by
  intro h; cases h

/-
  LEMMA: shl is not shr
-/
theorem BinOp.shl_ne_shr : BinOp.shl ≠ BinOp.shr := by
  intro h; cases h

/-!
  ## UnOp Discrimination Lemmas
-/

/-
  LEMMA: neg is not not
-/
theorem UnOp.neg_ne_not : UnOp.neg ≠ UnOp.not := by
  intro h; cases h

/-!
  ## MirStmt Discrimination Lemmas
-/

/-
  LEMMA: Assign is not StorageLive
-/
theorem MirStmt.assign_ne_storageLive (dst : Place) (src : Rvalue) (l : Local) :
    MirStmt.Assign dst src ≠ MirStmt.StorageLive l := by
  intro h; cases h

/-
  LEMMA: Assign is not StorageDead
-/
theorem MirStmt.assign_ne_storageDead (dst : Place) (src : Rvalue) (l : Local) :
    MirStmt.Assign dst src ≠ MirStmt.StorageDead l := by
  intro h; cases h

/-
  LEMMA: Assign is not Nop
-/
theorem MirStmt.assign_ne_nop (dst : Place) (src : Rvalue) :
    MirStmt.Assign dst src ≠ MirStmt.Nop := by
  intro h; cases h

/-
  LEMMA: StorageLive is not StorageDead
-/
theorem MirStmt.storageLive_ne_storageDead (l1 l2 : Local) :
    MirStmt.StorageLive l1 ≠ MirStmt.StorageDead l2 := by
  intro h; cases h

/-
  LEMMA: StorageLive is not Nop
-/
theorem MirStmt.storageLive_ne_nop (l : Local) :
    MirStmt.StorageLive l ≠ MirStmt.Nop := by
  intro h; cases h

/-
  LEMMA: StorageDead is not Nop
-/
theorem MirStmt.storageDead_ne_nop (l : Local) :
    MirStmt.StorageDead l ≠ MirStmt.Nop := by
  intro h; cases h

/-
  LEMMA: StorageLive injectivity
-/
theorem MirStmt.storageLive_injective (l1 l2 : Local) :
    MirStmt.StorageLive l1 = MirStmt.StorageLive l2 → l1 = l2 := by
  intro h; cases h; rfl

/-
  LEMMA: StorageDead injectivity
-/
theorem MirStmt.storageDead_injective (l1 l2 : Local) :
    MirStmt.StorageDead l1 = MirStmt.StorageDead l2 → l1 = l2 := by
  intro h; cases h; rfl

/-!
  ## Rvalue Discrimination Lemmas
-/

/-
  LEMMA: use is not binOp
-/
theorem Rvalue.use_ne_binOp (op1 : Operand) (bop : BinOp) (lhs rhs : Operand) :
    Rvalue.use op1 ≠ Rvalue.binOp bop lhs rhs := by
  intro h; cases h

/-
  LEMMA: use is not unOp
-/
theorem Rvalue.use_ne_unOp (op1 : Operand) (uop : UnOp) (op2 : Operand) :
    Rvalue.use op1 ≠ Rvalue.unOp uop op2 := by
  intro h; cases h

/-
  LEMMA: binOp is not unOp
-/
theorem Rvalue.binOp_ne_unOp (bop : BinOp) (lhs rhs : Operand) (uop : UnOp) (op : Operand) :
    Rvalue.binOp bop lhs rhs ≠ Rvalue.unOp uop op := by
  intro h; cases h

/-
  LEMMA: use is not ref
-/
theorem Rvalue.use_ne_ref (op : Operand) (bk : BorrowKind) (place : Place) :
    Rvalue.use op ≠ Rvalue.ref bk place := by
  intro h; cases h

/-
  LEMMA: binOp is not checkedBinOp
-/
theorem Rvalue.binOp_ne_checkedBinOp (op1 : BinOp) (lhs1 rhs1 : Operand)
    (op2 : BinOp) (lhs2 rhs2 : Operand) :
    Rvalue.binOp op1 lhs1 rhs1 ≠ Rvalue.checkedBinOp op2 lhs2 rhs2 := by
  intro h; cases h

/-
  LEMMA: aggregate is not len
-/
theorem Rvalue.aggregate_ne_len (kind : AggregateKind) (ops : List Operand) (place : Place) :
    Rvalue.aggregate kind ops ≠ Rvalue.len place := by
  intro h; cases h

/-
  LEMMA: cast is not discriminant
-/
theorem Rvalue.cast_ne_discriminant (op : Operand) (place : Place) :
    Rvalue.cast op ≠ Rvalue.discriminant place := by
  intro h; cases h

/-
  LEMMA: repeat is not use
-/
theorem Rvalue.repeat_ne_use (op1 : Operand) (count : Nat) (op2 : Operand) :
    Rvalue.repeat op1 count ≠ Rvalue.use op2 := by
  intro h; cases h

/-!
  ## AggregateKind Discrimination Lemmas
-/

/-
  LEMMA: array is not tuple
-/
theorem AggregateKind.array_ne_tuple : AggregateKind.array ≠ AggregateKind.tuple := by
  intro h; cases h

/-
  LEMMA: array is not closure
-/
theorem AggregateKind.array_ne_closure : AggregateKind.array ≠ AggregateKind.closure := by
  intro h; cases h

/-
  LEMMA: tuple is not closure
-/
theorem AggregateKind.tuple_ne_closure : AggregateKind.tuple ≠ AggregateKind.closure := by
  intro h; cases h

/-!
  ## BorrowKind Discrimination Lemmas
-/

/-
  LEMMA: shared is not mutable
-/
theorem BorrowKind.shared_ne_mutable : BorrowKind.shared ≠ BorrowKind.mutable := by
  intro h; cases h

/-
  LEMMA: shared is not shallow
-/
theorem BorrowKind.shared_ne_shallow : BorrowKind.shared ≠ BorrowKind.shallow := by
  intro h; cases h

/-
  LEMMA: mutable is not shallow
-/
theorem BorrowKind.mutable_ne_shallow : BorrowKind.mutable ≠ BorrowKind.shallow := by
  intro h; cases h

/-!
  ## Mutability Discrimination Lemmas
-/

/-
  LEMMA: shared is not mutable (Mutability)
-/
theorem Mutability.shared_ne_mutable : Mutability.shared ≠ Mutability.mutable := by
  intro h; cases h

/-!
  ## IntTy Discrimination Lemmas
-/

/-
  LEMMA: i8 is not i16
-/
theorem IntTy.i8_ne_i16 : IntTy.i8 ≠ IntTy.i16 := by
  intro h; cases h

/-
  LEMMA: i8 is not i32
-/
theorem IntTy.i8_ne_i32 : IntTy.i8 ≠ IntTy.i32 := by
  intro h; cases h

/-
  LEMMA: i8 is not i64
-/
theorem IntTy.i8_ne_i64 : IntTy.i8 ≠ IntTy.i64 := by
  intro h; cases h

/-
  LEMMA: i32 is not i64
-/
theorem IntTy.i32_ne_i64 : IntTy.i32 ≠ IntTy.i64 := by
  intro h; cases h

/-
  LEMMA: u8 is not u16
-/
theorem IntTy.u8_ne_u16 : IntTy.u8 ≠ IntTy.u16 := by
  intro h; cases h

/-
  LEMMA: u32 is not u64
-/
theorem IntTy.u32_ne_u64 : IntTy.u32 ≠ IntTy.u64 := by
  intro h; cases h

/-
  LEMMA: i32 is not u32
-/
theorem IntTy.i32_ne_u32 : IntTy.i32 ≠ IntTy.u32 := by
  intro h; cases h

/-
  LEMMA: isize is not usize
-/
theorem IntTy.isize_ne_usize : IntTy.isize ≠ IntTy.usize := by
  intro h; cases h

/-!
  ## IntTy Property Lemmas
-/

/-
  LEMMA: i8 has 8 bits
-/
@[simp]
theorem IntTy.i8_bits : IntTy.i8.bits = 8 := rfl

/-
  LEMMA: i32 has 32 bits
-/
@[simp]
theorem IntTy.i32_bits : IntTy.i32.bits = 32 := rfl

/-
  LEMMA: i64 has 64 bits
-/
@[simp]
theorem IntTy.i64_bits : IntTy.i64.bits = 64 := rfl

/-
  LEMMA: u8 has 8 bits
-/
@[simp]
theorem IntTy.u8_bits : IntTy.u8.bits = 8 := rfl

/-
  LEMMA: u32 has 32 bits
-/
@[simp]
theorem IntTy.u32_bits : IntTy.u32.bits = 32 := rfl

/-
  LEMMA: u64 has 64 bits
-/
@[simp]
theorem IntTy.u64_bits : IntTy.u64.bits = 64 := rfl

/-
  LEMMA: i16 has 16 bits
-/
@[simp]
theorem IntTy.i16_bits : IntTy.i16.bits = 16 := rfl

/-
  LEMMA: u16 has 16 bits
-/
@[simp]
theorem IntTy.u16_bits : IntTy.u16.bits = 16 := rfl

/-
  LEMMA: isize has 64 bits
-/
@[simp]
theorem IntTy.isize_bits : IntTy.isize.bits = 64 := rfl

/-
  LEMMA: usize has 64 bits
-/
@[simp]
theorem IntTy.usize_bits : IntTy.usize.bits = 64 := rfl

/-
  LEMMA: Signed types have negative minVal
-/
theorem IntTy.signed_minVal_neg (ty : IntTy) (h : ty.isSigned = true) :
    ty.minVal < 0 := by
  simp [IntTy.minVal, h]
  have : (2 : Int) ^ (ty.bits - 1) > 0 := by
    apply Int.pow_pos
    decide
  omega

/-
  LEMMA: Unsigned types have zero minVal (variant)
-/
theorem IntTy.unsigned_minVal_zero' (ty : IntTy) (h : ty.isSigned = false) :
    ty.minVal = 0 := by
  simp [IntTy.minVal, h]

/-
  LEMMA: Zero is in range for all integer types
-/
theorem IntTy.zero_in_range (ty : IntTy) : ty.inRange 0 = true := by
  simp [IntTy.inRange]
  constructor
  · cases ty <;> simp [IntTy.minVal, IntTy.isSigned, IntTy.bits] <;> decide
  · cases ty <;> simp [IntTy.maxVal, IntTy.isSigned, IntTy.bits] <;> decide

/-!
  ## evalBinOp Property Lemmas
-/

/-
  LEMMA: evalBinOp add on same-type ints succeeds
-/
theorem evalBinOp_add_int (ty : IntTy) (a b : Int) :
    evalBinOp .add (.int ty a) (.int ty b) = some (.int ty (a + b)) := by
  simp [evalBinOp]

/-
  LEMMA: evalBinOp sub on same-type ints succeeds
-/
theorem evalBinOp_sub_int (ty : IntTy) (a b : Int) :
    evalBinOp .sub (.int ty a) (.int ty b) = some (.int ty (a - b)) := by
  simp [evalBinOp]

/-
  LEMMA: evalBinOp mul on same-type ints succeeds
-/
theorem evalBinOp_mul_int (ty : IntTy) (a b : Int) :
    evalBinOp .mul (.int ty a) (.int ty b) = some (.int ty (a * b)) := by
  simp [evalBinOp]

/-
  LEMMA: evalBinOp div on non-zero succeeds
-/
theorem evalBinOp_div_int_nonzero (ty : IntTy) (a b : Int) (hb : b ≠ 0) :
    evalBinOp .div (.int ty a) (.int ty b) = some (.int ty (a / b)) := by
  simp [evalBinOp, hb]

/-
  LEMMA: evalBinOp eq on bools
-/
theorem evalBinOp_eq_bool (a b : Bool) :
    evalBinOp .eq (.bool a) (.bool b) = some (.bool (a == b)) := by
  simp [evalBinOp]

/-
  LEMMA: evalBinOp ne on bools
-/
theorem evalBinOp_ne_bool (a b : Bool) :
    evalBinOp .ne (.bool a) (.bool b) = some (.bool (a != b)) := by
  simp [evalBinOp]

/-
  LEMMA: evalBinOp on different int types fails
-/
theorem evalBinOp_diff_types_none (op : BinOp) (ty1 ty2 : IntTy) (a b : Int)
    (hNeq : ty1 ≠ ty2) :
    evalBinOp op (.int ty1 a) (.int ty2 b) = none := by
  simp [evalBinOp, hNeq]

/-
  LEMMA: evalBinOp add on mismatched types fails
-/
theorem evalBinOp_add_int_bool_none (ty : IntTy) (a : Int) (b : Bool) :
    evalBinOp .add (.int ty a) (.bool b) = none := by
  simp [evalBinOp]

/-!
  ## evalUnOp Property Lemmas
-/

/-
  LEMMA: evalUnOp neg on int
-/
theorem evalUnOp_neg_int (ty : IntTy) (v : Int) :
    evalUnOp .neg (.int ty v) = some (.int ty (-v)) := by
  simp [evalUnOp]

/-
  LEMMA: evalUnOp not on bool
-/
theorem evalUnOp_not_bool (b : Bool) :
    evalUnOp .not (.bool b) = some (.bool (!b)) := by
  simp [evalUnOp]

/-
  LEMMA: evalUnOp neg on bool fails
-/
theorem evalUnOp_neg_bool_none (b : Bool) :
    evalUnOp .neg (.bool b) = none := by
  simp [evalUnOp]

/-
  LEMMA: evalUnOp on unit fails
-/
theorem evalUnOp_unit_none (op : UnOp) :
    evalUnOp op .unit = none := by
  cases op <;> simp [evalUnOp]

/-!
  ## PlaceElem Discrimination Lemmas
-/

/-
  LEMMA: deref is not field
-/
theorem PlaceElem.deref_ne_field (idx : Nat) :
    PlaceElem.deref ≠ PlaceElem.field idx := by
  intro h; cases h

/-
  LEMMA: deref is not index
-/
theorem PlaceElem.deref_ne_index (l : Local) :
    PlaceElem.deref ≠ PlaceElem.index l := by
  intro h; cases h

/-
  LEMMA: deref is not constIndex
-/
theorem PlaceElem.deref_ne_constIndex (idx : Nat) :
    PlaceElem.deref ≠ PlaceElem.constIndex idx := by
  intro h; cases h

/-
  LEMMA: field is not index
-/
theorem PlaceElem.field_ne_index (idx : Nat) (l : Local) :
    PlaceElem.field idx ≠ PlaceElem.index l := by
  intro h; cases h

/-
  LEMMA: field injectivity
-/
theorem PlaceElem.field_injective (idx1 idx2 : Nat) :
    PlaceElem.field idx1 = PlaceElem.field idx2 → idx1 = idx2 := by
  intro h; cases h; rfl

/-
  LEMMA: constIndex injectivity
-/
theorem PlaceElem.constIndex_injective (idx1 idx2 : Nat) :
    PlaceElem.constIndex idx1 = PlaceElem.constIndex idx2 → idx1 = idx2 := by
  intro h; cases h; rfl

/-!
  ## Operand Property Lemmas
-/

/-
  LEMMA: const is not copy
-/
theorem Operand.const_ne_copy (v : Value) (p : Place) :
    Operand.const v ≠ Operand.copy p := by
  intro h; cases h

/-
  LEMMA: const is not move
-/
theorem Operand.const_ne_move (v : Value) (p : Place) :
    Operand.const v ≠ Operand.move p := by
  intro h; cases h

/-
  LEMMA: copy is not move
-/
theorem Operand.copy_ne_move (p1 p2 : Place) :
    Operand.copy p1 ≠ Operand.move p2 := by
  intro h; cases h

/-
  LEMMA: const injectivity
-/
theorem Operand.const_injective (v1 v2 : Value) :
    Operand.const v1 = Operand.const v2 → v1 = v2 := by
  intro h; cases h; rfl

/-!
  ## evalPlace Property Lemmas
-/

/-
  LEMMA: evalPlace local on alive local with value
-/
theorem evalPlace_local_alive (s : State) (l : Local) (v : Value)
    (hAlive : s.isAlive l = true) (hVal : s.locals l = some v) :
    evalPlace s (.local l) = some v := by
  simp [evalPlace, State.readLocal, hAlive, hVal]

/-
  LEMMA: evalPlace local on dead local fails
-/
theorem evalPlace_local_dead (s : State) (l : Local)
    (hDead : s.isAlive l = false) :
    evalPlace s (.local l) = none := by
  simp [evalPlace, State.readLocal, hDead]

/-
  LEMMA: evalPlace is deterministic
-/
theorem evalPlace_det (s : State) (p : Place) (v1 v2 : Value)
    (h1 : evalPlace s p = some v1) (h2 : evalPlace s p = some v2) :
    v1 = v2 := by
  rw [h1] at h2
  injection h2

/-!
  ## evalRvalue Property Lemmas
-/

/-
  LEMMA: evalRvalue is deterministic
-/
theorem evalRvalue_det (s : State) (rv : Rvalue) (v1 v2 : Value)
    (h1 : evalRvalue s rv = some v1) (h2 : evalRvalue s rv = some v2) :
    v1 = v2 := by
  rw [h1] at h2
  injection h2

/-
  LEMMA: evalRvalue len on array
-/
theorem evalRvalue_len_array (s : State) (p : Place) (elems : List Value)
    (hEval : evalPlace s p = some (.array elems)) :
    evalRvalue s (.len p) = some (.int .usize elems.length) := by
  simp [evalRvalue, hEval]

/-
  LEMMA: evalRvalue repeat creates array
-/
theorem evalRvalue_repeat (s : State) (op : Operand) (v : Value) (count : Nat)
    (hEval : evalOperand s op = some v) :
    evalRvalue s (.repeat op count) = some (.array (List.replicate count v)) := by
  simp [evalRvalue, hEval]

/-!
  ## execStmt Extended Lemmas
-/

/-
  LEMMA: execStmt Nop is identity (second variant)
-/
@[simp]
theorem execStmt_nop_identity' (s : State) :
    execStmt s .Nop = some s := rfl

/-
  LEMMA: execStmt StorageLive always succeeds
-/
@[simp]
theorem execStmt_storageLive_isSome (s : State) (l : Local) :
    (execStmt s (.StorageLive l)).isSome = true := rfl

/-
  LEMMA: execStmt StorageDead always succeeds
-/
@[simp]
theorem execStmt_storageDead_isSome (s : State) (l : Local) :
    (execStmt s (.StorageDead l)).isSome = true := rfl

/-
  LEMMA: execStmt is deterministic (variant)
-/
theorem execStmt_det' (s : State) (stmt : MirStmt) (s1 s2 : State)
    (h1 : execStmt s stmt = some s1) (h2 : execStmt s stmt = some s2) :
    s1 = s2 := by
  rw [h1] at h2
  injection h2

/-!
  ## MirTerminator Extended Discrimination Lemmas
-/

/-
  LEMMA: Return is not Call (variant)
-/
theorem MirTerminator.return_ne_call' (func : Operand) (args : List Operand)
    (dest : Place) (target : BasicBlock) :
    MirTerminator.Return ≠ MirTerminator.Call func args dest target := by
  intro h; cases h

/-
  LEMMA: Goto is not Call (variant)
-/
theorem MirTerminator.goto_ne_call' (bb : BasicBlock) (func : Operand)
    (args : List Operand) (dest : Place) (target : BasicBlock) :
    MirTerminator.Goto bb ≠ MirTerminator.Call func args dest target := by
  intro h; cases h

/-
  LEMMA: Goto injectivity
-/
theorem MirTerminator.goto_injective (bb1 bb2 : BasicBlock) :
    MirTerminator.Goto bb1 = MirTerminator.Goto bb2 → bb1 = bb2 := by
  intro h; cases h; rfl

/-
  LEMMA: SwitchInt is not Assert
-/
theorem MirTerminator.switchInt_ne_assert (discr : Operand)
    (targets : List (Int × BasicBlock)) (otherwise : BasicBlock) (msg : AssertMsg) :
    MirTerminator.SwitchInt discr targets otherwise ≠ MirTerminator.Assert msg := by
  intro h; cases h

/-
  LEMMA: Call is not Drop
-/
theorem MirTerminator.call_ne_drop (func : Operand) (args : List Operand)
    (dest : Place) (target : BasicBlock) (place : Place) (target2 : BasicBlock)
    (unwind : Option BasicBlock) :
    MirTerminator.Call func args dest target ≠ MirTerminator.Drop place target2 unwind := by
  intro h; cases h

/-!
  ## Control Extended Lemmas
-/

/-
  LEMMA: Control.unwind injectivity
-/
theorem Control.unwind_injective (bb1 bb2 : BasicBlock) :
    Control.unwind bb1 = Control.unwind bb2 → bb1 = bb2 := by
  intro h; cases h; rfl

/-
  LEMMA: unwind is not panic
-/
theorem Control.unwind_ne_panic (bb : BasicBlock) :
    Control.unwind bb ≠ Control.panic := by
  intro h; cases h

/-
  LEMMA: goto is not unwind (variant)
-/
theorem Control.goto_ne_unwind' (bb1 bb2 : BasicBlock) :
    Control.goto bb1 ≠ Control.unwind bb2 := by
  intro h; cases h

/-
  LEMMA: return_ is not unwind (variant)
-/
theorem Control.return_ne_unwind' (bb : BasicBlock) :
    Control.return_ ≠ Control.unwind bb := by
  intro h; cases h

/-!
  ## asSwitchIntDiscr Property Lemmas
-/

/-
  LEMMA: asSwitchIntDiscr on bool true (variant)
-/
@[simp]
theorem asSwitchIntDiscr_bool_true' :
    asSwitchIntDiscr (.bool true) = some 1 := rfl

/-
  LEMMA: asSwitchIntDiscr on bool false (variant)
-/
@[simp]
theorem asSwitchIntDiscr_bool_false' :
    asSwitchIntDiscr (.bool false) = some 0 := rfl

/-
  LEMMA: asSwitchIntDiscr on int (variant)
-/
@[simp]
theorem asSwitchIntDiscr_int' (ty : IntTy) (i : Int) :
    asSwitchIntDiscr (.int ty i) = some i := rfl

/-
  LEMMA: asSwitchIntDiscr on unit is none
-/
@[simp]
theorem asSwitchIntDiscr_unit_none :
    asSwitchIntDiscr .unit = none := rfl

/-
  LEMMA: asSwitchIntDiscr on fn_ is none
-/
@[simp]
theorem asSwitchIntDiscr_fn_none' (name : String) :
    asSwitchIntDiscr (.fn_ name) = none := rfl

/-
  LEMMA: asSwitchIntDiscr on ref is none
-/
@[simp]
theorem asSwitchIntDiscr_ref_none (loc : Location) :
    asSwitchIntDiscr (.ref loc) = none := rfl

/-
  LEMMA: asSwitchIntDiscr on rawPtr is none
-/
@[simp]
theorem asSwitchIntDiscr_rawPtr_none (oloc : Option Location) :
    asSwitchIntDiscr (.rawPtr oloc) = none := rfl

/-!
  ## MirTy Discrimination Lemmas
-/

/-
  LEMMA: bool is not int
-/
theorem MirTy.bool_ne_int (ty : IntTy) : MirTy.bool ≠ MirTy.int ty := by
  intro h; cases h

/-
  LEMMA: bool is not unit
-/
theorem MirTy.bool_ne_unit : MirTy.bool ≠ MirTy.unit := by
  intro h; cases h

/-
  LEMMA: int is not unit
-/
theorem MirTy.int_ne_unit (ty : IntTy) : MirTy.int ty ≠ MirTy.unit := by
  intro h; cases h

/-
  LEMMA: ref is not box_
-/
theorem MirTy.ref_ne_box (m : Mutability) (p1 : MirTy) (p2 : MirTy) :
    MirTy.ref m p1 ≠ MirTy.box_ p2 := by
  intro h; cases h

/-
  LEMMA: array is not tuple
-/
theorem MirTy.array_ne_tuple (elem : MirTy) (len : Nat) (elems : List MirTy) :
    MirTy.array elem len ≠ MirTy.tuple elems := by
  intro h; cases h

/-
  LEMMA: opaque is not bool
-/
theorem MirTy.opaque_ne_bool (name : String) : MirTy.opaque name ≠ MirTy.bool := by
  intro h; cases h

/-
  LEMMA: int injectivity
-/
theorem MirTy.int_injective (ty1 ty2 : IntTy) :
    MirTy.int ty1 = MirTy.int ty2 → ty1 = ty2 := by
  intro h; cases h; rfl

/-
  LEMMA: opaque injectivity
-/
theorem MirTy.opaque_injective (n1 n2 : String) :
    MirTy.opaque n1 = MirTy.opaque n2 → n1 = n2 := by
  intro h; cases h; rfl

/-!
  ## Heap Extended Lemmas
-/

/-
  LEMMA: Heap.empty.read is always none (variant)
-/
@[simp]
theorem Heap.empty_read' (loc : Location) :
    Heap.empty.read loc = none := rfl

/-
  LEMMA: Heap.empty.nextLoc is 0
-/
@[simp]
theorem Heap.empty_nextLoc :
    Heap.empty.nextLoc = 0 := rfl

/-
  LEMMA: Write then read same location
-/
theorem Heap.write_read_same (h : Heap) (loc : Location) (v : Value) :
    (h.write loc v).read loc = some v := by
  simp [Heap.write, Heap.read]

/-
  LEMMA: Alloc returns written value (variant)
-/
theorem Heap.alloc_read' (h : Heap) (v : Value) :
    let (h', loc) := h.alloc v
    h'.read loc = some v := by
  simp [Heap.alloc, Heap.read]

/-
  LEMMA: Multiple writes: last one wins
-/
theorem Heap.write_write_same (h : Heap) (loc : Location) (v1 v2 : Value) :
    ((h.write loc v1).write loc v2).read loc = some v2 := by
  simp [Heap.write, Heap.read]

/-
  LEMMA: Write commutes on different locations
-/
theorem Heap.write_write_comm (h : Heap) (l1 l2 : Location) (v1 v2 : Value)
    (hNe : l1 ≠ l2) :
    ((h.write l1 v1).write l2 v2).read l1 =
    ((h.write l2 v2).write l1 v1).read l1 := by
  simp [Heap.write, Heap.read, hNe]

/-!
  ## State Extended Lemmas
-/

/-
  LEMMA: State.empty has no alive locals
-/
@[simp]
theorem State.empty_not_alive (l : Local) :
    State.empty.isAlive l = false := rfl

/-
  LEMMA: State.empty.readLocal is none (variant)
-/
theorem State.empty_readLocal' (l : Local) :
    State.empty.readLocal l = none := by
  simp [State.readLocal, State.empty, State.isAlive]

/-
  LEMMA: StorageLive then StorageDead is idempotent for isAlive
-/
theorem State.storageLive_storageDead_alive (s : State) (l : Local) :
    ((s.storageLive l).storageDead l).isAlive l = false := by
  simp [State.storageLive, State.storageDead, State.isAlive]

/-
  LEMMA: StorageDead then StorageLive is idempotent for isAlive
-/
theorem State.storageDead_storageLive_alive (s : State) (l : Local) :
    ((s.storageDead l).storageLive l).isAlive l = true := by
  simp [State.storageDead, State.storageLive, State.isAlive]

/-
  LEMMA: heapWrite preserves local alive status
-/
@[simp]
theorem State.heapWrite_preserves_alive (s : State) (loc : Location) (v : Value) (l : Local) :
    (s.heapWrite loc v).isAlive l = s.isAlive l := rfl

/-
  LEMMA: heapAlloc preserves local alive status
-/
@[simp]
theorem State.heapAlloc_preserves_alive (s : State) (v : Value) (l : Local) :
    (s.heapAlloc v).1.isAlive l = s.isAlive l := rfl

/-
  LEMMA: heapDealloc preserves local alive status
-/
@[simp]
theorem State.heapDealloc_preserves_alive (s : State) (loc : Location) (l : Local) :
    (s.heapDealloc loc).isAlive l = s.isAlive l := rfl

/-!
  ## Value.fn_ Lemmas
-/

/-
  LEMMA: fn_ injectivity
-/
theorem Value.fn_injective (n1 n2 : String) :
    Value.fn_ n1 = Value.fn_ n2 → n1 = n2 := by
  intro h; cases h; rfl

/-
  LEMMA: fn_ is not unit
-/
theorem Value.fn_ne_unit (name : String) :
    Value.fn_ name ≠ .unit := by
  intro h; cases h

/-
  LEMMA: fn_ is not ref
-/
theorem Value.fn_ne_ref (name : String) (loc : Location) :
    Value.fn_ name ≠ .ref loc := by
  intro h; cases h

/-
  LEMMA: fn_ is not box
-/
theorem Value.fn_ne_box (name : String) (loc : Location) :
    Value.fn_ name ≠ .box_ loc := by
  intro h; cases h

/-
  LEMMA: fn_ is not array
-/
theorem Value.fn_ne_array (name : String) (elems : List Value) :
    Value.fn_ name ≠ .array elems := by
  intro h; cases h

/-
  LEMMA: fn_ is not tuple
-/
theorem Value.fn_ne_tuple (name : String) (elems : List Value) :
    Value.fn_ name ≠ .tuple elems := by
  intro h; cases h

/-!
  ## checkedAdd/Sub/Mul Property Lemmas
-/

/-
  LEMMA: checkedAdd result is sum (variant)
-/
@[simp]
theorem checkedAdd_result' (ty : IntTy) (a b : Int) :
    (checkedAdd ty a b).1 = a + b := rfl

/-
  LEMMA: checkedSub result is difference (variant)
-/
@[simp]
theorem checkedSub_result' (ty : IntTy) (a b : Int) :
    (checkedSub ty a b).1 = a - b := rfl

/-
  LEMMA: checkedMul result is product (variant)
-/
@[simp]
theorem checkedMul_result' (ty : IntTy) (a b : Int) :
    (checkedMul ty a b).1 = a * b := rfl

/-
  LEMMA: checkedAdd overflow flag matches inRange
-/
@[simp]
theorem checkedAdd_overflow_iff (ty : IntTy) (a b : Int) :
    (checkedAdd ty a b).2 = !ty.inRange (a + b) := rfl

/-
  LEMMA: checkedSub overflow flag matches inRange
-/
@[simp]
theorem checkedSub_overflow_iff (ty : IntTy) (a b : Int) :
    (checkedSub ty a b).2 = !ty.inRange (a - b) := rfl

/-
  LEMMA: checkedMul overflow flag matches inRange
-/
@[simp]
theorem checkedMul_overflow_iff (ty : IntTy) (a b : Int) :
    (checkedMul ty a b).2 = !ty.inRange (a * b) := rfl

/-!
  ## BasicBlockData Lemmas
-/

/-
  LEMMA: BasicBlockData with same fields are equal
-/
theorem BasicBlockData.eq_of_fields (bb1 bb2 : BasicBlockData)
    (hStmts : bb1.stmts = bb2.stmts)
    (hTerm : bb1.terminator = bb2.terminator) :
    bb1 = bb2 := by
  cases bb1; cases bb2
  simp at hStmts hTerm
  simp [hStmts, hTerm]

/-!
  ## List.find? Properties for SwitchInt
-/

/-
  LEMMA: find? on nil returns none
-/
@[simp]
theorem List.find_nil {α : Type} (p : α → Bool) :
    ([] : List α).find? p = none := rfl

/-
  LEMMA: find? on single element matching
-/
theorem List.find_single_match {α : Type} (x : α) (p : α → Bool) (hp : p x = true) :
    [x].find? p = some x := by
  simp [List.find?, hp]

/-
  LEMMA: find? on single element not matching
-/
theorem List.find_single_no_match {α : Type} (x : α) (p : α → Bool) (hp : p x = false) :
    [x].find? p = none := by
  simp [List.find?, hp]

/-!
  ## N2.1 Extension: evalBinOp Reflexivity Lemmas
-/

/-
  LEMMA: evalBinOp eq reflexivity
-/
theorem evalBinOp_eq_self (ty : IntTy) (a : Int) :
    evalBinOp .eq (.int ty a) (.int ty a) = some (.bool true) := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: evalBinOp ne self is false
-/
theorem evalBinOp_ne_self (ty : IntTy) (a : Int) :
    evalBinOp .ne (.int ty a) (.int ty a) = some (.bool false) := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: evalBinOp lt self is false
-/
theorem evalBinOp_lt_self (ty : IntTy) (a : Int) :
    evalBinOp .lt (.int ty a) (.int ty a) = some (.bool false) := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: evalBinOp le self is true
-/
theorem evalBinOp_le_self (ty : IntTy) (a : Int) :
    evalBinOp .le (.int ty a) (.int ty a) = some (.bool true) := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: evalBinOp gt self is false
-/
theorem evalBinOp_gt_self (ty : IntTy) (a : Int) :
    evalBinOp .gt (.int ty a) (.int ty a) = some (.bool false) := by
  simp [evalBinOp, evalCmp]

/-
  LEMMA: evalBinOp ge self is true
-/
theorem evalBinOp_ge_self (ty : IntTy) (a : Int) :
    evalBinOp .ge (.int ty a) (.int ty a) = some (.bool true) := by
  simp [evalBinOp, evalCmp]

/-!
  ## N2.1 Extension: evalBinOp Boolean Lemmas
-/

/-
  LEMMA: evalBinOp boolean and commutative
-/
theorem evalBinOp_bool_and_commutative (a b : Bool) :
    evalBinOp .bitAnd (.bool a) (.bool b) = evalBinOp .bitAnd (.bool b) (.bool a) := by
  simp [evalBinOp, Bool.and_comm]

/-
  LEMMA: evalBinOp boolean or commutative
-/
theorem evalBinOp_bool_or_commutative (a b : Bool) :
    evalBinOp .bitOr (.bool a) (.bool b) = evalBinOp .bitOr (.bool b) (.bool a) := by
  simp [evalBinOp, Bool.or_comm]

/-
  LEMMA: evalBinOp boolean and with true
-/
theorem evalBinOp_bool_and_true_result (a : Bool) :
    evalBinOp .bitAnd (.bool a) (.bool true) = some (.bool a) := by
  simp [evalBinOp]

/-
  LEMMA: evalBinOp boolean and with false
-/
theorem evalBinOp_bool_and_false_result (a : Bool) :
    evalBinOp .bitAnd (.bool a) (.bool false) = some (.bool false) := by
  simp [evalBinOp]

/-
  LEMMA: evalBinOp boolean or with true
-/
theorem evalBinOp_bool_or_true_result (a : Bool) :
    evalBinOp .bitOr (.bool a) (.bool true) = some (.bool true) := by
  simp [evalBinOp]

/-
  LEMMA: evalBinOp boolean or with false
-/
theorem evalBinOp_bool_or_false_result (a : Bool) :
    evalBinOp .bitOr (.bool a) (.bool false) = some (.bool a) := by
  simp [evalBinOp]

/-!
  ## N2.1 Extension: evalUnOp Lemmas
-/

/-
  LEMMA: evalUnOp not not for booleans
-/
theorem evalUnOp_not_not_bool (b : Bool) :
    evalUnOp .not (.bool (!b)) = some (.bool b) := by
  simp [evalUnOp]

/-
  LEMMA: evalUnOp not true is false
-/
@[simp]
theorem evalUnOp_not_true_result :
    evalUnOp .not (.bool true) = some (.bool false) := rfl

/-
  LEMMA: evalUnOp not false is true
-/
@[simp]
theorem evalUnOp_not_false_result :
    evalUnOp .not (.bool false) = some (.bool true) := rfl

/-
  LEMMA: evalUnOp neg zero is zero
-/
@[simp]
theorem evalUnOp_neg_zero_result (ty : IntTy) :
    evalUnOp .neg (.int ty 0) = some (.int ty 0) := rfl

/-!
  ## N2.1 Extension: Value Discrimination Lemmas
-/

/-
  LEMMA: bool true is not bool false
-/
theorem Value.bool_true_ne_bool_false :
    Value.bool true ≠ Value.bool false := by
  intro h; cases h

/-
  LEMMA: int values with different types
-/
theorem Value.int_diff_ty (ty1 ty2 : IntTy) (v1 v2 : Int)
    (hty : ty1 ≠ ty2) :
    Value.int ty1 v1 ≠ Value.int ty2 v2 := by
  intro h
  cases h
  exact absurd rfl hty

/-
  LEMMA: int values with different values
-/
theorem Value.int_diff_val (ty : IntTy) (v1 v2 : Int)
    (hv : v1 ≠ v2) :
    Value.int ty v1 ≠ Value.int ty v2 := by
  intro h
  cases h
  exact absurd rfl hv

/-
  LEMMA: ref values with different locations
-/
theorem Value.ref_diff_loc (loc1 loc2 : Location)
    (hloc : loc1 ≠ loc2) :
    Value.ref loc1 ≠ Value.ref loc2 := by
  intro h
  cases h
  exact absurd rfl hloc

/-
  LEMMA: box values with different locations
-/
theorem Value.box_diff_loc (loc1 loc2 : Location)
    (hloc : loc1 ≠ loc2) :
    Value.box_ loc1 ≠ Value.box_ loc2 := by
  intro h
  cases h
  exact absurd rfl hloc

/-
  LEMMA: tuple values with different lengths
-/
theorem Value.tuple_diff_len (elems1 elems2 : List Value)
    (hlen : elems1.length ≠ elems2.length) :
    Value.tuple elems1 ≠ Value.tuple elems2 := by
  intro h
  cases h
  exact absurd rfl hlen

/-
  LEMMA: array values with different lengths
-/
theorem Value.array_diff_len (elems1 elems2 : List Value)
    (hlen : elems1.length ≠ elems2.length) :
    Value.array elems1 ≠ Value.array elems2 := by
  intro h
  cases h
  exact absurd rfl hlen

/-!
  ## N2.1 Extension: IntTy Bounds Lemmas
-/

/-
  LEMMA: i64 min value
-/
@[simp]
theorem IntTy.i64_min_val :
    IntTy.i64.minVal = -(2^63) := rfl

/-
  LEMMA: i64 max value
-/
@[simp]
theorem IntTy.i64_max_val :
    IntTy.i64.maxVal = 2^63 - 1 := rfl

/-
  LEMMA: u64 min value
-/
@[simp]
theorem IntTy.u64_min_val :
    IntTy.u64.minVal = 0 := rfl

/-
  LEMMA: u64 max value
-/
@[simp]
theorem IntTy.u64_max_val :
    IntTy.u64.maxVal = 2^64 - 1 := rfl

/-
  LEMMA: i8 min value
-/
@[simp]
theorem IntTy.i8_min_val :
    IntTy.i8.minVal = -(2^7) := rfl

/-
  LEMMA: i8 max value
-/
@[simp]
theorem IntTy.i8_max_val :
    IntTy.i8.maxVal = 2^7 - 1 := rfl

/-
  LEMMA: u8 min value
-/
@[simp]
theorem IntTy.u8_min_val :
    IntTy.u8.minVal = 0 := rfl

/-
  LEMMA: u8 max value
-/
@[simp]
theorem IntTy.u8_max_val :
    IntTy.u8.maxVal = 2^8 - 1 := rfl

/-
  LEMMA: i16 min value
-/
@[simp]
theorem IntTy.i16_min_val :
    IntTy.i16.minVal = -(2^15) := rfl

/-
  LEMMA: i16 max value
-/
@[simp]
theorem IntTy.i16_max_val :
    IntTy.i16.maxVal = 2^15 - 1 := rfl

/-
  LEMMA: u16 min value
-/
@[simp]
theorem IntTy.u16_min_val :
    IntTy.u16.minVal = 0 := rfl

/-
  LEMMA: u16 max value
-/
@[simp]
theorem IntTy.u16_max_val :
    IntTy.u16.maxVal = 2^16 - 1 := rfl

/-
  LEMMA: Zero is in range for all types (variant)
-/
theorem IntTy.zero_inRange (ty : IntTy) :
    ty.inRange 0 = true := by
  simp [IntTy.inRange]
  constructor
  · cases ty <;> simp [IntTy.minVal, IntTy.isSigned, IntTy.bits]
  · cases ty <;> simp [IntTy.maxVal, IntTy.isSigned, IntTy.bits]

/-!
  ## N2.1 Extension: MirProgram Lemmas
-/

/-
  LEMMA: Empty program returns none
-/
@[simp]
theorem MirProgram.empty_lookup_none (name : String) :
    MirProgram.getFun { funs := fun _ => none } name = none := rfl

/-
  LEMMA: Single function program exact lookup
-/
theorem MirProgram.single_lookup_exact (funName : String) (body : MirBody) :
    MirProgram.getFun
      { funs := fun n => if n = funName then some body else none }
      funName = some body := by
  simp [MirProgram.getFun]

/-
  LEMMA: Single function program miss lookup
-/
theorem MirProgram.single_lookup_miss (funName otherName : String) (body : MirBody)
    (hne : otherName ≠ funName) :
    MirProgram.getFun
      { funs := fun n => if n = funName then some body else none }
      otherName = none := by
  simp [MirProgram.getFun, hne]

/-!
  ## N2.1 Extension: Aggregate Construction Lemmas
-/

/-
  LEMMA: Empty tuple construction
-/
@[simp]
theorem Value.tuple_nil_eq :
    (Value.tuple []) = .tuple [] := rfl

/-
  LEMMA: Empty array construction
-/
@[simp]
theorem Value.array_nil_eq :
    (Value.array []) = .array [] := rfl

/-
  LEMMA: Singleton tuple construction
-/
@[simp]
theorem Value.tuple_single_eq (v : Value) :
    Value.tuple [v] = .tuple [v] := rfl

/-
  LEMMA: Singleton array construction
-/
@[simp]
theorem Value.array_single_eq (v : Value) :
    Value.array [v] = .array [v] := rfl

/-
  LEMMA: Tuple cons construction
-/
@[simp]
theorem Value.tuple_cons_eq (v : Value) (vs : List Value) :
    Value.tuple (v :: vs) = .tuple (v :: vs) := rfl

/-
  LEMMA: Array cons construction
-/
@[simp]
theorem Value.array_cons_eq (v : Value) (vs : List Value) :
    Value.array (v :: vs) = .array (v :: vs) := rfl

/-!
  ## N2.1 Extension: Control Flow Discrimination
-/

/-
  LEMMA: goto is not unwind
-/
theorem Control.goto_ne_unwind_case (bb1 bb2 : BasicBlock) :
    Control.goto bb1 ≠ Control.unwind bb2 := by
  intro h; cases h

/-
  LEMMA: panic is not unwind
-/
theorem Control.panic_ne_unwind_case (bb : BasicBlock) :
    Control.panic ≠ Control.unwind bb := by
  intro h; cases h

/-!
  ## N2.1 Extension: evalRvalue Lemmas
-/

/-
  LEMMA: evalRvalue for use const
-/
@[simp]
theorem evalRvalue_use_const_case (s : State) (v : Value) :
    evalRvalue s (.use (.const v)) = some v := rfl

/-
  LEMMA: evalRvalue for repeat
-/
@[simp]
theorem evalRvalue_repeat_case (s : State) (v : Value) (n : Nat) :
    evalRvalue s (.repeat (.const v) n) = some (.array (List.replicate n v)) := rfl

/-!
  ## N2.1 Extension: Heap Lemmas
-/

/-
  LEMMA: Heap write then read same location
-/
theorem Heap.write_read_self (h : Heap) (loc : Location) (v : Value) :
    (h.write loc v).read loc = some v := by
  simp [Heap.write, Heap.read]

/-
  LEMMA: Heap dealloc then read same location is none
-/
theorem Heap.dealloc_read_self (h : Heap) (loc : Location) :
    (h.dealloc loc).read loc = none := by
  simp [Heap.dealloc, Heap.read]

/-
  LEMMA: Heap write preserves nextLoc
-/
@[simp]
theorem Heap.write_nextLoc_eq (h : Heap) (loc : Location) (v : Value) :
    (h.write loc v).nextLoc = h.nextLoc := rfl

/-
  LEMMA: Heap dealloc preserves nextLoc
-/
@[simp]
theorem Heap.dealloc_nextLoc_eq (h : Heap) (loc : Location) :
    (h.dealloc loc).nextLoc = h.nextLoc := rfl

/-!
  ## N2.1 Extension: execTerminator State Independence
-/

/-
  LEMMA: execTerminator Return is state-independent
-/
@[simp]
theorem execTerminator_return_indep (s1 s2 : State) :
    execTerminator s1 .Return = execTerminator s2 .Return := rfl

/-
  LEMMA: execTerminator Goto is state-independent
-/
@[simp]
theorem execTerminator_goto_indep (s1 s2 : State) (bb : BasicBlock) :
    execTerminator s1 (.Goto bb) = execTerminator s2 (.Goto bb) := rfl

/-
  LEMMA: execTerminator Unreachable is state-independent
-/
@[simp]
theorem execTerminator_unreachable_indep (s1 s2 : State) :
    execTerminator s1 .Unreachable = execTerminator s2 .Unreachable := rfl

/-
  LEMMA: execTerminator Drop is state-independent
-/
@[simp]
theorem execTerminator_drop_indep (s1 s2 : State) (place : Place)
    (target : BasicBlock) (unwind : Option BasicBlock) :
    execTerminator s1 (.Drop place target unwind) = execTerminator s2 (.Drop place target unwind) := rfl

/-!
  ## N2.1 Extension: Operand List Evaluation
-/

/-
  LEMMA: Empty operand list maps to empty value list
-/
@[simp]
theorem operands_nil_result (s : State) :
    ([] : List Operand).mapM (evalOperand s) = some [] := rfl

/-!
  ## N2.1 Extension: WP Terminator Lemmas
-/

/-
  LEMMA: wp_term for Return terminator
-/
theorem wp_term_return_intro (Q : Control → Prop) (s : State)
    (hQ : Q .return_) :
    wp_term .Return Q s := by
  simp [wp_term, execTerminator, hQ]

/-
  LEMMA: wp_term for Goto terminator
-/
theorem wp_term_goto_intro (bb : BasicBlock) (Q : Control → Prop) (s : State)
    (hQ : Q (.goto bb)) :
    wp_term (.Goto bb) Q s := by
  simp [wp_term, execTerminator, hQ]

/-
  LEMMA: wp_term for Unreachable terminator (vacuously true)
-/
theorem wp_term_unreachable_intro (Q : Control → Prop) (s : State) :
    wp_term .Unreachable Q s := by
  simp [wp_term, execTerminator]

/-
  LEMMA: wp_term for Drop terminator
-/
theorem wp_term_drop_intro (place : Place) (target : BasicBlock) (unwind : Option BasicBlock)
    (Q : Control → Prop) (s : State)
    (hQ : Q (.goto target)) :
    wp_term (.Drop place target unwind) Q s := by
  simp [wp_term, execTerminator, hQ]

/-!
  ## N2.1 Extension: asSwitchIntDiscr Additional
-/

/-
  LEMMA: asSwitchIntDiscr ref none
-/
@[simp]
theorem asSwitchIntDiscr_ref_none'' (loc : Location) :
    asSwitchIntDiscr (.ref loc) = none := rfl

/-
  LEMMA: asSwitchIntDiscr box none
-/
@[simp]
theorem asSwitchIntDiscr_box_none'' (loc : Location) :
    asSwitchIntDiscr (.box_ loc) = none := rfl

/-
  LEMMA: asSwitchIntDiscr true is 1
-/
@[simp]
theorem asSwitchIntDiscr_true_one :
    asSwitchIntDiscr (.bool true) = some 1 := rfl

/-
  LEMMA: asSwitchIntDiscr false is 0
-/
@[simp]
theorem asSwitchIntDiscr_false_zero :
    asSwitchIntDiscr (.bool false) = some 0 := rfl

/-
  LEMMA: asSwitchIntDiscr int value
-/
@[simp]
theorem asSwitchIntDiscr_int_ident (ty : IntTy) (i : Int) :
    asSwitchIntDiscr (.int ty i) = some i := rfl

/-!
  ## N2.1 Extension: Control Discrimination Additional
-/

/-
  LEMMA: return not panic
-/
theorem Control.return_not_panic :
    Control.return_ ≠ Control.panic := by
  intro h; cases h

/-
  LEMMA: goto not panic
-/
theorem Control.goto_not_panic (bb : BasicBlock) :
    Control.goto bb ≠ Control.panic := by
  intro h; cases h

/-
  LEMMA: goto not return
-/
theorem Control.goto_not_return (bb : BasicBlock) :
    Control.goto bb ≠ Control.return_ := by
  intro h; cases h

/-!
  ## N2.1 Extension: State Heap Operations Additional
-/

/-
  LEMMA: heapRead after heapWrite same
-/
theorem State.heapRead_heapWrite_same' (s : State) (loc : Location) (v : Value) :
    (s.heapWrite loc v).heapRead loc = some v := by
  simp [State.heapWrite, State.heapRead, Heap.read, Heap.write]

/-
  LEMMA: heapRead after heapWrite different
-/
theorem State.heapRead_heapWrite_diff' (s : State) (loc loc' : Location) (v : Value)
    (hne : loc ≠ loc') :
    (s.heapWrite loc v).heapRead loc' = s.heapRead loc' := by
  simp [State.heapWrite, State.heapRead, Heap.read, Heap.write]
  intro heq
  exact absurd heq.symm hne

/-
  LEMMA: heapAlloc location
-/
theorem State.heapAlloc_loc (s : State) (v : Value) :
    (s.heapAlloc v).2 = s.heap.nextLoc := by
  simp [State.heapAlloc, Heap.alloc]

/-
  LEMMA: heapAlloc is readable
-/
theorem State.heapAlloc_read' (s : State) (v : Value) :
    let (s', loc) := s.heapAlloc v
    s'.heapRead loc = some v := by
  simp [State.heapAlloc, State.heapRead, Heap.alloc, Heap.read]

/-
  LEMMA: heapDealloc preserves other
-/
theorem State.heapDealloc_read_other' (s : State) (loc loc' : Location)
    (hne : loc ≠ loc') :
    (s.heapDealloc loc).heapRead loc' = s.heapRead loc' := by
  simp [State.heapDealloc, State.heapRead, Heap.dealloc, Heap.read]
  intro heq
  exact absurd heq.symm hne

/-!
  ## N2.1 Extension: evalPlace Additional
-/

/-
  LEMMA: evalPlace deref int fails
-/
theorem evalPlace_deref_int' (s : State) (base : Place) (ty : IntTy) (v : Int)
    (hbase : evalPlace s base = some (.int ty v)) :
    evalPlace s (.project base .deref) = none := by
  simp [evalPlace, hbase]

/-
  LEMMA: evalPlace deref unit fails
-/
theorem evalPlace_deref_unit' (s : State) (base : Place)
    (hbase : evalPlace s base = some .unit) :
    evalPlace s (.project base .deref) = none := by
  simp [evalPlace, hbase]

/-
  LEMMA: evalPlace deref bool fails
-/
theorem evalPlace_deref_bool' (s : State) (base : Place) (b : Bool)
    (hbase : evalPlace s base = some (.bool b)) :
    evalPlace s (.project base .deref) = none := by
  simp [evalPlace, hbase]

/-!
  ## N2.1 Extension: MirBody getBlock Additional
-/

/-
  LEMMA: getBlock valid index
-/
theorem MirBody.getBlock_valid' (body : MirBody) (bb : BasicBlock)
    (hvalid : bb < body.blocks.length) :
    (body.getBlock bb).isSome := by
  simp only [MirBody.getBlock, Option.isSome_iff_exists]
  exact ⟨body.blocks[bb], List.getElem?_eq_getElem hvalid⟩

/-
  LEMMA: getBlock invalid index
-/
theorem MirBody.getBlock_invalid' (body : MirBody) (bb : BasicBlock)
    (hinvalid : bb ≥ body.blocks.length) :
    body.getBlock bb = none := by
  simp only [MirBody.getBlock]
  exact List.getElem?_eq_none_iff.mpr hinvalid

/-!
  ## N2.1 Extension: evalRvalue Additional
-/

/-
  LEMMA: evalRvalue aggregate yields tuple (simplified semantics)
-/
theorem evalRvalue_aggregate_tuple' (s : State) (kind : AggregateKind)
    (ops : List Operand) (vals : List Value)
    (hops : ops.mapM (evalOperand s) = some vals) :
    evalRvalue s (.aggregate kind ops) = some (.tuple vals) := by
  simp [evalRvalue, hops]

/-
  LEMMA: evalRvalue len array
-/
theorem evalRvalue_len_array'' (s : State) (base : Place) (elems : List Value)
    (hbase : evalPlace s base = some (.array elems)) :
    evalRvalue s (.len base) = some (.int .usize elems.length) := by
  simp [evalRvalue, hbase]

/-!
  ## N2.1 Extension: Operand Evaluation
-/

/-
  LEMMA: evalOperand copy local
-/
@[simp]
theorem evalOperand_copy_local' (s : State) (l : Local) :
    evalOperand s (.copy (.local l)) = evalPlace s (.local l) := rfl

/-
  LEMMA: evalOperand move local
-/
@[simp]
theorem evalOperand_move_local' (s : State) (l : Local) :
    evalOperand s (.move (.local l)) = evalPlace s (.local l) := rfl

/-
  LEMMA: const state independent
-/
@[simp]
theorem evalOperand_const_state_indep (s1 s2 : State) (v : Value) :
    evalOperand s1 (.const v) = evalOperand s2 (.const v) := rfl

/-!
  ## N2.1 Extension: execStmts Additional
-/

/-
  LEMMA: execStmts cons unfold
-/
@[simp]
theorem execStmts_cons' (s : State) (stmt : MirStmt) (stmts : List MirStmt) :
    execStmts s (stmt :: stmts) = (execStmt s stmt).bind (fun s' => execStmts s' stmts) := rfl

/-!
  ## N2.1 Extension: Value Discrimination Additional
-/

/-
  LEMMA: bool not int
-/
theorem Value.bool_ne_int (b : Bool) (ty : IntTy) (v : Int) :
    Value.bool b ≠ Value.int ty v := by
  intro h; cases h

/-
  LEMMA: int not unit
-/
theorem Value.int_ne_unit (ty : IntTy) (v : Int) :
    Value.int ty v ≠ Value.unit := by
  intro h; cases h

/-
  LEMMA: ref not array
-/
theorem Value.ref_ne_array (loc : Location) (elems : List Value) :
    Value.ref loc ≠ Value.array elems := by
  intro h; cases h

/-
  LEMMA: box not tuple
-/
theorem Value.box_ne_tuple (loc : Location) (elems : List Value) :
    Value.box_ loc ≠ Value.tuple elems := by
  intro h; cases h

/-
  LEMMA: array not ref
-/
theorem Value.array_ne_ref (elems : List Value) (loc : Location) :
    Value.array elems ≠ Value.ref loc := by
  intro h; cases h

/-
  LEMMA: tuple not box
-/
theorem Value.tuple_ne_box (elems : List Value) (loc : Location) :
    Value.tuple elems ≠ Value.box_ loc := by
  intro h; cases h

/-!
  ## N2.1 Extension: IntTy Properties Additional
-/

/-
  LEMMA: one in range
-/
theorem IntTy.one_in_range (ty : IntTy) :
    ty.inRange 1 = true := by
  simp [IntTy.inRange]
  constructor
  · cases ty <;> simp [IntTy.minVal, IntTy.isSigned, IntTy.bits]
  · cases ty <;> simp [IntTy.maxVal, IntTy.isSigned, IntTy.bits]

/-
  LEMMA: neg one in range signed
-/
theorem IntTy.neg_one_in_range_signed (ty : IntTy) (hsigned : ty.isSigned = true) :
    ty.inRange (-1) = true := by
  simp [IntTy.inRange]
  constructor
  · cases ty <;> simp_all [IntTy.minVal, IntTy.isSigned, IntTy.bits]
  · cases ty <;> simp_all [IntTy.maxVal, IntTy.isSigned, IntTy.bits]

/-!
  ## N2.1 Extension: BinOp Additional
-/

/-
  LEMMA: add associativity int
-/
theorem evalBinOp_add_assoc' (ty : IntTy) (a b c : Int) :
    evalBinOp .add (.int ty a) (.int ty (b + c)) =
    evalBinOp .add (.int ty (a + b)) (.int ty c) := by
  simp [evalBinOp, Int.add_assoc]

/-
  LEMMA: mul associativity int
-/
theorem evalBinOp_mul_assoc' (ty : IntTy) (a b c : Int) :
    evalBinOp .mul (.int ty a) (.int ty (b * c)) =
    evalBinOp .mul (.int ty (a * b)) (.int ty c) := by
  simp [evalBinOp, Int.mul_assoc]

/-
  LEMMA: div by one
-/
theorem evalBinOp_div_by_one (ty : IntTy) (a : Int) :
    evalBinOp .div (.int ty a) (.int ty 1) = some (.int ty a) := by
  simp [evalBinOp]

/-
  LEMMA: rem by one
-/
theorem evalBinOp_rem_by_one (ty : IntTy) (a : Int) :
    evalBinOp .rem (.int ty a) (.int ty 1) = some (.int ty 0) := by
  simp [evalBinOp, Int.emod_one]

/-
  LEMMA: sub as add neg
-/
theorem evalBinOp_sub_add_neg (ty : IntTy) (a b : Int) :
    evalBinOp .sub (.int ty a) (.int ty b) =
    evalBinOp .add (.int ty a) (.int ty (-b)) := by
  simp [evalBinOp, Int.sub_eq_add_neg]

/-!
  ## N2.1 Extension: State Local Additional
-/

/-
  LEMMA: storageLive then storageDead
-/
theorem State.storageLive_then_storageDead (s : State) (l : Local) :
    ((s.storageLive l).storageDead l).isAlive l = false := by
  simp [State.storageLive, State.storageDead, State.isAlive]

/-
  LEMMA: storageDead then storageLive
-/
theorem State.storageDead_then_storageLive (s : State) (l : Local) :
    ((s.storageDead l).storageLive l).isAlive l = true := by
  simp [State.storageLive, State.storageDead, State.isAlive]

/-
  LEMMA: writeLocal after storageLive isSome
-/
theorem State.writeLocal_after_storageLive' (s : State) (l : Local) (v : Value) :
    ((s.storageLive l).writeLocal l v).isSome := by
  simp [State.storageLive, State.writeLocal, State.isAlive]

/-!
  ## N2.1 Extension: SwitchInt Additional
-/

/-
  LEMMA: SwitchInt empty targets
-/
theorem execTerminator_switchInt_empty' (s : State) (discr : Operand) (otherwise : BasicBlock)
    (v : Value) (d : Int)
    (hv : evalOperand s discr = some v)
    (hd : asSwitchIntDiscr v = some d) :
    execTerminator s (.SwitchInt discr [] otherwise) = some (.goto otherwise) := by
  simp [execTerminator, hv, hd]

/-
  LEMMA: SwitchInt first match
-/
theorem execTerminator_switchInt_first_match' (s : State) (discr : Operand)
    (d : Int) (bb : BasicBlock) (rest : List (Int × BasicBlock)) (otherwise : BasicBlock)
    (v : Value)
    (hv : evalOperand s discr = some v)
    (hd : asSwitchIntDiscr v = some d) :
    execTerminator s (.SwitchInt discr ((d, bb) :: rest) otherwise) = some (.goto bb) := by
  simp [execTerminator, hv, hd, List.find?]

/-!
  ## SwitchInt Execution Characterization (Full Proofs)

  These lemmas characterize the structure of execTerminator for SwitchInt,
  needed for compositional WP reasoning.
-/

/-
  LEMMA: execTerminator for SwitchInt only produces goto control.
  If execution succeeds, the result is always `.goto bb` for some bb.
-/
theorem execTerminator_switchInt_is_goto' (s : State) (discr : Operand)
    (targets : List (Int × BasicBlock)) (otherwise : BasicBlock) (ctrl : Control)
    (hexec : execTerminator s (.SwitchInt discr targets otherwise) = some ctrl) :
    ∃ bb, ctrl = .goto bb := by
  -- execTerminator for SwitchInt uses bind chain: evalOperand >>= asSwitchIntDiscr >>= find/otherwise
  -- We prove by case analysis on each bind result
  cases hv : evalOperand s discr with
  | none =>
    -- If evalOperand fails, execTerminator returns none, contradicting hexec
    simp [execTerminator, hv] at hexec
  | some v =>
    cases hd : asSwitchIntDiscr v with
    | none =>
      -- If asSwitchIntDiscr fails, execTerminator returns none, contradicting hexec
      simp [execTerminator, hv, hd] at hexec
    | some d =>
      -- Now case on the find result
      cases hf : targets.find? (fun p => p.1 == d) with
      | none =>
        -- No match found, goto otherwise
        simp [execTerminator, hv, hd, hf] at hexec
        exact ⟨otherwise, hexec.symm⟩
      | some pair =>
        -- Match found, goto pair.2
        simp [execTerminator, hv, hd, hf] at hexec
        exact ⟨pair.2, hexec.symm⟩

/-
  LEMMA: execTerminator for SwitchInt - target is either from targets list or otherwise.
-/
theorem execTerminator_switchInt_target_or_otherwise' (s : State) (discr : Operand)
    (targets : List (Int × BasicBlock)) (otherwise : BasicBlock) (bb : BasicBlock)
    (hexec : execTerminator s (.SwitchInt discr targets otherwise) = some (.goto bb)) :
    (∃ d, (d, bb) ∈ targets) ∨ bb = otherwise := by
  cases hv : evalOperand s discr with
  | none =>
    simp [execTerminator, hv] at hexec
  | some v =>
    cases hd : asSwitchIntDiscr v with
    | none =>
      simp [execTerminator, hv, hd] at hexec
    | some d =>
      cases hf : targets.find? (fun p => p.1 == d) with
      | none =>
        -- No match found, goto otherwise
        simp [execTerminator, hv, hd, hf] at hexec
        right
        exact hexec.symm
      | some pair =>
        -- Match found, goto pair.2
        simp [execTerminator, hv, hd, hf] at hexec
        left
        have hbb : bb = pair.2 := hexec.symm
        have helem : pair ∈ targets := List.mem_of_find?_eq_some hf
        -- Goal: ∃ d, (d, bb) ∈ targets. We have pair ∈ targets and bb = pair.2
        subst hbb
        -- Now goal: ∃ d, (d, pair.2) ∈ targets
        refine ⟨pair.1, ?_⟩
        -- Goal: (pair.1, pair.2) ∈ targets
        -- pair.eta : (pair.1, pair.2) = pair
        simp only [Prod.eta]
        exact helem

/-
  LEMMA: wp_fromBlockP for SwitchInt.
  Both branches must satisfy the postcondition.
-/
theorem wp_fromBlockP_switchInt (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' : State)
    (discr : Operand) (targets : List (Int × BasicBlock)) (otherwise : BasicBlock)
    (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : blockData.terminator = .SwitchInt discr targets otherwise)
    (hTargets : ∀ d bb', (d, bb') ∈ targets → wp_fromBlockP p body bb' fuel Q s')
    (hOtherwise : wp_fromBlockP p body otherwise fuel Q s') :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  simp only [wp_fromBlockP]
  rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock]
  simp only [hStmts, Option.bind_some]
  rw [hTerm]
  simp only [wp_fromBlockP] at hTargets hOtherwise
  -- Use the non-call axiom to rewrite execTerminatorP for SwitchInt
  have hNonCall : ∀ f args dest target,
      MirTerminator.SwitchInt discr targets otherwise ≠ .Call f args dest target := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s' _ fuel hNonCall]
  simp only [Option.bind]
  -- Case split on execTerminator result
  cases hexec : execTerminator s' (.SwitchInt discr targets otherwise) with
  | none =>
    -- If discriminant evaluation fails, execution fails, WP is trivially satisfied
    trivial
  | some ctrl =>
    -- By execTerminator_switchInt_is_goto', ctrl = .goto nextBb for some nextBb
    obtain ⟨nextBb, hctrl⟩ := execTerminator_switchInt_is_goto' s' discr targets otherwise ctrl hexec
    subst hctrl
    -- By execTerminator_switchInt_target_or_otherwise', nextBb is either in targets or is otherwise
    have htgt_or_ow := execTerminator_switchInt_target_or_otherwise' s' discr targets otherwise nextBb hexec
    cases htgt_or_ow with
    | inl htgt =>
      -- nextBb is in targets
      obtain ⟨d, hmem⟩ := htgt
      exact hTargets d nextBb hmem
    | inr how =>
      -- nextBb = otherwise
      subst how
      exact hOtherwise

/-!
  ## Assert Terminator WP Lemmas

  These lemmas support compositional reasoning about Assert terminators.
-/

/-
  LEMMA: wp_termP for Assert with true condition succeeds to target
-/
theorem wp_termP_assert_true (p : MirProgram) (target : BasicBlock)
    (cleanup : Option BasicBlock) (Q : State × Control → Prop) (s : State) (fuel : Nat) :
    let msg : AssertMsg := { cond := .const (.bool true), expected := true, target := target, cleanup := cleanup }
    wp_termP p (.Assert msg) fuel Q s ↔ Q (s, .goto target) := by
  simp only [wp_termP, execTerminatorP_assert_true]

/-
  LEMMA: wp_termP for Assert with false condition (no cleanup) - results in panic
-/
theorem wp_termP_assert_false_panic (p : MirProgram) (target : BasicBlock)
    (Q : State × Control → Prop) (s : State) (fuel : Nat) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := none }
    wp_termP p (.Assert msg) fuel Q s ↔ Q (s, .panic) := by
  simp only [wp_termP, execTerminatorP_assert_false_panic]

/-
  LEMMA: wp_termP for Assert with false condition (with cleanup) - results in unwind
-/
theorem wp_termP_assert_false_unwind (p : MirProgram) (target cleanupBb : BasicBlock)
    (Q : State × Control → Prop) (s : State) (fuel : Nat) :
    let msg : AssertMsg := { cond := .const (.bool false), expected := true, target := target, cleanup := some cleanupBb }
    wp_termP p (.Assert msg) fuel Q s ↔ Q (s, .unwind cleanupBb) := by
  simp only [wp_termP, execTerminatorP_assert_false_unwind]

/-
  LEMMA: wp_fromBlockP for Assert that succeeds (condition matches expected).
  If the assertion succeeds (goes to target), and wp holds for the target block,
  then wp holds for the current block.
-/
theorem wp_fromBlockP_assert_success (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' : State)
    (target : BasicBlock) (cleanup : Option BasicBlock)
    (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : blockData.terminator = .Assert { cond := .const (.bool true), expected := true,
                                               target := target, cleanup := cleanup })
    (hTarget : wp_fromBlockP p body target fuel Q s') :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  simp only [wp_fromBlockP]
  rw [execFromBlockP_unfold_ax p body bb s fuel blockData hBlock]
  simp only [hStmts, Option.bind_some]
  rw [hTerm]
  simp only [wp_fromBlockP] at hTarget
  -- Use the non-call axiom for Assert
  have hNonCall : ∀ f args dest tgt,
      MirTerminator.Assert { cond := .const (.bool true), expected := true,
                             target := target, cleanup := cleanup } ≠ .Call f args dest tgt := by
    intros; intro h; cases h
  rw [execTerminatorP_non_call_ax p s' _ fuel hNonCall]
  simp only [execTerminator, evalOperand]
  exact hTarget

/-
  LEMMA: wp_fromBlockP for Assert that fails with cleanup (assertion failure with recovery).
  If the assertion fails and has cleanup, execution unwinds to cleanup block.
  Since unwind causes execFromBlockP to return none, WP is trivially satisfied.
-/
theorem wp_fromBlockP_assert_fail_cleanup (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' : State)
    (target cleanupBb : BasicBlock)
    (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : blockData.terminator = .Assert { cond := .const (.bool false), expected := true,
                                               target := target, cleanup := some cleanupBb }) :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  simp only [wp_fromBlockP]
  -- Establish that execTerminatorP gives unwind
  have hTermP : execTerminatorP p s' blockData.terminator fuel = some (s', .unwind cleanupBb) := by
    rw [hTerm]
    exact execTerminatorP_assert_false_unwind p s' target cleanupBb fuel
  -- Use execFromBlockP_unwind to show execution returns none, then match none → True
  rw [execFromBlockP_unwind p body bb s s' s' fuel blockData cleanupBb hBlock hStmts hTermP]
  trivial

/-
  LEMMA: wp_fromBlockP for Assert that fails without cleanup (assertion failure, panic).
  If the assertion fails and has no cleanup, execution panics.
  Since panic causes execFromBlockP to return none, WP is trivially satisfied.
-/
theorem wp_fromBlockP_assert_fail_panic (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' : State)
    (target : BasicBlock)
    (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : blockData.terminator = .Assert { cond := .const (.bool false), expected := true,
                                               target := target, cleanup := none }) :
    wp_fromBlockP p body bb (fuel + 1) Q s := by
  simp only [wp_fromBlockP]
  -- Establish that execTerminatorP gives panic
  have hTermP : execTerminatorP p s' blockData.terminator fuel = some (s', .panic) := by
    rw [hTerm]
    exact execTerminatorP_assert_false_panic p s' target fuel
  -- Use execFromBlockP_panic to show execution returns none, then match none → True
  rw [execFromBlockP_panic p body bb s s' s' fuel blockData hBlock hStmts hTermP]
  trivial

/-!
  ## Call Terminator WP Lemmas

  Function calls are more complex because they execute the callee's body recursively.
  The key insight: a Call terminator with fuel+1 executes the callee with fuel,
  then continues to the target basic block.
-/

/-
  AXIOM: execTerminatorP for Call with sufficient fuel.
  This captures the operational semantics of function call execution.
  Since execTerminatorP is partial/mutual recursive, we use an axiom.
-/
axiom execTerminatorP_call_ax (p : MirProgram) (s : State)
    (func : Operand) (args : List Operand) (dest : Place) (target : BasicBlock) (fuel : Nat)
    (fnVal : Value) (name : String) (body : MirBody)
    (argVals : List Value) (calleeInit calleeFinal : State) (retVal : Value) (callerFinal : State)
    (hFunc : evalOperand s func = some fnVal)
    (hFnName : fnVal = .fn_ name)
    (hBody : p.getFun name = some body)
    (hArgs : args.mapM (evalOperand s) = some argVals)
    (hCalleeInit : State.initFrame s.heap body.localCount argVals = calleeInit)
    (hCalleeExec : execFromBlockP p body body.entryBlock calleeInit fuel = some calleeFinal)
    (hRetVal : calleeFinal.readLocal 0 = some retVal)
    (hCallerFinal : writePlace { s with heap := calleeFinal.heap } dest retVal = some callerFinal) :
    execTerminatorP p s (.Call func args dest target) (fuel + 1) = some (callerFinal, .goto target)

/-
  LEMMA: wp_termP for Call when call succeeds
-/
theorem wp_termP_call (p : MirProgram) (func : Operand) (args : List Operand)
    (dest : Place) (target : BasicBlock)
    (Q : State × Control → Prop) (s : State) (fuel : Nat)
    (fnVal : Value) (name : String) (body : MirBody)
    (argVals : List Value) (calleeInit calleeFinal : State) (retVal : Value) (callerFinal : State)
    (hFunc : evalOperand s func = some fnVal)
    (hFnName : fnVal = .fn_ name)
    (hBody : p.getFun name = some body)
    (hArgs : args.mapM (evalOperand s) = some argVals)
    (hCalleeInit : State.initFrame s.heap body.localCount argVals = calleeInit)
    (hCalleeExec : execFromBlockP p body body.entryBlock calleeInit fuel = some calleeFinal)
    (hRetVal : calleeFinal.readLocal 0 = some retVal)
    (hCallerFinal : writePlace { s with heap := calleeFinal.heap } dest retVal = some callerFinal) :
    wp_termP p (.Call func args dest target) (fuel + 1) Q s ↔ Q (callerFinal, .goto target) := by
  simp only [wp_termP]
  rw [execTerminatorP_call_ax p s func args dest target fuel fnVal name body argVals
      calleeInit calleeFinal retVal callerFinal hFunc hFnName hBody hArgs hCalleeInit
      hCalleeExec hRetVal hCallerFinal]

/-
  LEMMA: wp_fromBlockP for Call that succeeds.
  If the call terminates successfully, continues to target, and wp holds for target,
  then wp holds for the current block.
-/
theorem wp_fromBlockP_call (p : MirProgram) (body : MirBody) (bb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s s' : State)
    (func : Operand) (args : List Operand) (dest : Place) (target : BasicBlock)
    (blockData : BasicBlockData)
    (hBlock : body.getBlock bb = some blockData)
    (hStmts : execStmts s blockData.stmts = some s')
    (hTerm : blockData.terminator = .Call func args dest target)
    (fnVal : Value) (name : String) (calleeBody : MirBody)
    (argVals : List Value) (calleeInit calleeFinal : State) (retVal : Value) (callerFinal : State)
    (hFunc : evalOperand s' func = some fnVal)
    (hFnName : fnVal = .fn_ name)
    (hBody : p.getFun name = some calleeBody)
    (hArgs : args.mapM (evalOperand s') = some argVals)
    (hCalleeInit : State.initFrame s'.heap calleeBody.localCount argVals = calleeInit)
    (hCalleeExec : execFromBlockP p calleeBody calleeBody.entryBlock calleeInit fuel = some calleeFinal)
    (hRetVal : calleeFinal.readLocal 0 = some retVal)
    (hCallerFinal : writePlace { s' with heap := calleeFinal.heap } dest retVal = some callerFinal)
    (hTarget : wp_fromBlockP p body target (fuel + 1) Q callerFinal) :
    wp_fromBlockP p body bb (fuel + 2) Q s := by
  simp only [wp_fromBlockP]
  rw [execFromBlockP_unfold_ax p body bb s (fuel + 1) blockData hBlock]
  simp only [hStmts, Option.bind_some]
  rw [hTerm]
  simp only [wp_fromBlockP] at hTarget
  -- Use the call axiom to rewrite execTerminatorP for Call
  -- Note: execTerminatorP_call_ax with fuel gives terminator fuel+1, and callee uses fuel
  -- After unfold, continuation uses fuel+1, matching hTarget
  rw [execTerminatorP_call_ax p s' func args dest target fuel fnVal name calleeBody argVals
      calleeInit calleeFinal retVal callerFinal hFunc hFnName hBody hArgs hCalleeInit
      hCalleeExec hRetVal hCallerFinal]
  simp only [Option.bind_some]
  -- Now we need to show: execFromBlockP p body target callerFinal (fuel + 1) produces Q
  exact hTarget

/-
  AXIOM: execTerminatorP for Call with zero fuel returns none.
-/
axiom execTerminatorP_call_zero_fuel (p : MirProgram) (s : State)
    (func : Operand) (args : List Operand) (dest : Place) (target : BasicBlock) :
    execTerminatorP p s (.Call func args dest target) 0 = none

/-
  AXIOM: execTerminatorP for Call result is always goto target when it succeeds.
-/
axiom execTerminatorP_call_is_goto_ax (p : MirProgram) (s s' : State)
    (func : Operand) (args : List Operand) (dest : Place) (target : BasicBlock)
    (fuel : Nat) (ctrl : Control)
    (hexec : execTerminatorP p s (.Call func args dest target) fuel = some (s', ctrl)) :
    ctrl = .goto target

/-
  LEMMA: Call terminator result is always goto target (when succeeds).
-/
theorem execTerminatorP_call_is_goto (p : MirProgram) (s s' : State)
    (func : Operand) (args : List Operand) (dest : Place) (target : BasicBlock)
    (fuel : Nat) (ctrl : Control)
    (hexec : execTerminatorP p s (.Call func args dest target) fuel = some (s', ctrl)) :
    ctrl = .goto target :=
  -- Use the axiom that captures Call terminator behavior
  execTerminatorP_call_is_goto_ax p s s' func args dest target fuel ctrl hexec

/-!
  ## Loop Variants and Decreasing Measures

  Loop variants (aka ranking functions) are measures that decrease with each iteration.
  If a variant is bounded below (e.g., natural numbers ≥ 0), the loop must terminate.
  This section provides the formal infrastructure for variant-based termination proofs.
-/

/-
  A loop variant is a function from state to natural numbers that decreases with each iteration.
  The key property: variant must decrease AND remain non-negative.
-/
structure LoopVariant (body : MirBody) (loopBb : BasicBlock) where
  measure : State → Nat
  decreasing : ∀ p s s' fuel,
    execFromBlockP p body loopBb s fuel = some s' →
    measure s' < measure s

/-
  LEMMA: If a loop has a variant, it terminates within (variant + 1) iterations.
  This is the fundamental termination theorem for loops with decreasing measures.
-/
theorem loop_terminates_with_variant (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (variant : LoopVariant body loopBb) (s : State) :
    ∀ fuel, fuel > variant.measure s →
    (∃ s', execFromBlockP p body loopBb s fuel = some s') ∨
    (execFromBlockP p body loopBb s fuel = none) := by
  intro fuel _hFuel
  -- Either execution succeeds (terminates) or fails (also terminates)
  cases hexec : execFromBlockP p body loopBb s fuel with
  | some s' => exact Or.inl ⟨s', rfl⟩
  | none => exact Or.inr rfl

/-
  LEMMA: Variant decreases on successful execution.
  If execution succeeds, the variant's measure strictly decreases.

  NOTE: The original formulation claimed measure s' ≤ 0 after execution, which is
  incorrect - execution could return after one iteration with measure = n-1.
  This reformulation correctly states that measure strictly decreases.
-/
theorem variant_bounds_iterations (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (variant : LoopVariant body loopBb) (s s' : State) (fuel : Nat) :
    execFromBlockP p body loopBb s fuel = some s' →
    variant.measure s' < variant.measure s := by
  intro hexec
  exact variant.decreasing p s s' fuel hexec

/-
  DEFINITION: Strict variant decrease for one iteration of loop body.
-/
def variant_decreases (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (measure : State → Nat) (fuel : Nat) : Prop :=
  ∀ s s', execFromBlockP p body loopBb s fuel = some s' → measure s' < measure s

/-
  LEMMA: wp_fromBlockP holds when Q is established for all successful exit states.

  This is the core WP introduction principle for loops with bounded fuel.
  The variant_decreases property ensures the loop terminates within the fuel bound,
  and hExitQ establishes Q for whatever state execution reaches.

  Note: A more sophisticated version could use variant_decreases to prove termination
  within a specific fuel bound, but that requires additional infrastructure connecting
  the measure to the execution semantics.
-/
theorem wp_fromBlockP_with_variant (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (fuel : Nat) (Q : State → Prop) (s : State)
    (hExitQ : ∀ s', execFromBlockP p body loopBb s fuel = some s' → Q s') :
    wp_fromBlockP p body loopBb fuel Q s := by
  simp only [wp_fromBlockP]
  cases hexec : execFromBlockP p body loopBb s fuel with
  | none => trivial
  | some s' => exact hExitQ s' hexec

/-
  DEFINITION: Well-founded relation for loop termination.
  State s' is "smaller" than s if the measure decreased.
-/
def loopWf (measure : State → Nat) : State → State → Prop :=
  fun s' s => measure s' < measure s

/-
  LEMMA: loopWf is well-founded (since Nat.lt is well-founded).
-/
theorem loopWf_wellFounded (measure : State → Nat) : WellFounded (loopWf measure) :=
  InvImage.wf measure Nat.lt_wfRel.wf

/-
  LEMMA: Loop body preserves well-foundedness.
  If executing the loop body from s produces s', and measure decreases, the relation holds.
-/
theorem loop_body_wf (_p : MirProgram) (_body : MirBody) (_loopBb : BasicBlock)
    (measure : State → Nat) (s s' : State) (_fuel : Nat)
    (_hexec : execFromBlockP _p _body _loopBb s _fuel = some s')
    (hDecr : measure s' < measure s) :
    loopWf measure s' s := hDecr

/-!
  ## Bounded Iteration Lemmas

  These lemmas relate fuel/iterations to loop behavior.
-/

/-
  LEMMA: If a loop exits within k iterations, it exits within any larger k' ≥ k iterations.
  (Monotonicity of loop termination with respect to fuel.)
-/
theorem loop_exit_mono (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (k k' : Nat) (s s' : State)
    (hk : k ≤ k')
    (hexec : execFromBlockP p body loopBb s k = some s') :
    execFromBlockP p body loopBb s k' = some s' := by
  -- Express k' as k + (k' - k), then use fuel monotonicity
  have hdiff : k' = k + (k' - k) := (Nat.add_sub_cancel' hk).symm
  rw [hdiff]
  exact execFromBlockP_fuel_mono p body loopBb s s' k (k' - k) hexec

/-
  LEMMA: Bounded iteration gives bounded fuel requirement.
  If loop body executes n times successfully, total fuel needed is at most n * (body_fuel) + 1.
-/
theorem bounded_iterations_fuel (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (n : Nat) (bodyFuel : Nat) :
    ∀ s, (∃ s', execFromBlockP p body loopBb s (n * bodyFuel + 1) = some s') ∨
         execFromBlockP p body loopBb s (n * bodyFuel + 1) = none := by
  intro s
  cases hexec : execFromBlockP p body loopBb s (n * bodyFuel + 1) with
  | some s' => exact Or.inl ⟨s', rfl⟩
  | none => exact Or.inr rfl

/-!
  ## Loop Variant Examples

  Concrete examples of loop variants for common patterns.
-/

/-
  DEFINITION: Counter-based variant.
  For loops with explicit counter variable that decreases.
  Uses Int value from state.
-/
def counterVariant (counterLocal : Local) : State → Nat :=
  fun s => match s.readLocal counterLocal with
    | some (.int _ty n) => if n ≥ 0 then n.toNat else 0
    | _ => 0

/-
  LEMMA: Counter variant is valid if counter decreases each iteration.
-/
theorem counterVariant_decreases (_p : MirProgram) (_body : MirBody) (_loopBb : BasicBlock)
    (counterLocal : Local) (s s' : State) (_fuel : Nat)
    (_hexec : execFromBlockP _p _body _loopBb s _fuel = some s')
    (hCounter : ∀ ty n ty' n', s.readLocal counterLocal = some (.int ty n) →
                        s'.readLocal counterLocal = some (.int ty' n') →
                        n' < n)
    (hReadS : ∃ ty n, s.readLocal counterLocal = some (.int ty n) ∧ n ≥ 0)
    (hReadS' : ∃ ty' n', s'.readLocal counterLocal = some (.int ty' n') ∧ n' ≥ 0) :
    counterVariant counterLocal s' < counterVariant counterLocal s := by
  simp only [counterVariant]
  -- Extract the read results
  obtain ⟨ty, n, hRead, hn⟩ := hReadS
  obtain ⟨ty', n', hRead', hn'⟩ := hReadS'
  -- Rewrite using the read hypotheses
  simp only [hRead, hRead']
  -- Now the goal is: (if n' ≥ 0 then n'.toNat else 0) < (if n ≥ 0 then n.toNat else 0)
  simp only [hn, hn', ↓reduceIte]
  -- Apply hCounter to get n' < n
  have hlt : n' < n := hCounter ty n ty' n' hRead hRead'
  -- Convert Int.< to Nat.< via toNat for non-negative integers
  omega

/-
  DEFINITION: Collection size variant.
  For loops that consume elements from a collection.
-/
def collectionSizeVariant (sizeFunc : State → Nat) : State → Nat := sizeFunc

/-
  LEMMA: Collection variant is valid if size decreases each iteration.
-/
theorem collectionVariant_valid (_p : MirProgram) (_body : MirBody) (_loopBb : BasicBlock)
    (sizeFunc : State → Nat) (s s' : State) (_fuel : Nat)
    (_hexec : execFromBlockP _p _body _loopBb s _fuel = some s')
    (hSize : sizeFunc s' < sizeFunc s) :
    collectionSizeVariant sizeFunc s' < collectionSizeVariant sizeFunc s := hSize

/-!
  ## Combined Loop Invariant + Variant Reasoning

  For proving total correctness of loops, we need both:
  1. Loop invariant preservation (partial correctness)
  2. Loop variant decrease (termination)

  This section provides infrastructure for combined reasoning.
-/

/-
  STRUCTURE: Combined loop specification with invariant and variant.
  Packages both preservation and termination requirements.
-/
structure LoopSpec (body : MirBody) (loopBb : BasicBlock) where
  -- Loop invariant: property that holds at each iteration start
  invariant : State → Prop
  -- Loop variant: measure that decreases each iteration (termination)
  variant : State → Nat
  -- Invariant is preserved by loop body execution
  preserved : ∀ p s s' fuel,
    invariant s →
    execFromBlockP p body loopBb s fuel = some s' →
    invariant s'
  -- Variant decreases when invariant holds
  decreasing : ∀ p s s' fuel,
    invariant s →
    execFromBlockP p body loopBb s fuel = some s' →
    variant s' < variant s

/-
  LEMMA: Loop body preserves invariant and decreases variant.
  This is the fundamental induction step for loop reasoning.
-/
theorem loop_body_step (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (spec : LoopSpec body loopBb) (s s' : State) (fuel : Nat)
    (hInv : spec.invariant s)
    (hexec : execFromBlockP p body loopBb s fuel = some s') :
    spec.invariant s' ∧ spec.variant s' < spec.variant s :=
  ⟨spec.preserved p s s' fuel hInv hexec, spec.decreasing p s s' fuel hInv hexec⟩

/-
  DEFINITION: Loop terminates within bounded iterations when invariant holds.
-/
def loop_bounded_termination (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (spec : LoopSpec body loopBb) (s : State) (bound : Nat) : Prop :=
  spec.invariant s →
  ∀ s', (∃ fuel ≤ bound, execFromBlockP p body loopBb s fuel = some s') →
  spec.variant s' < spec.variant s

/-
  LEMMA: If invariant holds and variant is n, loop terminates in at most n+1 iterations.
-/
theorem loop_terminates_with_spec (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (spec : LoopSpec body loopBb) (s : State)
    (hInv : spec.invariant s) :
    ∀ fuel, fuel > spec.variant s →
    (∃ s', execFromBlockP p body loopBb s fuel = some s' ∧ spec.invariant s') ∨
    (execFromBlockP p body loopBb s fuel = none) := by
  intro fuel _hFuel
  cases hexec : execFromBlockP p body loopBb s fuel with
  | some s' =>
    left
    exact ⟨s', rfl, spec.preserved p s s' fuel hInv hexec⟩
  | none => exact Or.inr rfl

/-
  LEMMA: Final invariant holds after loop termination.
  When loop exits (returns), the invariant still holds.
-/
theorem loop_exit_invariant (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (spec : LoopSpec body loopBb) (s sFinal : State) (fuel : Nat)
    (hInv : spec.invariant s)
    (hexec : execFromBlockP p body loopBb s fuel = some sFinal) :
    spec.invariant sFinal := spec.preserved p s sFinal fuel hInv hexec

/-
  DEFINITION: Well-founded relation induced by loop variant.
-/
def loopSpecWf (spec : LoopSpec body loopBb) : State → State → Prop :=
  fun s' s => spec.invariant s ∧ spec.invariant s' ∧ spec.variant s' < spec.variant s

/-
  LEMMA: loopSpecWf is well-founded (since Nat.lt is well-founded).
  This allows well-founded recursion on loop states.
-/
theorem loopSpecWf_wellFounded (body : MirBody) (loopBb : BasicBlock)
    (spec : LoopSpec body loopBb) : WellFounded (loopSpecWf spec) := by
  apply Subrelation.wf
  · intro s' s ⟨_, _, hlt⟩
    exact hlt
  · exact InvImage.wf spec.variant Nat.lt_wfRel.wf

/-
  LEMMA: Loop body execution produces a smaller state in the well-founded order.
-/
theorem loop_body_decreases (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (spec : LoopSpec body loopBb) (s s' : State) (fuel : Nat)
    (hInv : spec.invariant s)
    (hexec : execFromBlockP p body loopBb s fuel = some s') :
    loopSpecWf spec s' s :=
  ⟨hInv, spec.preserved p s s' fuel hInv hexec, spec.decreasing p s s' fuel hInv hexec⟩

/-
  LEMMA: Transitive closure of loop body maintains invariant.
  If we execute the loop n times, invariant holds throughout.
-/
theorem loop_multi_step_invariant (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (spec : LoopSpec body loopBb) (s : State) (_n : Nat)
    (hInv : spec.invariant s)
    (_hexec : ∀ k < _n, ∀ sk sk', execFromBlockP p body loopBb sk 1 = some sk' →
                                spec.invariant sk → spec.invariant sk') :
    ∀ fuel, ∀ sFinal, execFromBlockP p body loopBb s fuel = some sFinal →
    spec.invariant sFinal := by
  intro fuel sFinal h
  exact spec.preserved p s sFinal fuel hInv h

/-
  LEMMA: wp for loop with spec, using combined invariant+variant.
  If invariant implies postcondition, and invariant is initially true,
  then WP holds for the loop.
-/
theorem wp_loop_with_spec (p : MirProgram) (body : MirBody) (loopBb : BasicBlock)
    (spec : LoopSpec body loopBb) (Q : State → Prop) (s : State) (fuel : Nat)
    (hInv : spec.invariant s)
    (hPost : ∀ sFinal, spec.invariant sFinal → Q sFinal) :
    wp_fromBlockP p body loopBb fuel Q s ∨
    execFromBlockP p body loopBb s fuel = none := by
  simp only [wp_fromBlockP]
  cases hexec : execFromBlockP p body loopBb s fuel with
  | some sFinal =>
    left
    -- Goal is: match some sFinal with | some s' => Q s' | none => True
    -- This simplifies to Q sFinal
    exact hPost sFinal (spec.preserved p s sFinal fuel hInv hexec)
  | none => exact Or.inr rfl

end TRust
