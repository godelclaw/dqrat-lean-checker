import DqratLean.Checker
import DqratLean.Semantics
import DqratLean.Soundness

namespace DqratLean.Counterexamples

/-- Post-delete formula from `repros/stale_delete_state.*`:
    only the clause `(-1 ∨ 2)` remains active. -/
def staleDeleteFormula : DQBF := {
  maxVar := 2
  internalName := #[(1, 1), (2, 2)]
  externalName := #[0, 1, 2]
  isExistential := #[false, true, true]
  univars := #[]
  exivars := #[1, 2]
  depset := #[#[], #[], #[]]
}

/-- Clause store after deleting the original unit clause `1`. -/
def staleDeleteStore : ClauseStore := {
  clauses := #[
    Clause.dummy,
    { lits := #[mkLit 1 true], deleted := true },
    { lits := #[mkLit 1 false, mkLit 2 true], deleted := false }
  ]
  occurrences := #[#[], #[], #[2], #[1], #[], #[2]]
}

def sigma0 : UnivAssignment := fun _ => false

/-- Witness assignment used in the plain semantic witness:
    both existentials evaluate to `false`. -/
def sk00 : SkolemAssignment := fun v _ =>
  if v = 1 then false else if v = 2 then false else false

/-- The remaining matrix is satisfied by the witness assignment. -/
theorem staleDelete_matrix_true :
    ClauseStore.matrixValue staleDeleteFormula staleDeleteStore sigma0 sk00 = true := by
  native_decide

/-- The candidate added clause `1` is false under the same witness assignment. -/
theorem staleDelete_addedUnit_false :
    DQBF.clauseValue staleDeleteFormula sigma0 sk00 #[mkLit 1 true] = false := by
  native_decide

/-- Plain semantic witness: after deleting `1`, the remaining matrix is true
    while the re-added unit clause `1` is false.
    This is weaker than a formal failure of the full DQRAT criterion. -/
theorem staleDelete_addedUnit_not_forced :
    ∃ σ sk,
      ClauseStore.matrixValue staleDeleteFormula staleDeleteStore σ sk = true ∧
      DQBF.clauseValue staleDeleteFormula σ sk #[mkLit 1 true] = false := by
  exact ⟨sigma0, sk00, staleDelete_matrix_true, staleDelete_addedUnit_false⟩

def honestState : CheckState := {
  formula := staleDeleteFormula
  clauses := staleDeleteStore
  isAssigned := #[false, false]
  value := #[false, false]
  trail := #[#[]]
  propQueue := #[]
  indepKnown := #[]
  indepOf := #[]
}

/-- Handcrafted stale state modeling the unfixed checker after deleting the unit
    clause `1`: assignment arrays still remember `1 = true` at level 0.
    This file proves behavior differences from this state, not reachability of
    this state from the old executable. -/
def staleState : CheckState := {
  formula := staleDeleteFormula
  clauses := staleDeleteStore
  isAssigned := #[true, false]
  value := #[true, false]
  trail := #[#[mkLit 1 true]]
  propQueue := #[]
  indepKnown := #[]
  indepOf := #[]
}

def ratRejected (st : CheckState) : Bool :=
  match checkRatClause 1 [1] st with
  | .ok (some (.Failed _ _ _ _)) _ => true
  | _ => false

def fullRunUnknown (st : CheckState) : Bool :=
  match (checkActions [DQRatAction.RatClause 1 [1]]) st with
  | .ok .Unknown _ => true
  | _ => false

/-- On an honest reset state, the clause is rejected by `checkRatClause`. -/
theorem staleDelete_honest_state_rejects :
    ratRejected honestState = true := by
  native_decide

/-- On the handcrafted stale state, the same clause is not rejected. -/
theorem staleDelete_stale_state_not_rejected :
    ratRejected staleState = false := by
  native_decide

/-- Running the one-step proof from the stale state produces `UNKNOWN`
    rather than an immediate failure. -/
theorem staleDelete_stale_run_unknown :
    fullRunUnknown staleState = true := by
  native_decide

/-- One existential variable `x`. -/
def occurrenceHoleFormula : DQBF := {
  maxVar := 1
  internalName := #[(1, 1)]
  externalName := #[0, 1]
  isExistential := #[false, true]
  univars := #[]
  exivars := #[1]
  depset := #[#[], #[]]
}

/-- A live blocker clause `¬x`, but with a broken occurrence index. -/
def occurrenceHoleStore : ClauseStore := {
  clauses := #[Clause.dummy, { lits := #[mkLit 1 false], deleted := false }]
  occurrences := #[#[], #[]]
}

/-- Minimal action-boundary-shaped checker state over `occurrenceHoleStore`. -/
def occurrenceHoleState : CheckState := {
  formula := occurrenceHoleFormula
  clauses := occurrenceHoleStore
  isAssigned := #[false]
  value := #[false]
  trail := #[#[]]
  propQueue := #[]
  indepKnown := #[false]
  indepOf := #[#[]]
}

def skFalse1 : SkolemAssignment := fun _ _ => false

def sigmaFalse1 : UnivAssignment := fun _ => false

/-- The missing occurrence witness: the live clause `¬x` is not indexed under `¬x`. -/
theorem occurrenceHoleStore_not_liveOccurrencesComplete :
    ¬ ClauseStore.LiveOccurrencesComplete occurrenceHoleStore := by
  intro hocc
  have hget : occurrenceHoleStore.getClause 1 = some { lits := #[mkLit 1 false], deleted := false } := by
    simp [occurrenceHoleStore, ClauseStore.getClause, ClauseStore.getClauseAt, CRef_Undef]
  have hmem : mkLit 1 false ∈ (#[mkLit 1 false] : Array Literal).toList := by
    simp
  have hoccMem := hocc hget hmem
  have hnone : occurrenceHoleStore.getOcc (mkLit 1 false) = #[] := by
    simp [occurrenceHoleStore, ClauseStore.getOcc, mkLit]
  simp [hnone] at hoccMem

def occurrenceHoleAccepted : Bool :=
  match checkDQRATE #[mkLit 1 true] occurrenceHoleState with
  | .ok (true, none) _ => true
  | _ => false

/-- With the broken occurrence index, `checkDQRATE` incorrectly accepts adding `x`. -/
theorem occurrenceHoleAccepted_true :
    occurrenceHoleAccepted = true := by
  native_decide

/-- The old matrix is satisfied by the witness assignment `x := false`. -/
theorem occurrenceHole_matrix_true :
    ClauseStore.matrixValue occurrenceHoleFormula occurrenceHoleStore sigmaFalse1 skFalse1 = true := by
  native_decide

/-- The added clause `x` is false under the same witness assignment. -/
theorem occurrenceHole_addedClause_false :
    DQBF.clauseValue occurrenceHoleFormula sigmaFalse1 skFalse1 #[mkLit 1 true] = false := by
  native_decide

/-- So after adding `x`, the matrix becomes false under that witness. -/
theorem occurrenceHole_addedMatrix_false :
    ClauseStore.matrixValue occurrenceHoleFormula
      (occurrenceHoleStore.addClause #[mkLit 1 true]).1 sigmaFalse1 skFalse1 = false := by
  native_decide

/-- One universal `u`, two existential variables `x, y`, both with empty dependency sets. -/
def dqrateBridgeFormula : DQBF := {
  maxVar := 3
  internalName := #[(1, 1), (2, 2), (3, 3)]
  externalName := #[0, 1, 2, 3]
  isExistential := #[false, false, true, true]
  univars := #[1]
  exivars := #[2, 3]
  depset := #[#[], #[], #[], #[]]
}

/-- Clauses:
    D1 = (¬x ∨ ¬u)
    D2 = (¬x ∨ ¬y ∨ ¬u)
    D3 = (¬x ∨ y ∨ u) -/
def dqrateBridgeStore : ClauseStore := {
  clauses := #[
    Clause.dummy,
    { lits := #[mkLit 2 false, mkLit 1 false], deleted := false },
    { lits := #[mkLit 2 false, mkLit 3 false, mkLit 1 false], deleted := false },
    { lits := #[mkLit 2 false, mkLit 3 true, mkLit 1 true], deleted := false }
  ]
  occurrences := #[
    #[],
    #[],
    #[1, 2],
    #[3],
    #[1, 2, 3],
    #[],
    #[2],
    #[3]
  ]
}

/-- Minimal action-boundary state over `dqrateBridgeStore`. -/
def dqrateBridgeState : CheckState := {
  formula := dqrateBridgeFormula
  clauses := dqrateBridgeStore
  isAssigned := #[false, false, false]
  value := #[false, false, false]
  trail := #[#[]]
  propQueue := #[]
  indepKnown := #[false]
  indepOf := #[#[]]
}

/-- Candidate clause `C = (y)`. -/
def dqrateBridgeClause : Array Literal := #[mkLit 3 true]

def dqrateBridgeAccepted : Bool :=
  match checkDQRATE dqrateBridgeClause dqrateBridgeState with
  | .ok (true, none) _ => true
  | _ => false

/-- The executable DQRATE path accepts adding `y`. -/
theorem dqrateBridgeAccepted_true :
    dqrateBridgeAccepted = true := by
  native_decide

/-- Witness universal assignment: `u = false`. -/
def dqrateBridgeSigma : UnivAssignment := fun _ => false

/-- Witness Skolem assignment: constants `x = true`, `y = true`. -/
def dqrateBridgeSk : SkolemAssignment :=
  fun v _ => if v = 2 then true else if v = 3 then true else false

/-- The original matrix is true under the witness assignment. -/
theorem dqrateBridgeMatrixTrue :
    ClauseStore.matrixValue dqrateBridgeFormula dqrateBridgeStore
      dqrateBridgeSigma dqrateBridgeSk = true := by
  native_decide

/-- The blocker resolvent for `D2` and pivot `y` is just `(¬x)`. -/
theorem dqrateBridgeResolvent_eq :
    dqrateResolvent dqrateBridgeFormula dqrateBridgeClause
      #[mkLit 2 false, mkLit 3 false, mkLit 1 false] (mkLit 3 true) =
        #[mkLit 2 false] := by
  native_decide

/-- The blocker resolvent `(¬x)` is false under the same witness assignment. -/
theorem dqrateBridgeResolventFalse :
    DQBF.clauseValue dqrateBridgeFormula dqrateBridgeSigma dqrateBridgeSk
      #[mkLit 2 false] = false := by
  native_decide

/-- So this accepted DQRATE step does not satisfy the legacy per-blocker
    `DQRATE_exec_Condition` bridge. -/
theorem dqrateBridge_not_exec_condition :
    ¬ DQRATE_exec_Condition dqrateBridgeFormula dqrateBridgeStore
        dqrateBridgeClause (mkLit 3 true) := by
  intro hcond
  have hraw :
      dqrateBridgeStore.getClauseRaw 2 =
        some { lits := #[mkLit 2 false, mkLit 3 false, mkLit 1 false], deleted := false } := by
    simp [dqrateBridgeStore, ClauseStore.getClauseRaw, ClauseStore.getClauseAt, CRef_Undef]
  have hblocker : (mkLit 3 true).negate ∈
      (#[mkLit 2 false, mkLit 3 false, mkLit 1 false] : Array Literal).toList := by
    native_decide
  have hsem :=
    hcond.2 2 { lits := #[mkLit 2 false, mkLit 3 false, mkLit 1 false], deleted := false }
      hraw rfl hblocker
  have hres_true := hsem dqrateBridgeSk dqrateBridgeSigma dqrateBridgeMatrixTrue
  rw [dqrateBridgeResolvent_eq] at hres_true
  simpa [dqrateBridgeResolventFalse] using hres_true

end DqratLean.Counterexamples
