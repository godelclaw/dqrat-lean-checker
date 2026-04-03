import DqratLean.Checker
import DqratLean.Semantics

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

/-- Witness assignment used in the semantic counterexample:
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

/-- Semantic counterexample: after deleting `1`, the step re-adding `1`
    is not forced by the remaining matrix. -/
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

/-- State left behind by the unfixed checker after deleting the unit clause `1`:
    assignment arrays still remember `1 = true` at level 0. -/
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

/-- On an honest reset state, the bad clause is rejected. -/
theorem staleDelete_honest_state_rejects :
    ratRejected honestState = true := by
  native_decide

/-- On the stale state left by the unfixed checker, the same bad clause is not rejected. -/
theorem staleDelete_stale_state_not_rejected :
    ratRejected staleState = false := by
  native_decide

/-- Running the one-step proof from the stale state produces `UNKNOWN`
    rather than an immediate failure. -/
theorem staleDelete_stale_run_unknown :
    fullRunUnknown staleState = true := by
  native_decide

end DqratLean.Counterexamples
