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
  simp [dqrateBridgeResolventFalse] at hres_true

/-- One universal `u`, two existentials `y, x`, both depending on `u`. -/
def deleteBridgeFormula : DQBF := {
  maxVar := 3
  internalName := #[(1, 1), (2, 2), (3, 3)]
  externalName := #[0, 1, 2, 3]
  isExistential := #[false, false, true, true]
  univars := #[1]
  exivars := #[2, 3]
  depset := #[#[], #[], #[1], #[1]]
}

/-- Clauses:
    C1 = (u ∨ x)
    C2 = (¬y ∨ ¬x) -/
def deleteBridgeStore : ClauseStore := {
  clauses := #[
    Clause.dummy,
    { lits := #[mkLit 1 true, mkLit 3 true], deleted := false },
    { lits := #[mkLit 2 false, mkLit 3 false], deleted := false }
  ]
  occurrences := #[
    #[],
    #[],
    #[],
    #[1],
    #[2],
    #[],
    #[2],
    #[1]
  ]
}

/-- Minimal action-boundary state over `deleteBridgeStore`. -/
def deleteBridgeState : CheckState := {
  formula := deleteBridgeFormula
  clauses := deleteBridgeStore
  isAssigned := #[false, false, false]
  value := #[false, false, false]
  trail := #[#[]]
  propQueue := #[]
  indepKnown := #[false, false, false]
  indepOf := #[#[], #[], #[]]
}

def deleteBridgeNotDependsOnAccepted : Bool :=
  match notDependsOn 3 1 deleteBridgeState with
  | .ok true _ => true
  | _ => false

/-- The executable `notDependsOn` check accepts deleting `u` from `x`. -/
theorem deleteBridgeNotDependsOnAccepted_true :
    deleteBridgeNotDependsOnAccepted = true := by
  native_decide

def deleteBridgeNotDependsOnState : CheckState :=
  match notDependsOn 3 1 deleteBridgeState with
  | .ok _ s => s
  | .error _ s => s

/-- The recomputed independence set for `u` contains both existentials.
    This is why the right semantic target is a set-level bridge, not an
    `x`-only witness patch. -/
theorem deleteBridgeNotDependsOnState_indepOf :
    deleteBridgeNotDependsOnState.indepOf.getD 0 #[] = #[2, 3] := by
  native_decide

def deleteBridgeOtherExistentialAccepted : Bool :=
  match notDependsOn 2 1 deleteBridgeState with
  | .ok true _ => true
  | _ => false

/-- On `deleteBridge`, the same recomputation also accepts deleting `u` from `y`.
    The checker-side relation is naturally a set of independent existentials. -/
theorem deleteBridgeOtherExistentialAlsoAccepted :
    deleteBridgeOtherExistentialAccepted = true := by
  native_decide

/-- Witness Skolem assignment before deletion:
    `y = u` and `x = ¬u`. -/
def deleteBridgeOldSk : SkolemAssignment :=
  fun v args =>
    if v = 2 then args.getD 0 false
    else if v = 3 then !(args.getD 0 false)
    else false

def deleteBridgeSigmaFalse : UnivAssignment := fun _ => false

def deleteBridgeSigmaTrue : UnivAssignment := fun v =>
  if v = 1 then true else false

theorem deleteBridgeOldSk_sigmaFalse :
    ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
      deleteBridgeSigmaFalse deleteBridgeOldSk = true := by
  native_decide

theorem deleteBridgeOldSk_sigmaTrue :
    ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
      deleteBridgeSigmaTrue deleteBridgeOldSk = true := by
  native_decide

/-- The chosen old witness satisfies the original matrix on both Boolean
    assignments to the unique universal `u`. -/
theorem deleteBridgeOldSk_relevantCases :
    ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
        deleteBridgeSigmaFalse deleteBridgeOldSk = true ∧
      ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
        deleteBridgeSigmaTrue deleteBridgeOldSk = true := by
  exact ⟨deleteBridgeOldSk_sigmaFalse, deleteBridgeOldSk_sigmaTrue⟩

/-- A deletion-compatible witness:
    `y = false` and `x = true`. -/
def deleteBridgeGoodSk : SkolemAssignment :=
  fun v _ =>
    if v = 2 then false
    else if v = 3 then true
    else false

theorem deleteBridgeGoodSk_old_sigmaFalse :
    ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
      deleteBridgeSigmaFalse deleteBridgeGoodSk = true := by
  native_decide

theorem deleteBridgeGoodSk_old_sigmaTrue :
    ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
      deleteBridgeSigmaTrue deleteBridgeGoodSk = true := by
  native_decide

theorem deleteBridgeGoodSk_deleted_sigmaFalse :
    ClauseStore.matrixValue (deleteBridgeFormula.forceDelDep 3 1) deleteBridgeStore
      deleteBridgeSigmaFalse deleteBridgeGoodSk = true := by
  native_decide

theorem deleteBridgeGoodSk_deleted_sigmaTrue :
    ClauseStore.matrixValue (deleteBridgeFormula.forceDelDep 3 1) deleteBridgeStore
      deleteBridgeSigmaTrue deleteBridgeGoodSk = true := by
  native_decide

/-- `deleteBridge` is not an unsound deletion witness. It only shows that
    reusing one arbitrary old witness and patching only deleted `x` is too
    strong; a better witness exists and survives the deletion. -/
theorem deleteBridge_needs_better_witness_not_unsound :
    ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
        deleteBridgeSigmaFalse deleteBridgeGoodSk = true ∧
      ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
        deleteBridgeSigmaTrue deleteBridgeGoodSk = true ∧
      ClauseStore.matrixValue (deleteBridgeFormula.forceDelDep 3 1) deleteBridgeStore
        deleteBridgeSigmaFalse deleteBridgeGoodSk = true ∧
      ClauseStore.matrixValue (deleteBridgeFormula.forceDelDep 3 1) deleteBridgeStore
        deleteBridgeSigmaTrue deleteBridgeGoodSk = true := by
  exact ⟨deleteBridgeGoodSk_old_sigmaFalse, deleteBridgeGoodSk_old_sigmaTrue,
    deleteBridgeGoodSk_deleted_sigmaFalse, deleteBridgeGoodSk_deleted_sigmaTrue⟩

/-- Force `x = false` while leaving the old witness for every other variable. -/
def deleteBridgePatchFalse : SkolemAssignment :=
  fun v args => if v = 3 then false else deleteBridgeOldSk v args

/-- Force `x = true` while leaving the old witness for every other variable. -/
def deleteBridgePatchTrue : SkolemAssignment :=
  fun v args => if v = 3 then true else deleteBridgeOldSk v args

/-- After deleting `u` from `x`, forcing `x = false` breaks clause `C1`
    on the reduced pattern `[]` witnessed by `u = false`. -/
theorem deleteBridgePatchFalse_breaksClause :
    DQBF.clauseValue (deleteBridgeFormula.forceDelDep 3 1)
      deleteBridgeSigmaFalse deleteBridgePatchFalse
      #[mkLit 1 true, mkLit 3 true] = false := by
  native_decide

/-- After deleting `u` from `x`, forcing `x = true` breaks clause `C2`
    on the same reduced pattern `[]` witnessed by `u = true`. -/
theorem deleteBridgePatchTrue_breaksClause :
    DQBF.clauseValue (deleteBridgeFormula.forceDelDep 3 1)
      deleteBridgeSigmaTrue deleteBridgePatchTrue
      #[mkLit 2 false, mkLit 3 false] = false := by
  native_decide

/-- The two witnesses above show that the fixed-witness, `x`-only patch route is
    too strong: `notDependsOn` can succeed even though, for a particular old
    satisfying witness, both Boolean choices for deleted `x` fail on the unique
    reduced dependency pattern. -/
theorem deleteBridge_fixedWitnessPatchRouteTooStrong :
    deleteBridgeNotDependsOnAccepted = true ∧
      ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
        deleteBridgeSigmaFalse deleteBridgeOldSk = true ∧
      ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
        deleteBridgeSigmaTrue deleteBridgeOldSk = true ∧
      DQBF.clauseValue (deleteBridgeFormula.forceDelDep 3 1)
        deleteBridgeSigmaFalse deleteBridgePatchFalse
        #[mkLit 1 true, mkLit 3 true] = false ∧
      DQBF.clauseValue (deleteBridgeFormula.forceDelDep 3 1)
        deleteBridgeSigmaTrue deleteBridgePatchTrue
        #[mkLit 2 false, mkLit 3 false] = false := by
  exact ⟨deleteBridgeNotDependsOnAccepted_true,
    deleteBridgeOldSk_sigmaFalse,
    deleteBridgeOldSk_sigmaTrue,
    deleteBridgePatchFalse_breaksClause,
    deleteBridgePatchTrue_breaksClause⟩

end DqratLean.Counterexamples
