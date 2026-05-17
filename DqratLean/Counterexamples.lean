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
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue, DQBF.isVarExistential,
    staleDeleteFormula, staleDeleteStore, sigma0, sk00, mkLit, Literal.var, Literal.isPos,
    CRef_Undef]
  intro x hx
  have hx_cases : x = 0 ∨ x = 1 := by omega
  rcases hx_cases with rfl | rfl <;> simp

/-- The candidate added clause `1` is false under the same witness assignment. -/
theorem staleDelete_addedUnit_false :
    DQBF.clauseValue staleDeleteFormula sigma0 sk00 #[mkLit 1 true] = false := by
  simp [DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, staleDeleteFormula, sigma0, sk00, mkLit, Literal.var,
    Literal.isPos]

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

def staleAddedStore : ClauseStore := {
  clauses := #[
    Clause.dummy,
    { lits := #[mkLit 1 true], deleted := true },
    { lits := #[mkLit 1 false, mkLit 2 true], deleted := false },
    { lits := #[mkLit 1 true], deleted := false }
  ]
  occurrences := #[#[], #[], #[2], #[1, 3], #[], #[2]]
}

def staleAddedState : CheckState := { staleState with clauses := staleAddedStore }

theorem stale_translateRatLitBasicStep :
    translateRatLitBasicStep #[] 1 staleState = .ok #[mkLit 1 true] staleState := by
  unfold translateRatLitBasicStep
  simp only [get, getThe, MonadState.get, MonadStateOf.get, Bind.bind, EStateM.bind,
    Functor.map, EStateM.map, EStateM.get]
  simp [EStateM.bind, EStateM.map, EStateM.get, EStateM.pure, Pure.pure,
    DQBF.externalVarExists, DQBF.lookupInternal, staleState, staleDeleteFormula, mkLit]

theorem stale_translateRatLitsBasic :
    translateRatLitsBasic [1] staleState = .ok #[mkLit 1 true] staleState := by
  unfold translateRatLitsBasic
  simp [forIn, Bind.bind, EStateM.bind, EStateM.pure, Pure.pure,
    stale_translateRatLitBasicStep]

theorem stale_checkDQRATE :
    checkDQRATE #[mkLit 1 true] staleState = .ok (true, none) staleState := by
  unfold checkDQRATE negateAndPropagate newDecisionLevel backtrackBefore
  have hclear : backtrackBefore.clearLevels 1 #[#[({ x := 3 } : Literal)], #[]] #[true, false] =
      (#[#[({ x := 3 } : Literal)]], #[true, false]) := by
    rw [backtrackBefore.clearLevels.eq_1]
    simp [Literal.var]
    rw [backtrackBefore.clearLevels.eq_1]
    simp
  simp [Bind.bind, EStateM.bind, EStateM.pure, Pure.pure, get, getThe,
    MonadState.get, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, satisfied, staleState,
    staleDeleteFormula, mkLit, Literal.var, Literal.isPos]
  rw [hclear]
  simp

theorem stale_invalidateDepCaches :
    invalidateDepCaches #[mkLit 1 true] staleState = .ok () staleState := by
  rfl

theorem stale_addClauseAfterCache :
    addClauseAfterCache #[mkLit 1 true] staleState = .ok (some 3) staleAddedState := by
  unfold addClauseAfterCache staleAddedState staleAddedStore
  simp [staleState, staleDeleteFormula, staleDeleteStore, ClauseStore.addClause,
    mkLit, Literal.var, Literal.isPos]

theorem stale_addClause :
    addClause #[mkLit 1 true] staleState = .ok (some 3) staleAddedState := by
  unfold addClause
  simp [Bind.bind, EStateM.bind, stale_invalidateDepCaches, stale_addClauseAfterCache]

theorem stale_checkRatClause :
    checkRatClause 1 [1] staleState = .ok none staleAddedState := by
  unfold checkRatClause
  simp [Bind.bind, EStateM.bind, EStateM.pure, Pure.pure, stale_translateRatLitsBasic,
    stale_checkDQRATE, stale_addClause]

theorem stale_ratRejected_false :
    ratRejected staleState = false := by
  simp [ratRejected, stale_checkRatClause]

theorem stale_fullRunUnknown_true :
    fullRunUnknown staleState = true := by
  unfold fullRunUnknown checkActions checkAction
  simp [Bind.bind, EStateM.bind, EStateM.pure, Pure.pure, stale_checkRatClause, checkActions]

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

def occurrenceHoleNegatedState : CheckState := {
  occurrenceHoleState with
  isAssigned := #[true]
  value := #[false]
  trail := #[#[], #[mkLit 1 false]]
  propQueue := #[mkLit 1 false]
}

def occurrenceHolePropagatedState : CheckState := {
  occurrenceHoleNegatedState with
  propQueue := #[]
}

def occurrenceHolePoppedState : CheckState := {
  occurrenceHoleNegatedState with
  propQueue := #[]
}

theorem occurrenceHole_propagateOne_popped :
    propagateOne (mkLit 1 false) occurrenceHolePoppedState =
      .ok none occurrenceHolePoppedState := by
  rfl

theorem occurrenceHole_propagate_negated :
    propagate occurrenceHoleNegatedState = .ok none occurrenceHolePropagatedState := by
  unfold propagate
  rw [propagate.aux.eq_1]
  change (match propagateOne (mkLit 1 false) occurrenceHolePoppedState with
    | EStateM.Result.error e s => EStateM.Result.error e s
    | EStateM.Result.ok (some c) s => EStateM.Result.ok (some c) s
    | EStateM.Result.ok none s => propagate.aux s) =
      EStateM.Result.ok none occurrenceHolePropagatedState
  rw [occurrenceHole_propagateOne_popped]
  simp
  rw [propagate.aux.eq_1]
  rfl

theorem occurrenceHole_negateAndPropagate :
    negateAndPropagate #[mkLit 1 true] (fun _ => true) occurrenceHoleState =
      .ok false occurrenceHolePropagatedState := by
  unfold negateAndPropagate newDecisionLevel
  simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe,
    MonadState.get, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.set, set, MonadStateOf.set,
    satisfied, enqueue, occurrenceHoleState, occurrenceHoleFormula, occurrenceHoleNegatedState,
    occurrenceHolePropagatedState, mkLit, Literal.var, Literal.isPos, Literal.negate]
  have hprop : propagate
      { formula := {
          maxVar := 1
          internalName := #[(1, 1)]
          externalName := #[0, 1]
          isExistential := #[false, true]
          univars := #[]
          exivars := #[1]
          depset := #[#[], #[]]
        }
        clauses := occurrenceHoleStore
        isAssigned := #[true]
        value := #[false]
        trail := #[#[], #[{ x := 2 }]]
        propQueue := #[{ x := 2 }]
        indepKnown := #[false]
        indepOf := #[#[]] } =
      EStateM.Result.ok none
      { formula := {
          maxVar := 1
          internalName := #[(1, 1)]
          externalName := #[0, 1]
          isExistential := #[false, true]
          univars := #[]
          exivars := #[1]
          depset := #[#[], #[]]
        }
        clauses := occurrenceHoleStore
        isAssigned := #[true]
        value := #[false]
        trail := #[#[], #[{ x := 2 }]]
        propQueue := #[]
        indepKnown := #[false]
        indepOf := #[#[]] } := by
    simpa [occurrenceHoleNegatedState, occurrenceHolePropagatedState, occurrenceHoleState,
      occurrenceHoleFormula, mkLit] using occurrenceHole_propagate_negated
  rw [hprop]
  rfl

theorem occurrenceHole_runDQRATEPivotPhase :
    runDQRATEPivotPhase (mkLit 1 true) occurrenceHolePropagatedState =
      .ok (true, none) occurrenceHoleState := by
  unfold runDQRATEPivotPhase backtrackBefore
  have hclear : backtrackBefore.clearLevels 1 #[#[], #[({ x := 2 } : Literal)]] #[true] =
      (#[#[]], #[false]) := by
    rw [backtrackBefore.clearLevels.eq_1]
    simp [Literal.var]
    rw [backtrackBefore.clearLevels.eq_1]
    simp
  simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe,
    MonadState.get, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, occurrenceHolePropagatedState,
    occurrenceHoleNegatedState, occurrenceHoleState, occurrenceHoleFormula, occurrenceHoleStore,
    ClauseStore.getOcc, mkLit, Literal.negate]
  constructor <;> rw [hclear] <;> rfl

theorem occurrenceHole_checkDQRATE :
    checkDQRATE #[mkLit 1 true] occurrenceHoleState = .ok (true, none) occurrenceHoleState := by
  have hneg := occurrenceHole_negateAndPropagate
  unfold checkDQRATE
  simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, hneg]
  simp [get, getThe, MonadState.get, MonadStateOf.get, EStateM.get,
    occurrenceHolePropagatedState, occurrenceHoleNegatedState, occurrenceHoleState,
    occurrenceHoleFormula, mkLit, Literal.var]
  exact occurrenceHole_runDQRATEPivotPhase

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
  simp [occurrenceHoleAccepted, occurrenceHole_checkDQRATE]

/-- The old matrix is satisfied by the witness assignment `x := false`. -/
theorem occurrenceHole_matrix_true :
    ClauseStore.matrixValue occurrenceHoleFormula occurrenceHoleStore sigmaFalse1 skFalse1 = true := by
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, occurrenceHoleFormula, occurrenceHoleStore,
    sigmaFalse1, skFalse1, mkLit, Literal.var, Literal.isPos, CRef_Undef]

/-- The added clause `x` is false under the same witness assignment. -/
theorem occurrenceHole_addedClause_false :
    DQBF.clauseValue occurrenceHoleFormula sigmaFalse1 skFalse1 #[mkLit 1 true] = false := by
  simp [DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, occurrenceHoleFormula, sigmaFalse1, skFalse1,
    mkLit, Literal.var, Literal.isPos]

/-- So after adding `x`, the matrix becomes false under that witness. -/
theorem occurrenceHole_addedMatrix_false :
    ClauseStore.matrixValue occurrenceHoleFormula
      (occurrenceHoleStore.addClause #[mkLit 1 true]).1 sigmaFalse1 skFalse1 = false := by
  unfold ClauseStore.matrixValue
  simp [ClauseStore.addClause, ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, occurrenceHoleFormula, occurrenceHoleStore,
    sigmaFalse1, skFalse1, mkLit, Literal.var, Literal.isPos, CRef_Undef]
  exact ⟨1, by omega, by simp⟩

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

/-- RUP trial state immediately after enqueuing `¬y`. -/
def dqrateBridgeRupQueuedState : CheckState := {
  dqrateBridgeState with
  isAssigned := #[false, false, true]
  value := #[false, false, false]
  trail := #[#[], #[mkLit 3 false]]
  propQueue := #[mkLit 3 false]
}

/-- RUP trial state after propagating `¬y`. -/
def dqrateBridgeRupState : CheckState := {
  dqrateBridgeRupQueuedState with
  propQueue := #[]
}

/-- Outer blocker trial state after enqueuing `x`, before propagation. -/
def dqrateBridgeOuterQueuedState : CheckState := {
  dqrateBridgeState with
  isAssigned := #[false, true, true]
  value := #[false, true, false]
  trail := #[#[], #[mkLit 3 false], #[mkLit 2 true]]
  propQueue := #[mkLit 2 true]
}

/-- Outer blocker trial state after popping `x` from the propagation queue. -/
def dqrateBridgeOuterPoppedState : CheckState := {
  dqrateBridgeOuterQueuedState with
  propQueue := #[]
}

/-- Conflict state in the blocker trial: `x` implies `¬u`, falsifying clause 3. -/
def dqrateBridgeOuterConflictState : CheckState := {
  dqrateBridgeState with
  isAssigned := #[true, true, true]
  value := #[false, true, false]
  trail := #[#[], #[mkLit 3 false], #[mkLit 2 true, mkLit 1 false]]
  propQueue := #[mkLit 1 false]
}

/-- State after the blocker trial backtracks to level 1.  The checker leaves stale
    values behind, but clears the assignment flags. -/
def dqrateBridgeAfterOuterState : CheckState := {
  dqrateBridgeState with
  isAssigned := #[false, false, true]
  value := #[false, true, false]
  trail := #[#[], #[mkLit 3 false]]
  propQueue := #[]
}

/-- Final state after the successful DQRATE pivot phase backtracks to level 0. -/
def dqrateBridgeFinalState : CheckState := {
  dqrateBridgeState with
  isAssigned := #[false, false, false]
  value := #[false, true, false]
  trail := #[#[]]
  propQueue := #[]
}

theorem dqrateBridge_propagateOne_rup :
    propagateOne (mkLit 3 false) dqrateBridgeRupState =
      .ok none dqrateBridgeRupState := by
  unfold propagateOne
  simp [Bind.bind, EStateM.bind, EStateM.pure, Pure.pure, get, getThe,
    MonadState.get, MonadStateOf.get, EStateM.get, dqrateBridgeRupState,
    dqrateBridgeRupQueuedState, dqrateBridgeState, dqrateBridgeFormula, dqrateBridgeStore,
    ClauseStore.getOcc, ClauseStore.getClause, ClauseStore.getClauseAt, mkLit, Literal.var,
    Literal.isPos, Literal.negate, CRef_Undef]
  let P : Prop := ∃ (i : Nat)
      (h : i < ([({ x := 4 } : Literal), ({ x := 7 } : Literal), ({ x := 3 } : Literal)] :
        List Literal).length),
      ((2 ≤ (([({ x := 4 } : Literal), ({ x := 7 } : Literal), ({ x := 3 } : Literal)] :
            List Literal)[i]).x ∧
          (([({ x := 4 } : Literal), ({ x := 7 } : Literal), ({ x := 3 } : Literal)] :
            List Literal)[i]).x / 2 ≤ 3) ∧
        ([false, false, true] : List Bool)[(([({ x := 4 } : Literal), ({ x := 7 } : Literal),
          ({ x := 3 } : Literal)] : List Literal)[i]).x / 2 - 1]?.getD false = true) ∧
      ([false, false, false] : List Bool)[(([({ x := 4 } : Literal), ({ x := 7 } : Literal),
        ({ x := 3 } : Literal)] : List Literal)[i]).x / 2 - 1]?.getD false =
        ((([({ x := 4 } : Literal), ({ x := 7 } : Literal), ({ x := 3 } : Literal)] :
          List Literal)[i]).x % 2 == 1)
  have hnoSat : ¬ P := by
    intro h
    rcases h with ⟨i, hi, hprop⟩
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by
      simp at hi
      omega
    rcases hi_cases with rfl | rfl | rfl <;> simp at hprop
  change (match (((if P then EStateM.pure (none : Option CRef)
        else (EStateM.pure PUnit.unit).bind fun _ => EStateM.pure (none : Option CRef))
      ({ formula := dqrateBridgeFormula
         clauses := dqrateBridgeStore
         isAssigned := #[false, false, true]
         value := #[false, false, false]
         trail := #[#[], #[mkLit 3 false]]
         propQueue := #[]
         indepKnown := #[false]
         indepOf := #[#[]] } : CheckState)) : EStateM.Result String CheckState (Option CRef)) with
    | EStateM.Result.ok a s => EStateM.Result.ok a s
    | EStateM.Result.error e s => EStateM.Result.error e s) =
      EStateM.Result.ok none
      ({ formula := dqrateBridgeFormula
         clauses := dqrateBridgeStore
         isAssigned := #[false, false, true]
         value := #[false, false, false]
         trail := #[#[], #[mkLit 3 false]]
         propQueue := #[]
         indepKnown := #[false]
         indepOf := #[#[]] } : CheckState)
  rw [if_neg hnoSat]
  rfl

theorem dqrateBridge_propagate_rup :
    propagate dqrateBridgeRupQueuedState = .ok none dqrateBridgeRupState := by
  unfold propagate
  rw [propagate.aux.eq_def]
  simp [dqrateBridgeRupQueuedState, dqrateBridgeRupState, dqrateBridgeState, mkLit]
  rw [show (#[({ x := 6 } : Literal)].getD (#[({ x := 6 } : Literal)].size - 1)
      { x := 0 }) = mkLit 3 false by simp [mkLit]]
  have hstate :
      ({ formula := dqrateBridgeFormula
         clauses := dqrateBridgeStore
         isAssigned := #[false, false, true]
         value := #[false, false, false]
         trail := #[#[], #[({ x := 6 } : Literal)]]
         propQueue := #[({ x := 6 } : Literal)].pop
         indepKnown := #[false]
         indepOf := #[#[]] } : CheckState) = dqrateBridgeRupState := by
    simp [dqrateBridgeRupState, dqrateBridgeRupQueuedState, dqrateBridgeState, mkLit]
  rw [hstate]
  rw [dqrateBridge_propagateOne_rup]
  simp
  rw [propagate.aux.eq_def]
  rfl

theorem dqrateBridge_negateAndPropagate_rup :
    negateAndPropagate dqrateBridgeClause (fun _ => true) dqrateBridgeState =
      .ok false dqrateBridgeRupState := by
  unfold negateAndPropagate newDecisionLevel
  simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe,
    MonadState.get, MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.set, set, MonadStateOf.set,
    satisfied, enqueue, dqrateBridgeClause, dqrateBridgeState, dqrateBridgeFormula,
    dqrateBridgeRupQueuedState, dqrateBridgeRupState, mkLit, Literal.var,
    Literal.isPos, Literal.negate]
  have hprop : propagate
      { formula := ({
          maxVar := 3
          internalName := #[(1, 1), (2, 2), (3, 3)]
          externalName := #[0, 1, 2, 3]
          isExistential := #[false, false, true, true]
          univars := #[1]
          exivars := #[2, 3]
          depset := #[#[], #[], #[], #[]]
        } : DQBF)
        clauses := dqrateBridgeStore
        isAssigned := #[false, false, true]
        value := #[false, false, false]
        trail := #[#[], #[({ x := 6 } : Literal)]]
        propQueue := #[({ x := 6 } : Literal)]
        indepKnown := #[false]
        indepOf := #[#[]] } =
      EStateM.Result.ok none
      { formula := ({
          maxVar := 3
          internalName := #[(1, 1), (2, 2), (3, 3)]
          externalName := #[0, 1, 2, 3]
          isExistential := #[false, false, true, true]
          univars := #[1]
          exivars := #[2, 3]
          depset := #[#[], #[], #[], #[]]
        } : DQBF)
        clauses := dqrateBridgeStore
        isAssigned := #[false, false, true]
        value := #[false, false, false]
        trail := #[#[], #[({ x := 6 } : Literal)]]
        propQueue := #[]
        indepKnown := #[false]
        indepOf := #[#[]] } := by
    simpa [dqrateBridgeRupQueuedState, dqrateBridgeRupState, dqrateBridgeState,
      dqrateBridgeFormula, mkLit] using dqrateBridge_propagate_rup
  rw [hprop]
  rfl

theorem dqrateBridge_enqueue_outer_u :
    enqueue (mkLit 1 false) dqrateBridgeOuterPoppedState =
      .ok () dqrateBridgeOuterConflictState := by
  unfold enqueue
  simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, get, getThe,
    MonadState.get, MonadStateOf.get, EStateM.get, EStateM.set, set, MonadStateOf.set,
    dqrateBridgeOuterPoppedState, dqrateBridgeOuterQueuedState, dqrateBridgeOuterConflictState,
    dqrateBridgeState, dqrateBridgeFormula, dqrateBridgeStore, mkLit, Literal.var,
    Literal.isPos]

/-- Witness universal assignment: `u = false`. -/
def dqrateBridgeSigma : UnivAssignment := fun _ => false

/-- Witness Skolem assignment: constants `x = true`, `y = true`. -/
def dqrateBridgeSk : SkolemAssignment :=
  fun v _ => if v = 2 then true else if v = 3 then true else false

/-- The original matrix is true under the witness assignment. -/
theorem dqrateBridgeMatrixTrue :
    ClauseStore.matrixValue dqrateBridgeFormula dqrateBridgeStore
      dqrateBridgeSigma dqrateBridgeSk = true := by
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, dqrateBridgeFormula, dqrateBridgeStore,
    dqrateBridgeSigma, dqrateBridgeSk, mkLit, Literal.var, Literal.isPos, CRef_Undef]
  intro x hx
  have hx_cases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  rcases hx_cases with rfl | rfl | rfl <;> simp

/-- The blocker resolvent for `D2` and pivot `y` is just `(¬x)`. -/
theorem dqrateBridgeResolvent_eq :
    dqrateResolvent dqrateBridgeFormula dqrateBridgeClause
      #[mkLit 2 false, mkLit 3 false, mkLit 1 false] (mkLit 3 true) =
        #[mkLit 2 false] := by
  simp [dqrateResolvent, outerClause, DQBF.isVarOuterOfExivar, DQBF.isVarExistential,
    dqrateBridgeFormula, dqrateBridgeClause, mkLit, Literal.var, Literal.negate]

/-- The blocker resolvent `(¬x)` is false under the same witness assignment. -/
theorem dqrateBridgeResolventFalse :
    DQBF.clauseValue dqrateBridgeFormula dqrateBridgeSigma dqrateBridgeSk
      #[mkLit 2 false] = false := by
  simp [DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, dqrateBridgeFormula, dqrateBridgeSigma, dqrateBridgeSk,
    mkLit, Literal.var, Literal.isPos]

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
    simp [mkLit, Literal.negate]
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

def deleteBridgeNotDependsOnState : CheckState :=
  match notDependsOn 3 1 deleteBridgeState with
  | .ok _ s => s
  | .error _ s => s

def deleteBridgeOtherExistentialAccepted : Bool :=
  match notDependsOn 2 1 deleteBridgeState with
  | .ok true _ => true
  | _ => false

theorem deleteBridge_reachPos :
    getReachable deleteBridgeState (mkLit 1 true) =
      #[false, false, false, false, true, false, false, true] := by
  unfold getReachable
  simp [getReachable.go.eq_1, deleteBridgeState, deleteBridgeFormula, deleteBridgeStore,
    ClauseStore.getOcc, getReachableCRefStep, ClauseStore.getClauseRaw,
    ClauseStore.getClauseAt, getReachableLitStep, DQBF.isVarExistential,
    mkLit, Literal.var, Literal.negate, CRef_Undef]

theorem deleteBridge_reachNeg :
    getReachable deleteBridgeState (mkLit 1 false) =
      #[false, false, false, false, false, false, false, false] := by
  unfold getReachable
  simp [getReachable.go.eq_1, deleteBridgeState, deleteBridgeFormula, deleteBridgeStore,
    ClauseStore.getOcc, DQBF.isVarExistential, mkLit, Literal.var, Literal.negate]

def deleteBridgeComputedIndepState : CheckState := {
  deleteBridgeState with
  indepKnown := #[true, false, false]
  indepOf := #[#[2, 3], #[], #[]]
}

theorem deleteBridge_notDependsOn_x :
    notDependsOn 3 1 deleteBridgeState = .ok true deleteBridgeComputedIndepState := by
  unfold notDependsOn computeDeps
  simp only [Bind.bind, EStateM.bind, EStateM.pure, Pure.pure, get, getThe,
    MonadState.get, MonadStateOf.get, EStateM.get]
  rw [deleteBridge_reachPos, deleteBridge_reachNeg]
  simp [EStateM.bind, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, deleteBridgeComputedIndepState, deleteBridgeState,
    deleteBridgeFormula, DQBF.isVarExistential]

theorem deleteBridge_notDependsOn_y :
    notDependsOn 2 1 deleteBridgeState = .ok true deleteBridgeComputedIndepState := by
  unfold notDependsOn computeDeps
  simp only [Bind.bind, EStateM.bind, EStateM.pure, Pure.pure, get, getThe,
    MonadState.get, MonadStateOf.get, EStateM.get]
  rw [deleteBridge_reachPos, deleteBridge_reachNeg]
  simp [EStateM.bind, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, deleteBridgeComputedIndepState, deleteBridgeState,
    deleteBridgeFormula, DQBF.isVarExistential]

/-- `notDependsOn` accepts deleting `u` from `x` on the delete-bridge instance. -/
theorem deleteBridgeNotDependsOnAccepted_true :
    deleteBridgeNotDependsOnAccepted = true := by
  simp [deleteBridgeNotDependsOnAccepted, deleteBridge_notDependsOn_x]

/-- The recomputed independence set for `u` contains both existentials. This is
    why the semantic target is a set-level bridge, not an `x`-only witness patch. -/
theorem deleteBridgeNotDependsOnState_indepOf :
    deleteBridgeNotDependsOnState.indepOf.getD 0 #[] = #[2, 3] := by
  simp [deleteBridgeNotDependsOnState, deleteBridge_notDependsOn_x,
    deleteBridgeComputedIndepState]

/-- On `deleteBridge`, the same recomputation also accepts deleting `u` from `y`.
    The checker-side relation is naturally a set of independent existentials. -/
theorem deleteBridgeOtherExistentialAccepted_true :
    deleteBridgeOtherExistentialAccepted = true := by
  simp [deleteBridgeOtherExistentialAccepted, deleteBridge_notDependsOn_y]

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
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, deleteBridgeFormula, deleteBridgeStore,
    deleteBridgeSigmaFalse, deleteBridgeOldSk, mkLit, Literal.var, Literal.isPos,
    CRef_Undef]
  intro x hx
  have hx_cases : x = 0 ∨ x = 1 := by omega
  rcases hx_cases with rfl | rfl <;> simp [deleteBridgeSigmaFalse]

theorem deleteBridgeOldSk_sigmaTrue :
    ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
      deleteBridgeSigmaTrue deleteBridgeOldSk = true := by
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, deleteBridgeFormula, deleteBridgeStore,
    deleteBridgeSigmaTrue, deleteBridgeOldSk, mkLit, Literal.var, Literal.isPos,
    CRef_Undef]
  intro x hx
  have hx_cases : x = 0 ∨ x = 1 := by omega
  rcases hx_cases with rfl | rfl <;> simp

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
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, deleteBridgeFormula, deleteBridgeStore,
    deleteBridgeSigmaFalse, deleteBridgeGoodSk, mkLit, Literal.var, Literal.isPos,
    CRef_Undef]
  intro x hx
  have hx_cases : x = 0 ∨ x = 1 := by omega
  rcases hx_cases with rfl | rfl <;> simp

theorem deleteBridgeGoodSk_old_sigmaTrue :
    ClauseStore.matrixValue deleteBridgeFormula deleteBridgeStore
      deleteBridgeSigmaTrue deleteBridgeGoodSk = true := by
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, deleteBridgeFormula, deleteBridgeStore,
    deleteBridgeSigmaTrue, deleteBridgeGoodSk, mkLit, Literal.var, Literal.isPos,
    CRef_Undef]
  intro x hx
  have hx_cases : x = 0 ∨ x = 1 := by omega
  rcases hx_cases with rfl | rfl <;> simp

theorem deleteBridgeGoodSk_deleted_sigmaFalse :
    ClauseStore.matrixValue (deleteBridgeFormula.forceDelDep 3 1) deleteBridgeStore
      deleteBridgeSigmaFalse deleteBridgeGoodSk = true := by
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, DQBF.forceDelDep, deleteBridgeFormula, deleteBridgeStore,
    deleteBridgeSigmaFalse, deleteBridgeGoodSk, mkLit, Literal.var, Literal.isPos,
    CRef_Undef]
  intro x hx
  have hx_cases : x = 0 ∨ x = 1 := by omega
  rcases hx_cases with rfl | rfl <;> simp

theorem deleteBridgeGoodSk_deleted_sigmaTrue :
    ClauseStore.matrixValue (deleteBridgeFormula.forceDelDep 3 1) deleteBridgeStore
      deleteBridgeSigmaTrue deleteBridgeGoodSk = true := by
  unfold ClauseStore.matrixValue
  simp [ClauseStore.getClause, ClauseStore.getClauseAt,
    DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, DQBF.forceDelDep, deleteBridgeFormula, deleteBridgeStore,
    deleteBridgeSigmaTrue, deleteBridgeGoodSk, mkLit, Literal.var, Literal.isPos,
    CRef_Undef]
  intro x hx
  have hx_cases : x = 0 ∨ x = 1 := by omega
  rcases hx_cases with rfl | rfl <;> simp

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
  simp [DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, DQBF.forceDelDep, deleteBridgeFormula,
    deleteBridgeSigmaFalse, deleteBridgePatchFalse, deleteBridgeOldSk,
    mkLit, Literal.var, Literal.isPos]

/-- After deleting `u` from `x`, forcing `x = true` breaks clause `C2`
    on the same reduced pattern `[]` witnessed by `u = true`. -/
theorem deleteBridgePatchTrue_breaksClause :
    DQBF.clauseValue (deleteBridgeFormula.forceDelDep 3 1)
      deleteBridgeSigmaTrue deleteBridgePatchTrue
      #[mkLit 2 false, mkLit 3 false] = false := by
  simp [DQBF.clauseValue, DQBF.litValue, DQBF.varValue, DQBF.exiValue,
    DQBF.isVarExistential, DQBF.forceDelDep, deleteBridgeFormula,
    deleteBridgeSigmaTrue, deleteBridgePatchTrue, deleteBridgeOldSk,
    mkLit, Literal.var, Literal.isPos]

/-- The two witnesses above show that the fixed-witness, `x`-only patch route is
    too strong: `notDependsOn` can succeed even though, for a particular old
    satisfying witness, both Boolean choices for deleted `x` fail on the unique
    reduced dependency pattern. -/
theorem deleteBridge_fixedWitnessPatchRouteTooStrong :
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
  exact ⟨deleteBridgeOldSk_sigmaFalse,
    deleteBridgeOldSk_sigmaTrue,
    deleteBridgePatchFalse_breaksClause,
    deleteBridgePatchTrue_breaksClause⟩

end DqratLean.Counterexamples
