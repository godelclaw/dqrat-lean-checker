import DqratLean.Checker
import DqratLean.WatchedState

/-!
# Watched Checker

Executable checker operations routed through the watched-runtime propagation
layer.

Trust status: experimental watched-layer executable code, outside the certified
default path.
-/
namespace DqratLean.Watched

/--
Executable checker routed through the runtime-oriented propagation stack from
`WatchedState.lean`.

Reference notes:
- `docs/watched_runtime_references.md`
- particularly the separation between long-clause watches and binary implication
  propagation.
-/
def negateAndPropagate (lits : Array Literal) (which : Literal → Bool) : CheckM Bool := do
  newDecisionLevel
  lits.foldlM (fun conflict l => do
    if conflict then return true
    if !which l then return false
    let st ← get
    let v := l.var
    if v = 0 || v > st.formula.maxVar then return false
    if satisfied st l then
      return true
    else if satisfied st l.negate then
      return false
    else
      enqueue l.negate
      let cref ← propagate
      return cref.isSome
  ) false

def addClauseAfterCache (lits : Array Literal) : CheckM (Option CRef) := do
  let st0 ← get
  let cref := st0.clauses.clauses.size
  modify fun st => addClauseStoreState st lits
  addClauseLiveOccs lits cref
  if lits.isEmpty then
    return none
  else if lits.size = 1 then
    let st ← get
    let lit := lits.getD 0 (mkLit 0 false)
    if satisfied st lit then
      return some cref
    else if assigned st lit.var then
      return none
    else
      enqueue lit
      let conflict ← propagate
      if conflict.isSome then return none else return some cref
  else if lits.size = 2 then
    let lit0 := lits.getD 0 (mkLit 0 false)
    let lit1 := lits.getD 1 (mkLit 0 false)
    -- Binary clauses stay out of the long-clause watch path and are propagated
    -- as the two direct implications `¬lit0 -> lit1` and `¬lit1 -> lit0`.
    let _ ← appendBinaryImp lit0.negate { cref := cref, implied := lit1 }
    let _ ← appendBinaryImp lit1.negate { cref := cref, implied := lit0 }
    let st ← get
    let sat := satisfied st lit0 || satisfied st lit1
    if sat then
      return some cref
    let unassigned := lits.filter fun lit =>
      !assigned st lit.var
    if unassigned.isEmpty then
      return none
    else if unassigned.size = 1 then
      enqueue (unassigned.getD 0 (mkLit 0 false))
      let conflict ← propagate
      if conflict.isSome then return none else return some cref
    else
      return some cref
  else
    let lit0 := lits.getD 0 (mkLit 0 false)
    let lit1 := lits.getD 1 (mkLit 0 false)
    let entry0 : WatchEntry := { cref := cref, blocker := lit1 }
    let entry1 : WatchEntry := { cref := cref, blocker := lit0 }
    let _ ← appendWatch lit0 entry0
    let _ ← appendWatch lit1 entry1
    let (ok, _) ← updateWatchedLiterals cref
    if !ok then
      return none
    let conflict ← propagate
    if conflict.isSome then return none else return some cref

def addClause (lits : Array Literal) : CheckM (Option CRef) := do
  invalidateDepCaches lits
  addClauseAfterCache lits

def outerClause (f : DQBF) (blockerLits : Array Literal) (pivot : Literal) :
    Array Literal :=
  blockerLits.filter fun l => l ≠ pivot.negate && f.isVarOuterOfExivar l.var pivot.var

def runDQRATEOuterClauseTrial (outerLits : Array Literal) : CheckM Bool := do
  let gotConflict ← negateAndPropagate outerLits (fun _ => true)
  backtrackBefore 2
  return gotConflict

def runDQRATEBlockerTrial (pivot : Literal) (f : DQBF)
    (blockerLits : Array Literal) : CheckM Bool := do
  runDQRATEOuterClauseTrial (outerClause f blockerLits pivot)

def checkDQRATEBlockerStep (pivot : Literal)
    (acc : Option CRef) (cref : CRef) : CheckM (Option CRef) := do
  match acc with
  | some _ => return acc
  | none =>
      let st ← get
      match st.clauses.getClauseRaw cref with
      | none => return none
      | some clause =>
          if clause.deleted then return none
          let gotConflict ← runDQRATEBlockerTrial pivot st.formula clause.lits
          if gotConflict then
            return none
          else
            return some cref

def runDQRATEPivotPhase (pivot : Literal) : CheckM (Bool × Option CRef) := do
  let st ← get
  let occPivot := getLiveOcc st pivot.negate
  let blocker ← occPivot.foldlM (checkDQRATEBlockerStep pivot) none
  backtrackBefore 1
  match blocker with
  | some c => return (false, some c)
  | none => return (true, none)

def checkDQRATE (lits : Array Literal) : CheckM (Bool × Option CRef) := do
  let isRup ← negateAndPropagate lits (fun _ => true)
  if isRup then
    backtrackBefore 1
    return (true, none)
  if lits.isEmpty then
    backtrackBefore 1
    return (false, none)
  let pivot := lits.getD 0 (mkLit 0 false)
  let st ← get
  if !st.formula.isVarExistential pivot.var then
    backtrackBefore 1
    return (false, none)
  runDQRATEPivotPhase pivot

def checkPathC (st : CheckState) (l : Literal) (lits : Array Literal) (target : CRef) : Bool :=
  let lvar := l.var
  if st.formula.isVarExistential lvar then false
  else
    Id.run do
      let initWorklist : Array Literal := lits.foldl (fun wl lit =>
        let v := lit.var
        if !st.formula.isVarExistential v then wl
        else
          let deps := st.formula.depset.getD v #[]
          if deps.contains lvar then wl.push lit.negate else wl
      ) #[]
      let numLits := st.formula.maxVar * 2 + 2
      let mut worklist := initWorklist
      let mut explored : Array Bool := (List.replicate numLits false).toArray
      let mut found := false
      let mut fuel := numLits + 2
      while fuel > 0 && !found && !worklist.isEmpty do
        fuel := fuel - 1
        let cur := worklist.getD (worklist.size - 1) (mkLit 0 false)
        worklist := worklist.pop
        let idx := cur.x
        if explored.getD idx false then
          pure ()
        else
          explored := explored.setIfInBounds idx true
          let occs := getLiveOcc st cur
          for cref in occs do
            if found then
              pure ()
            else if cref = target then
              found := true
            else
              match st.clauses.getClauseRaw cref with
              | none => pure ()
              | some clause =>
                  if clause.deleted || clause.lits.contains l then
                    pure ()
                  else
                    for lit in clause.lits do
                      if lit = cur || explored.getD lit.negate.x false then
                        pure ()
                      else
                        let litvar := lit.var
                        if st.formula.isVarExistential litvar then
                          let deps := st.formula.depset.getD litvar #[]
                          if deps.contains lvar then
                            worklist := worklist.push lit.negate
      return found

def outerUClause (f : DQBF) (blockerLits : Array Literal) (pivot : Literal) :
    Array Literal :=
  blockerLits.filter fun l =>
    l ≠ pivot.negate && DQBF.isVarOuterOfUnivar f l.var pivot.var

def runDQRATUOuterClauseTrial (outerLits : Array Literal) : CheckM Bool := do
  let gotConflict ← negateAndPropagate outerLits (fun _ => true)
  backtrackBefore 2
  return gotConflict

def runDQRATUBlockerTrial (pivot : Literal) (f : DQBF)
    (blockerLits : Array Literal) : CheckM Bool := do
  runDQRATUOuterClauseTrial (outerUClause f blockerLits pivot)

def checkDQRATUBlockerStep (pivot : Literal) (lits : Array Literal)
    (crefOfLits : Option CRef) (allOk : Bool) (cref : CRef) : CheckM Bool := do
  if !allOk then return false
  let st ← get
  match st.clauses.getClauseRaw cref with
  | none => return true
  | some clause =>
      if clause.deleted then return true
      let connected := checkPathC st pivot lits cref || crefOfLits = some cref
      if !connected then return true
      runDQRATUBlockerTrial pivot st.formula clause.lits

def checkDQRATU (lits : Array Literal) (pivot : Literal) : CheckM Bool := do
  let isRup ← negateAndPropagate lits (fun l => l ≠ pivot)
  if isRup then
    backtrackBefore 1
    return true
  let st ← get
  let negPivot := pivot.negate
  let occPivot := getLiveOcc st negPivot
  let sortedLits := ClauseStore.sortLits lits
  let crefOfLits := findSortedClauseLive st sortedLits
  let isRat ← occPivot.foldlM (checkDQRATUBlockerStep pivot lits crefOfLits) true
  backtrackBefore 1
  return isRat

def checkAddUniversalStep (lineNum : Nat) (cv : Int)
    (r : MProd (Option (Option ProofResult)) PUnit) :
    CheckM (ForInStep (MProd (Option (Option ProofResult)) PUnit)) := do
  let _ := r.snd
  if cv < 0 then
    let extVar := (-cv).toNat
    let f ← (·.formula) <$> get
    if f.externalVarExists extVar then
      pure (ForInStep.done
        (MProd.mk (some (some (.Failed lineNum #["UADD"] #[cv] none))) PUnit.unit))
    else
      pure (ForInStep.yield
        (MProd.mk (none : Option (Option ProofResult)) PUnit.unit))
  else
    let extVar := cv.toNat
    let f ← (·.formula) <$> get
    if f.externalVarExists extVar then
      pure (ForInStep.done
        (MProd.mk (some (some (.Failed lineNum #["UADD"] #[cv] none))) PUnit.unit))
    else
      let _ ← addVarForall extVar
      pure (ForInStep.yield
        (MProd.mk (none : Option (Option ProofResult)) PUnit.unit))

def checkAddUniversal (lineNum : Nat) (extVars : List Int) : CheckM (Option ProofResult) := do
  let r ←
    forIn extVars (MProd.mk (none : Option (Option ProofResult)) PUnit.unit)
      (checkAddUniversalStep lineNum)
  match r.fst with
  | some res => return res
  | none =>
      resetPropagationState
      return none

def translateExistingLits (extLits : List Int) : CheckM (Array Literal) := do
  let mut acc := #[]
  for lit in extLits do
    let f ← (·.formula) <$> get
    match f.lookupInternal lit.natAbs with
    | none => pure ()
    | some iv => acc := acc.push (mkLit iv (lit > 0))
  pure acc

def checkModifyExistentialAddStep (internalExi : Var) (cv : Int) : CheckM Unit := do
  let extDep := cv.toNat
  let f ← (·.formula) <$> get
  let internalDep ←
    if !f.externalVarExists extDep then addVarForall extDep
    else match f.lookupInternal extDep with
      | none => throw s!"Dep var {extDep} not found"
      | some v => pure v
  addDependencyReset internalExi internalDep

def checkModifyExistentialDelStep
    (lineNum : Nat) (extExi : Nat) (internalExi : Var) (cv : Int) :
    CheckM (Option ProofResult) := do
  let extDep := (-cv).toNat
  let f ← (·.formula) <$> get
  if !f.externalVarExists extDep then
    return none
  match f.lookupInternal extDep with
  | none => pure none
  | some internalDep =>
      let ok ← delDependencyReset internalExi internalDep
      if !ok then
        return some (.Failed lineNum #["DPURE"] #[cv, Int.ofNat extExi] none)
      return none

def checkModifyExistential (lineNum : Nat) (extExi : Nat) (depChanges : List Int) :
    CheckM (Option ProofResult) := do
  if extExi = 0 then return some (.Failed lineNum #["UADD"] #[] none)
  let f ← (·.formula) <$> get
  let internalExi ←
    if !f.externalVarExists extExi then addVarExists extExi #[]
    else match f.lookupInternal extExi with
      | none => throw s!"Var {extExi} not found"
      | some v => pure v
  for cv in depChanges do
    if cv < 0 then
      match (← checkModifyExistentialDelStep lineNum extExi internalExi cv) with
      | some res => return some res
      | none => pure ()
    else
      checkModifyExistentialAddStep internalExi cv
  resetPropagationState
  return none

def checkModifyExistentialAddOnlyCore (extExi : Nat) (depChanges : List Int) :
    CheckM (Option ProofResult) := do
  let internalExi ←
    (do
      let f ← (·.formula) <$> get
      if !f.externalVarExists extExi then
        addVarExists extExi #[]
      else
        match f.lookupInternal extExi with
        | none => throw s!"Var {extExi} not found"
        | some v => pure v)
  let _ ←
    (forIn depChanges PUnit.unit (fun cv _ => do
      if cv < 0 then
        pure (ForInStep.yield PUnit.unit)
      else
        let _ ← checkModifyExistentialAddStep internalExi cv
        pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
  resetPropagationState
  pure none

def checkModifyExistentialAddOnly (lineNum : Nat) (extExi : Nat) (depChanges : List Int) :
    CheckM (Option ProofResult) := do
  if extExi = 0 then
    return some (.Failed lineNum #["UADD"] #[] none)
  if depChanges.any (· < 0) then
    throw s!"line {lineNum}: dependency deletion is not supported in no-negative-e mode"
  checkModifyExistentialAddOnlyCore extExi depChanges

def checkDeleteClause (lineNum : Nat) (extLits : List Int) : CheckM (Option ProofResult) := do
  let lits ← translateExistingLits extLits
  let st ← get
  match findSortedClauseLive st (ClauseStore.sortLits lits) with
  | none => return some (.Failed lineNum #["LOCATE", "DEL"] #[] none)
  | some cref =>
      match st.clauses.getClauseRaw cref with
      | none => return some (.Failed lineNum #["LOCATE", "DEL"] #[] none)
      | some clause =>
          modify fun s => deleteClauseCacheState s cref clause
      resetPropagationState
      return none

def checkUniversalReductionLocated
    (lineNum : Nat) (lits : Array Literal) (pivot : Literal) :
    CheckM (Option ProofResult) := do
  let f2 ← (·.formula) <$> get
  let pivotReducible := !lits.any (· = pivot.negate) && lits.all fun l =>
    !f2.isVarExistential l.var || !f2.isVarOuterOfExivar pivot.var l.var
  if pivotReducible then
    let r ← addClause (lits.filter (· ≠ pivot))
    if r.isNone then return some (.Verified lineNum)
  else
    let ok ← checkDQRATU lits pivot
    if !ok then return some (.Failed lineNum #["UR", "DQRATU"] #[] none)
    let r ← addClause lits
    if r.isNone then return some (.Verified lineNum)
  return none

def checkUniversalReductionTranslated
    (lineNum : Nat) (lits : Array Literal) : CheckM (Option ProofResult) := do
  if lits.isEmpty then return some (.Failed lineNum #["UR"] #[] none)
  let pivot := lits.getD 0 (mkLit 0 false)
  let f ← (·.formula) <$> get
  if f.isVarExistential pivot.var then
    return some (.Failed lineNum #["UR"] #[f.externalizeLit pivot] none)
  let st ← get
  match findSortedClauseLive st (ClauseStore.sortLits lits) with
  | none => return some (.Failed lineNum #["LOCATE", "UR"] #[] none)
  | some _ => checkUniversalReductionLocated lineNum lits pivot

def checkUniversalReduction (lineNum : Nat) (extLits : List Int) :
    CheckM (Option ProofResult) := do
  let lits ← translateExistingLits extLits
  checkUniversalReductionTranslated lineNum lits

def translateRatLitBasicStep (acc : Array Literal) (lit : Int) : CheckM (Array Literal) := do
  let extVar := lit.natAbs
  let f ← (·.formula) <$> get
  if !f.externalVarExists extVar then
    let _ ← addVarExists extVar f.univars
  let f2 ← (·.formula) <$> get
  match f2.lookupInternal extVar with
  | none => pure acc
  | some iv => pure (acc.push (mkLit iv (lit > 0)))

def translateRatLitsBasic (extLits : List Int) : CheckM (Array Literal) := do
  let mut acc := #[]
  for lit in extLits do
    acc ← translateRatLitBasicStep acc lit
  pure acc

def runRupTrial (lits : Array Literal) : CheckM Bool := do
  let isRup ← negateAndPropagate lits (fun _ => true)
  backtrackBefore 1
  pure isRup

def checkRatClause (lineNum : Nat) (extLits : List Int) : CheckM (Option ProofResult) := do
  let lits ← translateRatLitsBasic extLits
  let (success, blocker) ← checkDQRATE lits
  if !success then return some (.Failed lineNum #["RUP", "DQRATE"] #[] blocker)
  let r ← addClause lits
  if r.isNone then return some (.Verified lineNum)
  return none

def checkUniversalReductionBasic (lineNum : Nat) (extLits : List Int) :
    CheckM (Option ProofResult) := do
  let lits ← translateExistingLits extLits
  if lits.isEmpty then return some (.Failed lineNum #["UR"] #[] none)
  let pivot := lits.getD 0 (mkLit 0 false)
  let f ← (·.formula) <$> get
  if f.isVarExistential pivot.var then
    return some (.Failed lineNum #["UR"] #[f.externalizeLit pivot] none)
  let st ← get
  match findSortedClauseLive st (ClauseStore.sortLits lits) with
  | none => return some (.Failed lineNum #["LOCATE", "UR"] #[] none)
  | some _ =>
      let f2 ← (·.formula) <$> get
      let pivotReducible := !lits.any (· = pivot.negate) && lits.all fun l =>
        !f2.isVarExistential l.var || !f2.isVarOuterOfExivar pivot.var l.var
      if pivotReducible then
        let r ← addClause (lits.filter (· ≠ pivot))
        if r.isNone then return some (.Verified lineNum)
      else
        return some (.Failed lineNum #["UR"] #[] none)
      return none

def checkRatClauseBasic (lineNum : Nat) (extLits : List Int) : CheckM (Option ProofResult) := do
  let lits ← translateRatLitsBasic extLits
  let isRup ← runRupTrial lits
  if !isRup then return some (.Failed lineNum #["RUP"] #[] none)
  let r ← addClause lits
  if r.isNone then return some (.Verified lineNum)
  return none

def checkAction (action : DQRatAction) : CheckM (Option ProofResult) :=
  match action with
  | .AddUniversal lineNum extVars => checkAddUniversal lineNum extVars
  | .ModifyExistential lineNum extExi depChanges => checkModifyExistential lineNum extExi depChanges
  | .DeleteClause lineNum extLits => checkDeleteClause lineNum extLits
  | .UniversalReduction lineNum extLits => checkUniversalReduction lineNum extLits
  | .RatClause lineNum extLits => checkRatClause lineNum extLits

def checkActionBasic (action : DQRatAction) : CheckM (Option ProofResult) :=
  match action with
  | .AddUniversal _ _ =>
      throw "AddUniversal is not supported in basic mode"
  | .ModifyExistential _ _ _ =>
      throw "ModifyExistential is not supported in basic mode"
  | .DeleteClause _ _ =>
      throw "DeleteClause is not supported in basic mode"
  | .UniversalReduction lineNum extLits =>
      checkUniversalReductionBasic lineNum extLits
  | .RatClause lineNum extLits =>
      checkRatClauseBasic lineNum extLits

/-- Restricted scaffold checker matching `DqratLean.Checker.checkActionNoNegE`.
    Dependency deletion is rejected, while RAT additions stay on the RUP-only path. -/
def checkActionNoNegE (action : DQRatAction) : CheckM (Option ProofResult) :=
  match action with
  | .AddUniversal lineNum extVars => checkAddUniversal lineNum extVars
  | .ModifyExistential lineNum extExi depChanges =>
      checkModifyExistentialAddOnly lineNum extExi depChanges
  | .DeleteClause lineNum extLits => checkDeleteClause lineNum extLits
  | .UniversalReduction lineNum extLits => checkUniversalReduction lineNum extLits
  | .RatClause lineNum extLits => checkRatClauseBasic lineNum extLits

def checkActionsCore (step : DQRatAction → CheckM (Option ProofResult))
    (actions : List DQRatAction) : CheckM ProofResult := do
  for action in actions do
    match (← step action) with
    | some res => return res
    | none => pure ()
  return .Unknown

def checkActions (actions : List DQRatAction) : CheckM ProofResult :=
  checkActionsCore checkAction actions

def checkActionsBasic (actions : List DQRatAction) : CheckM ProofResult :=
  checkActionsCore checkActionBasic actions

def checkActionsNoNegE (actions : List DQRatAction) : CheckM ProofResult :=
  checkActionsCore checkActionNoNegE actions

end DqratLean.Watched
