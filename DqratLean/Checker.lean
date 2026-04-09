import DqratLean.CheckState

-- ─── Core checking routines ────────────────────────────────────────────────

-- Negate filtered literals and propagate; returns true if conflict found.
-- Opens a new decision level. Caller must backtrack.
def negateAndPropagate (lits : Array Literal) (which : Literal → Bool) : CheckM Bool := do
  newDecisionLevel
  lits.foldlM (fun conflict l => do
    if conflict then return true
    if !which l then return false
    let st ← get
    let v := l.var
    if v = 0 || v > st.formula.maxVar then return false
    if satisfied st l then
      return true  -- l is already true; ~l would be false = contradiction
    else if satisfied st l.negate then
      return false  -- ~l already true; no need to enqueue
    else
      enqueue l.negate
      let cref ← propagate
      return cref.isSome
  ) false

-- ─── Add clause to state (with UP) ────────────────────────────────────────

-- Returns None if UP detects UNSAT (= proof verified), Some cref otherwise.
-- Assumes independence caches have already been invalidated for `lits`.
def addClauseAfterCache (lits : Array Literal) : CheckM (Option CRef) := fun st0 =>
  let st := { st0 with clauses := (st0.clauses.addClause lits).1 }
  let cref := st.clauses.clauses.size - 1  -- just-added clause index
  if lits.isEmpty then
    .ok none st
  else
    let sat := lits.any fun l =>
      let v := l.var
      v > 0 && v <= st.formula.maxVar &&
      st.isAssigned.getD (v - 1) false &&
      (st.value.getD (v - 1) false == l.isPos)
    if sat then
      .ok (some cref) st
    else
      let unassigned := lits.filter fun l =>
        let v := l.var
        v > 0 && v <= st.formula.maxVar &&
        !st.isAssigned.getD (v - 1) false
      if unassigned.isEmpty then
        .ok none st  -- all literals false = conflict
      else if unassigned.size = 1 then
        match enqueue (unassigned.getD 0 ⟨0⟩) st with
        | .error e s => .error e s
        | .ok _ s =>
            match propagate s with
            | .error e s' => .error e s'
            | .ok conflict s' =>
                if conflict.isSome then .ok none s'
                else .ok (some cref) s'
      else
        .ok (some cref) st

-- Returns None if UP detects UNSAT (= proof verified), Some cref otherwise.
def addClause (lits : Array Literal) : CheckM (Option CRef) := do
  -- Invalidate independence caches for universals appearing in dep-sets of existentials
  invalidateDepCaches lits
  addClauseAfterCache lits

-- ─── DQRATE check ─────────────────────────────────────────────────────────

def runDQRATEBlockerTrial (pivot : Literal) (f : DQBF)
    (blockerLits : Array Literal) : CheckM Bool := do
  let isouter : Literal → Bool := fun l =>
    l ≠ pivot.negate && f.isVarOuterOfExivar l.var pivot.var
  let gotConflict ← negateAndPropagate blockerLits isouter
  backtrackBefore 2
  return gotConflict

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
  let occPivot := st.clauses.getOcc pivot.negate
  let blocker ← occPivot.foldlM (checkDQRATEBlockerStep pivot) none
  backtrackBefore 1
  match blocker with
  | some c => return (false, some c)
  | none => return (true, none)

-- Full DQRATE check: try RUP first, then RAT with pivot lits[0].
-- Returns (success, blocker_cref_if_rat_failed)
def checkDQRATE (lits : Array Literal) : CheckM (Bool × Option CRef) := do
  -- ── RUP attempt (opens decision level 1) ──
  let isRup ← negateAndPropagate lits (fun _ => true)
  if isRup then
    backtrackBefore 1
    return (true, none)

  -- ── RAT attempt ──
  if lits.isEmpty then
    backtrackBefore 1
    return (false, none)

  let pivot := lits.getD 0 ⟨0⟩
  let st ← get
  if !st.formula.isVarExistential pivot.var then
    backtrackBefore 1
    return (false, none)
  runDQRATEPivotPhase pivot

-- ─── D^∀-pure path reachability to a target clause ───────────────────────

-- Check if there is a D^∀-pure path from the negations of existential literals
-- in `lits` (that depend on var(l)) through the clause store to `target`.
-- Used in DQRATU to skip blocker clauses that are disconnected from the proof clause.
-- l must be a universal literal.
def checkPathC (st : CheckState) (l : Literal) (lits : Array Literal) (target : CRef) : Bool :=
  let lvar := l.var
  if st.formula.isVarExistential lvar then false
  else
    let numLits := st.formula.maxVar * 2 + 2
    -- Starting worklist: ~e for each existential e in lits that depends on lvar
    let initWorklist : Array Literal := lits.foldl (fun wl lit =>
      let v := lit.var
      if !st.formula.isVarExistential v then wl
      else
        let deps := st.formula.depset.getD v #[]
        if deps.contains lvar then wl.push lit.negate else wl
    ) #[]
    let explored : Array Bool := (List.replicate numLits false).toArray
    -- Fuel-bounded DFS
    let rec go : Nat → Array Literal → Array Bool → Bool
      | 0, _, _ => false
      | f + 1, wl, expl =>
          if wl.isEmpty then false
          else
            let cur := wl.getD (wl.size - 1) ⟨0⟩
            let wl' := wl.pop
            let idx := cur.x
            if expl.getD idx false then go f wl' expl
            else
              let expl' := expl.setIfInBounds idx true
              let occs := st.clauses.getOcc cur
              let (found, wl'') := occs.foldl (fun (fd, acc) cref =>
                if fd then (true, acc)
                else if cref = target then (true, acc)  -- target reached
                else
                  match st.clauses.getClauseRaw cref with
                  | none => (false, acc)
                  | some clause =>
                      if clause.deleted then (false, acc)
                      -- Skip clauses containing l (not u-pure)
                      else if clause.lits.contains l then (false, acc)
                      else
                        -- Add ~lit to worklist for existentials depending on lvar
                        let acc' := clause.lits.foldl (fun acc2 lit =>
                          if lit = cur then acc2
                          else if expl'.getD lit.negate.x false then acc2
                          else
                            let litvar := lit.var
                            if !st.formula.isVarExistential litvar then acc2
                            else
                              let deps := st.formula.depset.getD litvar #[]
                              if deps.contains lvar then acc2.push lit.negate else acc2
                        ) acc
                        (false, acc')
              ) (false, wl')
              if found then true
              else go f wl'' expl'
    go (numLits + 2) initWorklist explored

-- ─── DQRATU check ─────────────────────────────────────────────────────────

-- DQRATU check: pivot must be universal; try RUP-without-pivot then RAT.
-- Only checks blocker clauses that are connected to the proof clause via
-- a D^∀-pure path (checkPathC), or that are the proof clause itself.
def runDQRATUBlockerTrial (pivot : Literal) (f : DQBF)
    (blockerLits : Array Literal) : CheckM Bool := do
  let isouter : Literal → Bool := fun l =>
    l ≠ pivot.negate && DQBF.isVarOuterOfUnivar f l.var pivot.var
  let gotConflict ← negateAndPropagate blockerLits isouter
  backtrackBefore 2
  return gotConflict

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
  -- ── RUP without pivot (opens decision level 1) ──
  let isRup ← negateAndPropagate lits (fun l => l ≠ pivot)
  if isRup then
    backtrackBefore 1
    return true

  -- ── RAT for universal pivot ──
  let st ← get
  let negPivot := pivot.negate
  let occPivot := st.clauses.getOcc negPivot
  -- CRef of the clause being proved (if it already exists in the formula)
  let sortedLits := ClauseStore.sortLits lits
  let crefOfLits := st.clauses.findSortedClause sortedLits

  let isRat ← occPivot.foldlM (checkDQRATUBlockerStep pivot lits crefOfLits) true

  backtrackBefore 1
  return isRat

-- ─── Proof result ──────────────────────────────────────────────────────────

inductive ProofResult where
  | Verified (line : Nat)
  | Failed   (line : Nat) (rules : Array String) (info : Array Int) (blocker : Option CRef)
  | Unknown

def formatResult : ProofResult → String
  | .Verified _ => "s VERIFIED"
  | .Failed _ _ _ _ => "s FAILED"
  | .Unknown => "s UNKNOWN"

-- ─── Proof actions ─────────────────────────────────────────────────────────

/-- A single step in a DQRAT proof, with external variable numbers still unresolved. -/
inductive DQRatAction where
  /-- 'a': add universal variables (extVars may include negatives for error reporting) -/
  | AddUniversal      (lineNum : Nat) (extVars    : List Int)
  /-- 'e': modify existential; positive dep = add, negative dep = remove -/
  | ModifyExistential (lineNum : Nat) (extExi     : Nat) (depChanges : List Int)
  /-- 'd': delete clause given by external literals -/
  | DeleteClause      (lineNum : Nat) (extLits    : List Int)
  /-- 'u': universal reduction -/
  | UniversalReduction(lineNum : Nat) (extLits    : List Int)
  /-- digit: RUP / DQRATE step -/
  | RatClause         (lineNum : Nat) (extLits    : List Int)

-- ─── Individual action handlers ────────────────────────────────────────────

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
    else do
      pure PUnit.unit
      pure (ForInStep.yield
        (MProd.mk (none : Option (Option ProofResult)) PUnit.unit))
  else
    let extVar := cv.toNat
    let f ← (·.formula) <$> get
    if f.externalVarExists extVar then
      pure (ForInStep.done
        (MProd.mk (some (some (.Failed lineNum #["UADD"] #[cv] none))) PUnit.unit))
    else do
      let _ ← addVarForall extVar
      pure PUnit.unit
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

/-- Translate already-existing external literals to internal literals.
    Missing variables are skipped. -/
def translateExistingLits (extLits : List Int) : CheckM (Array Literal) := do
  let mut acc := #[]
  for lit in extLits do
    let f ← (·.formula) <$> get
    match f.lookupInternal lit.natAbs with
    | none    => pure ()
    | some iv => acc := acc.push (mkLit iv (lit > 0))
  pure acc

def checkModifyExistentialAddStep (internalExi : Var) (cv : Int) : CheckM Unit := do
  let extDep := cv.toNat
  let f ← (·.formula) <$> get
  let internalDep ←
    if !f.externalVarExists extDep then addVarForall extDep
    else match f.lookupInternal extDep with
      | none   => throw s!"Dep var {extDep} not found"
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
      | none   => throw s!"Var {extExi} not found"
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

/-- Positive-only existential modification core: create the existential if needed,
    add nonnegative dependency changes, then return to the action boundary. -/
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

/-- Restricted existential modification: negative dependency changes are unsupported. -/
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
  match st.clauses.findSortedClause (ClauseStore.sortLits lits) with
  | none      => return some (.Failed lineNum #["LOCATE", "DEL"] #[] none)
  | some cref =>
    modify fun s => { s with clauses := s.clauses.deleteClause cref }
    resetPropagationState
    return none

def checkUniversalReductionLocated
    (lineNum : Nat) (lits : Array Literal) (pivot : Literal) :
    CheckM (Option ProofResult) := do
  let f2 ← (·.formula) <$> get
  -- Not reducible if clause contains ~pivot (Mixed-EUR: no tautology reductions)
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
  let pivot := lits.getD 0 ⟨0⟩
  let f ← (·.formula) <$> get
  if f.isVarExistential pivot.var then
    return some (.Failed lineNum #["UR"] #[f.externalizeLit pivot] none)
  let st ← get
  match st.clauses.findSortedClause (ClauseStore.sortLits lits) with
  | none   => return some (.Failed lineNum #["LOCATE", "UR"] #[] none)
  | some _ => checkUniversalReductionLocated lineNum lits pivot

def checkUniversalReduction (lineNum : Nat) (extLits : List Int) : CheckM (Option ProofResult) := do
  let lits ← translateExistingLits extLits
  checkUniversalReductionTranslated lineNum lits

/-- Translate RAT/RUP literals, creating fresh existential extension variables for
    missing external names using all current universal variables as the initial dep set. -/
def translateRatLitBasicStep (acc : Array Literal) (lit : Int) : CheckM (Array Literal) := do
  let extVar := lit.natAbs
  let f ← (·.formula) <$> get
  if !f.externalVarExists extVar then
    let _ ← addVarExists extVar f.univars
  let f2 ← (·.formula) <$> get
  match f2.lookupInternal extVar with
  | none    => pure acc
  | some iv => pure (acc.push (mkLit iv (lit > 0)))

/-- Translate RAT/RUP literals, creating fresh existential extension variables for
    missing external names using all current universal variables as the initial dep set. -/
def translateRatLitsBasic (extLits : List Int) : CheckM (Array Literal) := do
  let mut acc := #[]
  for lit in extLits do
    acc ← translateRatLitBasicStep acc lit
  pure acc

/-- Run the basic RUP trial and restore the action-boundary state before returning. -/
def runRupTrial (lits : Array Literal) : CheckM Bool := do
  let isRup ← negateAndPropagate lits (fun _ => true)
  backtrackBefore 1
  pure isRup

/-- Full DQRATE step: RUP first, then RAT with existential pivot. -/
def checkRatClause (lineNum : Nat) (extLits : List Int) : CheckM (Option ProofResult) := do
  let lits ← translateRatLitsBasic extLits
  let (success, blocker) ← checkDQRATE lits
  if !success then return some (.Failed lineNum #["RUP", "DQRATE"] #[] blocker)
  let r ← addClause lits
  if r.isNone then return some (.Verified lineNum)
  return none

/-- UR step for the basic checker: only handles the `pivotReducible` case (simple UR).
    When the non-trivial branch (DQRATU) would be needed, fails immediately. -/
def checkUniversalReductionBasic (lineNum : Nat) (extLits : List Int) : CheckM (Option ProofResult) := do
  let lits ← translateExistingLits extLits
  if lits.isEmpty then return some (.Failed lineNum #["UR"] #[] none)
  let pivot := lits.getD 0 ⟨0⟩
  let f ← (·.formula) <$> get
  if f.isVarExistential pivot.var then
    return some (.Failed lineNum #["UR"] #[f.externalizeLit pivot] none)
  let st ← get
  match st.clauses.findSortedClause (ClauseStore.sortLits lits) with
  | none   => return some (.Failed lineNum #["LOCATE", "UR"] #[] none)
  | some _ =>
    let f2 ← (·.formula) <$> get
    let pivotReducible := !lits.any (· = pivot.negate) && lits.all fun l =>
      !f2.isVarExistential l.var || !f2.isVarOuterOfExivar pivot.var l.var
    if pivotReducible then
      let r ← addClause (lits.filter (· ≠ pivot))
      if r.isNone then return some (.Verified lineNum)
    else
      -- DQRATU not supported in basic mode
      return some (.Failed lineNum #["UR"] #[] none)
    return none

/-- RUP-only step: no RAT fallback. Fails immediately if unit propagation finds no conflict. -/
def checkRatClauseBasic (lineNum : Nat) (extLits : List Int) : CheckM (Option ProofResult) := do
  let lits ← translateRatLitsBasic extLits
  let isRup ← runRupTrial lits
  if !isRup then return some (.Failed lineNum #["RUP"] #[] none)
  let r ← addClause lits
  if r.isNone then return some (.Verified lineNum)
  return none

-- ─── Single-action checker ─────────────────────────────────────────────────

/-- Check a single proof action (full DQRAT). Returns `none` to continue, `some r` to stop. -/
def checkAction (action : DQRatAction) : CheckM (Option ProofResult) :=
  match action with
  | .AddUniversal      lineNum extVars              => checkAddUniversal lineNum extVars
  | .ModifyExistential lineNum extExi depChanges    => checkModifyExistential lineNum extExi depChanges
  | .DeleteClause      lineNum extLits              => checkDeleteClause lineNum extLits
  | .UniversalReduction lineNum extLits             => checkUniversalReduction lineNum extLits
  | .RatClause         lineNum extLits              => checkRatClause lineNum extLits

/-- Check a single proof action (UR and RUP only).
    `AddUniversal`, `ModifyExistential`, and `DeleteClause` are not supported and throw.
    Returns `none` to continue, `some r` to stop. -/
def checkActionBasic (action : DQRatAction) : CheckM (Option ProofResult) :=
  match action with
  | .AddUniversal      lineNum _         => throw s!"line {lineNum}: universal addition is not supported in basic mode"
  | .ModifyExistential lineNum _ _       => throw s!"line {lineNum}: existential modification is not supported in basic mode"
  | .DeleteClause      lineNum _         => throw s!"line {lineNum}: deletion is not supported in basic mode"
  | .UniversalReduction lineNum extLits  => checkUniversalReductionBasic lineNum extLits
  | .RatClause         lineNum extLits   => checkRatClauseBasic lineNum extLits

/-- Restricted scaffold checker: supports `a`, `d`, full `u`, and positive-only `e`,
    while keeping clause-addition on the already-proved RUP-only path. -/
def checkActionNoNegE (action : DQRatAction) : CheckM (Option ProofResult) :=
  match action with
  | .AddUniversal       lineNum extVars    => checkAddUniversal lineNum extVars
  | .ModifyExistential  lineNum extExi ds  => checkModifyExistentialAddOnly lineNum extExi ds
  | .DeleteClause       lineNum extLits    => checkDeleteClause lineNum extLits
  | .UniversalReduction lineNum extLits    => checkUniversalReduction lineNum extLits
  | .RatClause          lineNum extLits    => checkRatClauseBasic lineNum extLits

-- ─── Action list checkers ──────────────────────────────────────────────────

/-- Check a list of proof actions (full DQRAT), returning the first decisive result or `Unknown`. -/
def checkActions : List DQRatAction → CheckM ProofResult
  | [] => pure .Unknown
  | action :: actions => do
      if let some r ← checkAction action then
        return r
      checkActions actions

/-- Check a list of proof actions (UR and RUP only; no DQRATE),
    returning the first decisive result or `Unknown`. -/
def checkActionsBasic : List DQRatAction → CheckM ProofResult
  | [] => pure .Unknown
  | action :: actions => do
      if let some r ← checkActionBasic action then
        return r
      checkActionsBasic actions

/-- Check a list of proof actions in the no-negative-`e` scaffold mode. -/
def checkActionsNoNegE : List DQRatAction → CheckM ProofResult
  | [] => pure .Unknown
  | action :: actions => do
      if let some r ← checkActionNoNegE action then
        return r
      checkActionsNoNegE actions
