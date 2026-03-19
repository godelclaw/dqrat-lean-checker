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
    if v == 0 || v > st.formula.maxVar then return false
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
def addClause (lits : Array Literal) : CheckM (Option CRef) := do
  -- Invalidate independence caches for universals appearing in dep-sets of existentials
  invalidateDepCaches lits
  -- Add to clause store
  modify fun st =>
    let (cs', _) := st.clauses.addClause lits
    { st with clauses := cs' }
  let st ← get
  let cref := st.clauses.clauses.size - 1  -- just-added clause index
  -- Handle empty clause
  if lits.isEmpty then return none
  -- Check under current assignment
  let sat := lits.any fun l =>
    let v := l.var
    v > 0 && v <= st.formula.maxVar &&
    st.isAssigned.getD (v - 1) false &&
    (st.value.getD (v - 1) false == l.isPos)
  if sat then return some cref
  let unassigned := lits.filter fun l =>
    let v := l.var
    v > 0 && v <= st.formula.maxVar &&
    !st.isAssigned.getD (v - 1) false
  if unassigned.isEmpty then
    return none  -- all literals false = conflict
  else if unassigned.size == 1 then
    enqueue (unassigned.getD 0 ⟨0⟩)
    let conflict ← propagate
    if conflict.isSome then return none
    else return some cref
  else
    return some cref

-- ─── DQRATE check ─────────────────────────────────────────────────────────

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

  let negPivot := pivot.negate
  let occPivot := st.clauses.getOcc negPivot

  -- For each clause containing ~pivot, check that negating outer lits gives conflict
  let blocker ← occPivot.foldlM (fun acc cref => do
    match acc with
    | some _ => return acc  -- already found a blocker
    | none =>
      let st ← get
      match st.clauses.getClauseRaw cref with
      | none => return none
      | some clause =>
        if clause.deleted then return none
        -- Negate outer lits of clause (outer w.r.t. exivar pivot.var)
        -- outer lit l ≠ ~pivot and isVarOuterOfExivar(var(l), var(pivot))
        let f := st.formula
        let isouter : Literal → Bool := fun l =>
          l != negPivot && f.isVarOuterOfExivar l.var pivot.var
        -- Opens decision level 2
        let gotConflict ← negateAndPropagate clause.lits isouter
        if gotConflict then
          backtrackBefore 2  -- keep level 1, remove level 2
          return none
        else
          backtrackBefore 2
          return some cref  -- RAT fails on this clause
  ) none

  backtrackBefore 1

  match blocker with
  | some c => return (false, some c)
  | none   => return (true, none)

-- ─── DQRATU check ─────────────────────────────────────────────────────────

-- DQRATU check: pivot must be universal; try RUP-without-pivot then RAT.
def checkDQRATU (lits : Array Literal) (pivot : Literal) : CheckM Bool := do
  -- ── RUP without pivot (opens decision level 1) ──
  let isRup ← negateAndPropagate lits (fun l => l != pivot)
  if isRup then
    backtrackBefore 1
    return true

  -- ── RAT for universal pivot ──
  let st ← get
  let negPivot := pivot.negate
  let occPivot := st.clauses.getOcc negPivot

  let isRat ← occPivot.foldlM (fun allOk cref => do
    if !allOk then return false
    let st ← get
    match st.clauses.getClauseRaw cref with
    | none => return true
    | some clause =>
      if clause.deleted then return true
      let f := st.formula
      let isouter : Literal → Bool := fun l =>
        l != negPivot && f.isVarOuterOfUnivar l.var pivot.var
      let gotConflict ← negateAndPropagate clause.lits isouter
      backtrackBefore 2
      return gotConflict
  ) true

  backtrackBefore 1
  return isRat
