import DqratLean.Types
import DqratLean.Formula
import DqratLean.ClauseStore

-- Combined checker state
structure CheckState where
  formula    : DQBF
  clauses    : ClauseStore
  -- Assignment arrays indexed by (var - 1)
  isAssigned : Array Bool         -- is variable assigned?
  value      : Array Bool         -- assigned value (meaningful if isAssigned)
  -- Trail: decision levels; each level is a list of literals assigned at that level
  trail      : Array (Array Literal) := #[#[]]  -- start with level 0
  -- Propagation queue (LIFO)
  propQueue  : Array Literal := #[]
  -- Independence cache indexed by (univar - 1)
  indepKnown : Array Bool := #[]
  indepOf    : Array (Array Var) := #[]   -- existential vars independent of this univar

abbrev CheckM := StateT CheckState (Except String)

-- ─── Assignment helpers ────────────────────────────────────────────────────

def satisfied (st : CheckState) (l : Literal) : Bool :=
  let v := l.var
  v > 0 && v <= st.formula.maxVar &&
  st.isAssigned.getD (v - 1) false &&
  (st.value.getD (v - 1) false == l.isPos)

def isAssigned (st : CheckState) (v : Var) : Bool :=
  v > 0 && v <= st.formula.maxVar &&
  st.isAssigned.getD (v - 1) false

-- ─── Trail / decision level management ────────────────────────────────────

def newDecisionLevel : CheckM Unit :=
  modify fun st => { st with trail := st.trail.push #[] }

def backtrackBefore (level : Nat) : CheckM Unit :=
  modify fun st =>
    let rec clearLevels : Nat → Array (Array Literal) → Array Bool → (Array (Array Literal) × Array Bool)
      | 0, tr, ia => (tr, ia)
      | n + 1, tr, ia =>
        if tr.size <= level then (tr, ia)
        else
          let lvl := tr.getD (tr.size - 1) #[]
          let ia' := lvl.foldl (fun acc l =>
            let v := l.var
            if v > 0 then acc.setIfInBounds (v - 1) false else acc
          ) ia
          clearLevels n tr.pop ia'
    let (trail', isAssigned') := clearLevels (st.trail.size + 1) st.trail st.isAssigned
    { st with trail := trail', isAssigned := isAssigned', propQueue := #[] }

-- ─── Enqueue ───────────────────────────────────────────────────────────────

def enqueue (l : Literal) : CheckM Unit := do
  let st ← get
  let v := l.var
  if v = 0 || v > st.formula.maxVar then return ()
  if st.isAssigned.getD (v - 1) false then return ()
  let lastIdx := st.trail.size - 1
  let lastLevel := st.trail.getD lastIdx #[]
  set { st with
    isAssigned := st.isAssigned.setIfInBounds (v - 1) true
    value      := st.value.setIfInBounds      (v - 1) l.isPos
    trail      := st.trail.setIfInBounds      lastIdx (lastLevel.push l)
    propQueue  := st.propQueue.push l
  }

-- ─── Occurrence-list unit propagation ─────────────────────────────────────

-- Process one propagated literal: check all clauses containing its negation
-- Returns Some cref on conflict, None on success
def propagateOne (l : Literal) : CheckM (Option CRef) := do
  let negL := l.negate
  let st ← get
  let occs := st.clauses.getOcc negL
  occs.foldlM (fun acc cref => do
    match acc with
    | some _ => return acc
    | none =>
      let st ← get
      match st.clauses.getClause cref with
      | none => return none  -- deleted or invalid
      | some clause =>
        -- Check if clause is satisfied
        let sat := clause.lits.any fun lit =>
          let v := lit.var
          v > 0 && v <= st.formula.maxVar &&
          st.isAssigned.getD (v - 1) false &&
          (st.value.getD (v - 1) false == lit.isPos)
        if sat then return none
        -- Find unassigned literals
        let unassigned := clause.lits.filter fun lit =>
          let v := lit.var
          v > 0 && v <= st.formula.maxVar &&
          !st.isAssigned.getD (v - 1) false
        if unassigned.isEmpty then
          return some cref  -- all literals false = conflict
        else if unassigned.size = 1 then
          enqueue (unassigned.getD 0 ⟨0⟩)
          return none
        else
          return none
  ) none

def propagateAux : Nat → CheckM (Option CRef)
  | 0 => return none
  | n + 1 => do
    let st ← get
    if st.propQueue.isEmpty then return none
    let l := st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩
    modify fun s => { s with propQueue := s.propQueue.pop }
    let result ← propagateOne l
    match result with
    | some c => return some c
    | none   => propagateAux n

def propagate : CheckM (Option CRef) := do
  let st ← get
  -- fuel: each literal can be enqueued at most once per variable
  propagateAux (st.formula.maxVar * 2 + 100)

-- ─── BFS reachability for D^∀-pure dep scheme ─────────────────────────────

-- Compute reachable literals starting from literal l (for universal l).
-- reachable[lit.x] = true if lit can be reached via u-pure paths in clauses.
def getReachable (st : CheckState) (l : Literal) : Array Bool :=
  let numLits := st.formula.maxVar * 2 + 2
  let lvar    := l.var
  -- Only meaningful for universal l
  if st.formula.isVarExistential lvar then
    (List.replicate numLits true).toArray  -- existential: all reachable (conservative)
  else
    let negL   := l.negate
    let reachable := (List.replicate numLits false).toArray
    let explored  := (List.replicate numLits false).toArray
    -- BFS/DFS with fuel
    let fuel := numLits + 2
    let rec go : Nat → Array Literal → Array Bool → Array Bool → Array Bool
      | 0, _, reach, _ => reach
      | f + 1, worklist, reach, expl =>
        if worklist.isEmpty then reach
        else
          let cur  := worklist.getD (worklist.size - 1) ⟨0⟩
          let wl'  := worklist.pop
          let idx  := cur.x
          if expl.getD idx false then
            go f wl' reach expl
          else
            let expl' := expl.setIfInBounds idx true
            -- Process each clause containing cur
            let occs := st.clauses.getOcc cur
            let (wl'', reach') := occs.foldl (fun (wl, rch) cref =>
              match st.clauses.getClauseRaw cref with
              | none => (wl, rch)
              | some clause =>
                if clause.deleted then (wl, rch)
                -- Skip if clause contains ~l (not u-pure)
                else if clause.lits.contains negL then (wl, rch)
                else
                  clause.lits.foldl (fun (wl2, rch2) lit =>
                    if lit = cur then (wl2, rch2)
                    else if expl'.getD lit.negate.x false then (wl2, rch2)
                    else
                      let litvar   := lit.var
                      let litIsExi := st.formula.isVarExistential litvar
                      let depset   := st.formula.depset.getD litvar #[]
                      -- lit's variable must depend on lvar
                      let dependsOnL := depset.contains lvar
                      -- Push ~lit if lit is existential and depends on lvar
                      let wl3 := if litIsExi && dependsOnL then wl2.push lit.negate else wl2
                      -- Mark lit reachable if it is existential and depends on lvar
                      let rch3 := if litIsExi && dependsOnL then
                        rch2.setIfInBounds lit.x true else rch2
                      (wl3, rch3)
                  ) (wl, rch)
            ) (wl', reach)
            go f wl'' reach' expl'
    go fuel #[l] reachable explored

-- ─── Independence cache management ────────────────────────────────────────

def makeIndepUnknown (univar : Var) : CheckM Unit :=
  if univar = 0 then return ()
  else modify fun st =>
    { st with
      indepKnown := st.indepKnown.setIfInBounds (univar - 1) false
      indepOf    := st.indepOf.setIfInBounds    (univar - 1) #[]
    }

-- Compute and cache independence for universal var v
def computeDeps (v : Var) : CheckM Unit := do
  let st ← get
  if st.formula.isVarExistential v then return ()  -- only for universals
  let reachPos := getReachable st (mkLit v true)
  let reachNeg := getReachable st (mkLit v false)
  -- Collect existential vars with internal index > v that are independent
  let indep := st.formula.exivars.filter fun xvar =>
    if xvar <= v then false
    else
      let xNeg := xvar * 2      -- negative literal index
      let xPos := xvar * 2 + 1  -- positive literal index
      -- dependent if there's a path from pos(v) to neg(xvar) and neg(v) to pos(xvar)
      --          or from pos(v) to pos(xvar) and neg(v) to neg(xvar)
      -- independent = NOT dependent
      !((reachPos.getD xNeg false && reachNeg.getD xPos false) ||
        (reachPos.getD xPos false && reachNeg.getD xNeg false))
  modify fun s =>
    { s with
      indepKnown := s.indepKnown.setIfInBounds (v - 1) true
      indepOf    := s.indepOf.setIfInBounds    (v - 1) indep
    }

-- Check if existential exiVar does NOT depend on universal univar
-- (using and lazily computing the independence cache)
def notDependsOn (exiVar univar : Var) : CheckM Bool := do
  let st ← get
  let idx := univar - 1
  if !st.indepKnown.getD idx false then
    computeDeps univar
  let st ← get
  let indep := st.indepOf.getD idx #[]
  return indep.contains exiVar

-- Invalidate independence cache for all universals in dep-union of exi vars in clause
def invalidateDepCaches (lits : Array Literal) : CheckM Unit := do
  let st ← get
  for l in lits do
    let v := l.var
    if v > 0 && st.formula.isVarExistential v then
      let deps := st.formula.depset.getD v #[]
      for u in deps do
        makeIndepUnknown u

-- ─── Variable addition (updates all state arrays) ─────────────────────────

def addVarForall (ext : Nat) : CheckM Var := do
  let st ← get
  let v := st.formula.maxVar + 1
  let f := { st.formula with
    maxVar       := v
    internalName := st.formula.internalName.push (ext, v)
    externalName := st.formula.externalName.push ext
    isExistential := st.formula.isExistential.push false
    univars      := st.formula.univars.push v
    depset       := st.formula.depset.push #[]
  }
  set { st with
    formula    := f
    isAssigned := st.isAssigned.push false
    value      := st.value.push false
    indepKnown := st.indepKnown.push false
    indepOf    := st.indepOf.push #[]
  }
  return v

def addVarExists (ext : Nat) (deps : Array Var) : CheckM Var := do
  let st ← get
  let v := st.formula.maxVar + 1
  let f := { st.formula with
    maxVar        := v
    internalName  := st.formula.internalName.push (ext, v)
    externalName  := st.formula.externalName.push ext
    isExistential := st.formula.isExistential.push true
    exivars       := st.formula.exivars.push v
    depset        := st.formula.depset.push deps
  }
  set { st with
    formula    := f
    isAssigned := st.isAssigned.push false
    value      := st.value.push false
    indepKnown := st.indepKnown.push false
    indepOf    := st.indepOf.push #[]
  }
  -- Invalidate independence cache for each universal in the initial dep set
  for u in deps do
    makeIndepUnknown u
  return v

-- Add a dependency: existential of_ now depends on universal on_
-- Matches C++ addDependency behavior (no-op if on_ is existential)
def addDependency (of_ on_ : Var) : CheckM Unit := do
  let st ← get
  if !st.formula.isVarExistential of_ then return ()
  if st.formula.isVarExistential on_ then return ()  -- C++ bug: no-op
  let deps := st.formula.depset.getD of_ #[]
  if deps.contains on_ then return ()  -- already there
  let deps' := deps.push on_
  modify fun s => { s with
    formula := { s.formula with depset := s.formula.depset.setIfInBounds of_ deps' }
  }
  -- NOTE: C++ addDependency does NOT call makeIndependenciesUnknown here

-- Delete a dependency after checking via dep scheme
-- Returns false (in Except) if deletion not allowed
def delDependency (of_ on_ : Var) : CheckM Bool := do
  let st ← get
  if !st.formula.isVarExistential of_ then return true
  let allowed ← notDependsOn of_ on_
  if allowed then
    modify fun s => { s with
      formula := s.formula.forceDelDep of_ on_
    }
    return true
  else
    return false

-- ─── Initial CheckState ────────────────────────────────────────────────────

def CheckState.empty : CheckState :=
  { formula    := {}
    clauses    := {}
    isAssigned := #[]
    value      := #[]
    trail      := #[#[]]
    propQueue  := #[]
    indepKnown := #[]
    indepOf    := #[]
  }
