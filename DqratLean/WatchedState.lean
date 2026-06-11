import DqratLean.Types
import DqratLean.Formula
import DqratLean.ClauseStore
import DqratLean.CheckState

/-!
# Watched State

Runtime state and cache update operations for the watched-literal propagation
layer.

Trust status: experimental watched-layer executable infrastructure, outside the
certified default path.
-/
namespace DqratLean.Watched

/--
Runtime-oriented propagation state.

References for the design choices in this file live in:
`docs/watched_runtime_references.md`.

The intended proof story is:
- `clauses` is semantic state;
- `watchedBy` and `binaryImpBy` are cache layers;
- long clauses and binary clauses are accelerated separately.
-/
structure WatchEntry where
  cref : CRef
  blocker : Literal := mkLit 0 false

structure BinaryImpEntry where
  cref : CRef
  implied : Literal

structure CheckState where
  formula    : DQBF
  clauses    : ClauseStore
  isAssigned : Array Bool
  value      : Array Bool
  trail      : Array (Array Literal) := #[#[]]
  propQueue  : Array Literal := #[]
  indepKnown : Array Bool := #[]
  indepOf    : Array (Array Var) := #[]
  -- Long-clause watch cache with optional blocker literals.
  watchedBy  : Array (Array WatchEntry) := #[#[], #[]]
  -- Binary-clause fast path indexed by the literal set to true.
  binaryImpBy : Array (Array BinaryImpEntry) := #[#[], #[]]
  -- Live occurrence cache used by DQRATE/path traversals.
  liveOccBy  : Array (Array CRef) := #[#[], #[]]

abbrev CheckM := EStateM String CheckState

private def dummyLit : Literal := mkLit 0 false

def satisfied (st : CheckState) (l : Literal) : Bool :=
  let v := l.var
  v > 0 && v <= st.formula.maxVar &&
  st.isAssigned.getD (v - 1) false &&
  (st.value.getD (v - 1) false == l.isPos)

def assigned (st : CheckState) (v : Var) : Bool :=
  v > 0 && v <= st.formula.maxVar &&
  st.isAssigned.getD (v - 1) false

def newDecisionLevel : CheckM Unit :=
  modify fun st => { st with trail := st.trail.push #[] }

def backtrackBefore (level : Nat) : CheckM Unit :=
  modify fun st =>
    let rec clearLevels (tr : Array (Array Literal)) (ia : Array Bool) :
        Array (Array Literal) × Array Bool :=
      if tr.size <= level then (tr, ia)
      else
        let lvl := tr.getD (tr.size - 1) #[]
        let ia' := lvl.foldl (fun acc l =>
          let v := l.var
          if v > 0 then acc.setIfInBounds (v - 1) false else acc
        ) ia
        clearLevels tr.pop ia'
    termination_by tr.size
    let (trail', isAssigned') := clearLevels st.trail st.isAssigned
    { st with trail := trail', isAssigned := isAssigned', propQueue := #[] }

private def enqueueState (st : CheckState) (l : Literal) : CheckState :=
  let v := l.var
  if v = 0 || v > st.formula.maxVar then st
  else if v - 1 >= st.isAssigned.size then st
  else if st.isAssigned.getD (v - 1) false then st
  else
    let lastIdx := st.trail.size - 1
    let lastLevel := st.trail.getD lastIdx #[]
    { st with
      isAssigned := st.isAssigned.setIfInBounds (v - 1) true
      value      := st.value.setIfInBounds (v - 1) l.isPos
      trail      := st.trail.setIfInBounds lastIdx (lastLevel.push l)
      propQueue  := st.propQueue.push l
    }

def enqueue (l : Literal) : CheckM Unit :=
  modify fun st => enqueueState st l

private def setWatchListArray
    (watchedBy : Array (Array WatchEntry)) (l : Literal) (entries : Array WatchEntry) :
    Array (Array WatchEntry) :=
  let watchedBy' := watchedBy.rightpad (l.x + 1) #[]
  watchedBy'.setIfInBounds l.x entries

private def appendWatchArray
    (watchedBy : Array (Array WatchEntry)) (l : Literal) (entry : WatchEntry) :
    Array (Array WatchEntry) :=
  let watchedBy' := watchedBy.rightpad (l.x + 1) #[]
  let cur := watchedBy'.getD l.x #[]
  watchedBy'.setIfInBounds l.x (cur.push entry)

def appendWatch (l : Literal) (entry : WatchEntry) : CheckM Unit :=
  modify fun st => { st with watchedBy := appendWatchArray st.watchedBy l entry }

private def setWatchList (l : Literal) (entries : Array WatchEntry) : CheckM Unit :=
  modify fun st => { st with watchedBy := setWatchListArray st.watchedBy l entries }

private def watchList (st : CheckState) (l : Literal) : Array WatchEntry :=
  st.watchedBy.getD l.x #[]

/-- Proof-facing cache transition: add one live occurrence entry. -/
def appendLiveOccArray
    (liveOccBy : Array (Array CRef)) (l : Literal) (cref : CRef) :
    Array (Array CRef) :=
  let liveOccBy' := liveOccBy.rightpad (l.x + 1) #[]
  let cur := liveOccBy'.getD l.x #[]
  liveOccBy'.setIfInBounds l.x (cur.push cref)

/-- Proof-facing cache transition: remove one clause reference from a literal bucket. -/
def removeLiveOccArray
    (liveOccBy : Array (Array CRef)) (l : Literal) (cref : CRef) :
    Array (Array CRef) :=
  let liveOccBy' := liveOccBy.rightpad (l.x + 1) #[]
  let cur := liveOccBy'.getD l.x #[]
  liveOccBy'.setIfInBounds l.x (cur.filter fun old => old ≠ cref)

/-- Proof-facing cache transition: index a whole live clause. -/
def appendClauseLiveOccArray
    (liveOccBy : Array (Array CRef)) (lits : Array Literal) (cref : CRef) :
    Array (Array CRef) :=
  lits.foldl (fun occ lit => appendLiveOccArray occ lit cref) liveOccBy

/-- Proof-facing cache transition: remove a whole live clause from the cache. -/
def removeClauseLiveOccArray
    (liveOccBy : Array (Array CRef)) (lits : Array Literal) (cref : CRef) :
    Array (Array CRef) :=
  lits.foldl (fun occ lit => removeLiveOccArray occ lit cref) liveOccBy

def addClauseLiveOccs (lits : Array Literal) (cref : CRef) : CheckM Unit :=
  modify fun st => { st with liveOccBy := appendClauseLiveOccArray st.liveOccBy lits cref }

def removeClauseLiveOccs (lits : Array Literal) (cref : CRef) : CheckM Unit :=
  modify fun st => { st with liveOccBy := removeClauseLiveOccArray st.liveOccBy lits cref }

def getLiveOcc (st : CheckState) (l : Literal) : Array CRef :=
  st.liveOccBy.getD l.x #[]

def findSortedClauseLive (st : CheckState) (sortedLits : Array Literal) : Option CRef :=
  if sortedLits.isEmpty then none
  else
    let pivot := sortedLits.foldl (fun best l =>
      if (getLiveOcc st l).size < (getLiveOcc st best).size then l else best
    ) (sortedLits.getD 0 dummyLit)
    let pivotOccs := getLiveOcc st pivot
    pivotOccs.toList.findSome? fun cref =>
      match st.clauses.getClause cref with
      | none => none
      | some c =>
          if ClauseStore.sortLits c.lits = sortedLits then some cref
          else none

/-- Proof-facing cache transition: add one binary implication entry. -/
def appendBinaryImpArray
    (binaryImpBy : Array (Array BinaryImpEntry)) (l : Literal) (entry : BinaryImpEntry) :
    Array (Array BinaryImpEntry) :=
  let binaryImpBy' := binaryImpBy.rightpad (l.x + 1) #[]
  let cur := binaryImpBy'.getD l.x #[]
  binaryImpBy'.setIfInBounds l.x (cur.push entry)

/-- Proof-facing cache transition: replace one implication bucket. -/
def setBinaryImpListArray
    (binaryImpBy : Array (Array BinaryImpEntry)) (l : Literal) (entries : Array BinaryImpEntry) :
    Array (Array BinaryImpEntry) :=
  let binaryImpBy' := binaryImpBy.rightpad (l.x + 1) #[]
  binaryImpBy'.setIfInBounds l.x entries

def appendBinaryImp (l : Literal) (entry : BinaryImpEntry) : CheckM Unit :=
  modify fun st => { st with binaryImpBy := appendBinaryImpArray st.binaryImpBy l entry }

private def setBinaryImpList (l : Literal) (entries : Array BinaryImpEntry) : CheckM Unit :=
  modify fun st => { st with binaryImpBy := setBinaryImpListArray st.binaryImpBy l entries }

def getBinaryImp (st : CheckState) (l : Literal) : Array BinaryImpEntry :=
  st.binaryImpBy.getD l.x #[]

private def clauseIsWatchedByLiteral (clause : Clause) (l : Literal) : Bool :=
  ((clause.lits.size > 0) && clause.lits.getD 0 dummyLit == l) ||
  ((clause.lits.size > 1) && clause.lits.getD 1 dummyLit == l)

private def isDisabled (st : CheckState) (clause : Clause) : Bool :=
  clause.lits.any fun lit => satisfied st lit

private def findSatisfiedLiteral (st : CheckState) (clause : Clause) : Option Literal :=
  clause.lits.find? fun lit => satisfied st lit

private def otherWatchedLiteral (clause : Clause) (watcher : Literal) : Literal :=
  if clause.lits.size > 0 && clause.lits.getD 0 dummyLit == watcher then
    clause.lits.getD 1 dummyLit
  else
    clause.lits.getD 0 dummyLit

private def blockerForWatcher (st : CheckState) (clause : Clause) (watcher : Literal) : Literal :=
  match findSatisfiedLiteral st clause with
  | some lit => lit
  | none => otherWatchedLiteral clause watcher

private def findUnassignedFrom
    (st : CheckState) (lits : Array Literal) (start : Nat) : Option Nat :=
  Id.run do
    let mut i := start
    while i < lits.size do
      let lit := lits.getD i dummyLit
      if !assigned st lit.var then
        return some i
      i := i + 1
    return none

private def swapClauseLits (cref : CRef) (i j : Nat) : CheckM Clause := do
  modify fun st => { st with clauses := st.clauses.swapLits cref i j }
  let st ← get
  match st.clauses.getClauseRaw cref with
  | some clause => return clause
  | none => return Clause.dummy

def updateWatchedLiterals (cref : CRef) : CheckM (Bool × Bool) := do
  let st ← get
  match st.clauses.getClauseRaw cref with
  | none => return (true, true)
  | some clause0 =>
      if clause0.deleted then
        return (true, true)
      if isDisabled st clause0 then
        return (true, false)
      if clause0.lits.size < 2 then
        if clause0.lits.isEmpty then
          return (false, false)
        else
          let lit0 := clause0.lits.getD 0 dummyLit
          return (!assigned st lit0.var, false)
      let mut clause := clause0
      let mut watcherChanged := false
      let st0 ← get
      if !assigned st0 (clause.lits.getD 1 dummyLit).var then
        clause ← swapClauseLits cref 0 1
      let st1 ← get
      if assigned st1 (clause.lits.getD 0 dummyLit).var then
        match findUnassignedFrom st1 clause.lits 2 with
        | some i =>
            clause ← swapClauseLits cref 0 i
            appendWatch (clause.lits.getD 0 dummyLit)
              { cref := cref, blocker := clause.lits.getD 1 dummyLit }
            watcherChanged := true
        | none =>
            return (false, watcherChanged)
      let st2 ← get
      if assigned st2 (clause.lits.getD 1 dummyLit).var then
        match findUnassignedFrom st2 clause.lits 2 with
        | some i =>
            clause ← swapClauseLits cref 1 i
            appendWatch (clause.lits.getD 1 dummyLit)
              { cref := cref, blocker := clause.lits.getD 0 dummyLit }
            watcherChanged := true
        | none =>
            let st3 ← get
            if assigned st3 (clause.lits.getD 1 dummyLit).var then
              enqueue (clause.lits.getD 0 dummyLit)
      return (true, watcherChanged)

/--
Propagate binary clauses through a direct implication cache.

This intentionally mirrors the standard solver split where size-2 clauses can be
handled without entering the long-clause watched-literal path.

See `docs/watched_runtime_references.md` for source notes.
-/
private def propagateBinaryImplications (l : Literal) : CheckM (Option CRef) := do
  let st ← get
  let entries := getBinaryImp st l
  let mut kept : Array BinaryImpEntry := #[]
  let mut sawDeadEntry := false
  let mut conflict : Option CRef := none
  let mut pos := 0
  for entry in entries do
    let stNow ← get
    match stNow.clauses.getClauseRaw entry.cref with
    | none =>
        if !sawDeadEntry then
          sawDeadEntry := true
          kept := (entries.toList.take pos).toArray
    | some clause =>
        if clause.deleted then
          if !sawDeadEntry then
            sawDeadEntry := true
            kept := (entries.toList.take pos).toArray
        else
          if sawDeadEntry then
            kept := kept.push entry
          if conflict.isNone then
            if satisfied stNow entry.implied then
              pure ()
            else if satisfied stNow entry.implied.negate then
              conflict := some entry.cref
            else
              enqueue entry.implied
    pos := pos + 1
  if sawDeadEntry then
    -- Keep direct-implication lists trimmed as clauses disappear, following the
    -- same "cache maintenance matters" principle used in modern implication
    -- graph implementations. See `docs/watched_runtime_references.md`.
    setBinaryImpList l kept
  return conflict

def propagateOne (l : Literal) : CheckM (Option CRef) := do
  let binaryConflict ← propagateBinaryImplications l
  if binaryConflict.isSome then
    return binaryConflict
  let watcher := l.negate
  let st ← get
  let records := watchList st watcher
  let mut kept : Array WatchEntry := #[]
  let mut remainder : Array WatchEntry := #[]
  let mut conflict : Option CRef := none
  let mut pos := 0
  let mut done := false
  while !done do
    if pos < records.size then
      let entry := records.getD pos { cref := CRef_Undef, blocker := dummyLit }
      let cref := entry.cref
      let stNow ← get
      if satisfied stNow entry.blocker then
        kept := kept.push entry
        pos := pos + 1
      else match stNow.clauses.getClauseRaw cref with
      | none =>
          pos := pos + 1
      | some clause =>
          if clause.deleted || !clauseIsWatchedByLiteral clause watcher then
            pos := pos + 1
          else
            let (ok, watcherChanged) ← updateWatchedLiterals cref
            if !ok then
              conflict := some cref
              remainder := (records.toList.drop pos).toArray
              done := true
            else
              if !watcherChanged then
                let stAfter ← get
                match stAfter.clauses.getClauseRaw cref with
                | none =>
                    pure ()
                | some clauseAfter =>
                    kept := kept.push
                      { cref := cref
                        blocker := blockerForWatcher stAfter clauseAfter watcher }
              pos := pos + 1
    else
      done := true
  let finalList :=
    match conflict with
    | some _ => kept ++ remainder
    | none => kept
  setWatchList watcher finalList
  return conflict

def propagate : CheckM (Option CRef) := do
  let mut conflict : Option CRef := none
  let mut done := false
  while !done do
    let st ← get
    if conflict.isSome || st.propQueue.isEmpty then
      done := true
    else
      let l := st.propQueue.getD (st.propQueue.size - 1) dummyLit
      set { st with propQueue := st.propQueue.pop }
      conflict ← propagateOne l
  return conflict

def getReachable (st : CheckState) (l : Literal) : Array Bool :=
  let numLits := st.formula.maxVar * 2 + 2
  let lvar := l.var
  if st.formula.isVarExistential lvar then
    (List.replicate numLits true).toArray
  else
    Id.run do
      let negL := l.negate
      let mut reachable := (List.replicate numLits false).toArray
      let mut explored := (List.replicate numLits false).toArray
      let mut worklist : Array Literal := #[l]
      while !worklist.isEmpty do
        let cur := worklist.getD (worklist.size - 1) dummyLit
        worklist := worklist.pop
        let idx := cur.x
        if explored.getD idx false then
          pure ()
        else
          explored := explored.setIfInBounds idx true
          let occs := getLiveOcc st cur
          for cref in occs do
            match st.clauses.getClauseRaw cref with
            | none => pure ()
            | some clause =>
                if clause.deleted || clause.lits.contains negL then
                  pure ()
                else
                  for lit in clause.lits do
                    if lit = cur || explored.getD lit.negate.x false then
                      pure ()
                    else
                      let litvar := lit.var
                      if st.formula.isVarExistential litvar then
                        let depset := st.formula.depset.getD litvar #[]
                        if depset.contains lvar then
                          worklist := worklist.push lit.negate
                          reachable := reachable.setIfInBounds lit.x true
      return reachable

def makeIndepUnknown (univar : Var) : CheckM Unit := do
  if univar = 0 then return ()
  modify fun st =>
    { st with
      indepKnown := st.indepKnown.setIfInBounds (univar - 1) false
      indepOf    := st.indepOf.setIfInBounds (univar - 1) #[]
    }

def computeDeps (v : Var) : CheckM Unit := do
  let st ← get
  if st.formula.isVarExistential v then return ()
  let reachPos := getReachable st (mkLit v true)
  let reachNeg := getReachable st (mkLit v false)
  let indep := st.formula.exivars.filter fun xvar =>
    if xvar <= v then false
    else
      let xNeg := xvar * 2
      let xPos := xvar * 2 + 1
      !((reachPos.getD xNeg false && reachNeg.getD xPos false) ||
        (reachPos.getD xPos false && reachNeg.getD xNeg false))
  modify fun s =>
    { s with
      indepKnown := s.indepKnown.setIfInBounds (v - 1) true
      indepOf    := s.indepOf.setIfInBounds (v - 1) indep
    }

def notDependsOn (exiVar univar : Var) : CheckM Bool := do
  computeDeps univar
  let st ← get
  let indep := st.indepOf.getD (univar - 1) #[]
  return indep.contains exiVar

def invalidateDepCaches (lits : Array Literal) : CheckM Unit := do
  let st ← get
  for l in lits do
    let v := l.var
    if v > 0 && st.formula.isVarExistential v then
      let deps := st.formula.depset.getD v #[]
      for u in deps do
        makeIndepUnknown u

def addVarForall (ext : Nat) : CheckM Var := do
  let st ← get
  let v := st.formula.maxVar + 1
  let f := { st.formula with
    maxVar        := v
    internalName  := st.formula.internalName.push (ext, v)
    externalName  := st.formula.externalName.push ext
    isExistential := st.formula.isExistential.push false
    univars       := st.formula.univars.push v
    depset        := st.formula.depset.push #[]
  }
  set { st with
    formula    := f
    isAssigned := st.isAssigned.push false
    value      := st.value.push false
    indepKnown := st.indepKnown.push false
    indepOf    := st.indepOf.push #[]
    watchedBy  := (st.watchedBy.push (#[] : Array WatchEntry)).push (#[] : Array WatchEntry)
    binaryImpBy := (st.binaryImpBy.push (#[] : Array BinaryImpEntry)).push (#[] : Array BinaryImpEntry)
    liveOccBy  := (st.liveOccBy.push (#[] : Array CRef)).push (#[] : Array CRef)
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
    watchedBy  := (st.watchedBy.push (#[] : Array WatchEntry)).push (#[] : Array WatchEntry)
    binaryImpBy := (st.binaryImpBy.push (#[] : Array BinaryImpEntry)).push (#[] : Array BinaryImpEntry)
    liveOccBy  := (st.liveOccBy.push (#[] : Array CRef)).push (#[] : Array CRef)
  }
  for u in deps do
    makeIndepUnknown u
  return v

def resetPropagationState : CheckM Unit := do
  let st ← get
  let n := st.formula.maxVar
  set { st with
    isAssigned := Array.replicate n false
    value      := Array.replicate n false
    trail      := #[#[]]
    propQueue  := #[] }

def addDependency (of_ on_ : Var) : CheckM Unit := do
  let st ← get
  if !st.formula.isVarExistential of_ then return ()
  if st.formula.isVarExistential on_ then return ()
  let deps := st.formula.depset.getD of_ #[]
  if deps.contains on_ then return ()
  modify fun s => { s with
    formula := s.formula.addDependencyFormula of_ on_
  }
  makeIndepUnknown on_

def addDependencyReset (of_ on_ : Var) : CheckM Unit := do
  addDependency of_ on_
  resetPropagationState

def delDependency (of_ on_ : Var) : CheckM Bool := do
  let st ← get
  if !st.formula.isVarExistential of_ then return true
  if st.formula.isVarExistential on_ then return true
  let allowed ← notDependsOn of_ on_
  if allowed then
    modify fun s => { s with
      formula := s.formula.forceDelDep of_ on_
    }
    makeIndepUnknown on_
    return true
  else
    return false

def delDependencyReset (of_ on_ : Var) : CheckM Bool := do
  let ok ← delDependency of_ on_
  if ok then
    resetPropagationState
    return true
  else
    return false

def CheckState.empty : CheckState :=
  { formula    := {}
    clauses    := {}
    isAssigned := #[]
    value      := #[]
    trail      := #[#[]]
    propQueue  := #[]
    indepKnown := #[]
    indepOf    := #[]
    watchedBy  := #[#[], #[]]
    binaryImpBy := #[#[], #[]]
    liveOccBy  := #[#[], #[]]
  }

/-- Drop watched-runtime caches to the theorem-backed abstract checker state. -/
def CheckState.toBase (st : CheckState) : _root_.CheckState :=
  { formula    := st.formula
    clauses    := st.clauses
    isAssigned := st.isAssigned
    value      := st.value
    trail      := st.trail
    propQueue  := st.propQueue
    indepKnown := st.indepKnown
    indepOf    := st.indepOf
  }

theorem CheckState.toBase_empty :
    CheckState.empty.toBase = _root_.CheckState.empty := by
  rfl

end DqratLean.Watched
