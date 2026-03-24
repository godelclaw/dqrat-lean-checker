import DqratLean.Types

-- Clause storage with occurrence lists
structure Clause where
  lits    : Array Literal
  deleted : Bool := false

def Clause.dummy : Clause := { lits := #[], deleted := false }

structure ClauseStore where
  -- index 0 is dummy (CRef_Undef = 0); real clauses start at index 1
  clauses     : Array Clause := #[Clause.dummy]
  -- occurrence lists indexed by literal.x
  occurrences : Array (Array CRef) := #[#[], #[]]

namespace ClauseStore

def getClauseAt (cs : ClauseStore) (cref : CRef) : Option Clause :=
  if h : cref < cs.clauses.size then some cs.clauses[cref] else none

def getClause (cs : ClauseStore) (cref : CRef) : Option Clause :=
  if cref = CRef_Undef then none
  else getClauseAt cs cref |>.bind fun c => if c.deleted then none else some c

-- Get clause including deleted ones (for RAT check)
def getClauseRaw (cs : ClauseStore) (cref : CRef) : Option Clause :=
  if cref = CRef_Undef then none
  else getClauseAt cs cref

def getOcc (cs : ClauseStore) (l : Literal) : Array CRef :=
  cs.occurrences.getD l.x #[]

-- Add a clause; returns updated store and the new CRef
def addClause (cs : ClauseStore) (lits : Array Literal) : ClauseStore × CRef :=
  let cref := cs.clauses.size  -- new clause goes at this index
  let newClause : Clause := { lits := lits, deleted := false }
  let clauses' := cs.clauses.push newClause
  -- Add cref to occurrence list of each literal
  let occs' := lits.foldl (fun occ l =>
    let occ' := occ.rightpad (l.x + 1) #[]
    let arr  := occ'.getD l.x #[]
    occ'.setIfInBounds l.x (arr.push cref)
  ) cs.occurrences
  ({ clauses := clauses', occurrences := occs' }, cref)

def deleteClause (cs : ClauseStore) (cref : CRef) : ClauseStore :=
  match getClauseAt cs cref with
  | none => cs
  | some c =>
    let c' : Clause := { lits := c.lits, deleted := true }
    { cs with clauses := cs.clauses.setIfInBounds cref c' }

-- Swap literals at positions i and j inside a clause in the store
def swapLits (cs : ClauseStore) (cref : CRef) (i j : Nat) : ClauseStore :=
  match getClauseAt cs cref with
  | none => cs
  | some c =>
    if i < c.lits.size && j < c.lits.size then
      let li := c.lits.getD i ⟨0⟩
      let lj := c.lits.getD j ⟨0⟩
      let lits' := (c.lits.setIfInBounds i lj).setIfInBounds j li
      let c' : Clause := { lits := lits', deleted := c.deleted }
      { cs with clauses := cs.clauses.setIfInBounds cref c' }
    else cs

-- Find a clause with exactly the given sorted literals (via pivot = fewest occurrences)
def findSortedClause (cs : ClauseStore) (sortedLits : Array Literal) : Option CRef :=
  if sortedLits.isEmpty then none
  else
    -- Find literal with fewest occurrences as pivot
    let pivot := sortedLits.foldl (fun best l =>
      if (cs.getOcc l).size < (cs.getOcc best).size then l else best
    ) (sortedLits.getD 0 ⟨0⟩)
    let pivotOccs := cs.getOcc pivot
    -- Search for matching clause
    pivotOccs.findSome? fun cref =>
      match getClauseAt cs cref with
      | none => none
      | some c =>
        if c.deleted then none
        else if c.lits.size != sortedLits.size then none
        else if c.lits.all (fun lit => sortedLits.contains lit) then some cref
        else none

-- ─── Soundness helper lemmas ────────────────────────────────────────────────

/-- `deleteClause` preserves the size of the clause array. -/
theorem deleteClause_clauses_size (cs : ClauseStore) (cref : CRef) :
    (cs.deleteClause cref).clauses.size = cs.clauses.size := by
  simp only [deleteClause, getClauseAt]
  split
  · rfl                                        -- none: deleteClause returns cs unchanged
  · exact Array.size_setIfInBounds              -- some: setIfInBounds preserves size

-- Internal helper: updating `clauses` at `cref` via `setIfInBounds` does not affect
-- `getClauseAt` at a different index `cref'`.
theorem getClauseAt_clauses_update_ne (cs : ClauseStore) (cref cref' : CRef)
    (h : cref' ≠ cref) (c' : Clause) :
    getClauseAt { cs with clauses := cs.clauses.setIfInBounds cref c' } cref' =
    getClauseAt cs cref' := by
  simp only [getClauseAt, Array.size_setIfInBounds]
  split
  next hlt' =>
    congr 1
    exact Array.getElem_setIfInBounds_ne hlt' (Ne.symm h)
  · rfl

/-- `getClause cref'` is unchanged after `deleteClause cref` when `cref' ≠ cref`. -/
theorem getClause_deleteClause_ne (cs : ClauseStore) (cref cref' : CRef) (h : cref' ≠ cref) :
    (cs.deleteClause cref).getClause cref' = cs.getClause cref' := by
  simp only [deleteClause]
  cases hca : getClauseAt cs cref with
  | none => rfl
  | some c =>
    simp only [getClause, getClauseAt_clauses_update_ne cs cref cref' h]

/-- After `deleteClause cref`, `getClause cref` returns `none` (clause is marked deleted). -/
theorem getClause_deleteClause_eq (cs : ClauseStore) (cref : CRef) (hsize : cref < cs.clauses.size) :
    (cs.deleteClause cref).getClause cref = none := by
  by_cases h0 : cref = CRef_Undef
  · simp [getClause, h0]
  · simp only [deleteClause, getClauseAt, hsize, ↓reduceDIte]
    simp only [getClause, if_neg h0]
    simp only [getClauseAt, Array.size_setIfInBounds, hsize, ↓reduceDIte]
    simp [Array.getElem_setIfInBounds hsize]

/-- `getClause` for existing indices is unchanged after `addClause`. -/
theorem getClause_addClause_lt (cs : ClauseStore) (lits : Array Literal) (cref' : CRef)
    (hlt : cref' < cs.clauses.size) :
    (cs.addClause lits).1.getClause cref' = cs.getClause cref' := by
  simp only [addClause, getClause, getClauseAt, Array.size_push, Array.getElem_push_lt hlt]
  have h1 : cref' < cs.clauses.size + 1 := Nat.lt_succ_of_lt hlt
  simp only [h1, ↓reduceDIte, hlt]

/-- getClause returning Some implies cref is in bounds. -/
theorem getClause_some_imp_lt (cs : ClauseStore) (cref : CRef) (c : Clause)
    (h : cs.getClause cref = some c) : cref < cs.clauses.size := by
  unfold getClause at h
  by_cases hne : cref = CRef_Undef
  · simp [hne] at h
  · simp only [if_neg hne] at h
    unfold getClauseAt at h
    by_cases hlt : cref < cs.clauses.size
    · exact hlt
    · simp [hlt] at h

/-- getClause returning Some implies cref ≠ CRef_Undef. -/
theorem getClause_some_imp_ne_undef (cs : ClauseStore) (cref : CRef) (c : Clause)
    (h : cs.getClause cref = some c) : cref ≠ CRef_Undef := by
  intro heq
  simp [getClause, if_pos heq] at h

/-- getClause for the newly added clause at its cref (= old size). -/
theorem getClause_addClause_new (cs : ClauseStore) (lits : Array Literal)
    (hpos : 0 < cs.clauses.size) :
    (cs.addClause lits).1.getClause cs.clauses.size =
    some { lits := lits, deleted := false } := by
  simp only [addClause, getClause, getClauseAt, Array.size_push]
  have hne : cs.clauses.size ≠ CRef_Undef := Nat.pos_iff_ne_zero.mp hpos
  simp only [if_neg hne, Nat.lt_succ_self, ↓reduceDIte]
  simp [Array.getElem_push_eq]

end ClauseStore
