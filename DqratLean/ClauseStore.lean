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

private def getClauseAt (cs : ClauseStore) (cref : CRef) : Option Clause :=
  if h : cref < cs.clauses.size then some cs.clauses[cref] else none

def getClause (cs : ClauseStore) (cref : CRef) : Option Clause :=
  if cref == CRef_Undef then none
  else getClauseAt cs cref |>.bind fun c => if c.deleted then none else some c

-- Get clause including deleted ones (for RAT check)
def getClauseRaw (cs : ClauseStore) (cref : CRef) : Option Clause :=
  if cref == CRef_Undef then none
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
    let occ' := arrayGrowTo occ (l.x + 1) #[]
    let arr  := occ'.getD l.x #[]
    arraySafeSet occ' l.x (arr.push cref)
  ) cs.occurrences
  ({ clauses := clauses', occurrences := occs' }, cref)

def deleteClause (cs : ClauseStore) (cref : CRef) : ClauseStore :=
  match getClauseAt cs cref with
  | none => cs
  | some c =>
    let c' : Clause := { lits := c.lits, deleted := true }
    { cs with clauses := arraySafeSet cs.clauses cref c' }

-- Swap literals at positions i and j inside a clause in the store
def swapLits (cs : ClauseStore) (cref : CRef) (i j : Nat) : ClauseStore :=
  match getClauseAt cs cref with
  | none => cs
  | some c =>
    if i < c.lits.size && j < c.lits.size then
      let li := c.lits.getD i ⟨0⟩
      let lj := c.lits.getD j ⟨0⟩
      let lits' := arraySafeSet (arraySafeSet c.lits i lj) j li
      let c' : Clause := { lits := lits', deleted := c.deleted }
      { cs with clauses := arraySafeSet cs.clauses cref c' }
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

end ClauseStore
