import Init.Data.Array.Perm
import Init.Data.List.Sort.Lemmas
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

/-- Canonical literal ordering used for clause lookup proofs. -/
def sortLits (lits : Array Literal) : Array Literal :=
  (lits.toList.mergeSort (fun a b => a.x <= b.x)).toArray

theorem sortLits_perm (lits : Array Literal) :
    Array.Perm (sortLits lits) lits := by
  unfold sortLits
  exact List.Perm.toArray (List.mergeSort_perm lits.toList _)

theorem mem_sortLits {lits : Array Literal} {l : Literal} :
    l ∈ sortLits lits ↔ l ∈ lits := by
  unfold sortLits
  simp

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

/-- One-way completeness for live-clause occurrences:
    every live clause literal is indexed in the corresponding occurrence list. -/
def LiveOccurrencesComplete (cs : ClauseStore) : Prop :=
  ∀ {cref : CRef} {c : Clause} {l : Literal},
    cs.getClause cref = some c →
    l ∈ c.lits.toList →
    cref ∈ cs.getOcc l

/-- Transport `LiveOccurrencesComplete` across definitional equality. -/
theorem liveOccurrencesComplete_congr {cs cs' : ClauseStore}
    (h : cs = cs') (hocc : LiveOccurrencesComplete cs) :
    LiveOccurrencesComplete cs' := by
  subst h
  exact hocc

/-- Accessor lemma for `LiveOccurrencesComplete`. -/
theorem mem_getOcc_of_liveOccurrencesComplete
    {cs : ClauseStore} (hocc : LiveOccurrencesComplete cs)
    {cref : CRef} {c : Clause} {l : Literal}
    (hget : cs.getClause cref = some c)
    (hmem : l ∈ c.lits.toList) :
    cref ∈ cs.getOcc l :=
  hocc hget hmem

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

-- Find a clause with exactly the given sorted literals (via pivot = fewest occurrences).
-- The store may contain clauses in unsorted order, so compare against its canonical form.
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
      match getClause cs cref with
      | none => none
      | some c =>
        if sortLits c.lits = sortedLits then some cref
        else none

private theorem arraySetIfInBounds_getD_eq
    {α : Type} (a : Array α) (i : Nat) (v fallback : α) (h : i < a.size) :
    (a.setIfInBounds i v).getD i fallback = v := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD, dif_pos (hsize ▸ h)]
  simp [Array.getElem_setIfInBounds h]

private theorem arraySetIfInBounds_getD_ne
    {α : Type} (a : Array α) (i j : Nat) (v fallback : α) (hij : i ≠ j) :
    (a.setIfInBounds i v).getD j fallback = a.getD j fallback := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD]
  rcases Nat.lt_or_ge j a.size with hjlt | hjge
  · rw [dif_pos (hsize ▸ hjlt), dif_pos hjlt]
    exact Array.getElem_setIfInBounds_ne hjlt hij
  · have hjlt' : ¬ j < a.size := Nat.not_lt.mpr hjge
    rw [dif_neg (hsize ▸ hjlt'), dif_neg hjlt']

private theorem getD_rightpad_eq_of_lt
    {α : Type} (a : Array α) (n : Nat) (x fallback : α) {i : Nat}
    (hi : i < a.size) :
    (a.rightpad n x).getD i fallback = a.getD i fallback := by
  have hlt : i < (a ++ Array.replicate (n - a.size) x).size := by
    exact Nat.lt_of_lt_of_le hi (by simp)
  rw [Array.getD, Array.getD, Array.rightpad, dif_pos hlt, dif_pos hi]
  simpa using
    (Array.getElem_append_left' (xs := a) (i := i) hi (Array.replicate (n - a.size) x)).symm

private theorem mem_getD_imp_lt_size
    {α : Type} {a : Array (Array α)} {i : Nat} {x : α}
    (hmem : x ∈ a.getD i #[]) :
    i < a.size := by
  by_cases hi : i < a.size
  · exact hi
  · simp [Array.getD, hi] at hmem

private def extendOccurrences (occ : Array (Array CRef)) (l : Literal) (cref : CRef) :
    Array (Array CRef) :=
  let occ' := occ.rightpad (l.x + 1) #[]
  let arr := occ'.getD l.x #[]
  occ'.setIfInBounds l.x (arr.push cref)

private theorem mem_extendOccurrences_preserved
    (occ : Array (Array CRef)) (l : Literal) (newCref cref : CRef) {target : Literal}
    (hmem : cref ∈ occ.getD target.x #[]) :
    cref ∈ (extendOccurrences occ l newCref).getD target.x #[] := by
  unfold extendOccurrences
  by_cases hsame : target.x = l.x
  · have htarget : target.x < occ.size := mem_getD_imp_lt_size hmem
    have hright :
        (occ.rightpad (l.x + 1) #[]).getD target.x #[] = occ.getD target.x #[] := by
      exact getD_rightpad_eq_of_lt occ (l.x + 1) #[] #[] htarget
    have hlt : l.x < (occ.rightpad (l.x + 1) #[]).size := by
      rw [Array.size_rightpad]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    rw [hsame, arraySetIfInBounds_getD_eq
      (a := occ.rightpad (l.x + 1) #[]) (i := l.x)
      (v := ((occ.rightpad (l.x + 1) #[]).getD l.x #[]).push newCref) (fallback := #[]) hlt]
    rw [hsame] at hright
    have hmem' : cref ∈ occ.getD l.x #[] := by simpa [hsame] using hmem
    exact Array.mem_push.mpr (Or.inl (hright ▸ hmem'))
  · rw [arraySetIfInBounds_getD_ne
      (a := occ.rightpad (l.x + 1) #[]) (i := l.x) (j := target.x)
      (v := ((occ.rightpad (l.x + 1) #[]).getD l.x #[]).push newCref)
      (fallback := #[]) (fun h => hsame h.symm)]
    have htarget : target.x < occ.size := mem_getD_imp_lt_size hmem
    rw [getD_rightpad_eq_of_lt occ (l.x + 1) #[] #[] htarget]
    exact hmem

private theorem mem_extendOccurrences_self
    (occ : Array (Array CRef)) (l : Literal) (newCref : CRef) :
    newCref ∈ (extendOccurrences occ l newCref).getD l.x #[] := by
  unfold extendOccurrences
  have hlt : l.x < (occ.rightpad (l.x + 1) #[]).size := by
    rw [Array.size_rightpad]
    have : l.x < l.x + 1 := Nat.lt_succ_self _
    omega
  rw [arraySetIfInBounds_getD_eq
    (a := occ.rightpad (l.x + 1) #[]) (i := l.x)
    (v := ((occ.rightpad (l.x + 1) #[]).getD l.x #[]).push newCref) (fallback := #[]) hlt]
  exact Array.mem_push.mpr (Or.inr rfl)

private theorem mem_foldExtendOccurrences_preserved
    (occ : Array (Array CRef)) (lits : Array Literal) (newCref cref : CRef) {target : Literal}
    (hmem : cref ∈ occ.getD target.x #[]) :
    cref ∈
      (lits.foldl (fun occ l =>
        let occ' := occ.rightpad (l.x + 1) #[]
        let arr := occ'.getD l.x #[]
        occ'.setIfInBounds l.x (arr.push newCref)) occ).getD target.x #[] := by
  let f := fun (occ : Array (Array CRef)) (l : Literal) =>
    let occ' := occ.rightpad (l.x + 1) #[]
    let arr := occ'.getD l.x #[]
    occ'.setIfInBounds l.x (arr.push newCref)
  have hlistAux :
      ∀ (ls : List Literal) (occ : Array (Array CRef)),
        cref ∈ occ.getD target.x #[] →
        cref ∈ (ls.foldl f occ).getD target.x #[] := by
    intro ls
    induction ls with
    | nil =>
        intro occ hmem
        simpa using hmem
    | cons l ls ih =>
        intro occ hmem
        have hmem' : cref ∈ (extendOccurrences occ l newCref).getD target.x #[] :=
          mem_extendOccurrences_preserved occ l newCref cref hmem
        simpa [f, extendOccurrences] using ih (extendOccurrences occ l newCref) hmem'
  have hlist :
      cref ∈ (lits.toList.foldl f occ).getD target.x #[] := by
    exact hlistAux lits.toList occ hmem
  simpa [f, Array.foldl_toList] using hlist

private theorem mem_foldExtendOccurrences_self
    (occ : Array (Array CRef)) (lits : Array Literal) (newCref : CRef) {target : Literal}
    (hmem : target ∈ lits.toList) :
    newCref ∈
      (lits.foldl (fun occ l =>
        let occ' := occ.rightpad (l.x + 1) #[]
        let arr := occ'.getD l.x #[]
        occ'.setIfInBounds l.x (arr.push newCref)) occ).getD target.x #[] := by
  let f := fun (occ : Array (Array CRef)) (l : Literal) =>
    let occ' := occ.rightpad (l.x + 1) #[]
    let arr := occ'.getD l.x #[]
    occ'.setIfInBounds l.x (arr.push newCref)
  have hlistAux :
      ∀ (ls : List Literal) (occ : Array (Array CRef)),
        target ∈ ls →
        newCref ∈ (ls.foldl f occ).getD target.x #[] := by
    intro ls
    induction ls with
    | nil =>
        intro occ hmem
        cases hmem
    | cons l ls ih =>
        intro occ hmem
        have hsplit : target = l ∨ target ∈ ls := by simpa using hmem
        cases hsplit with
        | inl hEq =>
            subst hEq
            simpa [List.foldl_cons, f, extendOccurrences] using
              mem_foldExtendOccurrences_preserved
              (occ := extendOccurrences occ target newCref) (lits := ls.toArray)
              (newCref := newCref) (cref := newCref)
              (target := target) (mem_extendOccurrences_self occ target newCref)
        | inr htail =>
            simpa [f, extendOccurrences] using ih (extendOccurrences occ l newCref) htail
  have hlist :
      newCref ∈ (lits.toList.foldl f occ).getD target.x #[] := by
    exact hlistAux lits.toList occ hmem
  simpa [f, Array.foldl_toList] using hlist

theorem findSortedClause_spec {cs : ClauseStore} {sortedLits : Array Literal} {cref : CRef}
    (hfind : cs.findSortedClause sortedLits = some cref) :
    ∃ c, getClause cs cref = some c ∧ sortLits c.lits = sortedLits := by
  unfold findSortedClause at hfind
  split at hfind
  · simp at hfind
  · simp only [Array.findSome?_eq_some_iff] at hfind
    rcases hfind with ⟨_, cref', _, _, hstep, _⟩
    cases hget : getClause cs cref' with
    | none =>
        simp [hget] at hstep
    | some c =>
        simp [hget] at hstep
        rcases hstep with ⟨hsorted, hcref⟩
        subst hcref
        exact ⟨c, hget, hsorted⟩

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

/-- `getClauseRaw` for existing indices is unchanged after `addClause`. -/
theorem getClauseRaw_addClause_lt (cs : ClauseStore) (lits : Array Literal) (cref' : CRef)
    (hlt : cref' < cs.clauses.size) :
    (cs.addClause lits).1.getClauseRaw cref' = cs.getClauseRaw cref' := by
  unfold getClauseRaw
  by_cases h0 : cref' = CRef_Undef
  · simp [h0]
  · simp [h0, getClauseAt, addClause, hlt, Nat.lt_succ_of_lt hlt, Array.getElem_push_lt hlt]

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

/-- `getClauseRaw` for the newly added clause at its cref (= old size). -/
theorem getClauseRaw_addClause_new (cs : ClauseStore) (lits : Array Literal)
    (hpos : 0 < cs.clauses.size) :
    (cs.addClause lits).1.getClauseRaw cs.clauses.size =
    some { lits := lits, deleted := false } := by
  unfold getClauseRaw getClauseAt
  have hne : cs.clauses.size ≠ CRef_Undef := Nat.pos_iff_ne_zero.mp hpos
  simp [addClause, if_neg hne, Array.getElem_push_eq]

/-- The empty clause store trivially satisfies live-occurrence completeness. -/
theorem liveOccurrencesComplete_empty :
    LiveOccurrencesComplete ({ clauses := #[Clause.dummy], occurrences := #[#[], #[]] } : ClauseStore) := by
  intro cref c l hget hmem
  have hlt : cref < 1 := by
    simpa using getClause_some_imp_lt
      (cs := ({ clauses := #[Clause.dummy], occurrences := #[#[], #[]] } : ClauseStore))
      (cref := cref) (c := c) hget
  have hne : cref ≠ 0 := by
    simpa using getClause_some_imp_ne_undef
      (cs := ({ clauses := #[Clause.dummy], occurrences := #[#[], #[]] } : ClauseStore))
      (cref := cref) (c := c) hget
  cases cref with
  | zero => exact False.elim (hne rfl)
  | succ n => simp at hlt

/-- Adding a clause preserves one-way completeness of the live occurrence lists. -/
theorem liveOccurrencesComplete_addClause
    {cs : ClauseStore} (hpos : 0 < cs.clauses.size)
    (hocc : LiveOccurrencesComplete cs) (lits : Array Literal) :
    LiveOccurrencesComplete (cs.addClause lits).1 := by
  intro cref c l hget hmem
  by_cases hnew : cref = cs.clauses.size
  · subst hnew
    have hgetNew := getClause_addClause_new cs lits hpos
    have hc : c = { lits := lits, deleted := false } := by
      rw [hgetNew] at hget
      cases hget
      rfl
    subst hc
    simpa [addClause, getOcc] using
      mem_foldExtendOccurrences_self cs.occurrences lits cs.clauses.size hmem
  · have hlt : cref < cs.clauses.size := by
      have hlt' := getClause_some_imp_lt (cs := (cs.addClause lits).1) (cref := cref) (c := c) hget
      have hle : cref ≤ cs.clauses.size := by
        have hlt'' : cref < cs.clauses.size + 1 := by
          simpa [addClause] using hlt'
        exact Nat.le_of_lt_succ hlt''
      exact Nat.lt_of_le_of_ne hle hnew
    have hold : cs.getClause cref = some c := by
      rw [getClause_addClause_lt cs lits cref hlt] at hget
      exact hget
    have hmemOld : cref ∈ cs.getOcc l := hocc hold hmem
    simpa [addClause, getOcc] using
      mem_foldExtendOccurrences_preserved cs.occurrences lits cs.clauses.size cref hmemOld

/-- Deleting a clause preserves live-occurrence completeness for the remaining live clauses. -/
theorem liveOccurrencesComplete_deleteClause
    {cs : ClauseStore} (hocc : LiveOccurrencesComplete cs) (cref : CRef) :
    LiveOccurrencesComplete (cs.deleteClause cref) := by
  intro cref' c l hget hmem
  have hne : cref' ≠ cref := by
    intro heq
    subst heq
    have hlt : cref' < cs.clauses.size := by
      have hlt' := getClause_some_imp_lt (cs := cs.deleteClause cref') (cref := cref') (c := c) hget
      simpa [deleteClause_clauses_size] using hlt'
    rw [getClause_deleteClause_eq cs cref' hlt] at hget
    simp at hget
  have hold : cs.getClause cref' = some c := by
    rw [getClause_deleteClause_ne cs cref cref' hne] at hget
    exact hget
  cases hca : getClauseAt cs cref <;> simpa [deleteClause, getOcc, hca] using hocc hold hmem

/-- `getClauseRaw cref'` is unchanged after `deleteClause cref` when `cref' ≠ cref`. -/
theorem getClauseRaw_deleteClause_ne (cs : ClauseStore) (cref cref' : CRef) (h : cref' ≠ cref) :
    (cs.deleteClause cref).getClauseRaw cref' = cs.getClauseRaw cref' := by
  unfold getClauseRaw
  by_cases h0 : cref' = CRef_Undef
  · simp [h0]
  · simp only [if_neg h0]
    simp only [deleteClause]
    cases hca : getClauseAt cs cref with
    | none => rfl
    | some c =>
        simp [getClauseAt_clauses_update_ne cs cref cref' h]

/-- After `deleteClause cref`, `getClauseRaw cref` returns the clause marked deleted. -/
theorem getClauseRaw_deleteClause_eq (cs : ClauseStore) (cref : CRef) (hsize : cref < cs.clauses.size) :
    (cs.deleteClause cref).getClauseRaw cref =
    (cs.getClauseRaw cref).map fun c => { c with deleted := true } := by
  unfold getClauseRaw
  by_cases h0 : cref = CRef_Undef
  · simp [h0]
  · simp only [if_neg h0]
    have hca : getClauseAt cs cref = some cs.clauses[cref] := by
      simp [getClauseAt, hsize]
    rw [deleteClause, hca]
    unfold getClauseAt
    simp [hsize, Array.getElem_setIfInBounds hsize]

end ClauseStore
