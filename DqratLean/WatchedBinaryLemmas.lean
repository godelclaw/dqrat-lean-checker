import DqratLean.WatchedArrayLemmas
import DqratLean.WatchedState

/-!
# Watched Binary Lemmas

Auxiliary lemmas for the watched binary-implication cache and its update
operations.

Trust status: experimental watched-layer support, outside the certified default
path.
-/
namespace DqratLean.Watched

/--
Shared helper facts for the binary implication cache.

The binary cache is maintained by explicit append operations, so the proof layer
benefits from dedicated membership lemmas and named post-states.
-/
theorem negate_negate (l : Literal) : l.negate.negate = l := by
  cases l
  simp [Literal.negate, Nat.xor_assoc]

theorem mem_appendBinaryImpArray_iff
    (binaryImpBy : Array (Array BinaryImpEntry)) (l target : Literal)
    (newEntry entry : BinaryImpEntry) :
    entry ∈ (appendBinaryImpArray binaryImpBy l newEntry).getD target.x #[] ↔
      entry ∈ binaryImpBy.getD target.x #[] ∨ (entry = newEntry ∧ target = l) := by
  unfold appendBinaryImpArray
  by_cases hsame : target.x = l.x
  · have htarget : target = l := lit_eq_of_x_eq hsame
    have hlt : l.x < (binaryImpBy.rightpad (l.x + 1) #[]).size := by
      rw [Array.size_rightpad]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    have hright :
        (binaryImpBy.rightpad (l.x + 1) #[]).getD l.x #[] = binaryImpBy.getD l.x #[] := by
      simpa [hsame] using getD_rightpad_eq binaryImpBy (l.x + 1) #[] target.x
    rw [hsame, arraySetIfInBounds_getD_eq
      (a := binaryImpBy.rightpad (l.x + 1) #[]) (i := l.x)
      (v := ((binaryImpBy.rightpad (l.x + 1) #[]).getD l.x #[]).push newEntry)
      (fallback := #[]) hlt]
    rw [Array.mem_push, hright]
    simp [htarget]
  · have hne : target ≠ l := by
      intro hEq
      exact hsame (by simp [hEq])
    have hright :
        (binaryImpBy.rightpad (l.x + 1) #[]).getD target.x #[] = binaryImpBy.getD target.x #[] := by
      exact getD_rightpad_eq binaryImpBy (l.x + 1) #[] target.x
    rw [arraySetIfInBounds_getD_ne
      (a := binaryImpBy.rightpad (l.x + 1) #[]) (i := l.x) (j := target.x)
      (v := ((binaryImpBy.rightpad (l.x + 1) #[]).getD l.x #[]).push newEntry)
      (fallback := #[]) (fun h => hsame h.symm)]
    rw [hright]
    simp [hne]

theorem mem_addBinaryClauseCache_iff
    (binaryImpBy : Array (Array BinaryImpEntry)) (lit0 lit1 target : Literal)
    (cref : CRef) (entry : BinaryImpEntry) :
    entry ∈ (addBinaryClauseCache binaryImpBy lit0 lit1 cref).getD target.x #[] ↔
      entry ∈ binaryImpBy.getD target.x #[] ∨
        (entry = { cref := cref, implied := lit1 } ∧ target = lit0.negate) ∨
        (entry = { cref := cref, implied := lit0 } ∧ target = lit1.negate) := by
  unfold addBinaryClauseCache
  rw [mem_appendBinaryImpArray_iff
    (binaryImpBy := appendBinaryImpArray binaryImpBy lit0.negate { cref := cref, implied := lit1 })
    (l := lit1.negate) (target := target) (newEntry := { cref := cref, implied := lit0 })
    (entry := entry)]
  constructor
  · intro h
    rcases h with h | h
    · have h' :=
        (mem_appendBinaryImpArray_iff
          (binaryImpBy := binaryImpBy) (l := lit0.negate) (target := target)
          (newEntry := { cref := cref, implied := lit1 }) (entry := entry)).mp h
      rcases h' with hOld | hNew
      · exact Or.inl hOld
      · exact Or.inr (Or.inl hNew)
    · exact Or.inr (Or.inr h)
  · intro h
    rcases h with hOld | hNew
    · exact Or.inl <|
        (mem_appendBinaryImpArray_iff
          (binaryImpBy := binaryImpBy) (l := lit0.negate) (target := target)
          (newEntry := { cref := cref, implied := lit1 }) (entry := entry)).mpr (Or.inl hOld)
    · rcases hNew with hNew | hNew
      · exact Or.inl <|
          (mem_appendBinaryImpArray_iff
            (binaryImpBy := binaryImpBy) (l := lit0.negate) (target := target)
            (newEntry := { cref := cref, implied := lit1 }) (entry := entry)).mpr (Or.inr hNew)
      · exact Or.inr hNew

def addNonbinaryClauseState (st : CheckState) (lits : Array Literal) : CheckState :=
  { st with clauses := (st.clauses.addClause lits).1 }

def addBinaryClauseState
    (st : CheckState) (lits : Array Literal) (lit0 lit1 : Literal) : CheckState :=
  { st with
    clauses := (st.clauses.addClause lits).1
    binaryImpBy := addBinaryClauseCache st.binaryImpBy lit0 lit1 st.clauses.clauses.size
  }

@[simp] theorem getBinaryImp_addNonbinaryClauseState
    (st : CheckState) (lits : Array Literal) (l : Literal) :
    getBinaryImp (addNonbinaryClauseState st lits) l = st.binaryImpBy.getD l.x #[] := rfl

end DqratLean.Watched
