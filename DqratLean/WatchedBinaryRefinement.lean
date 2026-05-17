import DqratLean.WatchedBinarySoundness

namespace DqratLean.Watched

/--
Completeness direction for the binary implication cache: every live binary
clause contributes both direct implication edges. Together with
`BinaryImpSound`, this gives the refinement invariant for `binaryImpBy`.
-/
def BinaryImpComplete (st : CheckState) : Prop :=
  ∀ ⦃cref : CRef⦄ ⦃c : Clause⦄ ⦃lit0 lit1 : Literal⦄,
    st.clauses.getClause cref = some c →
    c.lits.size = 2 →
    c.lits.getD 0 (mkLit 0 false) = lit0 →
    c.lits.getD 1 (mkLit 0 false) = lit1 →
    { cref := cref, implied := lit1 } ∈ getBinaryImp st lit0.negate ∧
      { cref := cref, implied := lit0 } ∈ getBinaryImp st lit1.negate

def BinaryImpInvariant (st : CheckState) : Prop :=
  BinaryImpSound st ∧ BinaryImpComplete st

theorem binaryImpComplete_empty : BinaryImpComplete CheckState.empty := by
  intro cref c lit0 lit1 hget hsize h0 h1
  cases cref with
  | zero =>
      simp [ClauseStore.getClause, CRef_Undef] at hget
  | succ n =>
      simp [CheckState.empty, ClauseStore.getClause, ClauseStore.getClauseAt, CRef_Undef] at hget

theorem binaryImpComplete_addNonbinaryClause
    {st : CheckState} (hcomplete : BinaryImpComplete st)
    (hpos : 0 < st.clauses.clauses.size) (lits : Array Literal)
    (hbin : lits.size ≠ 2) :
    BinaryImpComplete (addNonbinaryClauseState st lits) := by
  intro cref c lit0 lit1 hget hsize h0 h1
  by_cases hnew : cref = st.clauses.clauses.size
  · subst hnew
    have hc : c = { lits := lits, deleted := false } := by
      have hgetNew :
          (addNonbinaryClauseState st lits).clauses.getClause st.clauses.clauses.size =
            some { lits := lits, deleted := false } := by
        simpa [addNonbinaryClauseState] using
          ClauseStore.getClause_addClause_new st.clauses lits hpos
      rw [hgetNew] at hget
      cases hget
      rfl
    subst hc
    exfalso
    exact hbin (by simpa using hsize)
  · have hlt : cref < st.clauses.clauses.size := by
      have hlt' :=
        ClauseStore.getClause_some_imp_lt (cs := (st.clauses.addClause lits).1) (cref := cref)
          (c := c) hget
      have hltSucc : cref < st.clauses.clauses.size + 1 := by
        simpa [ClauseStore.addClause] using hlt'
      have hle : cref ≤ st.clauses.clauses.size := Nat.le_of_lt_succ hltSucc
      exact Nat.lt_of_le_of_ne hle hnew
    have hgetOld : st.clauses.getClause cref = some c := by
      have hgetEq :
          (addNonbinaryClauseState st lits).clauses.getClause cref = st.clauses.getClause cref := by
        simpa [addNonbinaryClauseState] using
          ClauseStore.getClause_addClause_lt st.clauses lits cref hlt
      rw [hgetEq] at hget
      exact hget
    simpa [getBinaryImp] using hcomplete hgetOld hsize h0 h1


set_option maxHeartbeats 400000 in
theorem binaryImpComplete_deleteClause
    {st : CheckState} (hcomplete : BinaryImpComplete st)
    (cref : CRef) :
    let clauses' := st.clauses.deleteClause cref
    let st' := { st with clauses := clauses' }
    BinaryImpComplete st' := by
  dsimp
  intro cref' c' lit0 lit1 hget' hsize h0 h1
  have hne : cref' ≠ cref := by
    intro heq
    subst cref'
    have hlt : cref < st.clauses.clauses.size := by
      have hlt' :=
        ClauseStore.getClause_some_imp_lt (cs := st.clauses.deleteClause cref)
          (cref := cref) (c := c') hget'
      simpa [ClauseStore.deleteClause_clauses_size] using hlt'
    rw [ClauseStore.getClause_deleteClause_eq st.clauses cref hlt] at hget'
    simp at hget'
  have hgetOld : st.clauses.getClause cref' = some c' := by
    rw [ClauseStore.getClause_deleteClause_ne st.clauses cref cref' hne] at hget'
    exact hget'
  simpa [getBinaryImp] using hcomplete hgetOld hsize h0 h1

theorem binaryImpInvariant_empty : BinaryImpInvariant CheckState.empty := by
  exact ⟨binaryImpSound_empty, binaryImpComplete_empty⟩

theorem binaryImpInvariant_deleteClause
    {st : CheckState} (hinv : BinaryImpInvariant st)
    (cref : CRef) :
    let clauses' := st.clauses.deleteClause cref
    let st' := { st with clauses := clauses' }
    BinaryImpInvariant st' := by
  rcases hinv with ⟨hsound, hcomplete⟩
  exact ⟨binaryImpSound_deleteClause hsound cref, binaryImpComplete_deleteClause hcomplete cref⟩

end DqratLean.Watched
