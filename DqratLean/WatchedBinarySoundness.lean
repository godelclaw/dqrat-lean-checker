import DqratLean.WatchedBinaryLemmas

namespace DqratLean.Watched

/--
`binaryImpBy` is a lazy runtime cache: each entry records one implication edge
coming from a live or recently deleted binary clause. This file proves only the
soundness direction first, which is enough to justify propagation through the
cache while we defer the completeness/refinement side to a later layer.
-/
def BinaryImpMatches (l : Literal) (entry : BinaryImpEntry) (c : Clause) : Prop :=
  c.lits.size = 2 ∧
    ((c.lits.getD 0 (mkLit 0 false) = l.negate ∧
        c.lits.getD 1 (mkLit 0 false) = entry.implied) ∨
      (c.lits.getD 1 (mkLit 0 false) = l.negate ∧
        c.lits.getD 0 (mkLit 0 false) = entry.implied))

def BinaryImpSound (st : CheckState) : Prop :=
  ∀ ⦃l : Literal⦄ ⦃entry : BinaryImpEntry⦄,
    entry ∈ getBinaryImp st l →
    ∃ c : Clause, st.clauses.getClauseRaw entry.cref = some c ∧ BinaryImpMatches l entry c

private theorem getClauseRaw_some_imp_lt (cs : ClauseStore) (cref : CRef) (c : Clause)
    (h : cs.getClauseRaw cref = some c) : cref < cs.clauses.size := by
  unfold ClauseStore.getClauseRaw at h
  by_cases hne : cref = CRef_Undef
  · simp [hne] at h
  · simp [hne, ClauseStore.getClauseAt] at h
    rcases h with ⟨hlt, _⟩
    exact hlt

private theorem binaryImpMatches_markDeleted
    {l : Literal} {entry : BinaryImpEntry} {c : Clause}
    (h : BinaryImpMatches l entry c) :
    BinaryImpMatches l entry { c with deleted := true } := by
  simpa [BinaryImpMatches] using h

theorem binaryImpSound_empty : BinaryImpSound CheckState.empty := by
  intro l entry hmem
  cases hx : l.x with
  | zero =>
      simp [CheckState.empty, getBinaryImp, hx] at hmem
  | succ n =>
      cases n with
      | zero =>
          simp [CheckState.empty, getBinaryImp, hx] at hmem
      | succ n' =>
          simp [CheckState.empty, getBinaryImp, hx] at hmem

theorem binaryImpSound_addNonbinaryClause
    {st : CheckState} (hsound : BinaryImpSound st) (lits : Array Literal) :
    BinaryImpSound (addNonbinaryClauseState st lits) := by
  intro l entry hmem
  have hold : entry ∈ getBinaryImp st l := by
    simpa [addNonbinaryClauseState, getBinaryImp] using hmem
  rcases hsound hold with ⟨c, hgetRaw, hmatch⟩
  have hlt : entry.cref < st.clauses.clauses.size :=
    getClauseRaw_some_imp_lt st.clauses entry.cref c hgetRaw
  refine ⟨c, ?_, hmatch⟩
  simpa [addNonbinaryClauseState] using
    (ClauseStore.getClauseRaw_addClause_lt st.clauses lits entry.cref hlt).trans hgetRaw

theorem binaryImpSound_addBinaryClause
    {st : CheckState} (hsound : BinaryImpSound st)
    (hpos : 0 < st.clauses.clauses.size) (lits : Array Literal)
    (lit0 lit1 : Literal)
    (hbin : lits.size = 2)
    (hLit0 : lits.getD 0 (mkLit 0 false) = lit0)
    (hLit1 : lits.getD 1 (mkLit 0 false) = lit1) :
    BinaryImpSound (addBinaryClauseState st lits lit0 lit1) := by
  intro l entry hmem
  have hcases :=
    (mem_addBinaryClauseCache_iff st.binaryImpBy lit0 lit1 l st.clauses.clauses.size entry).mp <|
      by simpa [addBinaryClauseState, getBinaryImp] using hmem
  rcases hcases with hOld | hNew | hNew
  · rcases hsound hOld with ⟨c, hgetRaw, hmatch⟩
    have hlt : entry.cref < st.clauses.clauses.size :=
      getClauseRaw_some_imp_lt st.clauses entry.cref c hgetRaw
    refine ⟨c, ?_, hmatch⟩
    simpa [addBinaryClauseState] using
      (ClauseStore.getClauseRaw_addClause_lt st.clauses lits entry.cref hlt).trans hgetRaw
  · rcases hNew with ⟨rfl, htarget⟩
    subst htarget
    refine ⟨{ lits := lits, deleted := false }, ?_, ?_⟩
    · exact ClauseStore.getClauseRaw_addClause_new st.clauses lits hpos
    · refine ⟨hbin, Or.inl ?_⟩
      constructor
      · simp [hLit0, negate_negate]
      · simp [hLit1]
  · rcases hNew with ⟨rfl, htarget⟩
    subst htarget
    refine ⟨{ lits := lits, deleted := false }, ?_, ?_⟩
    · exact ClauseStore.getClauseRaw_addClause_new st.clauses lits hpos
    · refine ⟨hbin, Or.inr ?_⟩
      constructor
      · simp [hLit1, negate_negate]
      · simp [hLit0]

theorem binaryImpSound_addClause
    {st : CheckState} (hsound : BinaryImpSound st)
    (hpos : 0 < st.clauses.clauses.size) (lits : Array Literal) :
    BinaryImpSound
      (if lits.size = 2 then
        addBinaryClauseState st lits (lits.getD 0 (mkLit 0 false)) (lits.getD 1 (mkLit 0 false))
      else
        addNonbinaryClauseState st lits) := by
  by_cases hbin : lits.size = 2
  · let lit0 := lits.getD 0 (mkLit 0 false)
    let lit1 := lits.getD 1 (mkLit 0 false)
    simpa [hbin, lit0, lit1, addBinaryClauseState] using
      (binaryImpSound_addBinaryClause (st := st) hsound hpos lits lit0 lit1 hbin rfl rfl)
  · simpa [hbin] using
      (binaryImpSound_addNonbinaryClause (st := st) hsound lits)

theorem binaryImpSound_deleteClause
    {st : CheckState} (hsound : BinaryImpSound st)
    (cref : CRef) :
    let clauses' := st.clauses.deleteClause cref
    let st' := { st with clauses := clauses' }
    BinaryImpSound st' := by
  dsimp
  intro l entry hmem
  have hold : entry ∈ getBinaryImp st l := by
    simpa [getBinaryImp] using hmem
  rcases hsound hold with ⟨c', hgetRaw, hmatch⟩
  by_cases hsame : entry.cref = cref
  · have hgetRaw' : st.clauses.getClauseRaw cref = some c' := by
      simpa [hsame] using hgetRaw
    have hlt : cref < st.clauses.clauses.size :=
      getClauseRaw_some_imp_lt st.clauses cref c' hgetRaw'
    refine ⟨{ c' with deleted := true }, ?_, binaryImpMatches_markDeleted hmatch⟩
    have hdel :
        (st.clauses.deleteClause cref).getClauseRaw cref = some { c' with deleted := true } := by
      rw [ClauseStore.getClauseRaw_deleteClause_eq st.clauses cref hlt, hgetRaw']
      rfl
    simpa [hsame] using hdel
  · refine ⟨c', ?_, hmatch⟩
    rw [ClauseStore.getClauseRaw_deleteClause_ne st.clauses cref entry.cref hsame]
    exact hgetRaw

end DqratLean.Watched
