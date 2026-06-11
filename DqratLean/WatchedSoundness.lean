import DqratLean.WatchedArrayLemmas
import DqratLean.WatchedState

namespace DqratLean.Watched

def LiveOccSound (st : CheckState) : Prop :=
  ∀ ⦃l : Literal⦄ ⦃cref : CRef⦄,
    cref ∈ getLiveOcc st l →
    ∃ c : Clause, st.clauses.getClause cref = some c ∧ l ∈ c.lits.toList

def LiveOccComplete (st : CheckState) : Prop :=
  ∀ ⦃cref : CRef⦄ ⦃c : Clause⦄ ⦃l : Literal⦄,
    st.clauses.getClause cref = some c →
    l ∈ c.lits.toList →
    cref ∈ getLiveOcc st l

def LiveOccInvariant (st : CheckState) : Prop :=
  LiveOccSound st ∧ LiveOccComplete st

private theorem mem_appendLiveOccArray_iff
    (liveOccBy : Array (Array CRef)) (l target : Literal) (newCref cref : CRef) :
    cref ∈ (appendLiveOccArray liveOccBy l newCref).getD target.x #[] ↔
      cref ∈ liveOccBy.getD target.x #[] ∨ (cref = newCref ∧ target = l) := by
  unfold appendLiveOccArray
  by_cases hsame : target.x = l.x
  · have htarget : target = l := lit_eq_of_x_eq hsame
    have hlt : l.x < (liveOccBy.rightpad (l.x + 1) #[]).size := by
      rw [Array.size_rightpad]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    have hright :
        (liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[] = liveOccBy.getD l.x #[] := by
      simpa [hsame] using getD_rightpad_eq liveOccBy (l.x + 1) #[] target.x
    rw [hsame, arraySetIfInBounds_getD_eq
      (a := liveOccBy.rightpad (l.x + 1) #[]) (i := l.x)
      (v := ((liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[]).push newCref)
      (fallback := #[]) hlt]
    rw [Array.mem_push]
    rw [hright]
    simp [htarget]
  · have hne : target ≠ l := by
      intro hEq
      exact hsame (by simp [hEq])
    have hright :
        (liveOccBy.rightpad (l.x + 1) #[]).getD target.x #[] = liveOccBy.getD target.x #[] := by
      exact getD_rightpad_eq liveOccBy (l.x + 1) #[] target.x
    rw [arraySetIfInBounds_getD_ne
      (a := liveOccBy.rightpad (l.x + 1) #[]) (i := l.x) (j := target.x)
      (v := ((liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[]).push newCref)
      (fallback := #[]) (fun h => hsame h.symm)]
    rw [hright]
    simp [hne]

private theorem mem_removeLiveOccArray_imp_old
    (liveOccBy : Array (Array CRef)) (l target : Literal) (removed cref : CRef) :
    cref ∈ (removeLiveOccArray liveOccBy l removed).getD target.x #[] →
      cref ∈ liveOccBy.getD target.x #[] := by
  intro hmem
  unfold removeLiveOccArray at hmem
  by_cases hsame : target.x = l.x
  · have hlt : l.x < (liveOccBy.rightpad (l.x + 1) #[]).size := by
      rw [Array.size_rightpad]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    have hright :
        (liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[] = liveOccBy.getD l.x #[] := by
      simpa [hsame] using getD_rightpad_eq liveOccBy (l.x + 1) #[] target.x
    rw [hsame, arraySetIfInBounds_getD_eq
      (a := liveOccBy.rightpad (l.x + 1) #[]) (i := l.x)
      (v := ((liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[]).filter fun old => old ≠ removed)
      (fallback := #[]) hlt] at hmem
    have hmem' :
        cref ∈ (liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[] :=
      (Array.mem_filter.mp hmem).1
    rw [hright] at hmem'
    simpa [hsame] using hmem'
  · rw [arraySetIfInBounds_getD_ne
      (a := liveOccBy.rightpad (l.x + 1) #[]) (i := l.x) (j := target.x)
      (v := ((liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[]).filter fun old => old ≠ removed)
      (fallback := #[]) (fun h => hsame h.symm)] at hmem
    rw [getD_rightpad_eq liveOccBy (l.x + 1) #[] target.x] at hmem
    exact hmem

private theorem mem_removeLiveOccArray_preserved_of_ne
    (liveOccBy : Array (Array CRef)) (l target : Literal) (removed cref : CRef)
    (hmem : cref ∈ liveOccBy.getD target.x #[]) (hne : cref ≠ removed) :
    cref ∈ (removeLiveOccArray liveOccBy l removed).getD target.x #[] := by
  unfold removeLiveOccArray
  by_cases hsame : target.x = l.x
  · have hlt : l.x < (liveOccBy.rightpad (l.x + 1) #[]).size := by
      rw [Array.size_rightpad]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    have hright :
        (liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[] = liveOccBy.getD l.x #[] := by
      simpa [hsame] using getD_rightpad_eq liveOccBy (l.x + 1) #[] target.x
    rw [hsame, arraySetIfInBounds_getD_eq
      (a := liveOccBy.rightpad (l.x + 1) #[]) (i := l.x)
      (v := ((liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[]).filter fun old => old ≠ removed)
      (fallback := #[]) hlt]
    have hmem' :
        cref ∈ (liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[] := by
      rw [hright]
      simpa [hsame] using hmem
    exact Array.mem_filter.mpr ⟨hmem', by simp [hne]⟩
  · rw [arraySetIfInBounds_getD_ne
      (a := liveOccBy.rightpad (l.x + 1) #[]) (i := l.x) (j := target.x)
      (v := ((liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[]).filter fun old => old ≠ removed)
      (fallback := #[]) (fun h => hsame h.symm)]
    rw [getD_rightpad_eq liveOccBy (l.x + 1) #[] target.x]
    exact hmem

private theorem not_mem_removeLiveOccArray_self
    (liveOccBy : Array (Array CRef)) (l : Literal) (removed : CRef) :
    removed ∉ (removeLiveOccArray liveOccBy l removed).getD l.x #[] := by
  intro hmem
  unfold removeLiveOccArray at hmem
  have hlt : l.x < (liveOccBy.rightpad (l.x + 1) #[]).size := by
    rw [Array.size_rightpad]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  rw [arraySetIfInBounds_getD_eq
    (a := liveOccBy.rightpad (l.x + 1) #[]) (i := l.x)
    (v := ((liveOccBy.rightpad (l.x + 1) #[]).getD l.x #[]).filter fun old => old ≠ removed)
    (fallback := #[]) hlt] at hmem
  have hkeep := (Array.mem_filter.mp hmem).2
  simp at hkeep

private theorem mem_listFoldAppendLiveOccArray_iff
    (ls : List Literal) (liveOccBy : Array (Array CRef))
    (newCref cref : CRef) (target : Literal) :
    cref ∈ (ls.foldl (fun occ lit => appendLiveOccArray occ lit newCref) liveOccBy).getD target.x #[] ↔
      cref ∈ liveOccBy.getD target.x #[] ∨ (cref = newCref ∧ target ∈ ls) := by
  induction ls generalizing liveOccBy with
  | nil =>
      simp
  | cons lit ls ih =>
      simp only [List.foldl_cons]
      rw [ih (appendLiveOccArray liveOccBy lit newCref), mem_appendLiveOccArray_iff]
      constructor
      · intro h
        rcases h with h | h
        · rcases h with h | h
          · exact Or.inl h
          · rcases h with ⟨hEq, hHead⟩
            exact Or.inr ⟨hEq, by simp [List.mem_cons, hHead]⟩
        · rcases h with ⟨hEq, hTail⟩
          exact Or.inr ⟨hEq, by simp [List.mem_cons, hTail]⟩
      · intro h
        rcases h with h | h
        · exact Or.inl (Or.inl h)
        · rcases h with ⟨hEq, hIn⟩
          have hsplit : target = lit ∨ target ∈ ls := by
            simpa [List.mem_cons] using hIn
          rcases hsplit with hHead | hTail
          · exact Or.inl (Or.inr ⟨hEq, hHead⟩)
          · exact Or.inr ⟨hEq, hTail⟩

private theorem mem_listFoldRemoveLiveOccArray_imp_old
    (ls : List Literal) (liveOccBy : Array (Array CRef))
    (removed cref : CRef) (target : Literal)
    (hmem : cref ∈ (ls.foldl (fun occ lit => removeLiveOccArray occ lit removed) liveOccBy).getD target.x #[]) :
    cref ∈ liveOccBy.getD target.x #[] := by
  induction ls generalizing liveOccBy with
  | nil =>
      simpa using hmem
  | cons lit ls ih =>
      have htail :
          cref ∈ (ls.foldl (fun occ lit => removeLiveOccArray occ lit removed)
            (removeLiveOccArray liveOccBy lit removed)).getD target.x #[] := by
        simpa using hmem
      have hmid :
          cref ∈ (removeLiveOccArray liveOccBy lit removed).getD target.x #[] :=
        ih _ htail
      exact mem_removeLiveOccArray_imp_old liveOccBy lit target removed cref hmid

private theorem mem_listFoldRemoveLiveOccArray_preserved_of_ne
    (ls : List Literal) (liveOccBy : Array (Array CRef))
    (removed cref : CRef) (target : Literal)
    (hmem : cref ∈ liveOccBy.getD target.x #[]) (hne : cref ≠ removed) :
    cref ∈ (ls.foldl (fun occ lit => removeLiveOccArray occ lit removed) liveOccBy).getD target.x #[] := by
  induction ls generalizing liveOccBy with
  | nil =>
      simpa using hmem
  | cons lit ls ih =>
      have hstep :
          cref ∈ (removeLiveOccArray liveOccBy lit removed).getD target.x #[] :=
        mem_removeLiveOccArray_preserved_of_ne liveOccBy lit target removed cref hmem hne
      have hrest :
          cref ∈ (ls.foldl (fun occ lit => removeLiveOccArray occ lit removed)
            (removeLiveOccArray liveOccBy lit removed)).getD target.x #[] :=
        ih _ hstep
      simpa using hrest

private theorem not_mem_listFoldRemoveLiveOccArray_self
    (ls : List Literal) (liveOccBy : Array (Array CRef))
    (removed : CRef) (target : Literal)
    (hmem : target ∈ ls) :
    removed ∉ (ls.foldl (fun occ lit => removeLiveOccArray occ lit removed) liveOccBy).getD target.x #[] := by
  induction ls generalizing liveOccBy with
  | nil =>
      cases hmem
  | cons lit ls ih =>
      have hsplit : target = lit ∨ target ∈ ls := by
        simpa [List.mem_cons] using hmem
      cases hsplit with
      | inl hEq =>
          subst hEq
          intro hfinal
          have htail :
              removed ∈ (ls.foldl (fun occ lit => removeLiveOccArray occ lit removed)
                (removeLiveOccArray liveOccBy target removed)).getD target.x #[] := by
            simpa [List.foldl_cons] using hfinal
          have hmid :
              removed ∈ (removeLiveOccArray liveOccBy target removed).getD target.x #[] :=
            mem_listFoldRemoveLiveOccArray_imp_old ls
              (removeLiveOccArray liveOccBy target removed) removed removed target htail
          exact not_mem_removeLiveOccArray_self liveOccBy target removed hmid
      | inr hTail =>
          intro hfinal
          have htail :
              removed ∈ (ls.foldl (fun occ lit => removeLiveOccArray occ lit removed)
                (removeLiveOccArray liveOccBy lit removed)).getD target.x #[] := by
            simpa [List.foldl_cons] using hfinal
          exact ih _ hTail htail

private theorem mem_appendClauseLiveOccArray_iff
    (liveOccBy : Array (Array CRef)) (lits : Array Literal)
    (newCref cref : CRef) (target : Literal) :
    cref ∈ (appendClauseLiveOccArray liveOccBy lits newCref).getD target.x #[] ↔
      cref ∈ liveOccBy.getD target.x #[] ∨ (cref = newCref ∧ target ∈ lits.toList) := by
  simpa [appendClauseLiveOccArray, Array.foldl_toList] using
    mem_listFoldAppendLiveOccArray_iff lits.toList liveOccBy newCref cref target

private theorem mem_removeClauseLiveOccArray_imp_old
    (liveOccBy : Array (Array CRef)) (lits : Array Literal)
    (removed cref : CRef) (target : Literal)
    (hmem : cref ∈ (removeClauseLiveOccArray liveOccBy lits removed).getD target.x #[]) :
    cref ∈ liveOccBy.getD target.x #[] := by
  unfold removeClauseLiveOccArray at hmem
  have hmem' :
      cref ∈ (lits.toList.foldl (fun occ lit => removeLiveOccArray occ lit removed)
        liveOccBy).getD target.x #[] := by
    simpa [Array.foldl_toList] using hmem
  exact mem_listFoldRemoveLiveOccArray_imp_old lits.toList liveOccBy removed cref target hmem'

private theorem mem_removeClauseLiveOccArray_preserved_of_ne
    (liveOccBy : Array (Array CRef)) (lits : Array Literal)
    (removed cref : CRef) (target : Literal)
    (hmem : cref ∈ liveOccBy.getD target.x #[]) (hne : cref ≠ removed) :
    cref ∈ (removeClauseLiveOccArray liveOccBy lits removed).getD target.x #[] := by
  simpa [removeClauseLiveOccArray, Array.foldl_toList] using
    mem_listFoldRemoveLiveOccArray_preserved_of_ne lits.toList liveOccBy removed cref target hmem hne

private theorem not_mem_removeClauseLiveOccArray_self
    (liveOccBy : Array (Array CRef)) (lits : Array Literal)
    (removed : CRef) (target : Literal)
    (hmem : target ∈ lits.toList) :
    removed ∉ (removeClauseLiveOccArray liveOccBy lits removed).getD target.x #[] := by
  simpa [removeClauseLiveOccArray, Array.foldl_toList] using
    not_mem_listFoldRemoveLiveOccArray_self lits.toList liveOccBy removed target hmem

theorem liveOccInvariant_empty : LiveOccInvariant CheckState.empty := by
  refine ⟨?_, ?_⟩
  · intro l cref hmem
    cases hx : l.x with
    | zero =>
        simp [CheckState.empty, getLiveOcc, hx] at hmem
    | succ n =>
        cases n with
        | zero =>
            simp [CheckState.empty, getLiveOcc, hx] at hmem
        | succ n' =>
            simp [CheckState.empty, getLiveOcc, hx] at hmem
  · intro cref c l hget hmem
    cases cref with
    | zero =>
        simp [ClauseStore.getClause, CRef_Undef] at hget
    | succ n =>
        simp [CheckState.empty, ClauseStore.getClause, ClauseStore.getClauseAt,
          CRef_Undef] at hget

theorem liveOccInvariant_addClause
    {st : CheckState} (hinv : LiveOccInvariant st)
    (hpos : 0 < st.clauses.clauses.size) (lits : Array Literal) :
    let res := st.clauses.addClause lits
    let clauses' := res.1
    let cref := res.2
    let st' := { st with clauses := clauses', liveOccBy := appendClauseLiveOccArray st.liveOccBy lits cref }
    LiveOccInvariant st' := by
  rcases hinv with ⟨hsound, hcomplete⟩
  dsimp
  refine ⟨?_, ?_⟩
  · intro l cref hmem
    have hcases :=
      (mem_appendClauseLiveOccArray_iff st.liveOccBy lits st.clauses.clauses.size cref l).mp hmem
    rcases hcases with hOld | ⟨rfl, hNew⟩
    · rcases hsound hOld with ⟨c, hget, hl⟩
      have hlt : cref < st.clauses.clauses.size :=
        ClauseStore.getClause_some_imp_lt st.clauses cref c hget
      refine ⟨c, ?_, hl⟩
      rw [ClauseStore.getClause_addClause_lt st.clauses lits cref hlt]
      exact hget
    · refine ⟨{ lits := lits, deleted := false }, ?_, hNew⟩
      exact ClauseStore.getClause_addClause_new st.clauses lits hpos
  · intro cref c l hget hl
    by_cases hnew : cref = st.clauses.clauses.size
    · subst hnew
      have hc : c = { lits := lits, deleted := false } := by
        rw [ClauseStore.getClause_addClause_new st.clauses lits hpos] at hget
        cases hget
        rfl
      subst hc
      exact (mem_appendClauseLiveOccArray_iff st.liveOccBy lits st.clauses.clauses.size
        st.clauses.clauses.size l).mpr (Or.inr ⟨rfl, hl⟩)
    · have hlt : cref < st.clauses.clauses.size := by
        have hlt' :=
          ClauseStore.getClause_some_imp_lt (cs := (st.clauses.addClause lits).1) (cref := cref)
            (c := c) hget
        have hle : cref ≤ st.clauses.clauses.size := by
          have : cref < st.clauses.clauses.size + 1 := by
            simpa [ClauseStore.addClause] using hlt'
          exact Nat.le_of_lt_succ this
        exact Nat.lt_of_le_of_ne hle hnew
      have hgetOld : st.clauses.getClause cref = some c := by
        rw [ClauseStore.getClause_addClause_lt st.clauses lits cref hlt] at hget
        exact hget
      have hmemOld : cref ∈ getLiveOcc st l := hcomplete hgetOld hl
      exact (mem_appendClauseLiveOccArray_iff st.liveOccBy lits st.clauses.clauses.size
        cref l).mpr (Or.inl hmemOld)

theorem liveOccInvariant_deleteClause
    {st : CheckState} (hinv : LiveOccInvariant st)
    {cref : CRef} {c : Clause}
    (hget : st.clauses.getClause cref = some c) :
    let clauses' := st.clauses.deleteClause cref
    let st' := { st with clauses := clauses', liveOccBy := removeClauseLiveOccArray st.liveOccBy c.lits cref }
    LiveOccInvariant st' := by
  rcases hinv with ⟨hsound, hcomplete⟩
  dsimp
  refine ⟨?_, ?_⟩
  · intro l cref' hmem
    by_cases hsame : cref' = cref
    · subst cref'
      have hold : cref ∈ getLiveOcc st l :=
        mem_removeClauseLiveOccArray_imp_old st.liveOccBy c.lits cref cref l hmem
      rcases hsound hold with ⟨c', hget', hlive⟩
      rw [hget] at hget'
      cases hget'
      exact False.elim (not_mem_removeClauseLiveOccArray_self st.liveOccBy c.lits cref l hlive hmem)
    · have hold : cref' ∈ getLiveOcc st l :=
        mem_removeClauseLiveOccArray_imp_old st.liveOccBy c.lits cref cref' l hmem
      rcases hsound hold with ⟨c', hget', hlive⟩
      refine ⟨c', ?_, hlive⟩
      rw [ClauseStore.getClause_deleteClause_ne st.clauses cref cref' hsame]
      exact hget'
  · intro cref' c' l hget' hl
    have hne : cref' ≠ cref := by
      intro heq
      subst cref'
      have hlt : cref < st.clauses.clauses.size :=
        ClauseStore.getClause_some_imp_lt st.clauses cref c hget
      rw [ClauseStore.getClause_deleteClause_eq st.clauses cref hlt] at hget'
      simp at hget'
    have hgetOld : st.clauses.getClause cref' = some c' := by
      rw [ClauseStore.getClause_deleteClause_ne st.clauses cref cref' hne] at hget'
      exact hget'
    have hmemOld : cref' ∈ getLiveOcc st l := hcomplete hgetOld hl
    exact mem_removeClauseLiveOccArray_preserved_of_ne st.liveOccBy c.lits cref cref' l hmemOld hne

end DqratLean.Watched
