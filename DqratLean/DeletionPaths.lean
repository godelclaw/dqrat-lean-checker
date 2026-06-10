import DqratLean.SoundnessCore

/-!
# Deletion Paths

`on_`-pure resolution paths (`DeletePurePath`), the executable
`getReachable` BFS specification and completeness, and the
`NoDeleteCrossPaths(Set)` reach-pair predicates certified by the checker,
including the orientation lemmas used by the exhibition proof.
-/
open Std.Do

def NoDeleteCrossPaths (st : CheckState) (on_ of_ : Var) : Prop :=
  let reachPos := getReachable st (mkLit on_ true)
  let reachNeg := getReachable st (mkLit on_ false)
  !((reachPos.getD (of_ * 2) false && reachNeg.getD (of_ * 2 + 1) false) ||
    (reachPos.getD (of_ * 2 + 1) false && reachNeg.getD (of_ * 2) false)) = true

def NoDeleteCrossPathsSet
    (st : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ of_ ∈ vars.toList, NoDeleteCrossPaths st on_ of_

theorem noDeleteCrossPaths_not_reachPos_neg_reachNeg_pos
    {st : CheckState} {on_ of_ : Var}
    (hpaths : NoDeleteCrossPaths st on_ of_) :
    ¬ ((getReachable st (mkLit on_ true)).getD (of_ * 2) false = true ∧
       (getReachable st (mkLit on_ false)).getD (of_ * 2 + 1) false = true) := by
  intro hbad
  rcases hbad with ⟨hposNeg, hnegPos⟩
  simp [NoDeleteCrossPaths, hposNeg, hnegPos] at hpaths

theorem noDeleteCrossPaths_not_reachPos_pos_reachNeg_neg
    {st : CheckState} {on_ of_ : Var}
    (hpaths : NoDeleteCrossPaths st on_ of_) :
    ¬ ((getReachable st (mkLit on_ true)).getD (of_ * 2 + 1) false = true ∧
       (getReachable st (mkLit on_ false)).getD (of_ * 2) false = true) := by
  intro hbad
  rcases hbad with ⟨hposPos, hnegNeg⟩
  simp [NoDeleteCrossPaths, hposPos, hnegNeg] at hpaths

theorem noDeleteCrossPaths_not_reachPos_lit_reachNeg_negate
    {st : CheckState} {on_ of_ : Var} {pos : Bool}
    (hpaths : NoDeleteCrossPaths st on_ of_) :
    ¬ ((getReachable st (mkLit on_ true)).getD (mkLit of_ pos).x false = true ∧
       (getReachable st (mkLit on_ false)).getD (mkLit of_ (!pos)).x false = true) := by
  cases pos
  · intro hbad
    exact noDeleteCrossPaths_not_reachPos_neg_reachNeg_pos hpaths (by
      simpa [mkLit] using hbad)
  · intro hbad
    exact noDeleteCrossPaths_not_reachPos_pos_reachNeg_neg hpaths (by
      simpa [mkLit] using hbad)

inductive DeletePurePath
    (st : CheckState) (on_ : Var) (start : Literal) : Literal → Prop
  | first
      {lit : Literal} {cref : CRef} {clause : Clause}
      (hget : st.clauses.getClause cref = some clause)
      (hstart : start ∈ clause.lits.toList)
      (hnoStartNeg : start.negate ∉ clause.lits.toList)
      (hlit : lit ∈ clause.lits.toList)
      (hne : lit ≠ start)
      (hexi : st.formula.isVarExistential lit.var = true)
      (hdep : (st.formula.depset.getD lit.var #[]).contains on_ = true) :
      DeletePurePath st on_ start lit
  | step
      {prev lit : Literal} {cref : CRef} {clause : Clause}
      (hprev : DeletePurePath st on_ start prev)
      (hget : st.clauses.getClause cref = some clause)
      (hcur : prev.negate ∈ clause.lits.toList)
      (hnoStartNeg : start.negate ∉ clause.lits.toList)
      (hlit : lit ∈ clause.lits.toList)
      (hne : lit ≠ prev.negate)
      (hexi : st.formula.isVarExistential lit.var = true)
      (hdep : (st.formula.depset.getD lit.var #[]).contains on_ = true) :
      DeletePurePath st on_ start lit

theorem deletePurePath_target_isVarExistential
    {st : CheckState} {on_ : Var} {start target : Literal}
    (hpath : DeletePurePath st on_ start target) :
    st.formula.isVarExistential target.var = true := by
  induction hpath with
  | first _ _ _ _ _ hexi _ =>
      exact hexi
  | step _ _ _ _ _ _ hexi _ _ =>
      exact hexi

theorem literal_x_lt_numLits_of_var_le_maxVar
    (l : Literal) {maxVar : Nat} (hle : l.var ≤ maxVar) :
    l.x < maxVar * 2 + 2 := by
  have hdecomp : l.x = (l.x / 2) * 2 + l.x % 2 := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod l.x 2).symm
  have hmod : l.x % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold Literal.var at hle
  calc
    l.x = (l.x / 2) * 2 + l.x % 2 := hdecomp
    _ < (l.x / 2) * 2 + 2 := Nat.add_lt_add_left hmod _
    _ = (l.x / 2 + 1) * 2 := by omega
    _ ≤ (maxVar + 1) * 2 := Nat.mul_le_mul_right 2 (Nat.succ_le_succ hle)
    _ = maxVar * 2 + 2 := by omega

theorem literal_negate_var (l : Literal) :
    l.negate.var = l.var := by
  unfold Literal.negate Literal.var
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [← Nat.testBit_succ, Nat.testBit_xor]
  have h1 : Nat.testBit 1 (k + 1) = false := by
    rw [Bool.eq_false_iff]
    exact fun h => Nat.succ_ne_zero k (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)
  simp [h1]

theorem one_testBit_succ_false (k : Nat) :
    Nat.testBit 1 (k + 1) = false := by
  rw [Bool.eq_false_iff]
  exact fun h => Nat.succ_ne_zero k (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)

theorem testBit_mul2_add_one_succ (v k : Nat) :
    (v * 2 + 1).testBit (k + 1) = (v * 2).testBit (k + 1) := by
  rw [Nat.testBit_succ, Nat.testBit_succ]
  have h1 : (v * 2 + 1) / 2 = v := by omega
  have h2 : (v * 2) / 2 = v := by omega
  rw [h1, h2]

theorem xor_mul_two_false (v : Nat) :
    v * 2 ^^^ 1 = v * 2 + 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp
  | succ k =>
      rw [Nat.testBit_xor, one_testBit_succ_false]
      simp [testBit_mul2_add_one_succ]

theorem xor_mul_two_true (v : Nat) :
    v * 2 + 1 ^^^ 1 = v * 2 := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp
  | succ k =>
      rw [Nat.testBit_xor, one_testBit_succ_false]
      simp [testBit_mul2_add_one_succ]

theorem mkLit_negate (v : Var) (pos : Bool) :
    (mkLit v pos).negate = mkLit v (!pos) := by
  cases pos <;> simp [mkLit, Literal.negate, xor_mul_two_false, xor_mul_two_true]

theorem deletePurePath_step_mkLit_of_var_ne
    {st : CheckState} {on_ prevOf nextOf : Var}
    {startPos prevPos nextPos : Bool}
    {cref : CRef} {clause : Clause}
    (hprev : DeletePurePath st on_ (mkLit on_ startPos) (mkLit prevOf prevPos))
    (hget : st.clauses.getClause cref = some clause)
    (hcur : (mkLit prevOf prevPos).negate ∈ clause.lits.toList)
    (hnoStartNeg : (mkLit on_ startPos).negate ∉ clause.lits.toList)
    (hnext : mkLit nextOf nextPos ∈ clause.lits.toList)
    (hnext_ne_prev : nextOf ≠ prevOf)
    (hexi : st.formula.isVarExistential nextOf = true)
    (hdep : (st.formula.depset.getD nextOf #[]).contains on_ = true) :
    DeletePurePath st on_ (mkLit on_ startPos) (mkLit nextOf nextPos) := by
  have hne : mkLit nextOf nextPos ≠ (mkLit prevOf prevPos).negate := by
    intro hEq
    have hvar := congrArg Literal.var hEq
    rw [mkLit_var_early, literal_negate_var, mkLit_var_early] at hvar
    exact hnext_ne_prev hvar
  exact DeletePurePath.step hprev hget hcur hnoStartNeg hnext hne
    (by simpa [mkLit_var_early] using hexi)
    (by simpa [mkLit_var_early] using hdep)

theorem literal_negate_x_lt_numLits_of_var_le_maxVar
    (l : Literal) {maxVar : Nat} (hle : l.var ≤ maxVar) :
    l.negate.x < maxVar * 2 + 2 := by
  exact literal_x_lt_numLits_of_var_le_maxVar l.negate
    (by simpa [literal_negate_var] using hle)

theorem mkLit_x_lt_numLits_of_var_le_maxVar
    {v maxVar : Nat} {pos : Bool} (hle : v ≤ maxVar) :
    (mkLit v pos).x < maxVar * 2 + 2 := by
  exact literal_x_lt_numLits_of_var_le_maxVar (mkLit v pos)
    (by simpa [mkLit_var_early] using hle)

theorem clauseLit_x_lt_numLits_of_fullCorrect_raw_not_deleted
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hfull : CheckState.FullCorrect dqbf cs st)
    {cref : CRef} {clause : Clause} {lit : Literal}
    (hraw : st.clauses.getClauseRaw cref = some clause)
    (hdeleted : clause.deleted = false)
    (hlit : lit ∈ clause.lits.toList) :
    lit.x < st.formula.maxVar * 2 + 2 := by
  have hget : st.clauses.getClause cref = some clause :=
    getClause_of_getClauseRaw_not_deleted hraw hdeleted
  exact literal_x_lt_numLits_of_var_le_maxVar lit
    ((hfull.toCorrect.clauses_wf cref clause hget lit hlit).2)

theorem isVarExistential_literal_var_le_maxVar_of_fullCorrect
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {lit : Literal}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hexi : st.formula.isVarExistential lit.var = true) :
    lit.var ≤ st.formula.maxVar := by
  have hlt : lit.var < st.formula.isExistential.size :=
    arrayGetD_true_imp_lt (a := st.formula.isExistential) (by
      simpa [DQBF.isVarExistential] using hexi)
  rw [hfull.toCorrect.toSound.isExistential_size] at hlt
  exact Nat.lt_succ_iff.mp hlt

theorem isVarExistential_literal_x_lt_numLits_of_fullCorrect
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {lit : Literal}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hexi : st.formula.isVarExistential lit.var = true) :
    lit.x < st.formula.maxVar * 2 + 2 :=
  literal_x_lt_numLits_of_var_le_maxVar lit
    (isVarExistential_literal_var_le_maxVar_of_fullCorrect hfull hexi)

theorem isVarExistential_literal_negate_x_lt_numLits_of_fullCorrect
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {lit : Literal}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hexi : st.formula.isVarExistential lit.var = true) :
    lit.negate.x < st.formula.maxVar * 2 + 2 :=
  literal_negate_x_lt_numLits_of_var_le_maxVar lit
    (isVarExistential_literal_var_le_maxVar_of_fullCorrect hfull hexi)

theorem literal_negate_negate_local (l : Literal) :
    l.negate.negate = l := by
  cases l
  simp [Literal.negate, Nat.xor_assoc]

theorem literal_eq_of_x_eq
    {a b : Literal} (h : a.x = b.x) : a = b := by
  cases a
  cases b
  simp at h ⊢
  exact h

theorem literal_eq_negate_of_negate_x_eq
    {a b : Literal} (h : a.negate.x = b.x) :
    a = b.negate := by
  cases a with
  | mk ax =>
      cases b with
      | mk bx =>
          simp [Literal.negate] at h ⊢
          rw [← h]
          simp [Nat.xor_assoc]

theorem array_toList_getLast_eq_getD_last
    {α : Type} {xs : Array α} (fallback : α) (h : xs.toList ≠ []) :
    xs.toList.getLast h = xs.getD (xs.size - 1) fallback := by
  rw [List.getLast_eq_getElem]
  have hsize_pos : 0 < xs.size := by
    cases hs : xs.size with
    | zero =>
        have hnil : xs.toList = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp [hs]
        exact (h hnil).elim
    | succ _ => omega
  have hidx : xs.size - 1 < xs.size := by omega
  rw [← Array.getElem_eq_getD (xs := xs) (i := xs.size - 1) (h := hidx) fallback]
  exact Array.getElem_toList (xs := xs) (i := xs.size - 1) hidx

theorem List.mem_dropLast_of_mem_ne_getLast'
    {α : Type} [DecidableEq α] {xs : List α} {x : α}
    (hne : xs ≠ []) (hmem : x ∈ xs) (hneLast : x ≠ xs.getLast hne) :
    x ∈ xs.dropLast := by
  rw [← List.dropLast_concat_getLast hne] at hmem
  simp at hmem
  exact hmem.resolve_right hneLast

theorem array_mem_pop_of_mem_ne_getD_last
    {α : Type} [DecidableEq α] {xs : Array α} {x : α} (fallback : α)
    (hmem : x ∈ xs.toList)
    (hneLast : x ≠ xs.getD (xs.size - 1) fallback) :
    x ∈ xs.pop.toList := by
  have hlist_ne : xs.toList ≠ [] := by
    intro hnil
    simp [hnil] at hmem
  rw [Array.toList_pop]
  exact List.mem_dropLast_of_mem_ne_getLast' hlist_ne hmem (by
    intro hx
    exact hneLast (by
      rw [← array_toList_getLast_eq_getD_last (xs := xs) fallback hlist_ne]
      exact hx))

theorem array_getD_last_mem_toList
    {α : Type} {xs : Array α} (fallback : α)
    (hlist_ne : xs.toList ≠ []) :
    xs.getD (xs.size - 1) fallback ∈ xs.toList := by
  have hlast : xs.toList.getLast hlist_ne ∈ xs.toList :=
    List.getLast_mem hlist_ne
  rwa [array_toList_getLast_eq_getD_last fallback hlist_ne] at hlast

theorem false_replicate_array_getD
    (n i : Nat) :
    ((List.replicate n false).toArray).getD i false = false := by
  by_cases hi : i < ((List.replicate n false).toArray).size
  · simp [Array.getD]
  · simp [Array.getD]

theorem array_set_getD_ne
    {α : Type} (a : Array α) (i j : Nat) (v fallback : α)
    (hi : i < a.size) (hne : i ≠ j) :
    (a.set i v hi).getD j fallback = a.getD j fallback := by
  have hsize : (a.set i v hi).size = a.size := Array.size_set hi
  simp only [Array.getD]
  by_cases hj : j < a.size
  · rw [dif_pos (hsize ▸ hj), dif_pos hj]
    simp [Array.getElem_set, hne]
  · have hj' : ¬ j < (a.set i v hi).size := by
      simpa [hsize] using hj
    rw [dif_neg hj', dif_neg hj]

theorem array_set_true_preserves_getD
    (a : Array Bool) (i target : Nat) (hi : i < a.size)
    (h : a.getD target false = true) :
    (a.set i true hi).getD target false = true := by
  by_cases heq : i = target
  · subst target
    have hidx : i < (a.set i true hi).size := by
      simpa [Array.size_set hi] using hi
    have hself : (a.set i true hi)[i]'hidx = true :=
      Array.getElem_set_self (xs := a) (i := i) hi (v := true)
    rw [Array.getElem_eq_getD (xs := a.set i true hi) (i := i) (h := hidx) false] at hself
    exact hself
  · rw [array_set_getD_ne a i target true false hi heq]
    exact h

theorem false_replicate_array_set_getD_of_ne
    (n i j : Nat) (hi : i < ((List.replicate n false).toArray).size) (hne : i ≠ j) :
    (((List.replicate n false).toArray).set i true hi).getD j false = false := by
  rw [array_set_getD_ne _ i j true false hi hne]
  exact false_replicate_array_getD n j

theorem arraySetIfInBounds_true_preserves_getD
    (a : Array Bool) (i target : Nat)
    (h : a.getD target false = true) :
    (a.setIfInBounds i true).getD target false = true := by
  by_cases hit : i = target
  · subst target
    by_cases hlt : i < a.size
    · exact arraySetIfInBounds_getD_eq a i true false hlt
    · simp [Array.getD, hlt] at h
  · rw [arraySetIfInBounds_getD_ne a i target true false hit]
    exact h

theorem array_getElem?_getD_eq_getD
    {α : Type} (a : Array α) (i : Nat) (fallback : α) :
    a[i]?.getD fallback = a.getD i fallback := by
  by_cases h : i < a.size
  · simp [Array.getD, h]
  · simp [Array.getD, h]

theorem getReachableLitStep_marks_reach_true
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur lit : Literal}
    {state : Array Literal × Array Bool}
    (hcur : lit ≠ cur)
    (hexpl : explored.getD lit.negate.x false = false)
    (hexi : st.formula.isVarExistential lit.var = true)
    (hdep : (st.formula.depset.getD lit.var #[]).contains lvar = true)
    (hlt : lit.x < state.2.size) :
    ((getReachableLitStep st lvar explored cur state lit).2).getD lit.x false = true := by
  rcases state with ⟨wl, rch⟩
  have hmem : lvar ∈ st.formula.depset.getD lit.var #[] :=
    Array.contains_iff_mem.mp hdep
  have hmem' : lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
    by_cases hlt_dep : lit.var < st.formula.depset.size
    · simpa [Array.getD, hlt_dep] using hmem
    · simp [Array.getD, hlt_dep] at hmem
  simpa [getReachableLitStep, hcur, hexpl, hexi, hmem'] using hlt

theorem getReachableLitStep_reach_size
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur : Literal}
    {state : Array Literal × Array Bool} {lit : Literal} :
    ((getReachableLitStep st lvar explored cur state lit).2).size = state.2.size := by
  rcases state with ⟨wl, rch⟩
  by_cases hcur : lit = cur
  · simp [getReachableLitStep, hcur]
  · by_cases hexpl : explored.getD lit.negate.x false = true
    · simp [getReachableLitStep, hcur, hexpl]
    · by_cases hguard :
        st.formula.isVarExistential lit.var = true ∧
          lvar ∈ st.formula.depset[lit.var]?.getD #[]
      · simp [getReachableLitStep, hcur, hexpl, hguard]
      · simp [getReachableLitStep, hcur, hexpl, hguard]

theorem getReachableLitStep_preserves_reach_true
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur : Literal}
    {state : Array Literal × Array Bool} {lit : Literal} {target : Nat}
    (h : state.2.getD target false = true) :
    ((getReachableLitStep st lvar explored cur state lit).2).getD target false = true := by
  rcases state with ⟨wl, rch⟩
  by_cases hcur : lit = cur
  · simp [getReachableLitStep, hcur, h]
  · by_cases hexpl : explored.getD lit.negate.x false = true
    · simp [getReachableLitStep, hcur, hexpl, h]
    · by_cases hexi : st.formula.isVarExistential lit.var = true
      · by_cases hmem : lvar ∈ st.formula.depset.getD lit.var #[]
        · have hmem' :
              lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
            by_cases hlt : lit.var < st.formula.depset.size
            · simpa [Array.getD, hlt] using hmem
            · simp [Array.getD, hlt] at hmem
          simp [getReachableLitStep, hcur, hexpl, hexi, hmem']
          rw [array_getElem?_getD_eq_getD]
          exact arraySetIfInBounds_true_preserves_getD rch lit.x target h
        · have hmem' :
              ¬ lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
            by_cases hlt : lit.var < st.formula.depset.size
            · simpa [Array.getD, hlt] using hmem
            · simp [hlt]
          simp [getReachableLitStep, hcur, hexpl, hexi, hmem', h]
      · simp [getReachableLitStep, hcur, hexpl, hexi, h]

theorem getReachableLitStep_marks_reach_true_of_pre
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur target : Literal}
    {state : Array Literal × Array Bool}
    (hcur : target ≠ cur)
    (hpre :
      explored.getD target.negate.x false = true →
        state.2.getD target.x false = true)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((getReachableLitStep st lvar explored cur state target).2).getD
      target.x false = true := by
  by_cases hexpl : explored.getD target.negate.x false = true
  · exact getReachableLitStep_preserves_reach_true (hpre hexpl)
  · have hexplFalse : explored.getD target.negate.x false = false := by
      cases hval : explored.getD target.negate.x false <;> simp [hval] at hexpl ⊢
    exact getReachableLitStep_marks_reach_true
      (st := st) (lvar := lvar) (explored := explored)
      (cur := cur) (lit := target) (state := state)
      hcur hexplFalse hexi hdep hlt

theorem getReachableLitStep_preserves_worklist_mem
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur lit keep : Literal}
    {state : Array Literal × Array Bool}
    (h : keep ∈ state.1.toList) :
    keep ∈ ((getReachableLitStep st lvar explored cur state lit).1).toList := by
  rcases state with ⟨wl, rch⟩
  by_cases hcur : lit = cur
  · simp [getReachableLitStep, hcur, h]
  · by_cases hexpl : explored.getD lit.negate.x false = true
    · simp [getReachableLitStep, hcur, hexpl, h]
    · by_cases hexi : st.formula.isVarExistential lit.var = true
      · by_cases hmem : lvar ∈ st.formula.depset.getD lit.var #[]
        · have hmem' :
              lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
            by_cases hlt : lit.var < st.formula.depset.size
            · simpa [Array.getD, hlt] using hmem
            · simp [Array.getD, hlt] at hmem
          simp [getReachableLitStep, hcur, hexpl, hexi, hmem', h]
        · have hmem' :
              ¬ lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
            by_cases hlt : lit.var < st.formula.depset.size
            · simpa [Array.getD, hlt] using hmem
            · simp [hlt]
          simp [getReachableLitStep, hcur, hexpl, hexi, hmem', h]
      · simp [getReachableLitStep, hcur, hexpl, hexi, h]

def ReachFrontierInvariant
    (start : Literal) (worklist : Array Literal) (reach expl : Array Bool) : Prop :=
  (∀ l, l ∈ worklist.toList → l ≠ start →
      reach.getD l.negate.x false = true) ∧
  (∀ l, expl.getD l.x false = true → l ≠ start →
      reach.getD l.negate.x false = true)

theorem ReachFrontierInvariant_initial
    (start : Literal) (numLits : Nat) :
    ReachFrontierInvariant start #[start]
      (List.replicate numLits false).toArray
      (List.replicate numLits false).toArray := by
  constructor
  · intro l hmem hne
    simp at hmem
    exact (hne hmem).elim
  · intro l hexpl _
    have hfalse :
        ((List.replicate numLits false).toArray).getD l.x false = false :=
      false_replicate_array_getD numLits l.x
    rw [hfalse] at hexpl
    cases hexpl

def ReachProcessedInvariant
    (st : CheckState) (lvar : Var) (negL : Literal)
    (reach expl : Array Bool) : Prop :=
  ∀ cur, expl.getD cur.x false = true →
    ∀ cref clause target,
      cref ∈ (st.clauses.getOcc cur).toList →
      st.clauses.getClauseRaw cref = some clause →
      clause.deleted = false →
      negL ∉ clause.lits →
      target ∈ clause.lits.toList →
      target ≠ cur →
      st.formula.isVarExistential target.var = true →
      (st.formula.depset.getD target.var #[]).contains lvar = true →
      target.x < reach.size →
      reach.getD target.x false = true

theorem ReachProcessedInvariant_initial
    (st : CheckState) (lvar : Var) (negL : Literal) (numLits : Nat) :
    ReachProcessedInvariant st lvar negL
      (List.replicate numLits false).toArray
      (List.replicate numLits false).toArray := by
  intro cur hexpl
  have hfalse :
      ((List.replicate numLits false).toArray).getD cur.x false = false :=
    false_replicate_array_getD numLits cur.x
  rw [hfalse] at hexpl
  cases hexpl

def ReachBackpointerInvariant
    (worklist : Array Literal) (reach expl : Array Bool) : Prop :=
  ∀ (lit : Literal), lit.negate.x < expl.size →
    reach.getD lit.x false = true →
      lit.negate ∈ worklist.toList ∨ expl.getD lit.negate.x false = true

theorem ReachBackpointerInvariant_initial
    (start : Literal) (numLits : Nat) :
    ReachBackpointerInvariant #[start]
      (List.replicate numLits false).toArray
      (List.replicate numLits false).toArray := by
  unfold ReachBackpointerInvariant
  intro lit _ hreach
  have hfalse :
      ((List.replicate numLits false).toArray).getD lit.x false = false :=
    false_replicate_array_getD numLits lit.x
  rw [hfalse] at hreach
  cases hreach

theorem getReachableLitStep_preserves_frontierInvariant
    {st : CheckState} {lvar : Var} {explored : Array Bool} {start cur lit : Literal}
    {state : Array Literal × Array Bool}
    (hinv : ReachFrontierInvariant start state.1 state.2 explored)
    (hlt : lit.x < state.2.size) :
    ReachFrontierInvariant start
      (getReachableLitStep st lvar explored cur state lit).1
      (getReachableLitStep st lvar explored cur state lit).2
      explored := by
  rcases state with ⟨wl, rch⟩
  rcases hinv with ⟨hwl, hexplInv⟩
  constructor
  · intro keep hkeep hkeep_ne_start
    by_cases hcur : lit = cur
    · simp [getReachableLitStep, hcur] at hkeep ⊢
      rw [array_getElem?_getD_eq_getD]
      simpa using hwl keep (Array.mem_toList_iff.mpr hkeep) hkeep_ne_start
    · by_cases hexpl : explored.getD lit.negate.x false = true
      · simp [getReachableLitStep, hcur, hexpl] at hkeep ⊢
        rw [array_getElem?_getD_eq_getD]
        simpa using hwl keep (Array.mem_toList_iff.mpr hkeep) hkeep_ne_start
      · have hexplFalse : explored.getD lit.negate.x false = false := by
          cases hval : explored.getD lit.negate.x false <;> simp [hval] at hexpl ⊢
        by_cases hexi : st.formula.isVarExistential lit.var = true
        · by_cases hdep : lvar ∈ st.formula.depset.getD lit.var #[]
          · have hdep' :
                lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
              by_cases hlt_dep : lit.var < st.formula.depset.size
              · simpa [Array.getD, hlt_dep] using hdep
              · simp [Array.getD, hlt_dep] at hdep
            simp [getReachableLitStep, hcur, hexplFalse, hexi, hdep'] at hkeep ⊢
            rcases hkeep with hkeep_old | hkeep_new
            · rw [array_getElem?_getD_eq_getD]
              exact arraySetIfInBounds_true_preserves_getD rch lit.x keep.negate.x
                (hwl keep (Array.mem_toList_iff.mpr hkeep_old) hkeep_ne_start)
            · subst keep
              have hmark :
                  (rch.setIfInBounds lit.x true).getD lit.x false = true :=
                arraySetIfInBounds_getD_eq rch lit.x true false hlt
              simpa [literal_negate_negate_local] using hmark
          · have hdep' :
                ¬ lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
              by_cases hlt_dep : lit.var < st.formula.depset.size
              · simpa [Array.getD, hlt_dep] using hdep
              · simp [hlt_dep]
            simp [getReachableLitStep, hcur, hexplFalse, hexi, hdep'] at hkeep ⊢
            rw [array_getElem?_getD_eq_getD]
            simpa using hwl keep (Array.mem_toList_iff.mpr hkeep) hkeep_ne_start
        · simp [getReachableLitStep, hcur, hexplFalse, hexi] at hkeep ⊢
          rw [array_getElem?_getD_eq_getD]
          simpa using hwl keep (Array.mem_toList_iff.mpr hkeep) hkeep_ne_start
  · intro keep hkeep hkeep_ne_start
    exact getReachableLitStep_preserves_reach_true
      (hexplInv keep hkeep hkeep_ne_start)

theorem getReachableLitFold_preserves_reach_true
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur : Literal}
    (lits : List Literal) {state : Array Literal × Array Bool} {target : Nat}
    (h : state.2.getD target false = true) :
    ((lits.foldl (getReachableLitStep st lvar explored cur) state).2).getD target false = true := by
  induction lits generalizing state with
  | nil =>
      simpa using h
  | cons lit rest ih =>
      rw [List.foldl_cons]
      exact ih (getReachableLitStep_preserves_reach_true h)

theorem getReachableLitFold_preserves_worklist_mem
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur keep : Literal}
    (lits : List Literal) {state : Array Literal × Array Bool}
    (h : keep ∈ state.1.toList) :
    keep ∈ ((lits.foldl (getReachableLitStep st lvar explored cur) state).1).toList := by
  induction lits generalizing state with
  | nil =>
      simpa using h
  | cons lit rest ih =>
      rw [List.foldl_cons]
      exact ih (getReachableLitStep_preserves_worklist_mem h)

theorem getReachableLitFold_reach_size
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur : Literal}
    (lits : List Literal) {state : Array Literal × Array Bool} :
    ((lits.foldl (getReachableLitStep st lvar explored cur) state).2).size = state.2.size := by
  induction lits generalizing state with
  | nil =>
      rfl
  | cons lit rest ih =>
      rw [List.foldl_cons]
      rw [ih]
      exact getReachableLitStep_reach_size
        (st := st) (lvar := lvar) (explored := explored)
        (cur := cur) (state := state) (lit := lit)

theorem getReachableLitFold_preserves_frontierInvariant
    {st : CheckState} {lvar : Var} {explored : Array Bool} {start cur : Literal}
    (lits : List Literal) {state : Array Literal × Array Bool}
    (hinv : ReachFrontierInvariant start state.1 state.2 explored)
    (hbounds : ∀ lit ∈ lits, lit.x < state.2.size) :
    ReachFrontierInvariant start
      ((lits.foldl (getReachableLitStep st lvar explored cur) state).1)
      ((lits.foldl (getReachableLitStep st lvar explored cur) state).2)
      explored := by
  induction lits generalizing state with
  | nil =>
      simpa using hinv
  | cons lit rest ih =>
      rw [List.foldl_cons]
      have hinv' :
          ReachFrontierInvariant start
            (getReachableLitStep st lvar explored cur state lit).1
            (getReachableLitStep st lvar explored cur state lit).2
            explored :=
        getReachableLitStep_preserves_frontierInvariant hinv
          (hbounds lit (by simp))
      have hsize :
          ((getReachableLitStep st lvar explored cur state lit).2).size = state.2.size :=
        getReachableLitStep_reach_size
          (st := st) (lvar := lvar) (explored := explored)
          (cur := cur) (state := state) (lit := lit)
      exact ih
        (state := getReachableLitStep st lvar explored cur state lit)
        hinv'
        (fun target htarget =>
          by
            have htarget' : target ∈ lit :: rest := List.mem_cons_of_mem lit htarget
            simpa [hsize] using hbounds target htarget')

theorem getReachableLitFold_marks_reach_true
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur target : Literal}
    (lits : List Literal) {state : Array Literal × Array Bool}
    (hmem : target ∈ lits)
    (hcur : target ≠ cur)
    (hexpl : explored.getD target.negate.x false = false)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((lits.foldl (getReachableLitStep st lvar explored cur) state).2).getD target.x false = true := by
  induction lits generalizing state with
  | nil =>
      simp at hmem
  | cons lit rest ih =>
      rw [List.foldl_cons]
      cases hmem with
      | head =>
        exact getReachableLitFold_preserves_reach_true rest
          (getReachableLitStep_marks_reach_true
            (st := st) (lvar := lvar) (explored := explored)
            (cur := cur) (lit := target) (state := state)
            hcur hexpl hexi hdep hlt)
      | tail _ hrest =>
        have hsize :
            ((getReachableLitStep st lvar explored cur state lit).2).size = state.2.size :=
          getReachableLitStep_reach_size
            (st := st) (lvar := lvar) (explored := explored)
            (cur := cur) (state := state) (lit := lit)
        exact ih (state := getReachableLitStep st lvar explored cur state lit)
          hrest (by simpa [hsize] using hlt)

theorem getReachableLitFold_marks_reach_true_of_pre
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur target : Literal}
    (lits : List Literal) {state : Array Literal × Array Bool}
    (hmem : target ∈ lits)
    (hcur : target ≠ cur)
    (hpre :
      explored.getD target.negate.x false = true →
        state.2.getD target.x false = true)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((lits.foldl (getReachableLitStep st lvar explored cur) state).2).getD
      target.x false = true := by
  induction lits generalizing state with
  | nil =>
      simp at hmem
  | cons lit rest ih =>
      rw [List.foldl_cons]
      cases hmem with
      | head =>
          exact getReachableLitFold_preserves_reach_true rest
            (getReachableLitStep_marks_reach_true_of_pre
              (st := st) (lvar := lvar) (explored := explored)
              (cur := cur) (target := target) (state := state)
              hcur hpre hexi hdep hlt)
      | tail _ hrest =>
          have hsize :
              ((getReachableLitStep st lvar explored cur state lit).2).size = state.2.size :=
            getReachableLitStep_reach_size
              (st := st) (lvar := lvar) (explored := explored)
              (cur := cur) (state := state) (lit := lit)
          exact ih (state := getReachableLitStep st lvar explored cur state lit)
            hrest
            (fun hexpl =>
              getReachableLitStep_preserves_reach_true (hpre hexpl))
            (by simpa [hsize] using hlt)

theorem getReachableLitStep_preserves_backpointerInvariant
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur lit : Literal}
    {state : Array Literal × Array Bool}
    (hback : ReachBackpointerInvariant state.1 state.2 explored) :
    ReachBackpointerInvariant
      (getReachableLitStep st lvar explored cur state lit).1
      (getReachableLitStep st lvar explored cur state lit).2
      explored := by
  rcases state with ⟨wl, rch⟩
  unfold ReachBackpointerInvariant at hback ⊢
  intro target htarget_bound hreach
  by_cases hcur : lit = cur
  · simp [getReachableLitStep, hcur] at hreach ⊢
    rw [array_getElem?_getD_eq_getD] at hreach ⊢
    rcases hback target htarget_bound hreach with hqueued | hexplored
    · left
      exact Array.mem_toList_iff.mp hqueued
    · right
      exact hexplored
  · by_cases hexpl : explored.getD lit.negate.x false = true
    · simp [getReachableLitStep, hcur, hexpl] at hreach ⊢
      rw [array_getElem?_getD_eq_getD] at hreach ⊢
      rcases hback target htarget_bound hreach with hqueued | hexplored
      · left
        exact Array.mem_toList_iff.mp hqueued
      · right
        exact hexplored
    · have hexplFalse : explored.getD lit.negate.x false = false := by
        cases hval : explored.getD lit.negate.x false <;> simp [hval] at hexpl ⊢
      by_cases hexi : st.formula.isVarExistential lit.var = true
      · by_cases hdep : lvar ∈ st.formula.depset.getD lit.var #[]
        · have hdep' :
              lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
            by_cases hlt_dep : lit.var < st.formula.depset.size
            · simpa [Array.getD, hlt_dep] using hdep
            · simp [Array.getD, hlt_dep] at hdep
          simp [getReachableLitStep, hcur, hexplFalse, hexi, hdep'] at hreach ⊢
          rw [array_getElem?_getD_eq_getD] at hreach ⊢
          by_cases hx : target.x = lit.x
          · have htarget_eq : target = lit := literal_eq_of_x_eq hx
            subst target
            left
            right
            rfl
          · have hreach_old : rch.getD target.x false = true := by
              rw [arraySetIfInBounds_getD_ne rch lit.x target.x true false
                (fun h => hx h.symm)] at hreach
              exact hreach
            rcases hback target htarget_bound hreach_old with hqueued | hexplored
            · left
              left
              simpa using Array.mem_toList_iff.mp hqueued
            · right
              exact hexplored
        · have hdep' :
              ¬ lvar ∈ st.formula.depset[lit.var]?.getD #[] := by
            by_cases hlt_dep : lit.var < st.formula.depset.size
            · simpa [Array.getD, hlt_dep] using hdep
            · simp [hlt_dep]
          simp [getReachableLitStep, hcur, hexplFalse, hexi, hdep'] at hreach ⊢
          rw [array_getElem?_getD_eq_getD] at hreach ⊢
          rcases hback target htarget_bound hreach with hqueued | hexplored
          · left
            exact Array.mem_toList_iff.mp hqueued
          · right
            exact hexplored
      · simp [getReachableLitStep, hcur, hexplFalse, hexi] at hreach ⊢
        rw [array_getElem?_getD_eq_getD] at hreach ⊢
        rcases hback target htarget_bound hreach with hqueued | hexplored
        · left
          exact Array.mem_toList_iff.mp hqueued
        · right
          exact hexplored

theorem getReachableLitFold_preserves_backpointerInvariant
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur : Literal}
    (lits : List Literal) {state : Array Literal × Array Bool}
    (hback : ReachBackpointerInvariant state.1 state.2 explored) :
    ReachBackpointerInvariant
      ((lits.foldl (getReachableLitStep st lvar explored cur) state).1)
      ((lits.foldl (getReachableLitStep st lvar explored cur) state).2)
      explored := by
  induction lits generalizing state with
  | nil =>
      simpa using hback
  | cons lit rest ih =>
      rw [List.foldl_cons]
      exact ih
        (state := getReachableLitStep st lvar explored cur state lit)
        (getReachableLitStep_preserves_backpointerInvariant
          (st := st) (lvar := lvar) (explored := explored)
          (cur := cur) (lit := lit) (state := state) hback)

theorem getReachableLitArrayFold_preserves_reach_true
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur : Literal}
    (lits : Array Literal) {state : Array Literal × Array Bool} {target : Nat}
    (h : state.2.getD target false = true) :
    ((lits.foldl (getReachableLitStep st lvar explored cur) state).2).getD target false = true := by
  rw [← Array.foldl_toList]
  exact getReachableLitFold_preserves_reach_true lits.toList h

theorem getReachableLitArrayFold_preserves_worklist_mem
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur keep : Literal}
    (lits : Array Literal) {state : Array Literal × Array Bool}
    (h : keep ∈ state.1.toList) :
    keep ∈ ((lits.foldl (getReachableLitStep st lvar explored cur) state).1).toList := by
  rw [← Array.foldl_toList]
  exact getReachableLitFold_preserves_worklist_mem lits.toList h

theorem getReachableLitArrayFold_reach_size
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur : Literal}
    (lits : Array Literal) {state : Array Literal × Array Bool} :
    ((lits.foldl (getReachableLitStep st lvar explored cur) state).2).size = state.2.size := by
  rw [← Array.foldl_toList]
  exact getReachableLitFold_reach_size lits.toList

theorem getReachableLitArrayFold_preserves_frontierInvariant
    {st : CheckState} {lvar : Var} {explored : Array Bool} {start cur : Literal}
    (lits : Array Literal) {state : Array Literal × Array Bool}
    (hinv : ReachFrontierInvariant start state.1 state.2 explored)
    (hbounds : ∀ lit ∈ lits.toList, lit.x < state.2.size) :
    ReachFrontierInvariant start
      ((lits.foldl (getReachableLitStep st lvar explored cur) state).1)
      ((lits.foldl (getReachableLitStep st lvar explored cur) state).2)
      explored := by
  rw [← Array.foldl_toList]
  exact getReachableLitFold_preserves_frontierInvariant lits.toList hinv hbounds

theorem getReachableLitArrayFold_preserves_backpointerInvariant
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur : Literal}
    (lits : Array Literal) {state : Array Literal × Array Bool}
    (hback : ReachBackpointerInvariant state.1 state.2 explored) :
    ReachBackpointerInvariant
      ((lits.foldl (getReachableLitStep st lvar explored cur) state).1)
      ((lits.foldl (getReachableLitStep st lvar explored cur) state).2)
      explored := by
  rw [← Array.foldl_toList]
  exact getReachableLitFold_preserves_backpointerInvariant lits.toList hback

theorem getReachableLitArrayFold_marks_reach_true
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur target : Literal}
    (lits : Array Literal) {state : Array Literal × Array Bool}
    (hmem : target ∈ lits.toList)
    (hcur : target ≠ cur)
    (hexpl : explored.getD target.negate.x false = false)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((lits.foldl (getReachableLitStep st lvar explored cur) state).2).getD target.x false = true := by
  rw [← Array.foldl_toList]
  exact getReachableLitFold_marks_reach_true lits.toList hmem hcur hexpl hexi hdep hlt

theorem getReachableLitArrayFold_marks_reach_true_of_pre
    {st : CheckState} {lvar : Var} {explored : Array Bool} {cur target : Literal}
    (lits : Array Literal) {state : Array Literal × Array Bool}
    (hmem : target ∈ lits.toList)
    (hcur : target ≠ cur)
    (hpre :
      explored.getD target.negate.x false = true →
        state.2.getD target.x false = true)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((lits.foldl (getReachableLitStep st lvar explored cur) state).2).getD
      target.x false = true := by
  rw [← Array.foldl_toList]
  exact getReachableLitFold_marks_reach_true_of_pre lits.toList
    hmem hcur hpre hexi hdep hlt

theorem getReachableCRefStep_preserves_reach_true
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    {state : Array Literal × Array Bool} {cref : CRef} {target : Nat}
    (h : state.2.getD target false = true) :
    ((getReachableCRefStep st lvar negL explored cur state cref).2).getD target false = true := by
  rcases state with ⟨wl, rch⟩
  unfold getReachableCRefStep
  cases hraw : st.clauses.getClauseRaw cref with
  | none =>
      simp [h]
  | some clause =>
      by_cases hdel : clause.deleted = true
      · simp [hdel, h]
      · by_cases hcontains : negL ∈ clause.lits
        · simp [hdel, hcontains, h]
        · simp [hdel, hcontains]
          rw [array_getElem?_getD_eq_getD]
          exact getReachableLitArrayFold_preserves_reach_true clause.lits h

theorem getReachableCRefStep_preserves_worklist_mem
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur keep : Literal}
    {state : Array Literal × Array Bool} {cref : CRef}
    (h : keep ∈ state.1.toList) :
    keep ∈ ((getReachableCRefStep st lvar negL explored cur state cref).1).toList := by
  rcases state with ⟨wl, rch⟩
  unfold getReachableCRefStep
  cases hraw : st.clauses.getClauseRaw cref with
  | none =>
      simpa using h
  | some clause =>
      by_cases hdel : clause.deleted = true
      · simp [hdel, h]
      · by_cases hcontains : negL ∈ clause.lits
        · simp [hdel, hcontains, h]
        · simp [hdel, hcontains]
          exact Array.mem_toList_iff.mp
            (getReachableLitArrayFold_preserves_worklist_mem clause.lits h)

theorem getReachableCRefStep_marks_reach_true
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur target : Literal}
    {state : Array Literal × Array Bool} {cref : CRef} {clause : Clause}
    (hraw : st.clauses.getClauseRaw cref = some clause)
    (hdel : clause.deleted = false)
    (hnoNeg : negL ∉ clause.lits)
    (hmem : target ∈ clause.lits.toList)
    (hcur : target ≠ cur)
    (hexpl : explored.getD target.negate.x false = false)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((getReachableCRefStep st lvar negL explored cur state cref).2).getD target.x false = true := by
  rcases state with ⟨wl, rch⟩
  unfold getReachableCRefStep
  rw [hraw]
  simp [hdel, hnoNeg]
  rw [array_getElem?_getD_eq_getD]
  exact getReachableLitArrayFold_marks_reach_true clause.lits hmem hcur hexpl hexi hdep hlt

theorem getReachableCRefStep_marks_reach_true_of_pre
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur target : Literal}
    {state : Array Literal × Array Bool} {cref : CRef} {clause : Clause}
    (hraw : st.clauses.getClauseRaw cref = some clause)
    (hdel : clause.deleted = false)
    (hnoNeg : negL ∉ clause.lits)
    (hmem : target ∈ clause.lits.toList)
    (hcur : target ≠ cur)
    (hpre :
      explored.getD target.negate.x false = true →
        state.2.getD target.x false = true)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((getReachableCRefStep st lvar negL explored cur state cref).2).getD
      target.x false = true := by
  rcases state with ⟨wl, rch⟩
  unfold getReachableCRefStep
  rw [hraw]
  simp [hdel, hnoNeg]
  rw [array_getElem?_getD_eq_getD]
  exact getReachableLitArrayFold_marks_reach_true_of_pre clause.lits
    hmem hcur hpre hexi hdep hlt

theorem getReachableCRefStep_reach_size
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    {state : Array Literal × Array Bool} {cref : CRef} :
    ((getReachableCRefStep st lvar negL explored cur state cref).2).size = state.2.size := by
  rcases state with ⟨wl, rch⟩
  unfold getReachableCRefStep
  cases hraw : st.clauses.getClauseRaw cref with
  | none =>
      rfl
  | some clause =>
      by_cases hdel : clause.deleted = true
      · simp [hdel]
      · by_cases hcontains : negL ∈ clause.lits
        · simp [hdel, hcontains]
        · simp [hdel, hcontains]
          exact getReachableLitArrayFold_reach_size clause.lits

theorem getReachableCRefStep_preserves_frontierInvariant
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {start cur : Literal}
    {state : Array Literal × Array Bool} {cref : CRef}
    (hinv : ReachFrontierInvariant start state.1 state.2 explored)
    (hbounds :
      ∀ clause,
        st.clauses.getClauseRaw cref = some clause →
        clause.deleted = false →
        negL ∉ clause.lits →
        ∀ lit ∈ clause.lits.toList, lit.x < state.2.size) :
    ReachFrontierInvariant start
      ((getReachableCRefStep st lvar negL explored cur state cref).1)
      ((getReachableCRefStep st lvar negL explored cur state cref).2)
      explored := by
  rcases state with ⟨wl, rch⟩
  unfold getReachableCRefStep
  cases hraw : st.clauses.getClauseRaw cref with
  | none =>
      simpa using hinv
  | some clause =>
      by_cases hdel : clause.deleted = true
      · simp [hdel]
        exact hinv
      · have hdelFalse : clause.deleted = false := by
          cases h : clause.deleted <;> simp [h] at hdel ⊢
        by_cases hcontains : negL ∈ clause.lits
        · simp [hdelFalse, hcontains]
          exact hinv
        · simp [hdelFalse, hcontains]
          exact getReachableLitArrayFold_preserves_frontierInvariant
            (st := st) (lvar := lvar) (explored := explored)
            (start := start) (cur := cur) (lits := clause.lits)
            (state := (wl, rch)) hinv
            (hbounds clause hraw hdelFalse hcontains)

theorem getReachableCRefStep_preserves_backpointerInvariant
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    {state : Array Literal × Array Bool} {cref : CRef}
    (hback : ReachBackpointerInvariant state.1 state.2 explored) :
    ReachBackpointerInvariant
      ((getReachableCRefStep st lvar negL explored cur state cref).1)
      ((getReachableCRefStep st lvar negL explored cur state cref).2)
      explored := by
  rcases state with ⟨wl, rch⟩
  unfold getReachableCRefStep
  cases hraw : st.clauses.getClauseRaw cref with
  | none =>
      simpa using hback
  | some clause =>
      by_cases hdel : clause.deleted = true
      · simp [hdel]
        exact hback
      · by_cases hcontains : negL ∈ clause.lits
        · simp [hdel, hcontains]
          exact hback
        · simp [hdel, hcontains]
          exact getReachableLitArrayFold_preserves_backpointerInvariant
            (st := st) (lvar := lvar) (explored := explored)
            (cur := cur) (lits := clause.lits) (state := (wl, rch)) hback

theorem getReachableCRefFold_preserves_reach_true
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    (crefs : List CRef) {state : Array Literal × Array Bool} {target : Nat}
    (h : state.2.getD target false = true) :
    ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2).getD target false = true := by
  induction crefs generalizing state with
  | nil =>
      simpa using h
  | cons cref rest ih =>
      rw [List.foldl_cons]
      exact ih (getReachableCRefStep_preserves_reach_true h)

theorem getReachableCRefFold_preserves_worklist_mem
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur keep : Literal}
    (crefs : List CRef) {state : Array Literal × Array Bool}
    (h : keep ∈ state.1.toList) :
    keep ∈ ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).1).toList := by
  induction crefs generalizing state with
  | nil =>
      simpa using h
  | cons cref rest ih =>
      rw [List.foldl_cons]
      exact ih (getReachableCRefStep_preserves_worklist_mem h)

theorem getReachableCRefFold_reach_size
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    (crefs : List CRef) {state : Array Literal × Array Bool} :
    ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2).size = state.2.size := by
  induction crefs generalizing state with
  | nil =>
      rfl
  | cons cref rest ih =>
      rw [List.foldl_cons]
      rw [ih]
      exact getReachableCRefStep_reach_size
        (st := st) (lvar := lvar) (negL := negL)
        (explored := explored) (cur := cur) (state := state) (cref := cref)

theorem getReachableCRefFold_preserves_frontierInvariant
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {start cur : Literal}
    (crefs : List CRef) {state : Array Literal × Array Bool}
    (hinv : ReachFrontierInvariant start state.1 state.2 explored)
    (hbounds :
      ∀ cref ∈ crefs,
        ∀ clause,
          st.clauses.getClauseRaw cref = some clause →
          clause.deleted = false →
          negL ∉ clause.lits →
          ∀ lit ∈ clause.lits.toList, lit.x < state.2.size) :
    ReachFrontierInvariant start
      ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).1)
      ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2)
      explored := by
  induction crefs generalizing state with
  | nil =>
      simpa using hinv
  | cons cref rest ih =>
      rw [List.foldl_cons]
      have hinv' :
          ReachFrontierInvariant start
            (getReachableCRefStep st lvar negL explored cur state cref).1
            (getReachableCRefStep st lvar negL explored cur state cref).2
            explored :=
        getReachableCRefStep_preserves_frontierInvariant
          (st := st) (lvar := lvar) (negL := negL)
          (explored := explored) (start := start) (cur := cur)
          (state := state) (cref := cref) hinv
          (fun clause hraw hdel hnoNeg =>
            hbounds cref (by simp) clause hraw hdel hnoNeg)
      have hsize :
          ((getReachableCRefStep st lvar negL explored cur state cref).2).size =
            state.2.size :=
        getReachableCRefStep_reach_size
          (st := st) (lvar := lvar) (negL := negL)
          (explored := explored) (cur := cur) (state := state) (cref := cref)
      exact ih
        (state := getReachableCRefStep st lvar negL explored cur state cref)
        hinv'
        (fun hit hhit clause hraw hdel hnoNeg lit hlit =>
          by
            have hhit' : hit ∈ cref :: rest := List.mem_cons_of_mem cref hhit
            simpa [hsize] using
              hbounds hit hhit' clause hraw hdel hnoNeg lit hlit)

theorem getReachableCRefFold_preserves_backpointerInvariant
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    (crefs : List CRef) {state : Array Literal × Array Bool}
    (hback : ReachBackpointerInvariant state.1 state.2 explored) :
    ReachBackpointerInvariant
      ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).1)
      ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2)
      explored := by
  induction crefs generalizing state with
  | nil =>
      simpa using hback
  | cons cref rest ih =>
      rw [List.foldl_cons]
      exact ih
        (state := getReachableCRefStep st lvar negL explored cur state cref)
        (getReachableCRefStep_preserves_backpointerInvariant
          (st := st) (lvar := lvar) (negL := negL)
          (explored := explored) (cur := cur)
          (state := state) (cref := cref) hback)

theorem getReachableCRefFold_marks_reach_true
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur target : Literal}
    (crefs : List CRef) {state : Array Literal × Array Bool} {hit : CRef} {clause : Clause}
    (hhit : hit ∈ crefs)
    (hraw : st.clauses.getClauseRaw hit = some clause)
    (hdel : clause.deleted = false)
    (hnoNeg : negL ∉ clause.lits)
    (hmem : target ∈ clause.lits.toList)
    (hcur : target ≠ cur)
    (hexpl : explored.getD target.negate.x false = false)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2).getD target.x false = true := by
  induction crefs generalizing state with
  | nil =>
      simp at hhit
  | cons cref rest ih =>
      rw [List.foldl_cons]
      cases hhit with
      | head =>
          exact getReachableCRefFold_preserves_reach_true rest
            (getReachableCRefStep_marks_reach_true
              (st := st) (lvar := lvar) (negL := negL)
              (explored := explored) (cur := cur) (target := target)
              (state := state) (cref := hit) (clause := clause)
              hraw hdel hnoNeg hmem hcur hexpl hexi hdep hlt)
      | tail _ hrest =>
          have hsize :
              ((getReachableCRefStep st lvar negL explored cur state cref).2).size = state.2.size :=
            getReachableCRefStep_reach_size
              (st := st) (lvar := lvar) (negL := negL)
              (explored := explored) (cur := cur) (state := state) (cref := cref)
          exact ih (state := getReachableCRefStep st lvar negL explored cur state cref)
            hrest (by simpa [hsize] using hlt)

theorem getReachableCRefFold_marks_reach_true_of_pre
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur target : Literal}
    (crefs : List CRef) {state : Array Literal × Array Bool} {hit : CRef} {clause : Clause}
    (hhit : hit ∈ crefs)
    (hraw : st.clauses.getClauseRaw hit = some clause)
    (hdel : clause.deleted = false)
    (hnoNeg : negL ∉ clause.lits)
    (hmem : target ∈ clause.lits.toList)
    (hcur : target ≠ cur)
    (hpre :
      explored.getD target.negate.x false = true →
        state.2.getD target.x false = true)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2).getD
      target.x false = true := by
  induction crefs generalizing state with
  | nil =>
      simp at hhit
  | cons cref rest ih =>
      rw [List.foldl_cons]
      cases hhit with
      | head =>
          exact getReachableCRefFold_preserves_reach_true rest
            (getReachableCRefStep_marks_reach_true_of_pre
              (st := st) (lvar := lvar) (negL := negL)
              (explored := explored) (cur := cur) (target := target)
              (state := state) (cref := hit) (clause := clause)
              hraw hdel hnoNeg hmem hcur hpre hexi hdep hlt)
      | tail _ hrest =>
          have hsize :
              ((getReachableCRefStep st lvar negL explored cur state cref).2).size = state.2.size :=
            getReachableCRefStep_reach_size
              (st := st) (lvar := lvar) (negL := negL)
              (explored := explored) (cur := cur) (state := state) (cref := cref)
          exact ih (state := getReachableCRefStep st lvar negL explored cur state cref)
            hrest
            (fun hexpl =>
              getReachableCRefStep_preserves_reach_true (hpre hexpl))
            (by simpa [hsize] using hlt)

theorem getReachableCRefArrayFold_preserves_reach_true
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    (crefs : Array CRef) {state : Array Literal × Array Bool} {target : Nat}
    (h : state.2.getD target false = true) :
    ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2).getD target false = true := by
  rw [← Array.foldl_toList]
  exact getReachableCRefFold_preserves_reach_true crefs.toList h

theorem getReachableCRefArrayFold_preserves_worklist_mem
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur keep : Literal}
    (crefs : Array CRef) {state : Array Literal × Array Bool}
    (h : keep ∈ state.1.toList) :
    keep ∈ ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).1).toList := by
  rw [← Array.foldl_toList]
  exact getReachableCRefFold_preserves_worklist_mem crefs.toList h

theorem getReachableCRefArrayFold_reach_size
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    (crefs : Array CRef) {state : Array Literal × Array Bool} :
    ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2).size = state.2.size := by
  rw [← Array.foldl_toList]
  exact getReachableCRefFold_reach_size crefs.toList

theorem getReachableCRefArrayFold_preserves_frontierInvariant
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {start cur : Literal}
    (crefs : Array CRef) {state : Array Literal × Array Bool}
    (hinv : ReachFrontierInvariant start state.1 state.2 explored)
    (hbounds :
      ∀ cref ∈ crefs.toList,
        ∀ clause,
          st.clauses.getClauseRaw cref = some clause →
          clause.deleted = false →
          negL ∉ clause.lits →
          ∀ lit ∈ clause.lits.toList, lit.x < state.2.size) :
    ReachFrontierInvariant start
      ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).1)
      ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2)
      explored := by
  rw [← Array.foldl_toList]
  exact getReachableCRefFold_preserves_frontierInvariant crefs.toList hinv hbounds

theorem getReachableCRefArrayFold_preserves_backpointerInvariant
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur : Literal}
    (crefs : Array CRef) {state : Array Literal × Array Bool}
    (hback : ReachBackpointerInvariant state.1 state.2 explored) :
    ReachBackpointerInvariant
      ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).1)
      ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2)
      explored := by
  rw [← Array.foldl_toList]
  exact getReachableCRefFold_preserves_backpointerInvariant crefs.toList hback

theorem ReachBackpointerInvariant_pop_of_explored
    {worklist wl' : Array Literal} {reach expl : Array Bool} {cur : Literal}
    (hcur : cur = worklist.getD (worklist.size - 1) ⟨0⟩)
    (hwl' : wl' = worklist.pop)
    (hexplCur : expl.getD cur.x false = true)
    (hback : ReachBackpointerInvariant worklist reach expl) :
    ReachBackpointerInvariant wl' reach expl := by
  subst wl'
  unfold ReachBackpointerInvariant at hback ⊢
  intro lit hbound hreach
  rcases hback lit hbound hreach with hqueued | hexplored
  · by_cases hlit_cur : lit.negate = cur
    · right
      simpa [hlit_cur] using hexplCur
    · left
      exact array_mem_pop_of_mem_ne_getD_last
        (xs := worklist) (x := lit.negate) ⟨0⟩ hqueued
        (by
          intro heq
          exact hlit_cur (by simpa [hcur] using heq))
  · right
    exact hexplored

theorem ReachBackpointerInvariant_pop_of_outOfBounds
    {worklist wl' : Array Literal} {reach expl : Array Bool} {cur : Literal}
    (hcur : cur = worklist.getD (worklist.size - 1) ⟨0⟩)
    (hwl' : wl' = worklist.pop)
    (hcur_oob : ¬ cur.x < expl.size)
    (hback : ReachBackpointerInvariant worklist reach expl) :
    ReachBackpointerInvariant wl' reach expl := by
  subst wl'
  unfold ReachBackpointerInvariant at hback ⊢
  intro lit hbound hreach
  rcases hback lit hbound hreach with hqueued | hexplored
  · by_cases hlit_cur : lit.negate = cur
    · exact False.elim (hcur_oob (by simpa [hlit_cur] using hbound))
    · left
      exact array_mem_pop_of_mem_ne_getD_last
        (xs := worklist) (x := lit.negate) ⟨0⟩ hqueued
        (by
          intro heq
          exact hlit_cur (by simpa [hcur] using heq))
  · right
    exact hexplored

theorem ReachBackpointerInvariant_pop_set_current
    {worklist wl' : Array Literal} {reach expl : Array Bool} {cur : Literal}
    {idx : Nat}
    (hcur : cur = worklist.getD (worklist.size - 1) ⟨0⟩)
    (hwl' : wl' = worklist.pop)
    (hidx_eq : idx = cur.x)
    (hidx : idx < expl.size)
    (hback : ReachBackpointerInvariant worklist reach expl) :
    ReachBackpointerInvariant wl' reach (expl.set idx true hidx) := by
  subst wl'
  subst idx
  unfold ReachBackpointerInvariant at hback ⊢
  intro lit hbound hreach
  have hboundOld : lit.negate.x < expl.size := by
    simpa [Array.size_set hidx] using hbound
  rcases hback lit hboundOld hreach with hqueued | hexplored
  · by_cases hlit_cur : lit.negate = cur
    · right
      have hself : (expl.set cur.x true hidx).getD cur.x false = true := by
        have hidx' : cur.x < (expl.set cur.x true hidx).size := by
          simpa [Array.size_set hidx] using hidx
        have hget : (expl.set cur.x true hidx)[cur.x]'hidx' = true :=
          Array.getElem_set_self (xs := expl) (i := cur.x) hidx (v := true)
        rw [Array.getElem_eq_getD
          (xs := expl.set cur.x true hidx) (i := cur.x) (h := hidx') false] at hget
        exact hget
      simp [hlit_cur, hself]
    · left
      exact array_mem_pop_of_mem_ne_getD_last
        (xs := worklist) (x := lit.negate) ⟨0⟩ hqueued
        (by
          intro heq
          exact hlit_cur (by simpa [hcur] using heq))
  · right
    exact array_set_true_preserves_getD expl cur.x lit.negate.x hidx hexplored

theorem getReachableCRefArrayFold_marks_reach_true
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur target : Literal}
    (crefs : Array CRef) {state : Array Literal × Array Bool} {hit : CRef} {clause : Clause}
    (hhit : hit ∈ crefs.toList)
    (hraw : st.clauses.getClauseRaw hit = some clause)
    (hdel : clause.deleted = false)
    (hnoNeg : negL ∉ clause.lits)
    (hmem : target ∈ clause.lits.toList)
    (hcur : target ≠ cur)
    (hexpl : explored.getD target.negate.x false = false)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2).getD target.x false = true := by
  rw [← Array.foldl_toList]
  exact getReachableCRefFold_marks_reach_true crefs.toList hhit
    hraw hdel hnoNeg hmem hcur hexpl hexi hdep hlt

theorem getReachableCRefArrayFold_marks_reach_true_of_pre
    {st : CheckState} {lvar : Var} {negL : Literal}
    {explored : Array Bool} {cur target : Literal}
    (crefs : Array CRef) {state : Array Literal × Array Bool} {hit : CRef} {clause : Clause}
    (hhit : hit ∈ crefs.toList)
    (hraw : st.clauses.getClauseRaw hit = some clause)
    (hdel : clause.deleted = false)
    (hnoNeg : negL ∉ clause.lits)
    (hmem : target ∈ clause.lits.toList)
    (hcur : target ≠ cur)
    (hpre :
      explored.getD target.negate.x false = true →
        state.2.getD target.x false = true)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < state.2.size) :
    ((crefs.foldl (getReachableCRefStep st lvar negL explored cur) state).2).getD
      target.x false = true := by
  rw [← Array.foldl_toList]
  exact getReachableCRefFold_marks_reach_true_of_pre crefs.toList hhit
    hraw hdel hnoNeg hmem hcur hpre hexi hdep hlt

theorem getReachableCRefArrayFold_processedInvariant_after_current
    {st : CheckState} {lvar : Var} {negL start cur : Literal}
    {worklist wl' : Array Literal} {reach expl : Array Bool}
    (hnegL : negL = start.negate)
    (hcur_lt : cur.x < expl.size)
    (hfront : ReachFrontierInvariant start worklist reach expl)
    (hproc : ReachProcessedInvariant st lvar negL reach expl)
    (hcur_mem : cur ∈ worklist.toList) :
    ReachProcessedInvariant st lvar negL
      (((st.clauses.getOcc cur).foldl
        (getReachableCRefStep st lvar negL (expl.set cur.x true hcur_lt) cur)
        (wl', reach)).2)
      (expl.set cur.x true hcur_lt) := by
  intro seen hseen cref' clause' target' hocc' hraw' hdel' hnoNeg'
    hmem' hne' hexi' hdep' hlt'
  have hsize_fold :
      (((st.clauses.getOcc cur).foldl
        (getReachableCRefStep st lvar negL (expl.set cur.x true hcur_lt) cur)
        (wl', reach)).2).size = reach.size :=
    getReachableCRefArrayFold_reach_size
      (st := st) (lvar := lvar) (negL := negL)
      (explored := expl.set cur.x true hcur_lt) (cur := cur)
      (crefs := st.clauses.getOcc cur) (state := (wl', reach))
  by_cases hx : seen.x = cur.x
  · have hseen_cur : seen = cur := literal_eq_of_x_eq hx
    subst seen
    have hpre :
        (expl.set cur.x true hcur_lt).getD target'.negate.x false = true →
          reach.getD target'.x false = true := by
      intro hexplTarget
      by_cases htarget_cur : target'.negate.x = cur.x
      · have htarget_eq : target' = cur.negate :=
          literal_eq_negate_of_negate_x_eq
            (a := target') (b := cur) htarget_cur
        by_cases hcur_start : cur = start
        · have hneg_mem : negL ∈ clause'.lits := by
            have hmem_start : start.negate ∈ clause'.lits.toList := by
              simpa [htarget_eq, hcur_start] using hmem'
            have hmem_arr : start.negate ∈ clause'.lits :=
              Array.mem_toList_iff.mp hmem_start
            simpa [hnegL] using hmem_arr
          exact False.elim (hnoNeg' hneg_mem)
        · simpa [htarget_eq] using hfront.1 cur hcur_mem hcur_start
      · have hcur_ne_target : cur.x ≠ target'.negate.x := by
          intro hcur_eq
          exact htarget_cur hcur_eq.symm
        have hexplOld : expl.getD target'.negate.x false = true := by
          rw [array_set_getD_ne expl cur.x target'.negate.x true false
            hcur_lt hcur_ne_target] at hexplTarget
          exact hexplTarget
        have htarget_ne_start : target'.negate ≠ start := by
          intro hstart
          have htarget_eq_startNeg : target' = start.negate := by
            rw [← literal_negate_negate_local target', hstart]
          have hneg_mem : negL ∈ clause'.lits := by
            have hmem_arr : start.negate ∈ clause'.lits :=
              Array.mem_toList_iff.mp (by simpa [htarget_eq_startNeg] using hmem')
            simpa [hnegL] using hmem_arr
          exact hnoNeg' hneg_mem
        simpa [literal_negate_negate_local] using
          hfront.2 target'.negate hexplOld htarget_ne_start
    exact getReachableCRefArrayFold_marks_reach_true_of_pre
      (st := st) (lvar := lvar) (negL := negL)
      (explored := expl.set cur.x true hcur_lt) (cur := cur) (target := target')
      (crefs := st.clauses.getOcc cur) (state := (wl', reach))
      (hit := cref') (clause := clause')
      hocc' hraw' hdel' hnoNeg' hmem' hne' hpre hexi' hdep'
      (by simpa [hsize_fold] using hlt')
  · have hcur_ne_seen : cur.x ≠ seen.x := by
      intro hcur_eq
      exact hx hcur_eq.symm
    have hseenOld : expl.getD seen.x false = true := by
      rw [array_set_getD_ne expl cur.x seen.x true false hcur_lt hcur_ne_seen] at hseen
      exact hseen
    exact getReachableCRefArrayFold_preserves_reach_true
      (st := st) (lvar := lvar) (negL := negL)
      (explored := expl.set cur.x true hcur_lt) (cur := cur)
      (crefs := st.clauses.getOcc cur) (state := (wl', reach))
      (hproc seen hseenOld cref' clause' target' hocc' hraw' hdel'
        hnoNeg' hmem' hne' hexi' hdep'
        (by simpa [hsize_fold] using hlt'))

theorem getReachable_go_preserves_reach_true
    (st : CheckState) (lvar : Var) (negL : Literal)
    (worklist : Array Literal) (reach expl : Array Bool) {target : Nat}
    (h : reach.getD target false = true) :
    (getReachable.go st lvar negL worklist reach expl).getD target false = true := by
  let motive : Array Literal → Array Bool → Array Bool → Prop :=
    fun worklist reach expl =>
      ∀ {target : Nat}, reach.getD target false = true →
        (getReachable.go st lvar negL worklist reach expl).getD target false = true
  exact getReachable.go.induct st lvar negL motive
    (by
      intro worklist reach expl hempty target h
      rw [getReachable.go.eq_1]
      rw [if_pos hempty]
      exact h)
    (by
      intro worklist reach expl hne cur wl' idx hexpl ih target h
      rw [getReachable.go.eq_1]
      rw [if_neg hne]
      rw [if_pos hexpl]
      exact ih h)
    (by
      intro worklist reach expl hne cur wl' idx hexpl hidx expl' occs wl2 rch2 hfold ih target h
      rw [getReachable.go.eq_1]
      rw [if_neg hne]
      rw [if_neg hexpl]
      rw [dif_pos hidx]
      simp [cur, wl', idx, expl', occs] at hfold ⊢
      have hfold_pres :=
        (getReachableCRefArrayFold_preserves_reach_true
          (st := st) (lvar := lvar) (negL := negL)
          (explored := expl') (cur := cur) (state := (wl', reach)) occs h)
      simp [cur, wl', idx, expl', occs] at hfold_pres
      rw [hfold] at hfold_pres
      have hrch2 : rch2.getD target false = true := by
        simpa [Array.getD_eq_getD_getElem?] using hfold_pres
      rw [hfold]
      simpa [Array.getD_eq_getD_getElem?, cur, wl', idx, expl'] using ih hrch2)
    (by
      intro worklist reach expl hne cur wl' idx hexpl hidx ih target h
      rw [getReachable.go.eq_1]
      rw [if_neg hne]
      rw [if_neg hexpl]
      rw [dif_neg hidx]
      exact ih h)
    worklist reach expl h

theorem getReachable_go_worklist_clause_marks_reach_true_of_invariants
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hfull : CheckState.FullCorrect dqbf cs st)
    {lvar : Var} {negL start prev target : Literal}
    {worklist : Array Literal} {reach expl : Array Bool}
    {cref : CRef} {clause : Clause}
    (hnegL : negL = start.negate)
    (hbound :
      ∀ cref clause lit,
        st.clauses.getClauseRaw cref = some clause →
        clause.deleted = false →
        lit ∈ clause.lits.toList →
        lit.x < reach.size)
    (hfront : ReachFrontierInvariant start worklist reach expl)
    (hproc : ReachProcessedInvariant st lvar negL reach expl)
    (hprevIn : prev.negate ∈ worklist.toList)
    (hprevNeg_lt : prev.negate.x < expl.size)
    (hget : st.clauses.getClause cref = some clause)
    (hprev : prev.negate ∈ clause.lits.toList)
    (hnoNeg : negL ∉ clause.lits.toList)
    (hmem : target ∈ clause.lits.toList)
    (hne : target ≠ prev.negate)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < reach.size) :
    (getReachable.go st lvar negL worklist reach expl).getD target.x false = true := by
  rcases getClauseRaw_deleted_of_getClause hget with ⟨hraw, hdel⟩
  have hoccArr : cref ∈ st.clauses.getOcc prev.negate :=
    ClauseStore.mem_getOcc_of_liveOccurrencesComplete
      hfull.liveOccurrencesComplete hget hprev
  have hocc : cref ∈ (st.clauses.getOcc prev.negate).toList :=
    Array.mem_toList_iff.mpr hoccArr
  have hnoNegArr : negL ∉ clause.lits := by
    intro hneg
    exact hnoNeg (Array.mem_toList_iff.mpr hneg)
  let motive : Array Literal → Array Bool → Array Bool → Prop :=
    fun worklist reach expl =>
      (∀ cref clause lit,
        st.clauses.getClauseRaw cref = some clause →
        clause.deleted = false →
        lit ∈ clause.lits.toList →
        lit.x < reach.size) →
      ReachFrontierInvariant start worklist reach expl →
      ReachProcessedInvariant st lvar negL reach expl →
      prev.negate.x < expl.size →
      prev.negate ∈ worklist.toList →
      target.x < reach.size →
      (getReachable.go st lvar negL worklist reach expl).getD target.x false = true
  exact getReachable.go.induct st lvar negL motive
    (by
      intro worklist reach expl hempty _hbound _hfront _hproc _hprevNeg_lt hprevIn _hlt
      have hsize : worklist.size = 0 := by
        simpa [Array.isEmpty_iff_size_eq_zero] using hempty
      have hnil : worklist.toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa [Array.length_toList] using hsize
      rw [hnil] at hprevIn
      simp at hprevIn)
    (by
      intro worklist reach expl hneEmpty cur wl' idx hexplCur ih
        hbound hfront hproc hprevNeg_lt hprevIn hlt
      rw [getReachable.go.eq_1]
      rw [if_neg hneEmpty]
      rw [if_pos hexplCur]
      by_cases hsame : prev.negate = cur
      · have hreach : reach.getD target.x false = true := by
          exact hproc cur hexplCur cref clause target
            (by simpa [hsame] using hocc) hraw hdel hnoNegArr hmem
            (by simpa [hsame] using hne) hexi hdep hlt
        exact getReachable_go_preserves_reach_true
          st lvar negL wl' reach expl hreach
      · have hfront' : ReachFrontierInvariant start wl' reach expl := by
          rcases hfront with ⟨hwl, hexplInv⟩
          constructor
          · intro lit hlit hlit_ne_start
            have hlit_old : lit ∈ worklist.toList := by
              simp [wl'] at hlit
              exact List.dropLast_subset _ hlit
            exact hwl lit hlit_old hlit_ne_start
          · exact hexplInv
        have hprevIn' : prev.negate ∈ wl'.toList := by
          simpa [wl'] using
            (array_mem_pop_of_mem_ne_getD_last
              (xs := worklist) (x := prev.negate) ⟨0⟩ hprevIn
              (by simpa [cur] using hsame))
        exact ih hbound hfront' hproc hprevNeg_lt hprevIn' hlt)
    (by
      intro worklist reach expl hneEmpty cur wl' idx hexplCur hidx expl' occs wl2 rch2 hfold ih
        hbound hfront hproc hprevNeg_lt hprevIn hlt
      rw [getReachable.go.eq_1]
      rw [if_neg hneEmpty]
      rw [if_neg hexplCur]
      rw [dif_pos hidx]
      have hcur_mem : cur ∈ worklist.toList := by
        have hlist_ne : worklist.toList ≠ [] := by
          intro hnil
          have hempty : worklist.isEmpty = true := by
            have hsize : worklist.size = 0 := by
              simp [← Array.length_toList, hnil]
            simpa [Array.isEmpty_iff_size_eq_zero] using hsize
          exact hneEmpty hempty
        simpa [cur] using
          (array_getD_last_mem_toList (xs := worklist) ⟨0⟩ hlist_ne :
            worklist.getD (worklist.size - 1) ⟨0⟩ ∈ worklist.toList)
      have hfront_expl : ReachFrontierInvariant start wl' reach expl' := by
        rcases hfront with ⟨hwl, hexplInv⟩
        constructor
        · intro lit hlit hlit_ne_start
          have hlit_old : lit ∈ worklist.toList := by
            simp [wl'] at hlit
            exact List.dropLast_subset _ hlit
          exact hwl lit hlit_old hlit_ne_start
        · intro lit hexplLit hlit_ne_start
          by_cases hx : lit.x = cur.x
          · have hlit_cur : lit = cur := literal_eq_of_x_eq hx
            subst lit
            exact hwl cur hcur_mem hlit_ne_start
          · have hidx_ne : idx ≠ lit.x := by
              intro hidx_eq
              exact hx (by simpa [idx] using hidx_eq.symm)
            have hexplOld : expl.getD lit.x false = true := by
              rw [array_set_getD_ne expl idx lit.x true false hidx hidx_ne] at hexplLit
              simpa [expl'] using hexplLit
            exact hexplInv lit hexplOld hlit_ne_start
      have hsize_fold₀ :
          (((st.clauses.getOcc cur).foldl
            (getReachableCRefStep st lvar negL expl' cur)
            (wl', reach)).2).size = reach.size :=
        getReachableCRefArrayFold_reach_size
          (st := st) (lvar := lvar) (negL := negL)
          (explored := expl') (cur := cur)
          (crefs := st.clauses.getOcc cur) (state := (wl', reach))
      have hfront_fold₀ :
          ReachFrontierInvariant start
            (((st.clauses.getOcc cur).foldl
              (getReachableCRefStep st lvar negL expl' cur)
              (wl', reach)).1)
            (((st.clauses.getOcc cur).foldl
              (getReachableCRefStep st lvar negL expl' cur)
              (wl', reach)).2)
            expl' := by
        exact getReachableCRefArrayFold_preserves_frontierInvariant
          (st := st) (lvar := lvar) (negL := negL)
          (explored := expl') (start := start) (cur := cur)
          (crefs := st.clauses.getOcc cur) (state := (wl', reach))
          hfront_expl
          (fun cref _hcref clause hraw hdel _hnoNeg lit hlit =>
            hbound cref clause lit hraw hdel hlit)
      have hproc_fold₀ :
          ReachProcessedInvariant st lvar negL
            (((st.clauses.getOcc cur).foldl
              (getReachableCRefStep st lvar negL expl' cur)
              (wl', reach)).2)
            expl' := by
        intro seen hseen cref' clause' target' hocc' hraw' hdel' hnoNeg'
          hmem' hne' hexi' hdep' hlt'
        by_cases hx : seen.x = cur.x
        · have hseen_cur : seen = cur := literal_eq_of_x_eq hx
          subst seen
          have hpre :
              expl'.getD target'.negate.x false = true →
                reach.getD target'.x false = true := by
            intro hexplTarget
            by_cases htarget_cur : target'.negate.x = cur.x
            · have htarget_eq : target' = cur.negate :=
                literal_eq_negate_of_negate_x_eq
                  (a := target') (b := cur) htarget_cur
              by_cases hcur_start : cur = start
              · have hneg_mem : negL ∈ clause'.lits := by
                  have hmem_start : start.negate ∈ clause'.lits.toList := by
                    simpa [htarget_eq, hcur_start] using hmem'
                  have hmem_arr : start.negate ∈ clause'.lits :=
                    Array.mem_toList_iff.mp hmem_start
                  simpa [hnegL] using hmem_arr
                exact False.elim (hnoNeg' hneg_mem)
              · simpa [htarget_eq] using hfront.1 cur hcur_mem hcur_start
            · have hidx_ne : idx ≠ target'.negate.x := by
                intro hidx_eq
                exact htarget_cur (by simpa [idx] using hidx_eq.symm)
              have hexplOld : expl.getD target'.negate.x false = true := by
                rw [array_set_getD_ne expl idx target'.negate.x true false hidx hidx_ne]
                  at hexplTarget
                simpa [expl'] using hexplTarget
              have htarget_ne_start : target'.negate ≠ start := by
                intro hstart
                have htarget_eq_startNeg : target' = start.negate := by
                  rw [← literal_negate_negate_local target', hstart]
                have hneg_mem : negL ∈ clause'.lits := by
                  have hmem_arr : start.negate ∈ clause'.lits :=
                    Array.mem_toList_iff.mp (by simpa [htarget_eq_startNeg] using hmem')
                  simpa [hnegL] using hmem_arr
                exact hnoNeg' hneg_mem
              simpa [literal_negate_negate_local] using
                hfront.2 target'.negate hexplOld htarget_ne_start
          exact getReachableCRefArrayFold_marks_reach_true_of_pre
            (st := st) (lvar := lvar) (negL := negL)
            (explored := expl') (cur := cur) (target := target')
            (crefs := st.clauses.getOcc cur) (state := (wl', reach))
            (hit := cref') (clause := clause')
            hocc' hraw' hdel' hnoNeg' hmem' hne' hpre hexi' hdep'
            (by simpa [hsize_fold₀] using hlt')
        · have hidx_ne : idx ≠ seen.x := by
            intro hidx_eq
            exact hx (by simpa [idx] using hidx_eq.symm)
          have hseenOld : expl.getD seen.x false = true := by
            rw [array_set_getD_ne expl idx seen.x true false hidx hidx_ne] at hseen
            simpa [expl'] using hseen
          exact getReachableCRefArrayFold_preserves_reach_true
            (st := st) (lvar := lvar) (negL := negL)
            (explored := expl') (cur := cur)
            (crefs := st.clauses.getOcc cur) (state := (wl', reach))
            (hproc seen hseenOld cref' clause' target' hocc' hraw' hdel'
              hnoNeg' hmem' hne' hexi' hdep'
              (by simpa [hsize_fold₀] using hlt'))
      have hfront_fold : ReachFrontierInvariant start wl2 rch2 expl' := by
        rw [hfold] at hfront_fold₀
        exact hfront_fold₀
      have hproc_fold : ReachProcessedInvariant st lvar negL rch2 expl' := by
        rw [hfold] at hproc_fold₀
        exact hproc_fold₀
      have hsize_fold : rch2.size = reach.size := by
        rw [hfold] at hsize_fold₀
        exact hsize_fold₀
      have hbound' :
          ∀ cref clause lit,
            st.clauses.getClauseRaw cref = some clause →
            clause.deleted = false →
            lit ∈ clause.lits.toList →
            lit.x < rch2.size := by
        intro cref clause lit hraw hdel hlit
        simpa [hsize_fold] using hbound cref clause lit hraw hdel hlit
      have hcurExpl : expl'.getD cur.x false = true := by
        simp [expl', idx]
      by_cases hsame : prev.negate = cur
      · have hreach : rch2.getD target.x false = true := by
          exact hproc_fold cur hcurExpl cref clause target
            (by simpa [hsame] using hocc) hraw hdel hnoNegArr hmem
            (by simpa [hsame] using hne) hexi hdep
            (by simpa [hsize_fold] using hlt)
        simp [cur, wl', idx, expl', occs] at hfold ⊢
        rw [hfold]
        simpa [cur, wl', idx, expl', occs] using
          getReachable_go_preserves_reach_true
            st lvar negL wl2 rch2 expl' hreach
      · have hprevIn_wl' : prev.negate ∈ wl'.toList := by
          simpa [wl'] using
            (array_mem_pop_of_mem_ne_getD_last
              (xs := worklist) (x := prev.negate) ⟨0⟩ hprevIn
              (by simpa [cur] using hsame))
        have hprevIn_fold₀ :
            prev.negate ∈
              (((st.clauses.getOcc cur).foldl
                (getReachableCRefStep st lvar negL expl' cur)
                (wl', reach)).1).toList :=
          getReachableCRefArrayFold_preserves_worklist_mem
            (st := st) (lvar := lvar) (negL := negL)
            (explored := expl') (cur := cur)
            (crefs := st.clauses.getOcc cur) (state := (wl', reach))
            hprevIn_wl'
        have hprevIn_fold : prev.negate ∈ wl2.toList := by
          rw [hfold] at hprevIn_fold₀
          exact hprevIn_fold₀
        simp [cur, wl', idx, expl', occs] at hfold ⊢
        rw [hfold]
        simpa [cur, wl', idx, expl', occs] using
          ih hbound' hfront_fold hproc_fold
            (by simpa [expl'] using hprevNeg_lt) hprevIn_fold
            (by simpa [hsize_fold] using hlt))
    (by
      intro worklist reach expl hneEmpty cur wl' idx hexplCur hidx ih
        hbound hfront hproc hprevNeg_lt hprevIn hlt
      rw [getReachable.go.eq_1]
      rw [if_neg hneEmpty]
      rw [if_neg hexplCur]
      rw [dif_neg hidx]
      by_cases hsame : prev.negate = cur
      · exact False.elim (hidx (by simpa [idx, hsame] using hprevNeg_lt))
      · have hfront' : ReachFrontierInvariant start wl' reach expl := by
          rcases hfront with ⟨hwl, hexplInv⟩
          constructor
          · intro lit hlit hlit_ne_start
            have hlit_old : lit ∈ worklist.toList := by
              simp [wl'] at hlit
              exact List.dropLast_subset _ hlit
            exact hwl lit hlit_old hlit_ne_start
          · exact hexplInv
        have hprevIn' : prev.negate ∈ wl'.toList := by
          simpa [wl'] using
            (array_mem_pop_of_mem_ne_getD_last
              (xs := worklist) (x := prev.negate) ⟨0⟩ hprevIn
              (by simpa [cur] using hsame))
        exact ih hbound hfront' hproc hprevNeg_lt hprevIn' hlt)
    worklist reach expl hbound hfront hproc hprevNeg_lt hprevIn hlt

theorem getReachable_go_current_reachable_clause_marks_reach_true_of_invariants
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hfull : CheckState.FullCorrect dqbf cs st)
    {lvar : Var} {negL start prev target : Literal}
    {worklist : Array Literal} {reach expl : Array Bool}
    {cref : CRef} {clause : Clause}
    (hnegL : negL = start.negate)
    (hbound :
      ∀ cref clause lit,
        st.clauses.getClauseRaw cref = some clause →
        clause.deleted = false →
        lit ∈ clause.lits.toList →
        lit.x < reach.size)
    (hfront : ReachFrontierInvariant start worklist reach expl)
    (hproc : ReachProcessedInvariant st lvar negL reach expl)
    (hback : ReachBackpointerInvariant worklist reach expl)
    (hprevNeg_lt : prev.negate.x < expl.size)
    (hprevReach : reach.getD prev.x false = true)
    (hget : st.clauses.getClause cref = some clause)
    (hprev : prev.negate ∈ clause.lits.toList)
    (hnoNeg : negL ∉ clause.lits.toList)
    (hmem : target ∈ clause.lits.toList)
    (hne : target ≠ prev.negate)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < reach.size) :
    (getReachable.go st lvar negL worklist reach expl).getD target.x false = true := by
  rcases getClauseRaw_deleted_of_getClause hget with ⟨hraw, hdel⟩
  have hoccArr : cref ∈ st.clauses.getOcc prev.negate :=
    ClauseStore.mem_getOcc_of_liveOccurrencesComplete
      hfull.liveOccurrencesComplete hget hprev
  have hocc : cref ∈ (st.clauses.getOcc prev.negate).toList :=
    Array.mem_toList_iff.mpr hoccArr
  have hnoNegArr : negL ∉ clause.lits := by
    intro hneg
    exact hnoNeg (Array.mem_toList_iff.mpr hneg)
  rcases hback prev hprevNeg_lt hprevReach with hqueued | hexplPrev
  · exact getReachable_go_worklist_clause_marks_reach_true_of_invariants
      (hfull := hfull)
      (hnegL := hnegL)
      (hbound := hbound)
      (hfront := hfront)
      (hproc := hproc)
      (hprevIn := hqueued)
      (hprevNeg_lt := hprevNeg_lt)
      (hget := hget)
      (hprev := hprev)
      (hnoNeg := hnoNeg)
      (hmem := hmem)
      (hne := hne)
      (hexi := hexi)
      (hdep := hdep)
      (hlt := hlt)
  · have hreach : reach.getD target.x false = true :=
      hproc prev.negate hexplPrev cref clause target
        hocc hraw hdel hnoNegArr hmem hne hexi hdep hlt
    exact getReachable_go_preserves_reach_true st lvar negL worklist reach expl hreach

theorem getReachable_go_final_reachable_clause_marks_reach_true_of_invariants
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hfull : CheckState.FullCorrect dqbf cs st)
    {lvar : Var} {negL start prev target : Literal}
    {worklist : Array Literal} {reach expl : Array Bool}
    {cref : CRef} {clause : Clause}
    (hnegL : negL = start.negate)
    (hbound :
      ∀ cref clause lit,
        st.clauses.getClauseRaw cref = some clause →
        clause.deleted = false →
        lit ∈ clause.lits.toList →
        lit.x < reach.size)
    (hfront : ReachFrontierInvariant start worklist reach expl)
    (hproc : ReachProcessedInvariant st lvar negL reach expl)
    (hback : ReachBackpointerInvariant worklist reach expl)
    (hprevNeg_lt : prev.negate.x < expl.size)
    (hfinalPrev :
      (getReachable.go st lvar negL worklist reach expl).getD prev.x false = true)
    (hget : st.clauses.getClause cref = some clause)
    (hprev : prev.negate ∈ clause.lits.toList)
    (hnoNeg : negL ∉ clause.lits.toList)
    (hmem : target ∈ clause.lits.toList)
    (hne : target ≠ prev.negate)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains lvar = true)
    (hlt : target.x < reach.size) :
    (getReachable.go st lvar negL worklist reach expl).getD target.x false = true := by
  let motive : Array Literal → Array Bool → Array Bool → Prop :=
    fun worklist reach expl =>
      (∀ cref clause lit,
        st.clauses.getClauseRaw cref = some clause →
        clause.deleted = false →
        lit ∈ clause.lits.toList →
        lit.x < reach.size) →
      ReachFrontierInvariant start worklist reach expl →
      ReachProcessedInvariant st lvar negL reach expl →
      ReachBackpointerInvariant worklist reach expl →
      prev.negate.x < expl.size →
      (getReachable.go st lvar negL worklist reach expl).getD prev.x false = true →
      target.x < reach.size →
      (getReachable.go st lvar negL worklist reach expl).getD target.x false = true
  exact getReachable.go.induct st lvar negL motive
    (by
      intro worklist reach expl hempty hbound hfront hproc hback hprevNeg_lt
        hfinalPrev hlt
      rw [getReachable.go.eq_1] at hfinalPrev ⊢
      rw [if_pos hempty] at hfinalPrev ⊢
      have hmark :=
        getReachable_go_current_reachable_clause_marks_reach_true_of_invariants
          (hfull := hfull)
          (hnegL := hnegL)
          (hbound := hbound)
          (hfront := hfront)
          (hproc := hproc)
          (hback := hback)
          (hprevNeg_lt := hprevNeg_lt)
          (hprevReach := hfinalPrev)
          (hget := hget)
          (hprev := hprev)
          (hnoNeg := hnoNeg)
          (hmem := hmem)
          (hne := hne)
          (hexi := hexi)
          (hdep := hdep)
          (hlt := hlt)
      simpa [getReachable.go.eq_1, hempty] using hmark)
    (by
      intro worklist reach expl hneEmpty cur wl' idx hexplCur ih
        hbound hfront hproc hback hprevNeg_lt hfinalPrev hlt
      rw [getReachable.go.eq_1] at hfinalPrev ⊢
      rw [if_neg hneEmpty] at hfinalPrev ⊢
      rw [if_pos hexplCur] at hfinalPrev ⊢
      have hfront' : ReachFrontierInvariant start wl' reach expl := by
        rcases hfront with ⟨hwl, hexplInv⟩
        constructor
        · intro lit hlit hlit_ne_start
          have hlit_old : lit ∈ worklist.toList := by
            simp [wl'] at hlit
            exact List.dropLast_subset _ hlit
          exact hwl lit hlit_old hlit_ne_start
        · exact hexplInv
      have hback' : ReachBackpointerInvariant wl' reach expl :=
        ReachBackpointerInvariant_pop_of_explored
          (cur := cur) (hcur := rfl) (hwl' := rfl) hexplCur hback
      exact ih hbound hfront' hproc hback' hprevNeg_lt hfinalPrev hlt)
    (by
      intro worklist reach expl hneEmpty cur wl' idx hexplCur hidx expl' occs wl2 rch2
        hfold ih hbound hfront hproc hback hprevNeg_lt hfinalPrev hlt
      rw [getReachable.go.eq_1] at hfinalPrev ⊢
      rw [if_neg hneEmpty] at hfinalPrev ⊢
      rw [if_neg hexplCur] at hfinalPrev ⊢
      rw [dif_pos hidx] at hfinalPrev ⊢
      have hcur_mem : cur ∈ worklist.toList := by
        have hlist_ne : worklist.toList ≠ [] := by
          intro hnil
          have hempty : worklist.isEmpty = true := by
            have hsize : worklist.size = 0 := by
              simp [← Array.length_toList, hnil]
            simpa [Array.isEmpty_iff_size_eq_zero] using hsize
          exact hneEmpty hempty
        simpa [cur] using
          (array_getD_last_mem_toList (xs := worklist) ⟨0⟩ hlist_ne :
            worklist.getD (worklist.size - 1) ⟨0⟩ ∈ worklist.toList)
      have hfront_expl : ReachFrontierInvariant start wl' reach expl' := by
        rcases hfront with ⟨hwl, hexplInv⟩
        constructor
        · intro lit hlit hlit_ne_start
          have hlit_old : lit ∈ worklist.toList := by
            simp [wl'] at hlit
            exact List.dropLast_subset _ hlit
          exact hwl lit hlit_old hlit_ne_start
        · intro lit hexplLit hlit_ne_start
          by_cases hx : lit.x = cur.x
          · have hlit_cur : lit = cur := literal_eq_of_x_eq hx
            subst lit
            exact hwl cur hcur_mem hlit_ne_start
          · have hidx_ne : idx ≠ lit.x := by
              intro hidx_eq
              exact hx (by simpa [idx] using hidx_eq.symm)
            have hexplOld : expl.getD lit.x false = true := by
              rw [array_set_getD_ne expl idx lit.x true false hidx hidx_ne] at hexplLit
              simpa [expl'] using hexplLit
            exact hexplInv lit hexplOld hlit_ne_start
      have hback_expl : ReachBackpointerInvariant wl' reach expl' := by
        simpa [expl'] using
          (ReachBackpointerInvariant_pop_set_current
            (cur := cur) (idx := idx) (hcur := rfl) (hwl' := rfl)
            (hidx_eq := rfl) (hidx := hidx) hback)
      have hsize_fold₀ :
          (((st.clauses.getOcc cur).foldl
            (getReachableCRefStep st lvar negL expl' cur)
            (wl', reach)).2).size = reach.size :=
        getReachableCRefArrayFold_reach_size
          (st := st) (lvar := lvar) (negL := negL)
          (explored := expl') (cur := cur)
          (crefs := st.clauses.getOcc cur) (state := (wl', reach))
      have hfront_fold₀ :
          ReachFrontierInvariant start
            (((st.clauses.getOcc cur).foldl
              (getReachableCRefStep st lvar negL expl' cur)
              (wl', reach)).1)
            (((st.clauses.getOcc cur).foldl
              (getReachableCRefStep st lvar negL expl' cur)
              (wl', reach)).2)
            expl' := by
        exact getReachableCRefArrayFold_preserves_frontierInvariant
          (st := st) (lvar := lvar) (negL := negL)
          (explored := expl') (start := start) (cur := cur)
          (crefs := st.clauses.getOcc cur) (state := (wl', reach))
          hfront_expl
          (fun cref _hcref clause hraw hdel _hnoNeg lit hlit =>
            hbound cref clause lit hraw hdel hlit)
      have hback_fold₀ :
          ReachBackpointerInvariant
            (((st.clauses.getOcc cur).foldl
              (getReachableCRefStep st lvar negL expl' cur)
              (wl', reach)).1)
            (((st.clauses.getOcc cur).foldl
              (getReachableCRefStep st lvar negL expl' cur)
              (wl', reach)).2)
            expl' :=
        getReachableCRefArrayFold_preserves_backpointerInvariant
          (st := st) (lvar := lvar) (negL := negL)
          (explored := expl') (cur := cur)
          (crefs := st.clauses.getOcc cur) (state := (wl', reach))
          hback_expl
      have hproc_fold₀ :
          ReachProcessedInvariant st lvar negL
            (((st.clauses.getOcc cur).foldl
              (getReachableCRefStep st lvar negL expl' cur)
              (wl', reach)).2)
            expl' := by
        simpa [expl'] using
          (getReachableCRefArrayFold_processedInvariant_after_current
            (st := st) (lvar := lvar) (negL := negL) (start := start)
            (cur := cur) (worklist := worklist) (wl' := wl')
            (reach := reach) (expl := expl)
            hnegL (by simpa [idx] using hidx) hfront hproc hcur_mem)
      have hfront_fold : ReachFrontierInvariant start wl2 rch2 expl' := by
        rw [hfold] at hfront_fold₀
        exact hfront_fold₀
      have hback_fold : ReachBackpointerInvariant wl2 rch2 expl' := by
        rw [hfold] at hback_fold₀
        exact hback_fold₀
      have hproc_fold : ReachProcessedInvariant st lvar negL rch2 expl' := by
        rw [hfold] at hproc_fold₀
        exact hproc_fold₀
      have hsize_fold : rch2.size = reach.size := by
        rw [hfold] at hsize_fold₀
        exact hsize_fold₀
      have hbound' :
          ∀ cref clause lit,
            st.clauses.getClauseRaw cref = some clause →
            clause.deleted = false →
            lit ∈ clause.lits.toList →
            lit.x < rch2.size := by
        intro cref clause lit hraw hdel hlit
        simpa [hsize_fold] using hbound cref clause lit hraw hdel hlit
      change
        (getReachable.go st lvar negL
          (((st.clauses.getOcc cur).foldl
            (getReachableCRefStep st lvar negL expl' cur)
            (wl', reach)).1)
          (((st.clauses.getOcc cur).foldl
            (getReachableCRefStep st lvar negL expl' cur)
            (wl', reach)).2)
          expl').getD prev.x false = true
        at hfinalPrev
      change
        (getReachable.go st lvar negL
          (((st.clauses.getOcc cur).foldl
            (getReachableCRefStep st lvar negL expl' cur)
            (wl', reach)).1)
          (((st.clauses.getOcc cur).foldl
            (getReachableCRefStep st lvar negL expl' cur)
            (wl', reach)).2)
          expl').getD target.x false = true
      rw [hfold] at hfinalPrev ⊢
      have hfinalPrev' :
          (getReachable.go st lvar negL wl2 rch2 expl').getD prev.x false = true := by
        simpa using hfinalPrev
      simpa using
        ih hbound' hfront_fold hproc_fold hback_fold
          (by simpa [expl'] using hprevNeg_lt)
          hfinalPrev'
          (by simpa [hsize_fold] using hlt))
    (by
      intro worklist reach expl hneEmpty cur wl' idx hexplCur hidx ih
        hbound hfront hproc hback hprevNeg_lt hfinalPrev hlt
      rw [getReachable.go.eq_1] at hfinalPrev ⊢
      rw [if_neg hneEmpty] at hfinalPrev ⊢
      rw [if_neg hexplCur] at hfinalPrev ⊢
      rw [dif_neg hidx] at hfinalPrev ⊢
      have hfront' : ReachFrontierInvariant start wl' reach expl := by
        rcases hfront with ⟨hwl, hexplInv⟩
        constructor
        · intro lit hlit hlit_ne_start
          have hlit_old : lit ∈ worklist.toList := by
            simp [wl'] at hlit
            exact List.dropLast_subset _ hlit
          exact hwl lit hlit_old hlit_ne_start
        · exact hexplInv
      have hback' : ReachBackpointerInvariant wl' reach expl :=
        ReachBackpointerInvariant_pop_of_outOfBounds
          (cur := cur) (hcur := rfl) (hwl' := rfl)
          (hcur_oob := by simpa [idx] using hidx) hback
      exact ih hbound hfront' hproc hback' hprevNeg_lt hfinalPrev hlt)
    worklist reach expl hbound hfront hproc hback hprevNeg_lt hfinalPrev hlt

theorem getReachable_first_marks_reach_true
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hfull : CheckState.FullCorrect dqbf cs st)
    {start target : Literal} {cref : CRef} {clause : Clause}
    (hon_univ : st.formula.isVarExistential start.var = false)
    (hstart_lt : start.x < st.formula.maxVar * 2 + 2)
    (hget : st.clauses.getClause cref = some clause)
    (hstart : start ∈ clause.lits.toList)
    (hnoStartNeg : start.negate ∉ clause.lits.toList)
    (hmem : target ∈ clause.lits.toList)
    (hne : target ≠ start)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains start.var = true)
    (htarget_lt : target.x < st.formula.maxVar * 2 + 2) :
    (getReachable st start).getD target.x false = true := by
  let numLits := st.formula.maxVar * 2 + 2
  let reach0 : Array Bool := (List.replicate numLits false).toArray
  let expl0 : Array Bool := (List.replicate numLits false).toArray
  have hstart_lt_expl0 : start.x < expl0.size := by
    simpa [expl0, numLits] using hstart_lt
  have hnot_univ : ¬ st.formula.isVarExistential start.var = true := by
    simp [hon_univ]
  rcases getClauseRaw_deleted_of_getClause hget with ⟨hraw, hdel⟩
  have hoccArr : cref ∈ st.clauses.getOcc start :=
    ClauseStore.mem_getOcc_of_liveOccurrencesComplete
      hfull.liveOccurrencesComplete hget hstart
  have hocc : cref ∈ (st.clauses.getOcc start).toList :=
    Array.mem_toList_iff.mpr hoccArr
  have hnoNegArr : start.negate ∉ clause.lits := by
    intro hneg
    exact hnoStartNeg (Array.mem_toList_iff.mpr hneg)
  have htarget_ne_startNeg : target ≠ start.negate := by
    intro htarget
    exact hnoStartNeg (by simpa [htarget] using hmem)
  have hstart_x_ne_targetNeg : start.x ≠ target.negate.x := by
    intro hx
    have htarget_eq : target = start.negate :=
      literal_eq_negate_of_negate_x_eq (a := target) (b := start) hx.symm
    exact htarget_ne_startNeg htarget_eq
  have hexplTarget :
      (expl0.set start.x true hstart_lt_expl0).getD target.negate.x false = false := by
    simpa [expl0, numLits] using
      false_replicate_array_set_getD_of_ne numLits start.x target.negate.x
        (by simpa [expl0] using hstart_lt_expl0)
        hstart_x_ne_targetNeg
  have hmark :
      (((st.clauses.getOcc start).foldl
        (getReachableCRefStep st start.var start.negate
          (expl0.set start.x true hstart_lt_expl0) start)
        (#[], reach0)).2).getD target.x false = true := by
    exact getReachableCRefArrayFold_marks_reach_true
      (st := st) (lvar := start.var) (negL := start.negate)
      (explored := expl0.set start.x true hstart_lt_expl0)
      (cur := start) (target := target)
      (crefs := st.clauses.getOcc start) (state := (#[], reach0))
      (hit := cref) (clause := clause)
      hocc hraw hdel hnoNegArr hmem hne hexplTarget hexi hdep
      (by simpa [reach0, numLits] using htarget_lt)
  unfold getReachable
  rw [if_neg hnot_univ]
  change
    (getReachable.go st start.var start.negate #[start] reach0 expl0).getD target.x false = true
  rw [getReachable.go.eq_1]
  have hnonempty : ¬ (#[start] : Array Literal).isEmpty = true := by
    simp
  rw [if_neg hnonempty]
  have hexplStart : expl0.getD start.x false = false :=
    false_replicate_array_getD numLits start.x
  simp [hexplStart, hstart_lt_expl0]
  generalize hfold :
      (st.clauses.getOcc start).foldl
        (getReachableCRefStep st start.var start.negate
          (expl0.set start.x true hstart_lt_expl0) start)
        (#[], reach0) = folded
  rcases folded with ⟨wl2, rch2⟩
  have hmark' : rch2.getD target.x false = true := by
    simpa [hfold] using hmark
  rw [array_getElem?_getD_eq_getD]
  exact getReachable_go_preserves_reach_true st start.var start.negate wl2 rch2
    (expl0.set start.x true hstart_lt_expl0) hmark'

theorem getReachable_complete_first_mkLit
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hfull : CheckState.FullCorrect dqbf cs st)
    {on_ : Var} {pos : Bool} {target : Literal} {cref : CRef} {clause : Clause}
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hget : st.clauses.getClause cref = some clause)
    (hstart : mkLit on_ pos ∈ clause.lits.toList)
    (hnoStartNeg : (mkLit on_ pos).negate ∉ clause.lits.toList)
    (hmem : target ∈ clause.lits.toList)
    (hne : target ≠ mkLit on_ pos)
    (hexi : st.formula.isVarExistential target.var = true)
    (hdep : (st.formula.depset.getD target.var #[]).contains on_ = true) :
    (getReachable st (mkLit on_ pos)).getD target.x false = true := by
  have htarget_lt_isExi : target.var < st.formula.isExistential.size :=
    arrayGetD_true_imp_lt (a := st.formula.isExistential) (by
      simpa [DQBF.isVarExistential] using hexi)
  have htarget_le : target.var ≤ st.formula.maxVar := by
    rw [hfull.toCorrect.toSound.isExistential_size] at htarget_lt_isExi
    exact Nat.lt_succ_iff.mp htarget_lt_isExi
  exact getReachable_first_marks_reach_true
    (hfull := hfull)
    (start := mkLit on_ pos) (target := target) (cref := cref) (clause := clause)
    (by simpa [mkLit_var_early] using hon_univ)
    (mkLit_x_lt_numLits_of_var_le_maxVar hon_le)
    hget hstart hnoStartNeg hmem hne hexi
    (by simpa [mkLit_var_early] using hdep)
    (literal_x_lt_numLits_of_var_le_maxVar target htarget_le)

theorem getReachable_complete_mkLit
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hfull : CheckState.FullCorrect dqbf cs st)
    {on_ : Var} {pos : Bool} {target : Literal}
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hpath : DeletePurePath st on_ (mkLit on_ pos) target) :
    (getReachable st (mkLit on_ pos)).getD target.x false = true := by
  let numLits := st.formula.maxVar * 2 + 2
  let reach0 : Array Bool := (List.replicate numLits false).toArray
  let expl0 : Array Bool := (List.replicate numLits false).toArray
  induction hpath with
  | first hget hstart hnoStartNeg hlit hne hexi hdep =>
      exact getReachable_complete_first_mkLit
        (hfull := hfull) (on_ := on_) (pos := pos)
        (hon_le := hon_le) (hon_univ := hon_univ)
        hget hstart hnoStartNeg hlit hne hexi hdep
  | step hprev hget hcur hnoStartNeg hlit hne hexi hdep ih =>
      have hbound :
          ∀ cref clause lit,
            st.clauses.getClauseRaw cref = some clause →
            clause.deleted = false →
            lit ∈ clause.lits.toList →
            lit.x < reach0.size := by
        intro cref clause lit hraw hdel hlit'
        simpa [reach0, numLits] using
          clauseLit_x_lt_numLits_of_fullCorrect_raw_not_deleted
            hfull hraw hdel hlit'
      have hprev_exi :=
        deletePurePath_target_isVarExistential hprev
      have hprevNeg_lt_num :=
        isVarExistential_literal_negate_x_lt_numLits_of_fullCorrect hfull hprev_exi
      have htarget_lt_num :=
        isVarExistential_literal_x_lt_numLits_of_fullCorrect hfull hexi
      have hmark :=
        getReachable_go_final_reachable_clause_marks_reach_true_of_invariants
          (hfull := hfull)
          (lvar := on_) (negL := (mkLit on_ pos).negate)
          (start := mkLit on_ pos)
          (worklist := #[mkLit on_ pos]) (reach := reach0) (expl := expl0)
          (hnegL := rfl)
          (hbound := hbound)
          (hfront := ReachFrontierInvariant_initial (mkLit on_ pos) numLits)
          (hproc := ReachProcessedInvariant_initial st on_ (mkLit on_ pos).negate numLits)
          (hback := ReachBackpointerInvariant_initial (mkLit on_ pos) numLits)
          (hprevNeg_lt := by
            simpa [expl0, numLits] using hprevNeg_lt_num)
          (hfinalPrev := by
            simpa [getReachable, mkLit_var_early, hon_univ, reach0, expl0, numLits] using ih)
          (hget := hget)
          (hprev := hcur)
          (hnoNeg := hnoStartNeg)
          (hmem := hlit)
          (hne := hne)
          (hexi := hexi)
          (hdep := hdep)
          (hlt := by
            simpa [reach0, numLits] using htarget_lt_num)
      simpa [getReachable, mkLit_var_early, hon_univ, reach0, expl0, numLits] using hmark

def DeletePurePathComplete
    (st : CheckState) (on_ : Var) (start : Literal) : Prop :=
  ∀ target, DeletePurePath st on_ start target →
    (getReachable st start).getD target.x false = true

theorem deletePurePathComplete_mkLit
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hfull : CheckState.FullCorrect dqbf cs st)
    {on_ : Var} {pos : Bool}
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false) :
    DeletePurePathComplete st on_ (mkLit on_ pos) := by
  intro target hpath
  exact getReachable_complete_mkLit
    (hfull := hfull) (hon_le := hon_le) (hon_univ := hon_univ) hpath

theorem noDeleteCrossPaths_not_deletePurePath_pair
    {st : CheckState} {on_ of_ : Var} {pos : Bool}
    (hpaths : NoDeleteCrossPaths st on_ of_)
    (hcompletePos : DeletePurePathComplete st on_ (mkLit on_ true))
    (hcompleteNeg : DeletePurePathComplete st on_ (mkLit on_ false))
    (hposPath : DeletePurePath st on_ (mkLit on_ true) (mkLit of_ pos))
    (hnegPath : DeletePurePath st on_ (mkLit on_ false) (mkLit of_ (!pos))) :
    False := by
  exact noDeleteCrossPaths_not_reachPos_lit_reachNeg_negate hpaths
    ⟨hcompletePos (mkLit of_ pos) hposPath,
      hcompleteNeg (mkLit of_ (!pos)) hnegPath⟩

theorem noDeleteCrossPaths_not_deletePurePath_pair_of_fullCorrect
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {on_ of_ : Var} {pos : Bool}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hpaths : NoDeleteCrossPaths st on_ of_)
    (hposPath : DeletePurePath st on_ (mkLit on_ true) (mkLit of_ pos))
    (hnegPath : DeletePurePath st on_ (mkLit on_ false) (mkLit of_ (!pos))) :
    False :=
  noDeleteCrossPaths_not_deletePurePath_pair hpaths
    (deletePurePathComplete_mkLit
      (hfull := hfull) (pos := true) hon_le hon_univ)
    (deletePurePathComplete_mkLit
      (hfull := hfull) (pos := false) hon_le hon_univ)
    hposPath hnegPath

theorem noDeleteCrossPathsSet_not_deletePurePath_pair
    {st : CheckState} {vars : Array Var} {on_ of_ : Var} {pos : Bool}
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    (hof : of_ ∈ vars.toList)
    (hcompletePos : DeletePurePathComplete st on_ (mkLit on_ true))
    (hcompleteNeg : DeletePurePathComplete st on_ (mkLit on_ false))
    (hposPath : DeletePurePath st on_ (mkLit on_ true) (mkLit of_ pos))
    (hnegPath : DeletePurePath st on_ (mkLit on_ false) (mkLit of_ (!pos))) :
    False :=
  noDeleteCrossPaths_not_deletePurePath_pair (hpaths of_ hof)
    hcompletePos hcompleteNeg hposPath hnegPath

theorem noDeleteCrossPathsSet_not_deletePurePath_pair_of_fullCorrect
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {vars : Array Var} {on_ of_ : Var} {pos : Bool}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    (hof : of_ ∈ vars.toList)
    (hposPath : DeletePurePath st on_ (mkLit on_ true) (mkLit of_ pos))
    (hnegPath : DeletePurePath st on_ (mkLit on_ false) (mkLit of_ (!pos))) :
    False :=
  noDeleteCrossPaths_not_deletePurePath_pair_of_fullCorrect
    hfull hon_le hon_univ (hpaths of_ hof) hposPath hnegPath

theorem complementary_start_paths_to_forbidden_pair
    {st : CheckState} {on_ badOf : Var} {startPos badPos : Bool}
    (hpath : DeletePurePath st on_ (mkLit on_ startPos) (mkLit badOf badPos))
    (hpathCompl :
      DeletePurePath st on_ (mkLit on_ (!startPos)) (mkLit badOf (!badPos))) :
    ∃ pos : Bool,
      DeletePurePath st on_ (mkLit on_ true) (mkLit badOf pos) ∧
      DeletePurePath st on_ (mkLit on_ false) (mkLit badOf (!pos)) := by
  cases startPos
  · refine ⟨!badPos, ?_, ?_⟩
    · simpa using hpathCompl
    · simpa using hpath
  · refine ⟨badPos, ?_, ?_⟩
    · simpa using hpath
    · simpa using hpathCompl

theorem noDeleteCrossPathsSet_complement_start_path_forces_start_nonpath
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {vars : Array Var} {on_ of_ : Var} {startPos pos : Bool}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    (hof : of_ ∈ vars.toList)
    (hpathCompl :
      DeletePurePath st on_ (mkLit on_ (!startPos)) (mkLit of_ (!pos))) :
    ¬ DeletePurePath st on_ (mkLit on_ startPos) (mkLit of_ pos) := by
  intro hpath
  rcases complementary_start_paths_to_forbidden_pair
      (st := st) (on_ := on_) (badOf := of_)
      (startPos := startPos) (badPos := pos) hpath hpathCompl with
    ⟨badPos, hposPath, hnegPath⟩
  exact noDeleteCrossPathsSet_not_deletePurePath_pair_of_fullCorrect
    (dqbf := dqbf) (cs := cs) (st := st) (vars := vars)
    (on_ := on_) (of_ := of_) (pos := badPos)
    hfull hon_le hon_univ hpaths hof hposPath hnegPath

theorem noDeleteCrossPathsSet_orients_seed
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {vars : Array Var} {on_ of_ : Var} {σ : UnivAssignment} {pos : Bool}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    (hof : of_ ∈ vars.toList) :
    (¬ DeletePurePath st on_ (mkLit on_ (!(σ on_))) (mkLit of_ pos)) ∨
      (¬ DeletePurePath st on_ (mkLit on_ (σ on_)) (mkLit of_ (!pos))) := by
  classical
  by_cases hleft :
      DeletePurePath st on_ (mkLit on_ (!(σ on_))) (mkLit of_ pos)
  · right
    intro hright
    have hpathCompl :
        DeletePurePath st on_ (mkLit on_ (!(!(σ on_)))) (mkLit of_ (!pos)) := by
      simpa using hright
    rcases complementary_start_paths_to_forbidden_pair
        (st := st) (on_ := on_) (badOf := of_)
        (startPos := !(σ on_)) (badPos := pos) hleft hpathCompl with
      ⟨badPos, hposPath, hnegPath⟩
    exact noDeleteCrossPathsSet_not_deletePurePath_pair_of_fullCorrect
      (dqbf := dqbf) (cs := cs) (st := st) (vars := vars)
      (on_ := on_) (of_ := of_) (pos := badPos)
      hfull hon_le hon_univ hpaths hof hposPath hnegPath
  · exact Or.inl hleft

theorem noDeleteCrossPathsSet_path_forces_complement_nonpath
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {vars : Array Var} {on_ of_ : Var} {σ : UnivAssignment} {pos : Bool}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    (hof : of_ ∈ vars.toList)
    (hpath :
      ∃ startPos,
        startPos = !(σ on_) ∧
        DeletePurePath st on_ (mkLit on_ startPos) (mkLit of_ pos)) :
    ¬ DeletePurePath st on_ (mkLit on_ (σ on_)) (mkLit of_ (!pos)) := by
  rcases hpath with ⟨startPos, hstart, hpath⟩
  have hpath' :
      DeletePurePath st on_ (mkLit on_ (!(σ on_))) (mkLit of_ pos) := by
    subst startPos
    exact hpath
  rcases noDeleteCrossPathsSet_orients_seed
      (dqbf := dqbf) (cs := cs) (st := st) (vars := vars)
      (on_ := on_) (of_ := of_) (σ := σ) (pos := pos)
      hfull hon_le hon_univ hpaths hof with
    hleft | hright
  · exact False.elim (hleft hpath')
  · exact hright

theorem noDeleteCrossPathsSet_complement_path_forces_seed_nonpath
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {vars : Array Var} {on_ of_ : Var} {σ : UnivAssignment} {pos : Bool}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    (hof : of_ ∈ vars.toList)
    (hpath :
      DeletePurePath st on_ (mkLit on_ (σ on_)) (mkLit of_ (!pos))) :
    ¬ DeletePurePath st on_ (mkLit on_ (!(σ on_))) (mkLit of_ pos) := by
  rcases noDeleteCrossPathsSet_orients_seed
      (dqbf := dqbf) (cs := cs) (st := st) (vars := vars)
      (on_ := on_) (of_ := of_) (σ := σ) (pos := pos)
      hfull hon_le hon_univ hpaths hof with
    hleft | hright
  · exact hleft
  · exact False.elim (hright hpath)

theorem deletePurePath_step_from_opposite_target_tail
    {st : CheckState} {on_ of_ nextOf : Var}
    {startPos pos nextPos : Bool}
    {cref : CRef} {clause : Clause}
    (hprev :
      DeletePurePath st on_ (mkLit on_ startPos) (mkLit of_ (!pos)))
    (hget : st.clauses.getClause cref = some clause)
    (htarget : mkLit of_ pos ∈ clause.lits.toList)
    (hnoStartNeg : (mkLit on_ startPos).negate ∉ clause.lits.toList)
    (hnext : mkLit nextOf nextPos ∈ clause.lits.toList)
    (hnext_ne : nextOf ≠ of_)
    (hexi : st.formula.isVarExistential nextOf = true)
    (hdep : (st.formula.depset.getD nextOf #[]).contains on_ = true) :
    DeletePurePath st on_ (mkLit on_ startPos) (mkLit nextOf nextPos) := by
  have hcur : (mkLit of_ (!pos)).negate ∈ clause.lits.toList := by
    simpa [mkLit_negate] using htarget
  exact deletePurePath_step_mkLit_of_var_ne
    hprev hget hcur hnoStartNeg hnext hnext_ne hexi hdep

theorem noStartNeg_of_false_other_literals
    {s : CheckState} {on_ of_ : Var}
    {startPos pos : Bool} {c : Clause}
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hof_ne : of_ ≠ on_)
    (hstartNeg_true :
      s.formula.litValue σ sk (mkLit on_ startPos).negate = true)
    (hothers :
      ∀ l ∈ c.lits.toList, l ≠ mkLit of_ pos →
        s.formula.litValue σ sk l = false) :
    (mkLit on_ startPos).negate ∉ c.lits.toList := by
  intro hmem
  have hne : (mkLit on_ startPos).negate ≠ mkLit of_ pos := by
    intro hEq
    have hvar := congrArg Literal.var hEq
    rw [literal_negate_var, mkLit_var_early, mkLit_var_early] at hvar
    exact hof_ne hvar.symm
  have hfalse := hothers (mkLit on_ startPos).negate hmem hne
  rw [hstartNeg_true] at hfalse
  cases hfalse

theorem litValue_start_neg_true_of_start_eq_not_sigma
    {s : CheckState} {on_ : Var} {startPos : Bool}
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hstart : startPos = !(σ on_)) :
    s.formula.litValue σ sk (mkLit on_ startPos).negate = true := by
  subst startPos
  cases hσ : σ on_ <;>
    simp [mkLit_negate, litValue_mkLit_true, litValue_mkLit_false,
      DQBF.varValue, hon_univ, hσ]

theorem oriented_dependent_tail_forces_next_old_lit_nonpath
    {s : CheckState} {vars : Array Var} {on_ of_ nextOf : Var}
    {sk : SkolemAssignment} {σ : UnivAssignment}
    {cref : CRef} {c : Clause} {pos nextPos : Bool}
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hof : of_ ∈ vars.toList)
    (hget : s.clauses.getClause cref = some c)
    (hmem : mkLit of_ pos ∈ c.lits.toList)
    (hno_oriented :
      ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_))) (mkLit of_ pos))
    (hnext_ne : nextOf ≠ of_)
    (hnext_mem : mkLit nextOf nextPos ∈ c.lits.toList)
    (hothers :
      ∀ l ∈ c.lits.toList, l ≠ mkLit of_ pos →
        s.formula.litValue σ sk l = false) :
    ¬ DeletePurePath s on_
      (mkLit on_ (!(σ on_))) (mkLit nextOf (!nextPos)) := by
  intro hpath_next_old
  have hof_ne_on : of_ ≠ on_ := by
    intro hEq
    have hcontra : s.formula.isVarExistential of_ = false := by
      simpa [hEq] using hon_univ
    have hof_exi : s.formula.isVarExistential of_ = true := hexi of_ hof
    rw [hcontra] at hof_exi
    cases hof_exi
  have hstartNeg_true :
      s.formula.litValue σ sk (mkLit on_ (!(σ on_))).negate = true :=
    litValue_start_neg_true_of_start_eq_not_sigma
      (s := s) (on_ := on_) (startPos := !(σ on_))
      σ sk hon_univ rfl
  have hnoStartNeg :
      (mkLit on_ (!(σ on_))).negate ∉ c.lits.toList :=
    noStartNeg_of_false_other_literals
      (s := s) (on_ := on_) (of_ := of_) (startPos := !(σ on_))
      (pos := pos) (c := c) σ sk hof_ne_on hstartNeg_true hothers
  have hpath_to_original :
      DeletePurePath s on_ (mkLit on_ (!(σ on_))) (mkLit of_ pos) := by
    exact deletePurePath_step_from_opposite_target_tail
      (st := s) (on_ := on_) (of_ := nextOf) (nextOf := of_)
      (startPos := !(σ on_)) (pos := nextPos) (nextPos := pos)
      (cref := cref) (clause := c)
      hpath_next_old hget hnext_mem hnoStartNeg hmem
      (Ne.symm hnext_ne) (hexi of_ hof) (hcontains of_ hof)
  exact hno_oriented hpath_to_original
