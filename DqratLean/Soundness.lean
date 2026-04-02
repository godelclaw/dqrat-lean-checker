import DqratLean.Semantics
import DqratLean.Parser
open Std.Do

/-!
# Soundness of DQRAT Checker Rules

This file proves that each step in a DQRAT proof preserves truth (soundness).

A DQRAT refutation demonstrates that a formula Ψ is false by:
1. Starting from Ψ₁ = Ψ
2. Applying rules (DEL, UR, DQRATE, DQRATU) that preserve truth:
   if Ψᵢ is true then Ψᵢ₊₁ is true
3. Reaching Ψₖ which contains an empty clause (always false)
4. Concluding by contradiction: Ψ must be false.

## Sections
- Section 2: DEL rule soundness (fully proved)
- Section 3: addClause monotonicity (fully proved)
- Section 4: UR independence lemma (proved up to one array membership helper)
- Section 5: UR soundness (key step sorry'd)
- Section 6: DQRATE / DQRATU stubs (sorry'd)
- Section 7: Overall checker soundness stub (sorry'd)
-/

-- ─── Section 2: DEL Rule Soundness ──────────────────────────────────────────

/-- Deleting a clause can only make the matrix *easier* to satisfy:
    for any universal assignment satisfying the original matrix, the matrix
    with one clause removed is also satisfied. -/
theorem matrixValue_deleteClause_mono
    (f : DQBF) (cs : ClauseStore) (cref : CRef)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (h : cs.matrixValue f σ sk = true) :
    (cs.deleteClause cref).matrixValue f σ sk = true := by
  simp only [ClauseStore.matrixValue] at *
  -- Both sides range over the same index set (deleteClause preserves size)
  rw [ClauseStore.deleteClause_clauses_size]
  simp only [List.all_eq_true, List.mem_range] at *
  intro i hi
  -- i+1 is in the valid cref range
  have hlt : i + 1 < cs.clauses.size := by omega
  by_cases heq : i + 1 = cref
  · -- The deleted clause becomes `none` → vacuously true (match none = true by rfl)
    subst heq
    rw [ClauseStore.getClause_deleteClause_eq _ _ hlt]
  · -- Every other clause is unchanged
    rw [ClauseStore.getClause_deleteClause_ne _ _ _ heq]
    exact h i hi

/-- **DEL soundness**: deleting a clause from a true formula yields a true formula. -/
theorem DQBFTrue.delete_clause (f : DQBF) (cs : ClauseStore) (cref : CRef)
    (h : DQBFTrue f cs) : DQBFTrue f (cs.deleteClause cref) :=
  let ⟨sk, hsk⟩ := h
  ⟨sk, fun σ => matrixValue_deleteClause_mono f cs cref σ sk (hsk σ)⟩

-- ─── Section 3: addClause Monotonicity ──────────────────────────────────────

/-- Adding a clause to a formula adds a constraint: if the extended formula is
    satisfied, the original formula is also satisfied (contrapositive of the
    observation that adding a clause can only make a formula harder to satisfy). -/
theorem matrixValue_addClause_mono
    (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (h : (cs.addClause lits).1.matrixValue f σ sk = true) :
    cs.matrixValue f σ sk = true := by
  simp only [ClauseStore.matrixValue] at *
  simp only [ClauseStore.addClause, Array.size_push] at h
  simp only [List.all_eq_true, List.mem_range] at *
  intro i hi
  have hlt : i + 1 < cs.clauses.size := by omega
  -- The new clause is at index cs.clauses.size, which is beyond i+1
  -- so getClause (i+1) is unchanged
  rw [← ClauseStore.getClause_addClause_lt cs lits (i + 1) hlt]
  exact h i (by omega)

/-- **Corollary**: if the formula with an added clause is true, the original is true. -/
theorem DQBFTrue.of_addClause (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (h : DQBFTrue f (cs.addClause lits).1) : DQBFTrue f cs :=
  let ⟨sk, hsk⟩ := h
  ⟨sk, fun σ => matrixValue_addClause_mono f cs lits σ sk (hsk σ)⟩

-- ─── Section 4: UR Key Independence Lemma ───────────────────────────────────

/-- Helper: if `u` is not in `arr.toList`, then `arr[i] ≠ u` for any valid index `i`.
    This connects list non-membership to element-level inequality. -/
theorem not_mem_toList_getElem {arr : Array Var} {u : Var}
    (hdep : u ∉ arr.toList) (i : Nat) (hi : i < arr.size) : arr[i] ≠ u := by
  intro heq
  apply hdep
  exact heq ▸ Array.mem_toList_iff.mpr (Array.getElem_mem hi)

/-- If universal variable `u` is not in the dependency set of existential `v`,
    flipping `σ(u)` leaves the Skolem value of `v` unchanged.

    This is the key semantic fact behind Universal Reduction (UR): when the
    pivot universal `u` is not in D(x) for any existential x in the clause,
    the existential values are independent of `u`'s assignment, so we can
    safely remove `u` from the clause. -/
theorem exiValue_indep_of_non_dep
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (v : Var) (u : Var)
    (hdep : u ∉ (f.depset.getD v #[]).toList) :
    f.exiValue σ sk v =
    f.exiValue (fun w => if w == u then !σ w else σ w) sk v := by
  simp only [DQBF.exiValue]
  congr 1
  apply Array.ext (by simp [Array.size_map])
  intro i hi₁ _
  simp only [Array.getElem_map]
  have hi : i < (f.depset.getD v #[]).size := by simpa [Array.size_map] using hi₁
  have hne : (f.depset.getD v #[])[i]'hi ≠ u :=
    not_mem_toList_getElem hdep i hi
  -- Since d[i] ≠ u, the beq condition is false, so the if reduces to σ d[i]
  simp only [beq_iff_eq]; rw [if_neg hne]

-- ─── Section 5: UR Soundness ─────────────────────────────────────────────────

-- Helper: extract clauseValue from matrixValue
theorem clauseValue_of_matrixValue
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment) (sk : SkolemAssignment)
    (cref : CRef) (c : Clause)
    (hmat : cs.matrixValue f σ sk = true)
    (hget : cs.getClause cref = some c) :
    f.clauseValue σ sk c.lits = true := by
  have hlt : cref < cs.clauses.size := ClauseStore.getClause_some_imp_lt cs cref c hget
  have hne : cref ≠ CRef_Undef := ClauseStore.getClause_some_imp_ne_undef cs cref c hget
  have hge : 1 ≤ cref := by
    rcases Nat.eq_zero_or_pos cref with h | h
    · simp [h, CRef_Undef] at hne
    · exact h
  simp only [ClauseStore.matrixValue, List.all_eq_true, List.mem_range] at hmat
  have key := hmat (cref - 1) (Nat.sub_lt_sub_right hge hlt)
  have heq : cref - 1 + 1 = cref := Nat.succ_pred_eq_of_pos hge
  rw [heq, hget] at key
  exact key

theorem clauseValue_perm
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    {lits₁ lits₂ : Array Literal}
    (hperm : Array.Perm lits₁ lits₂) :
    f.clauseValue σ sk lits₁ = f.clauseValue σ sk lits₂ := by
  have hiff :
      f.clauseValue σ sk lits₁ = true ↔ f.clauseValue σ sk lits₂ = true := by
    constructor
    · intro htrue
      simp only [DQBF.clauseValue, Array.any_eq_true] at htrue ⊢
      rcases htrue with ⟨i, hi, hval⟩
      have hmem₁ : lits₁[i] ∈ lits₁ := Array.getElem_mem hi
      have hmem₂ : lits₁[i] ∈ lits₂ := (Array.Perm.mem_iff hperm).mp hmem₁
      rcases Array.mem_iff_getElem.mp hmem₂ with ⟨j, hj, heq⟩
      exact ⟨j, hj, heq ▸ hval⟩
    · intro htrue
      have hsymm : Array.Perm lits₂ lits₁ := Array.Perm.symm hperm
      simp only [DQBF.clauseValue, Array.any_eq_true] at htrue ⊢
      rcases htrue with ⟨i, hi, hval⟩
      have hmem₂ : lits₂[i] ∈ lits₂ := Array.getElem_mem hi
      have hmem₁ : lits₂[i] ∈ lits₁ := (Array.Perm.mem_iff hsymm).mp hmem₂
      rcases Array.mem_iff_getElem.mp hmem₁ with ⟨j, hj, heq⟩
      exact ⟨j, hj, heq ▸ hval⟩
  cases h₁ : f.clauseValue σ sk lits₁ <;> cases h₂ : f.clauseValue σ sk lits₂ <;>
    simp [h₁, h₂] at hiff ⊢

-- Helper: matrixValue after addClause when both old and new clauses are satisfied
theorem matrixValue_addClause_of_both
    (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hold : cs.matrixValue f σ sk = true)
    (hnew : f.clauseValue σ sk lits = true) :
    (cs.addClause lits).1.matrixValue f σ sk = true := by
  simp only [ClauseStore.matrixValue, List.all_eq_true, List.mem_range]
  intro i hi
  simp only [ClauseStore.addClause, Array.size_push] at hi
  by_cases hlt : i + 1 < cs.clauses.size
  · rw [ClauseStore.getClause_addClause_lt cs lits (i + 1) hlt]
    exact (List.all_eq_true.mp hold) i (List.mem_range.mpr (by omega))
  · have heq : i + 1 = cs.clauses.size := by omega
    have hpos : 0 < cs.clauses.size := by omega
    rw [show (cs.addClause lits).1.getClause (i + 1) =
        some { lits := lits, deleted := false } from by
      rw [heq]; exact ClauseStore.getClause_addClause_new cs lits hpos]
    simpa

theorem matrixValue_addClause_false_of_old_false
    (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hold : cs.matrixValue f σ sk = false) :
    (cs.addClause lits).1.matrixValue f σ sk = false := by
  cases h : (cs.addClause lits).1.matrixValue f σ sk <;> simp [h]
  have hmono := matrixValue_addClause_mono f cs lits σ sk h
  simp [hold] at hmono

theorem matrixValue_addClause_false_of_new_false
    (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hpos : 0 < cs.clauses.size)
    (hnew : f.clauseValue σ sk lits = false) :
    (cs.addClause lits).1.matrixValue f σ sk = false := by
  cases h : (cs.addClause lits).1.matrixValue f σ sk <;> simp [h]
  have hget :=
    ClauseStore.getClause_addClause_new cs lits hpos
  have hclause :=
    clauseValue_of_matrixValue f (cs.addClause lits).1 σ sk cs.clauses.size
      { lits := lits, deleted := false } h hget
  simp [hnew] at hclause

-- Literal arithmetic: if l.x / 2 = p.x / 2 and l.x ≠ p.x, then l.x = p.x ^^^ 1
theorem lit_raw (lx px : Nat)
    (hvar : lx / 2 = px / 2) (hne : lx ≠ px) : lx = px ^^^ 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    have hmod : lx % 2 ≠ px % 2 := by omega
    have hl := Nat.mod_two_eq_zero_or_one lx
    have hp := Nat.mod_two_eq_zero_or_one px
    rcases hl with h | h <;> rcases hp with h' | h' <;> simp_all
  | succ i =>
    simp only [Nat.testBit_succ]
    simp [hvar]

theorem lit_ne_pivot_of_same_var (l pivot : Literal)
    (hvar : l.var = pivot.var) (hne : l ≠ pivot) : l = pivot.negate := by
  cases l; cases pivot
  simp only [Literal.var, Literal.negate, ne_eq, Literal.mk.injEq] at *
  exact lit_raw _ _ hvar hne

theorem literal_eq_or_negate_of_same_var (l pivot : Literal)
    (h : l.var = pivot.var) : l = pivot ∨ l = pivot.negate := by
  by_cases heq : l.x = pivot.x
  · left; cases l; cases pivot; simp_all [Literal.var]
  · right; exact lit_ne_pivot_of_same_var l pivot h (by cases l; cases pivot; simp_all)

-- litValue is unchanged when flipping σ at u, provided l.var ≠ u
-- (for existentials, pivot.var must not be in the dep-set)
theorem litValue_flip_indep
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (l : Literal) (u : Var)
    (hvar_ne : l.var ≠ u)
    (hdep : f.isVarExistential l.var → u ∉ (f.depset.getD l.var #[]).toList) :
    f.litValue σ sk l =
    f.litValue (fun w => if w == u then !σ w else σ w) sk l := by
  simp only [DQBF.litValue, DQBF.varValue]
  by_cases hex : f.isVarExistential l.var
  · simp only [hex, ↓reduceIte]
    rw [exiValue_indep_of_non_dep f σ sk l.var u (hdep hex)]
  · simp only [hex, show (l.var == u) = false from by simp [hvar_ne]]; simp



/-- The UR condition: `pivot` is a universal literal, `lits` does not contain
    the complementary literal `pivot.negate` (no tautology w.r.t. u), and for
    every existential literal in `lits`, the pivot variable is not in its
    dependency set.

    The no-complementary-pair condition (`pivot.negate ∉ lits`) is required
    for soundness: if both `pivot` and `¬pivot` were in `lits`, the reduced
    clause `lits \ {pivot}` would contain `¬pivot`, which is false when pivot
    is true, making UR unsound. The checker enforces this (Parser.lean:287). -/
def URCondition (f : DQBF) (lits : Array Literal) (pivot : Literal) : Prop :=
  ¬f.isVarExistential pivot.var ∧
  pivot.negate ∉ lits.toList ∧
  ∀ l ∈ lits.toList, f.isVarExistential l.var →
    pivot.var ∉ (f.depset.getD l.var #[]).toList

theorem URCondition.perm
    {f : DQBF} {lits₁ lits₂ : Array Literal} {pivot : Literal}
    (hperm : Array.Perm lits₁ lits₂)
    (hcond : URCondition f lits₁ pivot) :
    URCondition f lits₂ pivot := by
  refine ⟨hcond.1, ?_, ?_⟩
  · intro hmem₂
    have hmem₁ : pivot.negate ∈ lits₁.toList := by
      apply Array.mem_toList_iff.mpr
      exact (Array.Perm.mem_iff hperm).mpr (Array.mem_toList_iff.mp hmem₂)
    exact hcond.2.1 hmem₁
  · intro l hl₂ hex
    have hl₁ : l ∈ lits₁.toList := by
      apply Array.mem_toList_iff.mpr
      exact (Array.Perm.mem_iff hperm).mpr (Array.mem_toList_iff.mp hl₂)
    exact hcond.2.2 l hl₁ hex

theorem urCondition_of_pivotReducible
    {f : DQBF} {lits : Array Literal} {pivot : Literal}
    (hpivot_univ : f.isVarExistential pivot.var = false)
    (hpivotReducible :
      (!lits.any (· = pivot.negate) &&
        lits.all (fun l =>
          !f.isVarExistential l.var || !f.isVarOuterOfExivar pivot.var l.var)) = true) :
    URCondition f lits pivot := by
  rw [Bool.and_eq_true] at hpivotReducible
  rcases hpivotReducible with ⟨hno_neg, hall⟩
  refine ⟨by simpa using hpivot_univ, ?_, ?_⟩
  · intro hmem
    have hmemA : pivot.negate ∈ lits := Array.mem_toList_iff.mp hmem
    rcases Array.mem_iff_getElem.mp hmemA with ⟨i, hi, heq⟩
    have hany : lits.any (· = pivot.negate) = true :=
      Array.any_eq_true.mpr ⟨i, hi, by simpa [heq]⟩
    have hfalse : lits.any (· = pivot.negate) = false := by
      simpa using hno_neg
    rw [hany] at hfalse
    cases hfalse
  · intro l hl hex
    have hlA : l ∈ lits := Array.mem_toList_iff.mp hl
    rcases Array.mem_iff_getElem.mp hlA with ⟨i, hi, heq⟩
    have hstep := (Array.all_eq_true.mp hall) i hi
    rw [heq] at hstep
    have hstep' : !f.isVarOuterOfExivar pivot.var l.var = true := by
      simpa [hex] using hstep
    have houter_false : (f.depset.getD l.var #[]).contains pivot.var = false := by
      simpa [DQBF.isVarOuterOfExivar, hpivot_univ] using hstep'
    intro hdep
    have hcontains : (f.depset.getD l.var #[]).contains pivot.var = true := by
      exact Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hdep)
    rw [hcontains] at houter_false
    cases houter_false

theorem urCondition_of_pivotReducible_prop
    {f : DQBF} {lits : Array Literal} {pivot : Literal}
    (hpivot_univ : f.isVarExistential pivot.var = false)
    (hpivotReducible :
      (∀ i (h : i < lits.size), ¬lits[i] = pivot.negate) ∧
      ∀ i (h : i < lits.size),
        f.isVarExistential lits[i].var = false ∨
          f.isVarOuterOfExivar pivot.var lits[i].var = false) :
    URCondition f lits pivot := by
  rcases hpivotReducible with ⟨hno_neg, houter⟩
  refine ⟨by simpa using hpivot_univ, ?_, ?_⟩
  · intro hmem
    rcases Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hmem) with ⟨i, hi, heq⟩
    exact hno_neg i hi (by simpa [heq])
  · intro l hl hex
    rcases Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hl) with ⟨i, hi, heq⟩
    have hstep := houter i hi
    rw [heq] at hstep
    cases hstep with
    | inl hex_false =>
        have hfalse : False := by
          simpa [hex] using hex_false
        exact False.elim hfalse
    | inr houter_false =>
        intro hdep
        have houter_false' : (f.depset.getD l.var #[]).contains pivot.var = false := by
          simpa [DQBF.isVarOuterOfExivar, hpivot_univ] using houter_false
        have hcontains : (f.depset.getD l.var #[]).contains pivot.var = true := by
          exact Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hdep)
        rw [hcontains] at houter_false'
        cases houter_false'

/-- **UR soundness** (sorry'd):
    If `cs` contains a clause with literals `lits` (including universal `pivot`),
    and the UR condition holds, then adding the reduced clause `lits \ {pivot}`
    preserves truth.

    This is Lemma (∀red soundness) from the IndExt paper (lines 647-658):
    "If Π φ ∧ L(u) is true and no existential x in L depends on u,
    then Π φ ∧ L(u) ∧ L(0) is also true — using the **same** Skolem functions."

    Proof sketch (same sk works):
    For any σ, we must show `f.clauseValue σ sk (lits.filter (≠pivot)) = true`.
    From `hmem` and `hsk σ`, clause `lits` is satisfied: some l ∈ lits has
    `f.litValue σ sk l = true`.
    - If l ≠ pivot: l is in the filtered clause, done.
    - If l = pivot (pivot is the only satisfying literal): let σ' flip σ at
      pivot.var. Under σ', pivot is false. By `hsk σ'`, lits is still satisfied
      by some l' ∈ lits. Since pivot.negate ∉ lits (no complementary pair) and
      l' ≠ pivot, we have l'.var ≠ pivot.var. So l' has the same value under σ
      as under σ': existential values are unchanged by `exiValue_indep_of_non_dep`
      (pivot ∉ D(l'.var) by hcond), universal values are unchanged since l'.var ≠
      pivot.var and σ' only differs from σ at pivot.var. Hence l' satisfies the
      filtered clause under σ. -/
theorem UR_soundness (f : DQBF) (cs : ClauseStore) (lits : Array Literal) (pivot : Literal)
    (hcond : URCondition f lits pivot)
    (hmem : ∃ cref, ∃ c, cs.getClause cref = some c ∧ c.lits = lits)
    (h : DQBFTrue f cs) :
    DQBFTrue f (cs.addClause (lits.filter (fun l => !(l == pivot)))).1 := by
  obtain ⟨sk, hsk⟩ := h
  refine ⟨sk, fun σ => ?_⟩
  apply matrixValue_addClause_of_both
  · exact hsk σ
  · obtain ⟨cref, c, hget, hlits⟩ := hmem
    have hclause : f.clauseValue σ sk lits = true :=
      hlits ▸ clauseValue_of_matrixValue f cs σ sk cref c (hsk σ) hget
    -- Extract satisfying element; Array.any_eq_true gives ∃ i x, p as[i] = true
    simp only [DQBF.clauseValue, Array.any_eq_true] at hclause
    obtain ⟨i, hi, hl_val⟩ := hclause
    -- Case split on whether lits[i] equals pivot
    cases hbeq : (lits[i]'hi == pivot)
    · -- hbeq : (lits[i] == pivot) = false → lits[i] ≠ pivot: passes the filter directly
      have hne : lits[i]'hi ≠ pivot := by
        intro heq; subst heq; simp at hbeq
      have hmem_filt : lits[i]'hi ∈ lits.filter (fun l => !(l == pivot)) :=
        Array.mem_filter.mpr ⟨Array.getElem_mem hi, by simp [hbeq]⟩
      obtain ⟨j, hj, hj_eq⟩ := Array.mem_iff_getElem.mp hmem_filt
      simp only [DQBF.clauseValue, Array.any_eq_true]
      exact ⟨j, hj, hj_eq ▸ hl_val⟩
    · -- hbeq : (lits[i] == pivot) = true → lits[i] = pivot
      have hl_eq : lits[i]'hi = pivot := beq_iff_eq.mp hbeq
      -- Lift hl_val to use pivot
      have hpivot_val : f.litValue σ sk pivot = true := hl_eq ▸ hl_val
      -- Define flipped assignment
      let σ' : UnivAssignment := fun w => if w == pivot.var then !σ w else σ w
      -- Under σ', original clause still satisfied
      have hclause' : f.clauseValue σ' sk lits = true :=
        hlits ▸ clauseValue_of_matrixValue f cs σ' sk cref c (hsk σ') hget
      simp only [DQBF.clauseValue, Array.any_eq_true] at hclause'
      obtain ⟨i', hi', hl'_val⟩ := hclause'
      -- pivot is false under σ' (we flipped it)
      have huni : f.isVarExistential pivot.var = false := by simpa using hcond.1
      have hpivot_false : f.litValue σ' sk pivot = false := by
        have hσ'_pivot : σ' pivot.var = !σ pivot.var := by
          show (fun w => if w == pivot.var then !σ w else σ w) pivot.var = !σ pivot.var
          simp
        simp only [DQBF.litValue, DQBF.varValue, huni]
        rw [hσ'_pivot]
        simp only [DQBF.litValue, DQBF.varValue, huni] at hpivot_val
        cases h : pivot.isPos <;> simp_all
      -- lits[i'] ≠ pivot
      have hl'_ne_pivot : lits[i']'hi' ≠ pivot := by
        intro heq
        rw [← heq] at hpivot_false
        exact absurd hl'_val (by simp [hpivot_false])
      -- lits[i'] ≠ pivot.negate (no complementary pair)
      have hl'_ne_neg : lits[i']'hi' ≠ pivot.negate := by
        intro heq
        have hmem : lits[i']'hi' ∈ lits.toList :=
          Array.mem_toList_iff.mpr (Array.getElem_mem hi')
        rw [heq] at hmem
        exact absurd hmem hcond.2.1
      -- lits[i'].var ≠ pivot.var
      have hl'_var_ne : (lits[i']'hi').var ≠ pivot.var := by
        intro hv
        rcases literal_eq_or_negate_of_same_var (lits[i']'hi') pivot hv with h | h
        · exact hl'_ne_pivot h
        · exact hl'_ne_neg h
      -- litValue same under σ and σ'
      have hsame : f.litValue σ sk (lits[i']'hi') = f.litValue σ' sk (lits[i']'hi') :=
        litValue_flip_indep f σ sk (lits[i']'hi') pivot.var hl'_var_ne
          (fun hex => hcond.2.2 (lits[i']'hi')
            (Array.mem_toList_iff.mpr (Array.getElem_mem hi')) hex)
      -- lits[i'] is in the filtered clause
      have hmem_filt : lits[i']'hi' ∈ lits.filter (fun l => !(l == pivot)) :=
        Array.mem_filter.mpr ⟨Array.getElem_mem hi',
          by simp [beq_eq_false_iff_ne.mpr hl'_ne_pivot]⟩
      obtain ⟨j, hj, hj_eq⟩ := Array.mem_iff_getElem.mp hmem_filt
      simp only [DQBF.clauseValue, Array.any_eq_true]
      exact ⟨j, hj, hj_eq ▸ (hsame ▸ hl'_val)⟩

theorem UR_soundness_perm (f : DQBF) (cs : ClauseStore) (lits : Array Literal) (pivot : Literal)
    (hcond : URCondition f lits pivot)
    (hmem : ∃ cref, ∃ c, cs.getClause cref = some c ∧ Array.Perm c.lits lits)
    (h : DQBFTrue f cs) :
    DQBFTrue f (cs.addClause (lits.filter (fun l => !(l == pivot)))).1 := by
  obtain ⟨sk, hsk⟩ := h
  refine ⟨sk, fun σ => ?_⟩
  apply matrixValue_addClause_of_both
  · exact hsk σ
  · obtain ⟨cref, c, hget, hperm⟩ := hmem
    have hclause_c : f.clauseValue σ sk c.lits = true :=
      clauseValue_of_matrixValue f cs σ sk cref c (hsk σ) hget
    have hclause : f.clauseValue σ sk lits = true := by
      simpa [clauseValue_perm f σ sk hperm] using hclause_c
    simp only [DQBF.clauseValue, Array.any_eq_true] at hclause
    obtain ⟨i, hi, hl_val⟩ := hclause
    cases hbeq : (lits[i]'hi == pivot)
    · have hne : lits[i]'hi ≠ pivot := by
        intro heq
        subst heq
        simp at hbeq
      have hmem_filt : lits[i]'hi ∈ lits.filter (fun l => !(l == pivot)) :=
        Array.mem_filter.mpr ⟨Array.getElem_mem hi, by simp [hbeq]⟩
      obtain ⟨j, hj, hj_eq⟩ := Array.mem_iff_getElem.mp hmem_filt
      simp only [DQBF.clauseValue, Array.any_eq_true]
      exact ⟨j, hj, hj_eq ▸ hl_val⟩
    · have hl_eq : lits[i]'hi = pivot := beq_iff_eq.mp hbeq
      have hpivot_val : f.litValue σ sk pivot = true := hl_eq ▸ hl_val
      let σ' : UnivAssignment := fun w => if w == pivot.var then !σ w else σ w
      have hclause_c' : f.clauseValue σ' sk c.lits = true :=
        clauseValue_of_matrixValue f cs σ' sk cref c (hsk σ') hget
      have hclause' : f.clauseValue σ' sk lits = true := by
        simpa [clauseValue_perm f σ' sk hperm] using hclause_c'
      simp only [DQBF.clauseValue, Array.any_eq_true] at hclause'
      obtain ⟨i', hi', hl'_val⟩ := hclause'
      have huni : f.isVarExistential pivot.var = false := by
        simpa using hcond.1
      have hpivot_false : f.litValue σ' sk pivot = false := by
        have hσ'_pivot : σ' pivot.var = !σ pivot.var := by
          show (fun w => if w == pivot.var then !σ w else σ w) pivot.var = !σ pivot.var
          simp
        simp only [DQBF.litValue, DQBF.varValue, huni]
        rw [hσ'_pivot]
        simp only [DQBF.litValue, DQBF.varValue, huni] at hpivot_val
        cases h : pivot.isPos <;> simp_all
      have hl'_ne_pivot : lits[i']'hi' ≠ pivot := by
        intro heq
        rw [← heq] at hpivot_false
        exact absurd hl'_val (by simp [hpivot_false])
      have hl'_ne_neg : lits[i']'hi' ≠ pivot.negate := by
        intro heq
        have hmem' : lits[i']'hi' ∈ lits.toList :=
          Array.mem_toList_iff.mpr (Array.getElem_mem hi')
        rw [heq] at hmem'
        exact absurd hmem' hcond.2.1
      have hl'_var_ne : (lits[i']'hi').var ≠ pivot.var := by
        intro hv
        rcases literal_eq_or_negate_of_same_var (lits[i']'hi') pivot hv with h | h
        · exact hl'_ne_pivot h
        · exact hl'_ne_neg h
      have hsame :
          f.litValue σ sk (lits[i']'hi') = f.litValue σ' sk (lits[i']'hi') :=
        litValue_flip_indep f σ sk (lits[i']'hi') pivot.var hl'_var_ne
          (fun hex => hcond.2.2 (lits[i']'hi')
            (Array.mem_toList_iff.mpr (Array.getElem_mem hi')) hex)
      have hmem_filt : lits[i']'hi' ∈ lits.filter (fun l => !(l == pivot)) :=
        Array.mem_filter.mpr ⟨Array.getElem_mem hi',
          by simp [beq_eq_false_iff_ne.mpr hl'_ne_pivot]⟩
      obtain ⟨j, hj, hj_eq⟩ := Array.mem_iff_getElem.mp hmem_filt
      simp only [DQBF.clauseValue, Array.any_eq_true]
      exact ⟨j, hj, hj_eq ▸ (hsame ▸ hl'_val)⟩

-- ─── Section 6: RUP, DQRATE and DQRATU Soundness Stubs ──────────────────────

/-- A clause is a *semantic consequence* of `(f, cs)`: it is true under every
    satisfying Skolem assignment and universal assignment. -/
def IsSemanticConsequence (f : DQBF) (cs : ClauseStore) (lits : Array Literal) : Prop :=
  ∀ (sk : SkolemAssignment) (σ : UnivAssignment),
    cs.matrixValue f σ sk = true → f.clauseValue σ sk lits = true

/-- **Semantic consequence soundness**: if `lits` is a semantic consequence of `(f, cs)`,
    adding `lits` preserves truth. -/
theorem SemanticConsequence_soundness (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (h_cons : IsSemanticConsequence f cs lits)
    (h : DQBFTrue f cs) : DQBFTrue f (cs.addClause lits).1 := by
  obtain ⟨sk, hsk⟩ := h
  exact ⟨sk, fun σ => matrixValue_addClause_of_both f cs lits σ sk (hsk σ) (h_cons sk σ (hsk σ))⟩

-- ─── State validity predicates ───────────────────────────────────────────────

/-- The checker state is *sound* w.r.t. the formula: every variable currently
    assigned in the trail is forced by every satisfying assignment of the matrix.
    Covers ALL variables (both universal and existential). -/
def StatePreservesModels (st : CheckState) : Prop :=
  ∀ v : Var, 0 < v →
    st.isAssigned.getD (v - 1) false = true →
    ∀ (sk : SkolemAssignment) (σ : UnivAssignment),
      st.clauses.matrixValue st.formula σ sk = true →
      st.formula.varValue σ sk v = st.value.getD (v - 1) false

/-- Well-formedness: all literals in all clauses have variables in [1, maxVar]. -/
def ClausesWellFormed (f : DQBF) (cs : ClauseStore) : Prop :=
  ∀ cref c, cs.getClause cref = some c →
    ∀ l ∈ c.lits.toList, 0 < l.var ∧ l.var ≤ f.maxVar

/-- Well-formedness of a clause literal array against a formula. -/
def ClauseLitsWellFormed (f : DQBF) (lits : Array Literal) : Prop :=
  ∀ l ∈ lits.toList, 0 < l.var ∧ l.var ≤ f.maxVar

theorem ClauseLitsWellFormed.mono
    {f g : DQBF} {lits : Array Literal}
    (hwf : ClauseLitsWellFormed f lits)
    (hmax : f.maxVar ≤ g.maxVar) :
    ClauseLitsWellFormed g lits := by
  intro l hl
  rcases hwf l hl with ⟨hpos, hle⟩
  exact ⟨hpos, Nat.le_trans hle hmax⟩

theorem ClauseLitsWellFormed.push
    {f : DQBF} {lits : Array Literal} {l : Literal}
    (hwf : ClauseLitsWellFormed f lits)
    (hl : 0 < l.var ∧ l.var ≤ f.maxVar) :
    ClauseLitsWellFormed f (lits.push l) := by
  intro l' hl'
  rcases Array.mem_push.mp (Array.mem_toList_iff.mp hl') with hl' | rfl
  · exact hwf l' (Array.mem_toList_iff.mpr hl')
  · exact hl

theorem ClauseLitsWellFormed.filter
    {f : DQBF} {lits : Array Literal} {p : Literal → Bool}
    (hwf : ClauseLitsWellFormed f lits) :
    ClauseLitsWellFormed f (lits.filter p) := by
  intro l hl
  exact hwf l (Array.mem_filter.mp (Array.mem_toList_iff.mp hl) |>.1 |> Array.mem_toList_iff.mpr)

theorem ClausesWellFormed.mono
    {f g : DQBF} {cs : ClauseStore}
    (hwf : ClausesWellFormed f cs)
    (hmax : f.maxVar ≤ g.maxVar) :
    ClausesWellFormed g cs := by
  intro cref c hget l hl
  rcases hwf cref c hget l hl with ⟨hpos, hle⟩
  exact ⟨hpos, Nat.le_trans hle hmax⟩

theorem ClausesWellFormed.addClause
    {f : DQBF} {cs : ClauseStore} {lits : Array Literal}
    (hwf : ClausesWellFormed f cs)
    (hlits : ClauseLitsWellFormed f lits) :
    ClausesWellFormed f (cs.addClause lits).1 := by
  intro cref c hget l hl
  by_cases hlt : cref < cs.clauses.size
  · rw [ClauseStore.getClause_addClause_lt cs lits cref hlt] at hget
    exact hwf cref c hget l hl
  · have hsize : cref < (cs.addClause lits).1.clauses.size :=
      ClauseStore.getClause_some_imp_lt (cs := (cs.addClause lits).1) cref c hget
    have hcref : cref = cs.clauses.size := by
      simp [ClauseStore.addClause] at hsize
      exact Nat.eq_of_lt_succ_of_not_lt hsize hlt
    subst hcref
    have hne : cs.clauses.size ≠ CRef_Undef := by
      exact ClauseStore.getClause_some_imp_ne_undef (cs := (cs.addClause lits).1) _ _ hget
    have hpos : 0 < cs.clauses.size := Nat.pos_iff_ne_zero.mpr hne
    rw [ClauseStore.getClause_addClause_new cs lits hpos] at hget
    cases hget
    exact hlits l hl

theorem ClausesWellFormed.deleteClause
    {f : DQBF} {cs : ClauseStore} {cref : CRef}
    (hwf : ClausesWellFormed f cs) :
    ClausesWellFormed f (cs.deleteClause cref) := by
  intro cref' c hget l hl
  by_cases hsame : cref' = cref
  · subst cref'
    have hlt' : cref < (cs.deleteClause cref).clauses.size :=
      ClauseStore.getClause_some_imp_lt (cs := cs.deleteClause cref) cref c hget
    have hlt : cref < cs.clauses.size := by
      rw [ClauseStore.deleteClause_clauses_size] at hlt'
      exact hlt'
    rw [ClauseStore.getClause_deleteClause_eq cs cref hlt] at hget
    cases hget
  · rw [ClauseStore.getClause_deleteClause_ne cs cref cref' hsame] at hget
    exact hwf cref' c hget l hl

theorem DQBFFalse.of_sound_extension
    {f₀ f₁ : DQBF} {cs₀ cs₁ : ClauseStore}
    (hsem : DQBFTrue f₀ cs₀ → DQBFTrue f₁ cs₁)
    (hfalse : DQBFFalse f₁ cs₁) :
    DQBFFalse f₀ cs₀ := by
  classical
  intro sk
  by_cases hex : ∃ σ, cs₀.matrixValue f₀ σ sk = false
  · exact hex
  · refine False.elim ?_
    have hall : ∀ σ, cs₀.matrixValue f₀ σ sk = true := by
      intro σ
      cases h : cs₀.matrixValue f₀ σ sk <;> simp at h ⊢
      exact False.elim (hex ⟨σ, h⟩)
    rcases hsem ⟨sk, hall⟩ with ⟨sk', htrue₁⟩
    rcases hfalse sk' with ⟨σ, hfalse₁⟩
    rw [htrue₁ σ] at hfalse₁
    simp at hfalse₁

theorem DQBFFalse.of_not_true
    {f : DQBF} {cs : ClauseStore}
    (hnot : ¬ DQBFTrue f cs) :
    DQBFFalse f cs := by
  classical
  intro sk
  by_cases hex : ∃ σ, cs.matrixValue f σ sk = false
  · exact hex
  · exfalso
    apply hnot
    refine ⟨sk, ?_⟩
    intro σ
    cases h : cs.matrixValue f σ sk <;> simp at h ⊢
    exact False.elim (hex ⟨σ, h⟩)

def addForallFormula (f : DQBF) (ext : Nat) : DQBF :=
  let v := f.maxVar + 1
  { f with
    maxVar := v
    internalName := f.internalName.push (ext, v)
    externalName := f.externalName.push ext
    isExistential := f.isExistential.push false
    univars := f.univars.push v
    depset := f.depset.push #[] }

def addExistsFormula (f : DQBF) (ext : Nat) (deps : Array Var) : DQBF :=
  let v := f.maxVar + 1
  { f with
    maxVar := v
    internalName := f.internalName.push (ext, v)
    externalName := f.externalName.push ext
    isExistential := f.isExistential.push true
    exivars := f.exivars.push v
    depset := f.depset.push deps }

theorem arrayGetD_push_lt {α : Type} (a : Array α) (x fallback : α) {i : Nat}
    (hi : i < a.size) :
    (a.push x).getD i fallback = a.getD i fallback := by
  simp [Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt hi]

theorem arrayGetD_push_eq {α : Type} (a : Array α) (x fallback : α) :
    (a.push x).getD a.size fallback = x := by
  simp [Array.getD, Array.getElem_push_eq]

theorem arrayGetD_true_imp_lt (a : Array Bool) {i : Nat}
    (h : a.getD i false = true) :
    i < a.size := by
  by_cases hi : i < a.size
  · exact hi
  · simp [Array.getD, hi] at h

theorem lookupInternal_addForallFormula_self
    (f : DQBF) (ext : Nat)
    (hfresh : f.externalVarExists ext = false) :
    (addForallFormula f ext).lookupInternal ext = some (f.maxVar + 1) := by
  rw [addForallFormula, DQBF.lookupInternal, Array.findSome?_eq_some_iff]
  refine ⟨f.internalName, (ext, f.maxVar + 1), #[], ?_, by simp, ?_⟩
  · simp
  · intro x hx
    have hneq : x.fst ≠ ext := by
      intro hxe
      have ⟨j, hj, hji⟩ := Array.mem_iff_getElem.mp hx
      have hany : f.internalName.any (fun p => p.fst = ext) = true :=
        Array.any_eq_true.mpr ⟨j, hj, by simpa [hji, hxe]⟩
      rw [DQBF.externalVarExists, hany] at hfresh
      cases hfresh
    simp [hneq]

theorem lookupInternal_addForallFormula_ne
    (f : DQBF) (ext ext' : Nat)
    (hne : ext' ≠ ext) :
    (addForallFormula f ext).lookupInternal ext' = f.lookupInternal ext' := by
  unfold addForallFormula DQBF.lookupInternal
  have hif : (if ext = ext' then some (f.maxVar + 1) else none) = none := by
    simp [hne.symm]
  simp [hif]

theorem varValue_addForallFormula_old
    (f : DQBF) (ext : Nat) (σ : UnivAssignment) (sk : SkolemAssignment)
    {v : Var}
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hle : v ≤ f.maxVar) :
    (addForallFormula f ext).varValue σ sk v = f.varValue σ sk v := by
  unfold DQBF.varValue DQBF.exiValue addForallFormula
  have hvis : v < f.isExistential.size := by
    simpa [his] using Nat.lt_succ_of_le hle
  have hvdeps : v < f.depset.size := by
    simpa [hdeps] using Nat.lt_succ_of_le hle
  have his' : (f.isExistential.push false).getD v false = f.isExistential.getD v false :=
    arrayGetD_push_lt f.isExistential false false hvis
  have hdeps' : (f.depset.push #[]).getD v #[] = f.depset.getD v #[] :=
    arrayGetD_push_lt f.depset #[] #[] hvdeps
  simp [DQBF.isVarExistential, his', hdeps']

theorem litValue_addForallFormula_old
    (f : DQBF) (ext : Nat) (σ : UnivAssignment) (sk : SkolemAssignment)
    {l : Literal}
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hwf : 0 < l.var ∧ l.var ≤ f.maxVar) :
    (addForallFormula f ext).litValue σ sk l = f.litValue σ sk l := by
  unfold DQBF.litValue
  simpa using congrArg (fun b => if l.isPos then b else !b)
    (varValue_addForallFormula_old f ext σ sk his hdeps hwf.2)

theorem clauseValue_addForallFormula_old
    (f : DQBF) (ext : Nat) (σ : UnivAssignment) (sk : SkolemAssignment)
    (lits : Array Literal)
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hwf : ∀ l ∈ lits.toList, 0 < l.var ∧ l.var ≤ f.maxVar) :
    (addForallFormula f ext).clauseValue σ sk lits = f.clauseValue σ sk lits := by
  unfold DQBF.clauseValue
  apply Bool.eq_iff_iff.mpr
  constructor <;> intro htrue <;> simp only [Array.any_eq_true] at htrue ⊢
  · rcases htrue with ⟨i, hi, hli⟩
    exact ⟨i, hi, by
      simpa [litValue_addForallFormula_old f ext σ sk his hdeps
        (hwf _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi)))] using hli⟩
  · rcases htrue with ⟨i, hi, hli⟩
    exact ⟨i, hi, by
      simpa [litValue_addForallFormula_old f ext σ sk his hdeps
        (hwf _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi)))] using hli⟩

theorem matrixValue_addForallFormula_old
    (f : DQBF) (cs : ClauseStore) (ext : Nat)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hwf : ClausesWellFormed f cs) :
    cs.matrixValue (addForallFormula f ext) σ sk = cs.matrixValue f σ sk := by
  unfold ClauseStore.matrixValue
  apply List.all_congr rfl
  intro i
  by_cases hget : cs.getClause (i + 1) = none
  · simp [hget]
  · rcases Option.ne_none_iff_exists'.mp hget with ⟨c, hc⟩
    simp [hc, clauseValue_addForallFormula_old f ext σ sk c.lits his hdeps
      (hwf (i + 1) c hc)]

theorem DQBFTrue_addForallFormula
    (f : DQBF) (cs : ClauseStore) (ext : Nat)
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hwf : ClausesWellFormed f cs)
    (htrue : DQBFTrue f cs) :
    DQBFTrue (addForallFormula f ext) cs := by
  rcases htrue with ⟨sk, hsk⟩
  refine ⟨sk, ?_⟩
  intro σ
  rw [matrixValue_addForallFormula_old f cs ext σ sk his hdeps hwf]
  exact hsk σ

theorem lookupInternal_addExistsFormula_self
    (f : DQBF) (ext : Nat) (deps : Array Var)
    (hfresh : f.externalVarExists ext = false) :
    (addExistsFormula f ext deps).lookupInternal ext = some (f.maxVar + 1) := by
  rw [addExistsFormula, DQBF.lookupInternal, Array.findSome?_eq_some_iff]
  refine ⟨f.internalName, (ext, f.maxVar + 1), #[], ?_, by simp, ?_⟩
  · simp
  · intro x hx
    have hneq : x.fst ≠ ext := by
      intro hxe
      have ⟨j, hj, hji⟩ := Array.mem_iff_getElem.mp hx
      have hany : f.internalName.any (fun p => p.fst = ext) = true :=
        Array.any_eq_true.mpr ⟨j, hj, by simpa [hji, hxe]⟩
      rw [DQBF.externalVarExists, hany] at hfresh
      cases hfresh
    simp [hneq]

theorem lookupInternal_addExistsFormula_ne
    (f : DQBF) (ext ext' : Nat) (deps : Array Var)
    (hne : ext' ≠ ext) :
    (addExistsFormula f ext deps).lookupInternal ext' = f.lookupInternal ext' := by
  unfold addExistsFormula DQBF.lookupInternal
  have hif : (if ext = ext' then some (f.maxVar + 1) else none) = none := by
    simp [hne.symm]
  simp [hif]

theorem varValue_addExistsFormula_old
    (f : DQBF) (ext : Nat) (deps : Array Var) (σ : UnivAssignment) (sk : SkolemAssignment)
    {v : Var}
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hle : v ≤ f.maxVar) :
    (addExistsFormula f ext deps).varValue σ sk v = f.varValue σ sk v := by
  unfold DQBF.varValue DQBF.exiValue addExistsFormula
  have hvis : v < f.isExistential.size := by
    simpa [his] using Nat.lt_succ_of_le hle
  have hvdeps : v < f.depset.size := by
    simpa [hdeps] using Nat.lt_succ_of_le hle
  have his' : (f.isExistential.push true).getD v false = f.isExistential.getD v false :=
    arrayGetD_push_lt f.isExistential true false hvis
  have hdeps' : (f.depset.push deps).getD v #[] = f.depset.getD v #[] :=
    arrayGetD_push_lt f.depset deps #[] hvdeps
  simp [DQBF.isVarExistential, his', hdeps']

theorem litValue_addExistsFormula_old
    (f : DQBF) (ext : Nat) (deps : Array Var) (σ : UnivAssignment) (sk : SkolemAssignment)
    {l : Literal}
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hwf : 0 < l.var ∧ l.var ≤ f.maxVar) :
    (addExistsFormula f ext deps).litValue σ sk l = f.litValue σ sk l := by
  unfold DQBF.litValue
  simpa using congrArg (fun b => if l.isPos then b else !b)
    (varValue_addExistsFormula_old f ext deps σ sk his hdeps hwf.2)

theorem clauseValue_addExistsFormula_old
    (f : DQBF) (ext : Nat) (deps : Array Var) (σ : UnivAssignment) (sk : SkolemAssignment)
    (lits : Array Literal)
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hwf : ∀ l ∈ lits.toList, 0 < l.var ∧ l.var ≤ f.maxVar) :
    (addExistsFormula f ext deps).clauseValue σ sk lits = f.clauseValue σ sk lits := by
  unfold DQBF.clauseValue
  apply Bool.eq_iff_iff.mpr
  constructor <;> intro htrue <;> simp only [Array.any_eq_true] at htrue ⊢
  · rcases htrue with ⟨i, hi, hli⟩
    exact ⟨i, hi, by
      simpa [litValue_addExistsFormula_old f ext deps σ sk his hdeps
        (hwf _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi)))] using hli⟩
  · rcases htrue with ⟨i, hi, hli⟩
    exact ⟨i, hi, by
      simpa [litValue_addExistsFormula_old f ext deps σ sk his hdeps
        (hwf _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi)))] using hli⟩

theorem matrixValue_addExistsFormula_old
    (f : DQBF) (cs : ClauseStore) (ext : Nat) (deps : Array Var)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hwf : ClausesWellFormed f cs) :
    cs.matrixValue (addExistsFormula f ext deps) σ sk = cs.matrixValue f σ sk := by
  unfold ClauseStore.matrixValue
  apply List.all_congr rfl
  intro i
  by_cases hget : cs.getClause (i + 1) = none
  · simp [hget]
  · rcases Option.ne_none_iff_exists'.mp hget with ⟨c, hc⟩
    simp [hc, clauseValue_addExistsFormula_old f ext deps σ sk c.lits his hdeps
      (hwf (i + 1) c hc)]

theorem DQBFTrue_addExistsFormula
    (f : DQBF) (cs : ClauseStore) (ext : Nat) (deps : Array Var)
    (his : f.isExistential.size = f.maxVar + 1)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hwf : ClausesWellFormed f cs)
    (htrue : DQBFTrue f cs) :
    DQBFTrue (addExistsFormula f ext deps) cs := by
  rcases htrue with ⟨sk, hsk⟩
  refine ⟨sk, ?_⟩
  intro σ
  rw [matrixValue_addExistsFormula_old f cs ext deps σ sk his hdeps hwf]
  exact hsk σ

private def extendSkolemIgnoreLast
    (sk : SkolemAssignment) (of_ : Var) : SkolemAssignment :=
  fun v args => if v = of_ then sk v args.pop else sk v args

theorem lookupInternal_addDependencyFormula
    (f : DQBF) (of_ on_ : Var) (ext : Nat) :
    (f.addDependencyFormula of_ on_).lookupInternal ext = f.lookupInternal ext := by
  simp [DQBF.addDependencyFormula, DQBF.lookupInternal]

theorem varValue_addDependencyFormula_old
    (f : DQBF) (of_ on_ v : Var) (σ : UnivAssignment) (sk : SkolemAssignment)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hof : 0 < of_) (hof_le : of_ ≤ f.maxVar) :
    (f.addDependencyFormula of_ on_).varValue σ (extendSkolemIgnoreLast sk of_) v =
      f.varValue σ sk v := by
  have hof_lt : of_ < f.depset.size := by
    have : of_ < f.maxVar + 1 := Nat.lt_succ_of_le hof_le
    simpa [hdeps] using this
  by_cases hex : f.isVarExistential v = true
  · by_cases hov : v = of_
    · subst hov
      have hex' : (f.addDependencyFormula v on_).isVarExistential v = true := by
        simpa [DQBF.addDependencyFormula, DQBF.isVarExistential] using hex
      rw [DQBF.varValue, DQBF.varValue, hex', hex]
      simp [DQBF.exiValue, DQBF.addDependencyFormula, extendSkolemIgnoreLast, hof_lt]
    · have hex' : (f.addDependencyFormula of_ on_).isVarExistential v = true := by
        simpa [DQBF.addDependencyFormula, DQBF.isVarExistential] using hex
      rw [DQBF.varValue, DQBF.varValue, hex', hex]
      have hne : of_ ≠ v := by simpa [eq_comm] using hov
      have hget :
          (f.depset.setIfInBounds of_ ((f.depset.getD of_ #[]).push on_)).getD v #[] =
            f.depset.getD v #[] := by
        simp [Array.setIfInBounds, hof_lt, hne]
      simp [DQBF.exiValue, DQBF.addDependencyFormula, extendSkolemIgnoreLast, hne]
      intro hv
      exact False.elim (hov hv)
  · have hex_false : f.isVarExistential v = false := by
      cases hval : f.isVarExistential v <;> simp_all
    have hex' : (f.addDependencyFormula of_ on_).isVarExistential v = false := by
      simpa [DQBF.addDependencyFormula, DQBF.isVarExistential] using hex_false
    rw [DQBF.varValue, DQBF.varValue, hex', hex_false]
    simp

theorem litValue_addDependencyFormula_old
    (f : DQBF) (of_ on_ : Var) (σ : UnivAssignment) (sk : SkolemAssignment)
    (l : Literal)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hof : 0 < of_) (hof_le : of_ ≤ f.maxVar) :
    (f.addDependencyFormula of_ on_).litValue σ (extendSkolemIgnoreLast sk of_) l =
      f.litValue σ sk l := by
  simp [DQBF.litValue, varValue_addDependencyFormula_old f of_ on_ l.var σ sk hdeps hof hof_le]

theorem clauseValue_addDependencyFormula_old
    (f : DQBF) (of_ on_ : Var) (σ : UnivAssignment) (sk : SkolemAssignment)
    (lits : Array Literal)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hof : 0 < of_) (hof_le : of_ ≤ f.maxVar) :
    (f.addDependencyFormula of_ on_).clauseValue σ (extendSkolemIgnoreLast sk of_) lits =
      f.clauseValue σ sk lits := by
  unfold DQBF.clauseValue
  simpa using
    (Array.any_congr (w := rfl)
      (h := fun l => litValue_addDependencyFormula_old f of_ on_ σ sk l hdeps hof hof_le)
      (wstart := rfl) (wstop := rfl))

theorem matrixValue_addDependencyFormula_old
    (f : DQBF) (cs : ClauseStore) (of_ on_ : Var)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hdeps : f.depset.size = f.maxVar + 1) (hof : 0 < of_) (hof_le : of_ ≤ f.maxVar) :
    cs.matrixValue (f.addDependencyFormula of_ on_) σ (extendSkolemIgnoreLast sk of_) =
      cs.matrixValue f σ sk := by
  unfold ClauseStore.matrixValue
  apply List.all_congr rfl
  intro i
  cases hclause : cs.getClause (i + 1) with
  | none =>
      simp [hclause]
  | some c =>
      simp [hclause, clauseValue_addDependencyFormula_old f of_ on_ σ sk c.lits hdeps hof hof_le]

theorem DQBFTrue_addDependencyFormula
    (f : DQBF) (cs : ClauseStore) (of_ on_ : Var)
    (hdeps : f.depset.size = f.maxVar + 1)
    (hof : 0 < of_) (hof_le : of_ ≤ f.maxVar)
    (htrue : DQBFTrue f cs) :
    DQBFTrue (f.addDependencyFormula of_ on_) cs := by
  rcases htrue with ⟨sk, hsk⟩
  refine ⟨extendSkolemIgnoreLast sk of_, ?_⟩
  intro σ
  rw [matrixValue_addDependencyFormula_old f cs of_ on_ σ sk hdeps hof hof_le]
  exact hsk σ


-- ─── Structural invariants ────────────────────────────────────────────────────

/-- Structural well-formedness of a `CheckState`.

Captures array-size consistency, trail coherence, and assignment bookkeeping.
Requires no external model witness and is preserved by every checker operation. -/
structure CheckState.Sound (st : CheckState) : Prop where
  /-- The assignment array is indexed by (var - 1), so its size must equal maxVar. -/
  isAssigned_size : st.isAssigned.size = st.formula.maxVar
  /-- The value array is parallel to isAssigned. -/
  value_size      : st.value.size = st.formula.maxVar
  /-- Independence cache arrays are also indexed by (univar - 1). -/
  indepKnown_size : st.indepKnown.size = st.formula.maxVar
  indepOf_size    : st.indepOf.size    = st.formula.maxVar
  /-- externalName[0] is the dummy entry; real entries at indices 1..maxVar. -/
  externalName_size  : st.formula.externalName.size  = st.formula.maxVar + 1
  isExistential_size : st.formula.isExistential.size = st.formula.maxVar + 1
  depset_size        : st.formula.depset.size        = st.formula.maxVar + 1
  /-- Clause store always contains the dummy clause at index 0. -/
  clauses_nonempty : 0 < st.clauses.clauses.size
  /-- There is always at least one decision level (level 0). -/
  trail_nonempty : 0 < st.trail.size
  /-- Every literal recorded in the trail refers to a valid variable. -/
  trail_lits_valid : ∀ i, i < st.trail.size →
      ∀ l ∈ st.trail.getD i #[], 0 < l.var ∧ l.var ≤ st.formula.maxVar
  /-- A variable is assigned iff it appears in some trail level.
      This is the key invariant that makes `backtrackBefore` correct. -/
  assigned_iff_in_trail : ∀ v : Var, 0 < v → v ≤ st.formula.maxVar →
      (st.isAssigned.getD (v - 1) false = true ↔
       ∃ i, i < st.trail.size ∧ ∃ l ∈ st.trail.getD i #[], l.var = v)

/-- High-level invariant of the checker state at action boundaries.

Extends `Sound` with semantic properties relative to the initial `(dqbf, cs)`:
the propagation queue is empty, only the base decision level is active, all clause
literals are well-formed, and the current formula is a sound extension of the original.
This invariant holds at entry and exit of every `checkAction` call. -/
structure CheckState.Correct (dqbf : DQBF) (cs : ClauseStore) (st : CheckState) : Prop
    extends Sound st where
  /-- No pending unit propagation (queue is drained before returning). -/
  propQueue_empty    : st.propQueue = #[]
  /-- Only the persistent base level remains (no active decision levels). -/
  trail_single_level : st.trail.size = 1
  /-- All literals in active clauses refer to valid variables. -/
  clauses_wf : ClausesWellFormed st.formula st.clauses
  /-- The formula may only grow: new variables can be added, none removed. -/
  formula_extends : dqbf.maxVar ≤ st.formula.maxVar
  /-- Every variable currently assigned in the trail is forced by every satisfying
      assignment — its value agrees with any model. -/
  preserves_models : StatePreservesModels st
  /-- Semantic soundness: proof steps never introduce falsity. -/
  formula_sound : DQBFTrue dqbf cs → DQBFTrue st.formula st.clauses
  /-- Every successful external-to-internal lookup stays within the current formula. -/
  lookupInternal_sound : ∀ ext v, st.formula.lookupInternal ext = some v →
      0 < v ∧ v ≤ st.formula.maxVar

/-- The non-semantic action-boundary invariant needed through propagation.

This is the structural part of `Correct` that survives `enqueue` / `propagate`,
without requiring the propagation queue to already be empty. -/
structure CheckState.PropStruct (st : CheckState) : Prop
    extends Sound st where
  clauses_wf : ClausesWellFormed st.formula st.clauses
  trail_single_level : st.trail.size = 1

-- ─── Model consistency predicate ─────────────────────────────────────────────

/-- The checker state is *consistent* with a satisfying assignment `(σ, sk)` for `(f, cs)`.

  Extends `Sound` with model-level fields needed to show unit propagation never
  conflicts when the model satisfies all clauses:
  - the state's formula and clauses match the reference `(f, cs)`,
  - all active clause literals are well-formed,
  - every assigned variable has the model-dictated value,
  - every literal queued for propagation is model-true.

  Because it extends `Sound`, every operation proved to preserve `ConsistentWith`
  automatically preserves all structural invariants (array-size coherence, trail
  non-emptiness, etc.). The size fields `isAssigned_size` and `value_size` are
  inherited from `Sound` (as `st.formula.maxVar`, equal to `f.maxVar` via
  `formula_eq`). -/
structure CheckState.ConsistentWith (f : DQBF) (cs : ClauseStore)
    (σ : UnivAssignment) (sk : SkolemAssignment) (st : CheckState) : Prop
    extends Sound st where
  /-- The state's formula matches the reference. -/
  formula_eq : st.formula = f
  /-- The state's clause store matches the reference. -/
  clauses_eq : st.clauses = cs
  /-- All literals in active clauses have variables in [1, maxVar]. -/
  clauses_wf : ClausesWellFormed f cs
  /-- Assigned variables have the model-dictated value. -/
  assigned_model : ∀ v : Var, 0 < v → st.isAssigned.getD (v - 1) false = true →
      f.varValue σ sk v = st.value.getD (v - 1) false
  /-- Every literal in the propagation queue is true in the model. -/
  queue_model : ∀ l ∈ st.propQueue.toList, f.litValue σ sk l = true

-- ─── Connection: Correct → ConsistentWith ────────────────────────────────────

/-- A `Correct` state is consistent with any satisfying model of the current formula.
    This is the key bridge between the inter-action invariant (`Correct`) and the
    propagation-level invariant (`CheckState.ConsistentWith`) used in soundness proofs. -/
theorem CheckState.Correct.to_consistentWith
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hcorr : CheckState.Correct dqbf cs st)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hmat : st.clauses.matrixValue st.formula σ sk = true) :
    CheckState.ConsistentWith st.formula st.clauses σ sk st :=
  { toSound      := hcorr.toSound
    formula_eq   := rfl
    clauses_eq   := rfl
    clauses_wf   := hcorr.clauses_wf
    assigned_model := fun v hpos hassign => hcorr.preserves_models v hpos hassign sk σ hmat
    queue_model  := by simp [hcorr.propQueue_empty] }

theorem CheckState.Correct.toPropStruct
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hcorr : CheckState.Correct dqbf cs st) :
    CheckState.PropStruct st :=
  { toSound := hcorr.toSound
    clauses_wf := hcorr.clauses_wf
    trail_single_level := hcorr.trail_single_level }

theorem CheckState.empty_correct :
    CheckState.Correct CheckState.empty.formula CheckState.empty.clauses CheckState.empty := by
  refine
    { toSound := ?_
      propQueue_empty := rfl
      trail_single_level := rfl
      clauses_wf := ?_
      formula_extends := by simp [CheckState.empty]
      preserves_models := ?_
      formula_sound := ?_
      lookupInternal_sound := ?_ }
  · refine
      { isAssigned_size := by simp [CheckState.empty]
        value_size := by simp [CheckState.empty]
        indepKnown_size := by simp [CheckState.empty]
        indepOf_size := by simp [CheckState.empty]
        externalName_size := by simp [CheckState.empty]
        isExistential_size := by simp [CheckState.empty]
        depset_size := by simp [CheckState.empty]
        clauses_nonempty := by simp [CheckState.empty]
        trail_nonempty := by simp [CheckState.empty]
        trail_lits_valid := ?_
        assigned_iff_in_trail := ?_ }
    · intro i hi l hl
      simp [CheckState.empty] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp [CheckState.empty] at hl
    · intro v hpos hle
      have hle0 : v ≤ 0 := by
        simpa [CheckState.empty] using hle
      have hv0 : v = 0 := Nat.eq_zero_of_le_zero hle0
      subst hv0
      simp at hpos
  · intro cref c hget l hl
    by_cases hzero : cref = CRef_Undef
    · have : False := by
        simpa [CheckState.empty, ClauseStore.getClause, CRef_Undef, hzero] using hget
      exact this.elim
    · have : False := by
        have hne0 : cref ≠ 0 := by
          simpa [CRef_Undef] using hzero
        have hnone :
            (if cref = 0 then some Clause.dummy else none) = none := by
          simp [hne0]
        simp [CheckState.empty, ClauseStore.getClause, ClauseStore.getClauseAt, CRef_Undef, hzero,
          hnone] at hget
      exact this.elim
  · intro v hpos hassign sk σ hmat
    simp [CheckState.empty] at hassign
  · intro htrue
    exact htrue
  · intro ext v hlookup
    simp [CheckState.empty, DQBF.lookupInternal] at hlookup

/-- Parser-side invariant during prefix loading.

    Before matrix parsing starts, the checker state is still relative to the empty
    initial formula/clause store, the clause store is untouched, and the trail is the
    clean base level.  This is the right invariant for `a/e/d` prefix lines. -/
def PrefixState (st : CheckState) : Prop :=
  CheckState.Correct CheckState.empty.formula CheckState.empty.clauses st ∧
    st.clauses = {} ∧
    (∀ v : Var, 0 < v → v ≤ st.formula.maxVar →
      st.isAssigned.getD (v - 1) false = false)

theorem PrefixState.empty : PrefixState CheckState.empty := by
  refine ⟨CheckState.empty_correct, rfl, ?_⟩
  intro v hpos hle
  have : False := by
    have hle0 : v ≤ 0 := by simpa [CheckState.empty] using hle
    exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hpos hle0)
  exact False.elim this

private theorem PrefixState.isAssigned_false
    {st : CheckState} (hpref : PrefixState st) {v : Var}
    (hpos : 0 < v) (hle : v ≤ st.formula.maxVar) :
    st.isAssigned.getD (v - 1) false = false :=
  hpref.2.2 v hpos hle

theorem PrefixState.withSetDepset
    {st : CheckState} (hpref : PrefixState st) (iv : Var) (deps : Array Var) :
    PrefixState
      { st with
        formula := { st.formula with depset := st.formula.depset.setIfInBounds iv deps } } := by
  let st' : CheckState :=
    { st with
      formula := { st.formula with depset := st.formula.depset.setIfInBounds iv deps } }
  rcases hpref with ⟨hcorr, hclauses, hallFalse⟩
  refine ⟨?_, ?_, ?_⟩
  · change CheckState.Correct CheckState.empty.formula CheckState.empty.clauses st'
    refine
      { toSound := ?_
        propQueue_empty := by simpa [st'] using hcorr.propQueue_empty
        trail_single_level := by simpa [st'] using hcorr.trail_single_level
        clauses_wf := by simpa [st'] using hcorr.clauses_wf
        formula_extends := hcorr.formula_extends
        preserves_models := ?_
        formula_sound := ?_
        lookupInternal_sound := ?_ }
    · refine
        { isAssigned_size := by simpa [st'] using hcorr.toSound.isAssigned_size
          value_size := by simpa [st'] using hcorr.toSound.value_size
          indepKnown_size := by simpa [st'] using hcorr.toSound.indepKnown_size
          indepOf_size := by simpa [st'] using hcorr.toSound.indepOf_size
          externalName_size := by simpa [st'] using hcorr.toSound.externalName_size
          isExistential_size := by simpa [st'] using hcorr.toSound.isExistential_size
          depset_size := by simp [st', Array.size_setIfInBounds, hcorr.toSound.depset_size]
          clauses_nonempty := by simpa [st'] using hcorr.toSound.clauses_nonempty
          trail_nonempty := by simpa [st'] using hcorr.toSound.trail_nonempty
          trail_lits_valid := ?_
          assigned_iff_in_trail := ?_ }
      · intro i hi l hl
        rcases hcorr.trail_lits_valid i hi l hl with ⟨hpos, hle_old⟩
        exact ⟨hpos, by simpa [st'] using hle_old⟩
      · intro v hpos hle
        have hle_old : v ≤ st.formula.maxVar := by
          simpa [st'] using hle
        simpa [st'] using hcorr.assigned_iff_in_trail v hpos hle_old
    · intro v hpos hassign sk σ hmat
      have hlt : v - 1 < st.isAssigned.size := arrayGetD_true_imp_lt (a := st.isAssigned) (by
        simpa [st'] using hassign)
      have hle : v ≤ st.formula.maxVar := by
        rw [hcorr.toSound.isAssigned_size] at hlt
        have hsucc : v - 1 + 1 ≤ st.formula.maxVar := Nat.succ_le_of_lt hlt
        simpa [Nat.sub_add_cancel hpos] using hsucc
      have hfalse : st.isAssigned.getD (v - 1) false = false :=
        PrefixState.isAssigned_false ⟨hcorr, hclauses, hallFalse⟩ hpos hle
      rw [show st'.isAssigned = st.isAssigned by rfl] at hassign
      rw [hfalse] at hassign
      cases hassign
    · intro _htrue
      have hclauses' : st'.clauses = {} := by
        simpa [st'] using hclauses
      rw [hclauses']
      simpa using DQBFTrue.of_empty_matrix st'.formula ({}) (by simp)
    · intro ext v hlookup
      have hlookup_old : st.formula.lookupInternal ext = some v := by
        simpa [st', DQBF.lookupInternal] using hlookup
      simpa [st'] using hcorr.lookupInternal_sound ext v hlookup_old
  · simpa [st'] using hclauses
  · intro v hpos hle
    have hle_old : v ≤ st.formula.maxVar := by
      simpa [st'] using hle
    simpa [st'] using hallFalse v hpos hle_old


/-- Extending the formula with one fresh existential variable preserves `Correct`.
    The new variable starts unassigned and does not occur in the existing clause store
    or trail, so only the formula-growth fields need real work. -/
theorem CheckState.Correct.withAddVarExists
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hcorr : CheckState.Correct dqbf cs st)
    (ext0 : Nat) (deps : Array Var)
    (hfresh : st.formula.externalVarExists ext0 = false) :
    CheckState.Correct dqbf cs
      { st with
        formula := addExistsFormula st.formula ext0 deps
        isAssigned := st.isAssigned.push false
        value := st.value.push false
        indepKnown := st.indepKnown.push false
        indepOf := st.indepOf.push #[] } := by
  let f' := addExistsFormula st.formula ext0 deps
  let st' : CheckState :=
    { st with
      formula := f'
      isAssigned := st.isAssigned.push false
      value := st.value.push false
      indepKnown := st.indepKnown.push false
      indepOf := st.indepOf.push #[] }
  change CheckState.Correct dqbf cs st'
  have hgrow : st.formula.maxVar ≤ f'.maxVar := by
    simp [f', addExistsFormula]
  refine
    { toSound := ?_
      propQueue_empty := hcorr.propQueue_empty
      trail_single_level := hcorr.trail_single_level
      clauses_wf := hcorr.clauses_wf.mono hgrow
      formula_extends := Nat.le_trans hcorr.formula_extends hgrow
      preserves_models := ?_
      formula_sound := ?_
      lookupInternal_sound := ?_ }
  · refine
      { isAssigned_size := ?_
        value_size := ?_
        indepKnown_size := ?_
        indepOf_size := ?_
        externalName_size := ?_
        isExistential_size := ?_
        depset_size := ?_
        clauses_nonempty := hcorr.toSound.clauses_nonempty
        trail_nonempty := hcorr.toSound.trail_nonempty
        trail_lits_valid := ?_
        assigned_iff_in_trail := ?_ }
    · simp [st', f', addExistsFormula, hcorr.toSound.isAssigned_size]
    · simp [st', f', addExistsFormula, hcorr.toSound.value_size]
    · simp [st', f', addExistsFormula, hcorr.toSound.indepKnown_size]
    · simp [st', f', addExistsFormula, hcorr.toSound.indepOf_size]
    · simp [st', f', addExistsFormula, hcorr.toSound.externalName_size]
    · simp [st', f', addExistsFormula, hcorr.toSound.isExistential_size]
    · simp [st', f', addExistsFormula, hcorr.toSound.depset_size]
    · intro i hi l hl
      rcases hcorr.trail_lits_valid i hi l hl with ⟨hpos, hle⟩
      exact ⟨hpos, Nat.le_trans hle hgrow⟩
    · intro v hpos hle
      dsimp [st']
      by_cases hnew : v = st.formula.maxVar + 1
      · constructor
        · intro hassign
          have : (st.isAssigned.push false).getD (v - 1) false = false := by
            subst v
            have hidx : (st.formula.maxVar + 1) - 1 = st.isAssigned.size := by
              simpa [hcorr.toSound.isAssigned_size]
            rw [hidx]
            simpa using (arrayGetD_push_eq st.isAssigned false false)
          rw [this] at hassign
          cases hassign
        · intro htrail
          rcases htrail with ⟨i, hi, l, hl, hlvar⟩
          rcases hcorr.trail_lits_valid i hi l hl with ⟨_, hle_old⟩
          subst v
          rw [hlvar] at hle_old
          exact False.elim (Nat.not_succ_le_self _ hle_old)
      · have hv_old : v ≤ st.formula.maxVar := by
          exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hle (by simpa [eq_comm] using hnew))
        have hlt : v - 1 < st.isAssigned.size := by
          have hlt' : v - 1 < st.formula.maxVar := by
            have : Nat.succ (v - 1) ≤ st.formula.maxVar := by
              have hv_eq : v - 1 + 1 = v := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
              simpa [Nat.succ_eq_add_one, hv_eq] using hv_old
            exact Nat.lt_of_succ_le this
          simpa [hcorr.toSound.isAssigned_size] using hlt'
        constructor
        · intro hassign
          have hassign_old : st.isAssigned.getD (v - 1) false = true := by
            simpa [arrayGetD_push_lt st.isAssigned false false hlt] using hassign
          exact (hcorr.assigned_iff_in_trail v hpos hv_old).mp hassign_old
        · intro htrail
          have hassign_old : st.isAssigned.getD (v - 1) false = true :=
            (hcorr.assigned_iff_in_trail v hpos hv_old).mpr htrail
          simpa [arrayGetD_push_lt st.isAssigned false false hlt] using hassign_old
  · intro v hpos hassign sk σ hmat
    dsimp [st', f'] at hassign hmat ⊢
    have hlt_new : v - 1 < (st.isAssigned.push false).size :=
      arrayGetD_true_imp_lt (a := st.isAssigned.push false) hassign
    by_cases hlt : v - 1 < st.isAssigned.size
    · have hv_le : v ≤ st.formula.maxVar := by
        have hlt' : v - 1 < st.formula.maxVar := by
          simpa [hcorr.toSound.isAssigned_size] using hlt
        have : Nat.succ (v - 1) ≤ st.formula.maxVar := Nat.succ_le_of_lt hlt'
        have hv_eq : v - 1 + 1 = v := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
        simpa [Nat.succ_eq_add_one, hv_eq] using this
      have hassign_old : st.isAssigned.getD (v - 1) false = true := by
        simpa [arrayGetD_push_lt st.isAssigned false false hlt] using hassign
      have hmat_old : st.clauses.matrixValue st.formula σ sk = true := by
        rw [matrixValue_addExistsFormula_old st.formula st.clauses ext0 deps σ sk
          hcorr.toSound.isExistential_size hcorr.toSound.depset_size hcorr.clauses_wf] at hmat
        exact hmat
      have hval_lt : v - 1 < st.value.size := by
        simpa [hcorr.toSound.value_size, hcorr.toSound.isAssigned_size] using hlt
      rw [varValue_addExistsFormula_old st.formula ext0 deps σ sk
          hcorr.toSound.isExistential_size hcorr.toSound.depset_size hv_le]
      rw [arrayGetD_push_lt st.value false false hval_lt]
      exact hcorr.preserves_models v hpos hassign_old sk σ hmat_old
    · have htop : v - 1 = st.isAssigned.size := by
        have hlt_push : v - 1 < st.isAssigned.size + 1 := by
          simpa [Array.size_push] using hlt_new
        exact Nat.eq_of_lt_succ_of_not_lt hlt_push hlt
      have : (st.isAssigned.push false).getD (v - 1) false = false := by
        rw [htop]
        simpa using (arrayGetD_push_eq st.isAssigned false false)
      rw [this] at hassign
      cases hassign
  · intro htrue
    exact DQBFTrue_addExistsFormula st.formula st.clauses ext0 deps
      hcorr.toSound.isExistential_size hcorr.toSound.depset_size hcorr.clauses_wf
      (hcorr.formula_sound htrue)
  · intro ext v hlookup
    dsimp [st', f'] at hlookup ⊢
    by_cases hext : ext = ext0
    · subst ext
      rw [lookupInternal_addExistsFormula_self st.formula ext0 deps hfresh] at hlookup
      cases hlookup
      simp [addExistsFormula]
    · have hlookup_old : st.formula.lookupInternal ext = some v := by
        simpa [lookupInternal_addExistsFormula_ne st.formula ext0 ext deps hext] using hlookup
      rcases hcorr.lookupInternal_sound ext v hlookup_old with ⟨hposv, hlev⟩
      exact ⟨hposv, Nat.le_trans hlev hgrow⟩

/-- Extending the formula with one fresh universal variable preserves `Correct`.
    The new variable starts unassigned and does not occur in the existing clause store
    or trail, so the semantic effect is only the introduction of an unused universal. -/
theorem CheckState.Correct.withAddVarForall
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hcorr : CheckState.Correct dqbf cs st)
    (ext0 : Nat)
    (hfresh : st.formula.externalVarExists ext0 = false) :
    CheckState.Correct dqbf cs
      { st with
        formula := addForallFormula st.formula ext0
        isAssigned := st.isAssigned.push false
        value := st.value.push false
        indepKnown := st.indepKnown.push false
        indepOf := st.indepOf.push #[] } := by
  let f' := addForallFormula st.formula ext0
  let st' : CheckState :=
    { st with
      formula := f'
      isAssigned := st.isAssigned.push false
      value := st.value.push false
      indepKnown := st.indepKnown.push false
      indepOf := st.indepOf.push #[] }
  change CheckState.Correct dqbf cs st'
  have hgrow : st.formula.maxVar ≤ f'.maxVar := by
    simp [f', addForallFormula]
  refine
    { toSound := ?_
      propQueue_empty := hcorr.propQueue_empty
      trail_single_level := hcorr.trail_single_level
      clauses_wf := hcorr.clauses_wf.mono hgrow
      formula_extends := Nat.le_trans hcorr.formula_extends hgrow
      preserves_models := ?_
      formula_sound := ?_
      lookupInternal_sound := ?_ }
  · refine
      { isAssigned_size := ?_
        value_size := ?_
        indepKnown_size := ?_
        indepOf_size := ?_
        externalName_size := ?_
        isExistential_size := ?_
        depset_size := ?_
        clauses_nonempty := hcorr.toSound.clauses_nonempty
        trail_nonempty := hcorr.toSound.trail_nonempty
        trail_lits_valid := ?_
        assigned_iff_in_trail := ?_ }
    · simp [st', f', addForallFormula, hcorr.toSound.isAssigned_size]
    · simp [st', f', addForallFormula, hcorr.toSound.value_size]
    · simp [st', f', addForallFormula, hcorr.toSound.indepKnown_size]
    · simp [st', f', addForallFormula, hcorr.toSound.indepOf_size]
    · simp [st', f', addForallFormula, hcorr.toSound.externalName_size]
    · simp [st', f', addForallFormula, hcorr.toSound.isExistential_size]
    · simp [st', f', addForallFormula, hcorr.toSound.depset_size]
    · intro i hi l hl
      rcases hcorr.trail_lits_valid i hi l hl with ⟨hpos, hle⟩
      exact ⟨hpos, Nat.le_trans hle hgrow⟩
    · intro v hpos hle
      dsimp [st']
      by_cases hnew : v = st.formula.maxVar + 1
      · constructor
        · intro hassign
          have : (st.isAssigned.push false).getD (v - 1) false = false := by
            subst v
            have hidx : (st.formula.maxVar + 1) - 1 = st.isAssigned.size := by
              simpa [hcorr.toSound.isAssigned_size]
            rw [hidx]
            simpa using (arrayGetD_push_eq st.isAssigned false false)
          rw [this] at hassign
          cases hassign
        · intro htrail
          rcases htrail with ⟨i, hi, l, hl, hlvar⟩
          rcases hcorr.trail_lits_valid i hi l hl with ⟨_, hle_old⟩
          subst v
          rw [hlvar] at hle_old
          exact False.elim (Nat.not_succ_le_self _ hle_old)
      · have hv_old : v ≤ st.formula.maxVar := by
          exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hle (by simpa [eq_comm] using hnew))
        have hlt : v - 1 < st.isAssigned.size := by
          have hlt' : v - 1 < st.formula.maxVar := by
            have : Nat.succ (v - 1) ≤ st.formula.maxVar := by
              have hv_eq : v - 1 + 1 = v := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
              simpa [Nat.succ_eq_add_one, hv_eq] using hv_old
            exact Nat.lt_of_succ_le this
          simpa [hcorr.toSound.isAssigned_size] using hlt'
        constructor
        · intro hassign
          have hassign_old : st.isAssigned.getD (v - 1) false = true := by
            simpa [arrayGetD_push_lt st.isAssigned false false hlt] using hassign
          exact (hcorr.assigned_iff_in_trail v hpos hv_old).mp hassign_old
        · intro htrail
          have hassign_old : st.isAssigned.getD (v - 1) false = true :=
            (hcorr.assigned_iff_in_trail v hpos hv_old).mpr htrail
          simpa [arrayGetD_push_lt st.isAssigned false false hlt] using hassign_old
  · intro v hpos hassign sk σ hmat
    dsimp [st', f'] at hassign hmat ⊢
    have hlt_new : v - 1 < (st.isAssigned.push false).size :=
      arrayGetD_true_imp_lt (a := st.isAssigned.push false) hassign
    by_cases hlt : v - 1 < st.isAssigned.size
    · have hv_le : v ≤ st.formula.maxVar := by
        have hlt' : v - 1 < st.formula.maxVar := by
          simpa [hcorr.toSound.isAssigned_size] using hlt
        have : Nat.succ (v - 1) ≤ st.formula.maxVar := Nat.succ_le_of_lt hlt'
        have hv_eq : v - 1 + 1 = v := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
        simpa [Nat.succ_eq_add_one, hv_eq] using this
      have hassign_old : st.isAssigned.getD (v - 1) false = true := by
        simpa [arrayGetD_push_lt st.isAssigned false false hlt] using hassign
      have hmat_old : st.clauses.matrixValue st.formula σ sk = true := by
        rw [matrixValue_addForallFormula_old st.formula st.clauses ext0 σ sk
          hcorr.toSound.isExistential_size hcorr.toSound.depset_size hcorr.clauses_wf] at hmat
        exact hmat
      have hval_lt : v - 1 < st.value.size := by
        simpa [hcorr.toSound.value_size, hcorr.toSound.isAssigned_size] using hlt
      rw [varValue_addForallFormula_old st.formula ext0 σ sk
          hcorr.toSound.isExistential_size hcorr.toSound.depset_size hv_le]
      rw [arrayGetD_push_lt st.value false false hval_lt]
      exact hcorr.preserves_models v hpos hassign_old sk σ hmat_old
    · have htop : v - 1 = st.isAssigned.size := by
        have hlt_push : v - 1 < st.isAssigned.size + 1 := by
          simpa [Array.size_push] using hlt_new
        exact Nat.eq_of_lt_succ_of_not_lt hlt_push hlt
      have : (st.isAssigned.push false).getD (v - 1) false = false := by
        rw [htop]
        simpa using (arrayGetD_push_eq st.isAssigned false false)
      rw [this] at hassign
      cases hassign
  · intro htrue
    exact DQBFTrue_addForallFormula st.formula st.clauses ext0
      hcorr.toSound.isExistential_size hcorr.toSound.depset_size hcorr.clauses_wf
      (hcorr.formula_sound htrue)
  · intro ext v hlookup
    dsimp [st', f'] at hlookup ⊢
    by_cases hext : ext = ext0
    · subst ext
      rw [lookupInternal_addForallFormula_self st.formula ext0 hfresh] at hlookup
      cases hlookup
      simp [addForallFormula]
    · have hlookup_old : st.formula.lookupInternal ext = some v := by
        simpa [lookupInternal_addForallFormula_ne st.formula ext0 ext hext] using hlookup
      rcases hcorr.lookupInternal_sound ext v hlookup_old with ⟨hposv, hlev⟩
      exact ⟨hposv, Nat.le_trans hlev hgrow⟩

/-- Build a `Correct` boundary state by resetting assignments/queue on top of a
    structurally sound state whose formula/clauses are already known to be a sound
    extension of the original input. -/
theorem CheckState.Correct.ofResetState
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hsound : CheckState.Sound st)
    (hclauses_wf : ClausesWellFormed st.formula st.clauses)
    (hformula_extends : dqbf.maxVar ≤ st.formula.maxVar)
    (hformula_sound : DQBFTrue dqbf cs → DQBFTrue st.formula st.clauses)
    (hlookupInternal_sound : ∀ ext v, st.formula.lookupInternal ext = some v →
      0 < v ∧ v ≤ st.formula.maxVar) :
    CheckState.Correct dqbf cs
      { st with
        isAssigned := Array.replicate st.formula.maxVar false
        value := Array.replicate st.formula.maxVar false
        trail := #[#[]]
        propQueue := #[] } := by
  let st' : CheckState :=
    { st with
      isAssigned := Array.replicate st.formula.maxVar false
      value := Array.replicate st.formula.maxVar false
      trail := #[#[]]
      propQueue := #[] }
  change CheckState.Correct dqbf cs st'
  refine
    { toSound := ?_
      propQueue_empty := rfl
      trail_single_level := rfl
      clauses_wf := hclauses_wf
      formula_extends := hformula_extends
      preserves_models := ?_
      formula_sound := hformula_sound
      lookupInternal_sound := hlookupInternal_sound }
  · refine
      { isAssigned_size := by simp [st', hsound.isAssigned_size]
        value_size := by simp [st', hsound.value_size]
        indepKnown_size := hsound.indepKnown_size
        indepOf_size := hsound.indepOf_size
        externalName_size := hsound.externalName_size
        isExistential_size := hsound.isExistential_size
        depset_size := hsound.depset_size
        clauses_nonempty := hsound.clauses_nonempty
        trail_nonempty := by simp [st']
        trail_lits_valid := ?_
        assigned_iff_in_trail := ?_ }
    · intro i hi l hl
      simp [st'] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp [st'] at hl
    · intro v hpos hle
      have hpred : v - 1 < v := by
        simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hpos)
      have hlt : v - 1 < st.formula.maxVar := Nat.lt_of_lt_of_le hpred hle
      constructor
      · intro hassign
        simp [st', hlt] at hassign
      · intro htrail
        rcases htrail with ⟨i, hi, l, hl, _⟩
        simp [st'] at hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp [st'] at hl
  · intro v hpos hassign sk σ hmat
    by_cases hlt : v - 1 < st.formula.maxVar
    · simp [st', hlt] at hassign
    · simp [st', hlt] at hassign

/-- Updating only the independence caches preserves `Correct` as long as the cache
    arrays keep the expected `maxVar` length.  None of the semantic fields in `Correct`
    depends on the cache contents themselves. -/
theorem CheckState.Correct.withIndepCaches
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hcorr : CheckState.Correct dqbf cs st)
    (indepKnown : Array Bool) (indepOf : Array (Array Var))
    (hknown : indepKnown.size = st.formula.maxVar)
    (hof : indepOf.size = st.formula.maxVar) :
    CheckState.Correct dqbf cs
      { st with indepKnown := indepKnown, indepOf := indepOf } := by
  refine
    { toSound := ?_
      propQueue_empty := hcorr.propQueue_empty
      trail_single_level := hcorr.trail_single_level
      clauses_wf := hcorr.clauses_wf
      formula_extends := hcorr.formula_extends
      preserves_models := hcorr.preserves_models
      formula_sound := hcorr.formula_sound
      lookupInternal_sound := hcorr.lookupInternal_sound }
  exact
    { isAssigned_size := hcorr.toSound.isAssigned_size
      value_size := hcorr.toSound.value_size
      indepKnown_size := hknown
      indepOf_size := hof
      externalName_size := hcorr.toSound.externalName_size
      isExistential_size := hcorr.toSound.isExistential_size
      depset_size := hcorr.toSound.depset_size
      clauses_nonempty := hcorr.toSound.clauses_nonempty
      trail_nonempty := hcorr.toSound.trail_nonempty
      trail_lits_valid := hcorr.trail_lits_valid
      assigned_iff_in_trail := hcorr.assigned_iff_in_trail }

/-- Clearing the active propagation state preserves `Correct`.
    This is the intended action-boundary reset after weakening or prefix edits:
    formula, clause store, and caches are preserved; assignments/queue are dropped. -/
theorem CheckState.Correct.withResetPropagationState
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    (hcorr : CheckState.Correct dqbf cs st) :
    CheckState.Correct dqbf cs
      { st with
        isAssigned := Array.replicate st.formula.maxVar false
        value := Array.replicate st.formula.maxVar false
        trail := #[#[]]
        propQueue := #[] } := by
  let st' : CheckState :=
    { st with
      isAssigned := Array.replicate st.formula.maxVar false
      value := Array.replicate st.formula.maxVar false
      trail := #[#[]]
      propQueue := #[] }
  change CheckState.Correct dqbf cs st'
  refine
    { toSound := ?_
      propQueue_empty := rfl
      trail_single_level := rfl
      clauses_wf := hcorr.clauses_wf
      formula_extends := hcorr.formula_extends
      preserves_models := ?_
      formula_sound := hcorr.formula_sound
      lookupInternal_sound := hcorr.lookupInternal_sound }
  · refine
      { isAssigned_size := by simp [st']
        value_size := by simp [st']
        indepKnown_size := hcorr.toSound.indepKnown_size
        indepOf_size := hcorr.toSound.indepOf_size
        externalName_size := hcorr.toSound.externalName_size
        isExistential_size := hcorr.toSound.isExistential_size
        depset_size := hcorr.toSound.depset_size
        clauses_nonempty := hcorr.toSound.clauses_nonempty
        trail_nonempty := by simp [st']
        trail_lits_valid := ?_
        assigned_iff_in_trail := ?_ }
    · intro i hi l hl
      simp [st'] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp [st'] at hl
    · intro v hpos hle
      have hle' : v ≤ st.formula.maxVar := by simpa [st'] using hle
      have hpred : v - 1 < v := by
        simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hpos)
      have hlt : v - 1 < st.formula.maxVar := Nat.lt_of_lt_of_le hpred hle'
      constructor
      · intro hassign
        simp [st', hlt] at hassign
      · intro htrail
        rcases htrail with ⟨i, hi, l, hl, _⟩
        simp [st'] at hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp [st'] at hl
  · intro v hpos hassign sk σ hmat
    by_cases hlt : v - 1 < st.formula.maxVar
    · simp [st', hlt] at hassign
    · simp [st', hlt] at hassign

theorem PrefixState.withIndepCaches
    {st : CheckState} (hpref : PrefixState st)
    (indepKnown : Array Bool) (indepOf : Array (Array Var))
    (hknown : indepKnown.size = st.formula.maxVar)
    (hof : indepOf.size = st.formula.maxVar) :
    PrefixState { st with indepKnown := indepKnown, indepOf := indepOf } := by
  rcases hpref with ⟨hcorr, hclauses, hallFalse⟩
  refine ⟨CheckState.Correct.withIndepCaches hcorr indepKnown indepOf hknown hof, ?_, ?_⟩
  · simpa using hclauses
  · intro v hpos hle
    simpa using hallFalse v hpos hle

theorem PrefixState.withAddVarForall
    {st : CheckState} (hpref : PrefixState st)
    (ext : Nat) (hfresh : st.formula.externalVarExists ext = false) :
    PrefixState
      { st with
        formula := addForallFormula st.formula ext
        isAssigned := st.isAssigned.push false
        value := st.value.push false
        indepKnown := st.indepKnown.push false
        indepOf := st.indepOf.push #[] } := by
  let st' : CheckState :=
    { st with
      formula := addForallFormula st.formula ext
      isAssigned := st.isAssigned.push false
      value := st.value.push false
      indepKnown := st.indepKnown.push false
      indepOf := st.indepOf.push #[] }
  rcases hpref with ⟨hcorr, hclauses, hallFalse⟩
  refine ⟨CheckState.Correct.withAddVarForall hcorr ext hfresh, ?_, ?_⟩
  · simpa [st'] using hclauses
  · intro v hpos hle
    by_cases hnew : v = st.formula.maxVar + 1
    · subst hnew
      have hidx : (st.formula.maxVar + 1) - 1 = st.isAssigned.size := by
        simpa [hcorr.toSound.isAssigned_size]
      rw [show st'.isAssigned = st.isAssigned.push false by rfl, hidx]
      simpa using (arrayGetD_push_eq st.isAssigned false false)
    · have hle_old : v ≤ st.formula.maxVar := by
        exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hle (by simpa [eq_comm] using hnew))
      have hlt : v - 1 < st.isAssigned.size := by
        have hlt' : v - 1 < st.formula.maxVar := by
          have : Nat.succ (v - 1) ≤ st.formula.maxVar := by
            have hv_eq : v - 1 + 1 = v := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
            simpa [Nat.succ_eq_add_one, hv_eq] using hle_old
          exact Nat.lt_of_succ_le this
        simpa [hcorr.toSound.isAssigned_size] using hlt'
      rw [show st'.isAssigned = st.isAssigned.push false by rfl]
      simpa [arrayGetD_push_lt st.isAssigned false false hlt] using
        hallFalse v hpos hle_old

theorem PrefixState.withAddVarExists
    {st : CheckState} (hpref : PrefixState st)
    (ext : Nat) (deps : Array Var) (hfresh : st.formula.externalVarExists ext = false) :
    PrefixState
      { st with
        formula := addExistsFormula st.formula ext deps
        isAssigned := st.isAssigned.push false
        value := st.value.push false
        indepKnown := st.indepKnown.push false
        indepOf := st.indepOf.push #[] } := by
  let st' : CheckState :=
    { st with
      formula := addExistsFormula st.formula ext deps
      isAssigned := st.isAssigned.push false
      value := st.value.push false
      indepKnown := st.indepKnown.push false
      indepOf := st.indepOf.push #[] }
  rcases hpref with ⟨hcorr, hclauses, hallFalse⟩
  refine ⟨CheckState.Correct.withAddVarExists hcorr ext deps hfresh, ?_, ?_⟩
  · simpa [st'] using hclauses
  · intro v hpos hle
    by_cases hnew : v = st.formula.maxVar + 1
    · subst hnew
      have hidx : (st.formula.maxVar + 1) - 1 = st.isAssigned.size := by
        simpa [hcorr.toSound.isAssigned_size]
      rw [show st'.isAssigned = st.isAssigned.push false by rfl, hidx]
      simpa using (arrayGetD_push_eq st.isAssigned false false)
    · have hle_old : v ≤ st.formula.maxVar := by
        exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hle (by simpa [eq_comm] using hnew))
      have hlt : v - 1 < st.isAssigned.size := by
        have hlt' : v - 1 < st.formula.maxVar := by
          have : Nat.succ (v - 1) ≤ st.formula.maxVar := by
            have hv_eq : v - 1 + 1 = v := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
            simpa [Nat.succ_eq_add_one, hv_eq] using hle_old
          exact Nat.lt_of_succ_le this
        simpa [hcorr.toSound.isAssigned_size] using hlt'
      rw [show st'.isAssigned = st.isAssigned.push false by rfl]
      simpa [arrayGetD_push_lt st.isAssigned false false hlt] using
        hallFalse v hpos hle_old

theorem resetPropagationState_run (s : CheckState) :
    resetPropagationState s =
      .ok () { s with
        isAssigned := Array.replicate s.formula.maxVar false
        value := Array.replicate s.formula.maxVar false
        trail := #[#[]]
        propQueue := #[] } := by
  rfl

theorem resetPropagationState_sameFC_spec (s₀ : CheckState) :
    ⦃fun s => ⌜SameFC s₀ s⌝⦄
    (resetPropagationState : CheckM Unit)
    ⦃⇓ _ s' => ⌜SameFC s₀ s'⌝⦄ := by
  intro s hsame
  simp only [WP.wp, PredTrans.apply, EStateM.run]
  rw [resetPropagationState_run]
  simpa [SameFC] using hsame

@[spec]
theorem resetPropagationState_correct_spec (dqbf : DQBF) (cs : ClauseStore) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (resetPropagationState : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
  intro s hcorr
  simp only [WP.wp, PredTrans.apply, EStateM.run]
  rw [resetPropagationState_run]
  exact CheckState.Correct.withResetPropagationState hcorr

theorem resetPropagationState_correct_sameFC_spec
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ SameFC s₀ s⌝⦄
    (resetPropagationState : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s' ∧ SameFC s₀ s'⌝⦄ := by
  exact Triple.entails_wp_of_post
    (h := Triple.and (resetPropagationState : CheckM Unit)
      (resetPropagationState_correct_spec dqbf cs)
      (resetPropagationState_sameFC_spec s₀))
    (by simp [PostCond.entails, SPred.entails, ExceptConds.entails])

@[spec]
theorem makeIndepUnknown_correct_spec (dqbf : DQBF) (cs : ClauseStore)
    (u : Var) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (makeIndepUnknown u : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
  intro s hcorr
  simp only [WP.wp, PredTrans.apply, EStateM.run, makeIndepUnknown]
  by_cases hu : u = 0
  · simp [hu]
    exact hcorr
  · simp [hu]
    exact CheckState.Correct.withIndepCaches hcorr
      (s.indepKnown.setIfInBounds (u - 1) false)
      (s.indepOf.setIfInBounds (u - 1) #[])
      (by simp [Array.size_setIfInBounds, hcorr.toSound.indepKnown_size])
      (by simp [Array.size_setIfInBounds, hcorr.toSound.indepOf_size])

@[spec]
theorem makeIndepUnknown_prefix_spec (u : Var) :
    ⦃fun s => ⌜PrefixState s⌝⦄
    (makeIndepUnknown u : CheckM Unit)
    ⦃⇓ _ s' => ⌜PrefixState s'⌝⦄ := by
  intro s hpref
  simp only [WP.wp, PredTrans.apply, EStateM.run, makeIndepUnknown]
  by_cases hu : u = 0
  · simp [hu]
    exact hpref
  · simp [hu]
    rcases hpref with ⟨hcorr, hclauses, hallFalse⟩
    exact PrefixState.withIndepCaches
      (st := s)
      (⟨hcorr, hclauses, hallFalse⟩)
      (s.indepKnown.setIfInBounds (u - 1) false)
      (s.indepOf.setIfInBounds (u - 1) #[])
      (by simp [Array.size_setIfInBounds, hcorr.toSound.indepKnown_size])
      (by simp [Array.size_setIfInBounds, hcorr.toSound.indepOf_size])

theorem makeIndepUnknown_correct_sameFC_spec
    (dqbf : DQBF) (cs : ClauseStore) (u : Var) (s₀ : CheckState) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ SameFC s₀ s⌝⦄
    (makeIndepUnknown u : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s' ∧ SameFC s₀ s'⌝⦄ := by
  exact Triple.entails_wp_of_post
    (h := Triple.and (makeIndepUnknown u : CheckM Unit)
      (makeIndepUnknown_correct_spec dqbf cs u)
      (makeIndepUnknown_sameFC_spec u s₀))
    (by simp [PostCond.entails, SPred.entails, ExceptConds.entails])

@[spec]
theorem makeIndepUnknown_correct_lookup_spec
    (dqbf : DQBF) (cs : ClauseStore) (u : Var) (ext : Nat) (v : Var) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ s.formula.lookupInternal ext = some v⌝⦄
    (makeIndepUnknown u : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr, hlookup⟩
  have hspec := makeIndepUnknown_correct_sameFC_spec dqbf cs u s s ⟨hcorr, ⟨rfl, rfl⟩⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec ⊢
  cases hrun : makeIndepUnknown u s with
  | error e s' =>
    rw [hrun] at hspec
    exact hspec.elim
  | ok _ s' =>
    rw [hrun] at hspec
    rcases hspec with ⟨hcorr', hsame⟩
    rcases hsame with ⟨hformula, _⟩
    exact ⟨hcorr', by simpa [hformula] using hlookup⟩

theorem makeIndepUnknown_prefix_lookup_spec
    (u : Var) (ext : Nat) (v : Var) :
    ⦃fun s => ⌜PrefixState s ∧ s.formula.lookupInternal ext = some v⌝⦄
    (makeIndepUnknown u : CheckM Unit)
    ⦃⇓ _ s' => ⌜PrefixState s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ := by
  intro s hs
  rcases hs with ⟨hpref, hlookup⟩
  have hprefix := makeIndepUnknown_prefix_spec u s hpref
  have hsame := makeIndepUnknown_sameFC_spec u s s ⟨rfl, rfl⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hprefix hsame ⊢
  cases hrun : makeIndepUnknown u s with
  | error e s' =>
      rw [hrun] at hprefix
      exact hprefix.elim
  | ok _ s' =>
      rw [hrun] at hprefix hsame
      rcases hsame with ⟨hformula, _⟩
      exact ⟨hprefix, by simpa [hformula] using hlookup⟩

theorem setDepset_prefix_spec (iv : Var) (deps : Array Var) :
    ⦃fun s => ⌜PrefixState s⌝⦄
    (modify fun st =>
      { st with
        formula := { st.formula with depset := st.formula.depset.setIfInBounds iv deps } } :
      CheckM Unit)
    ⦃⇓ _ s' => ⌜PrefixState s'⌝⦄ := by
  intro s hpref
  simp only [WP.wp, PredTrans.apply, EStateM.run, modify]
  exact PrefixState.withSetDepset hpref iv deps

theorem makeIndepUnknown_prefix_loop_spec
    (deps : Array Var) :
    ⦃fun s => ⌜PrefixState s⌝⦄
    (forIn deps PUnit.unit (fun u _ => do
      makeIndepUnknown u
      pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
    ⦃⇓ _ s' => ⌜PrefixState s'⌝⦄ := by
  simpa [Array.forIn_toList] using
    (show
      ⦃fun s => ⌜PrefixState s⌝⦄
      (forIn deps.toList PUnit.unit (fun u _ => do
        makeIndepUnknown u
        pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
      ⦃⇓ _ s' => ⌜PrefixState s'⌝⦄ from by
      refine (Spec.forIn_list_const_inv
        (xs := deps.toList)
        (init := PUnit.unit)
        (f := fun u _ => do
          makeIndepUnknown u
          pure (ForInStep.yield PUnit.unit))
        (inv := (⇓ _ s' => ⌜PrefixState s'⌝))
        ?_)
      intro u b
      cases b
      mintro hpref
      mspec (makeIndepUnknown_prefix_spec u)
      mleave)

theorem getFormula_run (s : CheckState) :
    (((fun x => x.formula) <$> (get : CheckM CheckState)) s) = .ok s.formula s := by
  rfl

theorem ensureWithinMaxVar_ok_run
    (declaredMaxVar extVar : Nat) (h : extVar ≤ declaredMaxVar) (s : CheckState) :
    ensureWithinMaxVar declaredMaxVar extVar s = .ok () s := by
  have h' : ¬ declaredMaxVar < extVar := Nat.not_lt_of_ge h
  simp [ensureWithinMaxVar, h', Pure.pure, EStateM.pure]

theorem ensureWithinMaxVar_error_run
    (declaredMaxVar extVar : Nat) (h : extVar > declaredMaxVar) (s : CheckState) :
    ensureWithinMaxVar declaredMaxVar extVar s =
      .error s!"Variable {extVar} exceeds maximum declared variable" s := by
  simp [ensureWithinMaxVar, h, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem ensureWithinMaxVar_prefix_spec
    (declaredMaxVar extVar : Nat) :
    ⦃fun s => ⌜PrefixState s⌝⦄
    (ensureWithinMaxVar declaredMaxVar extVar : CheckM Unit)
    ⦃⇓? _ s' => ⌜PrefixState s'⌝⦄ := by
  intro s hpref
  simp only [WP.wp, PredTrans.apply, EStateM.run, ensureWithinMaxVar]
  by_cases hgt : extVar > declaredMaxVar
  · simp [hgt, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  · simp [hgt]
    exact hpref

theorem addVarForall_prefix_spec
    (ext : Nat) :
    ⦃fun s => ⌜PrefixState s ∧ s.formula.externalVarExists ext = false⌝⦄
    (addVarForall ext : CheckM Var)
    ⦃⇓ _ s' => ⌜PrefixState s'⌝⦄ := by
  intro s hs
  rcases hs with ⟨hpref, hfresh⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run, addVarForall]
  exact PrefixState.withAddVarForall hpref ext hfresh

theorem addVarExists_prefix_spec
    (ext : Nat) (deps : Array Var) :
    ⦃fun s => ⌜PrefixState s ∧ s.formula.externalVarExists ext = false⌝⦄
    (addVarExists ext deps : CheckM Var)
    ⦃⇓ _ s' => ⌜PrefixState s'⌝⦄ := by
  have hprefix :
      ⦃fun s => ⌜PrefixState s ∧ s.formula.externalVarExists ext = false⌝⦄
      ((do
        let st ← get
        let v := st.formula.maxVar + 1
        let f := { st.formula with
          maxVar        := v
          internalName  := st.formula.internalName.push (ext, v)
          externalName  := st.formula.externalName.push ext
          isExistential := st.formula.isExistential.push true
          exivars       := st.formula.exivars.push v
          depset        := st.formula.depset.push deps }
        set { st with
          formula    := f
          isAssigned := st.isAssigned.push false
          value      := st.value.push false
          indepKnown := st.indepKnown.push false
          indepOf    := st.indepOf.push #[] }
        pure v) : CheckM Var)
      ⦃⇓ _ s' => ⌜PrefixState s'⌝⦄ := by
    intro s hs
    rcases hs with ⟨hpref, hfresh⟩
    simp only [WP.wp, PredTrans.apply, EStateM.run]
    exact PrefixState.withAddVarExists hpref ext deps hfresh
  have hbody :
      ⦃fun s => ⌜PrefixState s ∧ s.formula.externalVarExists ext = false⌝⦄
      ((do
          let v ← ((do
            let st ← get
            let v := st.formula.maxVar + 1
            let f := { st.formula with
              maxVar        := v
              internalName  := st.formula.internalName.push (ext, v)
              externalName  := st.formula.externalName.push ext
              isExistential := st.formula.isExistential.push true
              exivars       := st.formula.exivars.push v
              depset        := st.formula.depset.push deps }
            set { st with
              formula    := f
              isAssigned := st.isAssigned.push false
              value      := st.value.push false
              indepKnown := st.indepKnown.push false
              indepOf    := st.indepOf.push #[] }
            pure v) : CheckM Var)
          for u in deps do
            makeIndepUnknown u
          pure v) : CheckM Var)
      ⦃⇓ _ s' => ⌜PrefixState s'⌝⦄ := by
    mintro hs
    mspec hprefix
    mspec (makeIndepUnknown_prefix_loop_spec deps)
    mleave
  simpa [addVarExists] using hbody

@[spec]
theorem makeIndepUnknown_correct_lookup_wf_spec
    (dqbf : DQBF) (cs : ClauseStore) (u : Var)
    (acc : Array Literal) (ext : Nat) (v : Var) :
    ⦃fun s =>
      ⌜CheckState.Correct dqbf cs s ∧
       ClauseLitsWellFormed s.formula acc ∧
       s.formula.lookupInternal ext = some v⌝⦄
    (makeIndepUnknown u : CheckM Unit)
    ⦃⇓ _ s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       ClauseLitsWellFormed s'.formula acc ∧
       s'.formula.lookupInternal ext = some v⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr, hacc, hlookup⟩
  have hspec := makeIndepUnknown_correct_sameFC_spec dqbf cs u s s ⟨hcorr, ⟨rfl, rfl⟩⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec ⊢
  cases hrun : makeIndepUnknown u s with
  | error e s' =>
    rw [hrun] at hspec
    exact hspec.elim
  | ok _ s' =>
    rw [hrun] at hspec
    rcases hspec with ⟨hcorr', hsame⟩
    rcases hsame with ⟨hformula, _⟩
    exact ⟨hcorr', by simpa [hformula] using hacc, by simpa [hformula] using hlookup⟩

@[spec]
theorem addVarExists_loop_spec
    (dqbf : DQBF) (cs : ClauseStore) (deps : Array Var) (ext : Nat) (v : Var) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ s.formula.lookupInternal ext = some v⌝⦄
    (forIn deps PUnit.unit (fun u _ => do
      makeIndepUnknown u
      pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ := by
  simpa [Array.forIn_toList] using
    (show
      ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ s.formula.lookupInternal ext = some v⌝⦄
      (forIn deps.toList PUnit.unit (fun u _ => do
        makeIndepUnknown u
        pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
      ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ from by
      refine (Spec.forIn_list_const_inv
        (xs := deps.toList)
        (init := PUnit.unit)
        (f := fun u _ => do
          makeIndepUnknown u
          pure (ForInStep.yield PUnit.unit))
        (inv := (⇓ _ s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝))
        ?_)
      intro u b
      cases b
      mintro hpre
      mspec (makeIndepUnknown_correct_lookup_spec dqbf cs u ext v)
      mleave)

@[spec]
theorem addVarExists_loop_wf_spec
    (dqbf : DQBF) (cs : ClauseStore) (deps : Array Var)
    (acc : Array Literal) (ext : Nat) (v : Var) :
    ⦃fun s =>
      ⌜CheckState.Correct dqbf cs s ∧
       ClauseLitsWellFormed s.formula acc ∧
       s.formula.lookupInternal ext = some v⌝⦄
    (forIn deps PUnit.unit (fun u _ => do
      makeIndepUnknown u
      pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
    ⦃⇓ _ s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       ClauseLitsWellFormed s'.formula acc ∧
       s'.formula.lookupInternal ext = some v⌝⦄ := by
  simpa [Array.forIn_toList] using
    (show
      ⦃fun s =>
        ⌜CheckState.Correct dqbf cs s ∧
         ClauseLitsWellFormed s.formula acc ∧
         s.formula.lookupInternal ext = some v⌝⦄
      (forIn deps.toList PUnit.unit (fun u _ => do
        makeIndepUnknown u
        pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
      ⦃⇓ _ s' =>
        ⌜CheckState.Correct dqbf cs s' ∧
         ClauseLitsWellFormed s'.formula acc ∧
         s'.formula.lookupInternal ext = some v⌝⦄ from by
      refine (Spec.forIn_list_const_inv
        (xs := deps.toList)
        (init := PUnit.unit)
        (f := fun u _ => do
          makeIndepUnknown u
          pure (ForInStep.yield PUnit.unit))
        (inv := (⇓ _ s' =>
          ⌜CheckState.Correct dqbf cs s' ∧
           ClauseLitsWellFormed s'.formula acc ∧
           s'.formula.lookupInternal ext = some v⌝))
        ?_)
      intro u b
      cases b
      mintro hpre
      mspec (makeIndepUnknown_correct_lookup_wf_spec dqbf cs u acc ext v)
      mleave)

@[spec]
theorem addVarForall_correct_spec (dqbf : DQBF) (cs : ClauseStore)
    (ext : Nat) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ s.formula.externalVarExists ext = false⌝⦄
    (addVarForall ext : CheckM Var)
    ⦃⇓ v s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ := by
  have hprefix :
      ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ s.formula.externalVarExists ext = false⌝⦄
      ((do
        let st ← get
        let v := st.formula.maxVar + 1
        let f := { st.formula with
          maxVar        := v
          internalName  := st.formula.internalName.push (ext, v)
          externalName  := st.formula.externalName.push ext
          isExistential := st.formula.isExistential.push false
          univars       := st.formula.univars.push v
          depset        := st.formula.depset.push #[] }
        set { st with
          formula    := f
          isAssigned := st.isAssigned.push false
          value      := st.value.push false
          indepKnown := st.indepKnown.push false
          indepOf    := st.indepOf.push #[] }
        pure v) : CheckM Var)
      ⦃⇓ v s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ := by
    mvcgen
    rename_i s hs v f
    rcases hs with ⟨hcorr, hfresh⟩
    refine ⟨CheckState.Correct.withAddVarForall hcorr ext hfresh, ?_⟩
    simpa [f, v] using lookupInternal_addForallFormula_self s.formula ext hfresh
  simpa [addVarForall] using hprefix

@[spec]
theorem addVarExists_correct_spec (dqbf : DQBF) (cs : ClauseStore)
    (ext : Nat) (deps : Array Var) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ s.formula.externalVarExists ext = false⌝⦄
    (addVarExists ext deps : CheckM Var)
    ⦃⇓ v s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ := by
  have hprefix :
      ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ s.formula.externalVarExists ext = false⌝⦄
      ((do
        let st ← get
        let v := st.formula.maxVar + 1
        let f := { st.formula with
          maxVar        := v
          internalName  := st.formula.internalName.push (ext, v)
          externalName  := st.formula.externalName.push ext
          isExistential := st.formula.isExistential.push true
          exivars       := st.formula.exivars.push v
          depset        := st.formula.depset.push deps }
        set { st with
          formula    := f
          isAssigned := st.isAssigned.push false
          value      := st.value.push false
          indepKnown := st.indepKnown.push false
          indepOf    := st.indepOf.push #[] }
        pure v) : CheckM Var)
      ⦃⇓ v s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ := by
    mvcgen
    rename_i s hs v f
    rcases hs with ⟨hcorr, hfresh⟩
    refine ⟨CheckState.Correct.withAddVarExists hcorr ext deps hfresh, ?_⟩
    simpa [f, v] using lookupInternal_addExistsFormula_self s.formula ext deps hfresh
  have hbody :
      ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ s.formula.externalVarExists ext = false⌝⦄
      ((do
          let v ← ((do
            let st ← get
            let v := st.formula.maxVar + 1
            let f := { st.formula with
              maxVar        := v
              internalName  := st.formula.internalName.push (ext, v)
              externalName  := st.formula.externalName.push ext
              isExistential := st.formula.isExistential.push true
              exivars       := st.formula.exivars.push v
              depset        := st.formula.depset.push deps }
            set { st with
              formula    := f
              isAssigned := st.isAssigned.push false
              value      := st.value.push false
              indepKnown := st.indepKnown.push false
              indepOf    := st.indepOf.push #[] }
            pure v) : CheckM Var)
          for u in deps do
            makeIndepUnknown u
          pure v) : CheckM Var)
      ⦃⇓ v s' => ⌜CheckState.Correct dqbf cs s' ∧ s'.formula.lookupInternal ext = some v⌝⦄ := by
    mintro hs
    mspec hprefix
    rename_i v
    mspec (addVarExists_loop_spec dqbf cs deps ext v)
    mleave
  simpa [addVarExists] using hbody

@[spec]
theorem addVarExists_correct_wf_spec (dqbf : DQBF) (cs : ClauseStore)
    (ext : Nat) (deps : Array Var) (acc : Array Literal) :
    ⦃fun s =>
      ⌜CheckState.Correct dqbf cs s ∧
       ClauseLitsWellFormed s.formula acc ∧
       s.formula.externalVarExists ext = false⌝⦄
    (addVarExists ext deps : CheckM Var)
    ⦃⇓ v s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       ClauseLitsWellFormed s'.formula acc ∧
       s'.formula.lookupInternal ext = some v⌝⦄ := by
  have hprefix :
      ⦃fun s =>
        ⌜CheckState.Correct dqbf cs s ∧
         ClauseLitsWellFormed s.formula acc ∧
         s.formula.externalVarExists ext = false⌝⦄
      ((do
        let st ← get
        let v := st.formula.maxVar + 1
        let f := { st.formula with
          maxVar        := v
          internalName  := st.formula.internalName.push (ext, v)
          externalName  := st.formula.externalName.push ext
          isExistential := st.formula.isExistential.push true
          exivars       := st.formula.exivars.push v
          depset        := st.formula.depset.push deps }
        set { st with
          formula    := f
          isAssigned := st.isAssigned.push false
          value      := st.value.push false
          indepKnown := st.indepKnown.push false
          indepOf    := st.indepOf.push #[] }
        pure v) : CheckM Var)
      ⦃⇓ v s' =>
        ⌜CheckState.Correct dqbf cs s' ∧
         ClauseLitsWellFormed s'.formula acc ∧
         s'.formula.lookupInternal ext = some v⌝⦄ := by
    mvcgen
    rename_i s hs v f
    rcases hs with ⟨hcorr, hacc, hfresh⟩
    have hcorr' : CheckState.Correct dqbf cs
        { s with
          formula := f
          isAssigned := s.isAssigned.push false
          value := s.value.push false
          indepKnown := s.indepKnown.push false
          indepOf := s.indepOf.push #[] } :=
      CheckState.Correct.withAddVarExists hcorr ext deps hfresh
    have hgrow : s.formula.maxVar ≤
        ({ s.formula with
          maxVar        := v
          internalName  := s.formula.internalName.push (ext, v)
          externalName  := s.formula.externalName.push ext
          isExistential := s.formula.isExistential.push true
          exivars       := s.formula.exivars.push v
          depset        := s.formula.depset.push deps }).maxVar := by
      simp [v]
    refine ⟨hcorr', ClauseLitsWellFormed.mono hacc hgrow, ?_⟩
    simpa [f, v] using lookupInternal_addExistsFormula_self s.formula ext deps hfresh
  have hbody :
      ⦃fun s =>
        ⌜CheckState.Correct dqbf cs s ∧
         ClauseLitsWellFormed s.formula acc ∧
         s.formula.externalVarExists ext = false⌝⦄
      ((do
          let v ← ((do
            let st ← get
            let v := st.formula.maxVar + 1
            let f := { st.formula with
              maxVar        := v
              internalName  := st.formula.internalName.push (ext, v)
              externalName  := st.formula.externalName.push ext
              isExistential := st.formula.isExistential.push true
              exivars       := st.formula.exivars.push v
              depset        := st.formula.depset.push deps }
            set { st with
              formula    := f
              isAssigned := st.isAssigned.push false
              value      := st.value.push false
              indepKnown := st.indepKnown.push false
              indepOf    := st.indepOf.push #[] }
            pure v) : CheckM Var)
          for u in deps do
            makeIndepUnknown u
          pure v) : CheckM Var)
      ⦃⇓ v s' =>
        ⌜CheckState.Correct dqbf cs s' ∧
         ClauseLitsWellFormed s'.formula acc ∧
         s'.formula.lookupInternal ext = some v⌝⦄ := by
    mintro hs
    mspec hprefix
    rename_i v
    mspec (addVarExists_loop_wf_spec dqbf cs deps acc ext v)
    mleave
  simpa [addVarExists] using hbody

@[spec]
theorem translateExistingLits_spec
    (dqbf : DQBF) (cs : ClauseStore) (extLits : List Int) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (translateExistingLits extLits : CheckM (Array Literal))
    ⦃⇓ lits s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       ClauseLitsWellFormed s'.formula lits⌝⦄ := by
  mvcgen [translateExistingLits] invariants
  · ⇓⟨_, acc⟩ s => ⌜CheckState.Correct dqbf cs s ∧ ClauseLitsWellFormed s.formula acc⌝
    with
  case vc2.pre =>
    rename_i acc s hcorr
    subst acc
    exact ⟨hcorr, by simpa [ClauseLitsWellFormed]⟩
  case vc1.step =>
    rename_i _ _ _ cur _ _ acc s hs
    rcases hs with ⟨hcorr, hacc⟩
    cases hlookup : s.formula.lookupInternal cur.natAbs with
    | none =>
        simpa [WP.wp, PredTrans.apply, EStateM.run, hlookup] using
          (show CheckState.Correct dqbf cs s ∧ ClauseLitsWellFormed s.formula acc from
            ⟨hcorr, hacc⟩)
    | some iv =>
        rcases hcorr.lookupInternal_sound cur.natAbs iv hlookup with ⟨hpos, hle⟩
        have hmk : (mkLit iv (cur > 0)).var = iv := by
          unfold Literal.var mkLit
          by_cases hsign : cur > 0
          · simp [hsign]
            rw [Nat.add_comm (iv * 2) 1]
            rw [Nat.add_mul_div_right 1 iv (by decide)]
            simp
          · simp [hsign]
        simpa [WP.wp, PredTrans.apply, EStateM.run, hlookup] using
          (show CheckState.Correct dqbf cs s ∧
              ClauseLitsWellFormed s.formula (acc.push (mkLit iv (cur > 0))) from
            ⟨hcorr, ClauseLitsWellFormed.push hacc (by simpa [hmk] using (show 0 < iv ∧ iv ≤ s.formula.maxVar from ⟨hpos, hle⟩))⟩)

theorem lookupInternal_some_of_externalVarExists
    (f : DQBF) (ext : Nat) (hex : f.externalVarExists ext = true) :
    ∃ v, f.lookupInternal ext = some v := by
  rw [DQBF.externalVarExists] at hex
  simp only [Array.any_eq_true] at hex
  rcases hex with ⟨i, hi, hpair⟩
  let p := f.internalName[i]
  have hp : p.fst = ext := by
    simpa [p] using hpair
  have hisSome : (f.lookupInternal ext).isSome := by
    rw [DQBF.lookupInternal, Array.findSome?_isSome_iff]
    refine ⟨p, Array.getElem_mem hi, ?_⟩
    simp [p, hp]
  cases hlookup : f.lookupInternal ext with
  | none =>
      simp [hlookup] at hisSome
  | some v =>
      exact ⟨v, rfl⟩

@[spec]
theorem translateRatLitBasicStep_spec
    (dqbf : DQBF) (cs : ClauseStore) (acc : Array Literal) (lit : Int) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ ClauseLitsWellFormed s.formula acc⌝⦄
    (translateRatLitBasicStep acc lit : CheckM (Array Literal))
    ⦃⇓ acc' s' =>
      ⌜CheckState.Correct dqbf cs s' ∧ ClauseLitsWellFormed s'.formula acc'⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr, hacc⟩
  let extVar := lit.natAbs
  by_cases hex : s.formula.externalVarExists extVar = true
  · rcases lookupInternal_some_of_externalVarExists s.formula extVar hex with ⟨iv, hlookup⟩
    rcases hcorr.lookupInternal_sound extVar iv hlookup with ⟨hpos, hle⟩
    have hmk : (mkLit iv (lit > 0)).var = iv := by
      unfold Literal.var mkLit
      by_cases hsign : lit > 0
      · simp [hsign]
        rw [Nat.add_comm (iv * 2) 1]
        rw [Nat.add_mul_div_right 1 iv (by decide)]
        simp
      · simp [hsign]
    simpa [translateRatLitBasicStep, extVar, hex, hlookup] using
      (show CheckState.Correct dqbf cs s ∧
          ClauseLitsWellFormed s.formula (acc.push (mkLit iv (lit > 0))) from
        ⟨hcorr,
          ClauseLitsWellFormed.push hacc
            (by
              simpa [hmk] using
                (show 0 < iv ∧ iv ≤ s.formula.maxVar from ⟨hpos, hle⟩))⟩)
  · have hmissing : s.formula.externalVarExists extVar = false := by
      cases hval : s.formula.externalVarExists extVar <;> simp_all
    have hbody :
        ⦃fun s' =>
          ⌜CheckState.Correct dqbf cs s' ∧
           ClauseLitsWellFormed s'.formula acc ∧
           s'.formula.externalVarExists extVar = false⌝⦄
        ((do
            let _ ← addVarExists extVar s.formula.univars
            let f2 ← (·.formula) <$> get
            match f2.lookupInternal extVar with
            | none => pure acc
            | some iv => pure (acc.push (mkLit iv (lit > 0)))) : CheckM (Array Literal))
        ⦃⇓ acc' s' =>
          ⌜CheckState.Correct dqbf cs s' ∧
           ClauseLitsWellFormed s'.formula acc'⌝⦄ := by
      mintro hs'
      mspec (addVarExists_correct_wf_spec dqbf cs extVar s.formula.univars acc)
      rename_i v
      mleave
      intro s' hcorr' hacc' hlookup
      rcases hcorr'.lookupInternal_sound extVar v hlookup with ⟨hpos, hle⟩
      have hmk : (mkLit v (lit > 0)).var = v := by
        unfold Literal.var mkLit
        by_cases hsign : lit > 0
        · simp [hsign]
          rw [Nat.add_comm (v * 2) 1]
          rw [Nat.add_mul_div_right 1 v (by decide)]
          simp
        · simp [hsign]
      simpa [hlookup] using
        (show CheckState.Correct dqbf cs s' ∧
            ClauseLitsWellFormed s'.formula (acc.push (mkLit v (lit > 0))) from
          ⟨hcorr',
            ClauseLitsWellFormed.push hacc'
              (by
                simpa [hmk] using
                  (show 0 < v ∧ v ≤ s'.formula.maxVar from ⟨hpos, hle⟩))⟩)
    simpa [translateRatLitBasicStep, extVar, hmissing] using
      hbody s ⟨hcorr, hacc, hmissing⟩

@[spec]
theorem translateRatLitsBasic_spec
    (dqbf : DQBF) (cs : ClauseStore) (extLits : List Int) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (translateRatLitsBasic extLits : CheckM (Array Literal))
    ⦃⇓ lits s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       ClauseLitsWellFormed s'.formula lits⌝⦄ := by
  mvcgen [translateRatLitsBasic, translateRatLitBasicStep_spec] invariants
  · ⇓⟨_, acc⟩ s => ⌜CheckState.Correct dqbf cs s ∧ ClauseLitsWellFormed s.formula acc⌝
    with
  case vc5.pre =>
    rename_i acc s hcorr
    subst acc
    exact ⟨hcorr, by simpa [ClauseLitsWellFormed]⟩

@[spec]
theorem invalidateDepCaches_correct_spec (dqbf : DQBF) (cs : ClauseStore)
    (lits : Array Literal) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (invalidateDepCaches lits : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
  intro s hcorr
  have hfor :
      ⦃fun s' => ⌜CheckState.Correct dqbf cs s'⌝⦄
      (forIn lits.toList PUnit.unit (fun l _ => do
        let v := l.var
        if v > 0 && s.formula.isVarExistential v then
          let _ ← forIn (s.formula.depset.getD v #[]).toList PUnit.unit (fun u _ => do
            makeIndepUnknown u
            pure (ForInStep.yield PUnit.unit))
          pure (ForInStep.yield PUnit.unit)
        else
          pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
      ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
    refine (Spec.forIn_list_const_inv
      (xs := lits.toList)
      (init := PUnit.unit)
      (f := fun l _ => do
        let v := l.var
        if v > 0 && s.formula.isVarExistential v then
          let _ ← forIn (s.formula.depset.getD v #[]).toList PUnit.unit (fun u _ => do
            makeIndepUnknown u
            pure (ForInStep.yield PUnit.unit))
          pure (ForInStep.yield PUnit.unit)
        else
          pure (ForInStep.yield PUnit.unit))
      (inv := (⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝))
      ?_)
    intro l b
    cases b
    mvcgen [makeIndepUnknown_correct_spec] invariants
    · ⇓⟨xs, ()⟩ s' => ⌜CheckState.Correct dqbf cs s'⌝
      with all_goals first | assumption | exact ‹CheckState.Correct dqbf cs _›
  simpa [invalidateDepCaches, Array.forIn_toList] using hfor s hcorr

theorem invalidateDepCaches_correct_sameFC_spec
    (dqbf : DQBF) (cs : ClauseStore) (lits : Array Literal) (s₀ : CheckState) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ SameFC s₀ s⌝⦄
    (invalidateDepCaches lits : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s' ∧ SameFC s₀ s'⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr, hsame⟩
  have hcorr' := invalidateDepCaches_correct_spec dqbf cs lits s hcorr
  have hsame' := invalidateDepCaches_sameFC_spec lits s₀ s hsame
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hcorr' hsame' ⊢
  cases hrun : invalidateDepCaches lits s with
  | error e s' =>
    rw [hrun] at hcorr'
    exact hcorr'.elim
  | ok _ s' =>
      rw [hrun] at hcorr' hsame'
      exact ⟨hcorr', hsame'⟩

theorem clauseLitsWellFormed_of_sameFC
    {s₀ s₁ : CheckState} {lits : Array Literal}
    (hsame : SameFC s₀ s₁)
    (hwf : ClauseLitsWellFormed s₀.formula lits) :
    ClauseLitsWellFormed s₁.formula lits := by
  rcases hsame with ⟨hformula, _⟩
  simpa [hformula] using hwf

theorem addClause_semantics_of_sameFC
    {dqbf : DQBF} {cs : ClauseStore}
    {s₀ s₁ : CheckState} {lits : Array Literal}
    (hsame : SameFC s₀ s₁)
    (hsem : DQBFTrue dqbf cs → DQBFTrue s₀.formula (s₀.clauses.addClause lits).1) :
    DQBFTrue dqbf cs → DQBFTrue s₁.formula (s₁.clauses.addClause lits).1 := by
  rcases hsame with ⟨hformula, hclauses⟩
  simpa [hformula, hclauses] using hsem

theorem CheckState.Correct.withAddClause
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {lits : Array Literal}
    (hcorr : CheckState.Correct dqbf cs st)
    (hlits : ClauseLitsWellFormed st.formula lits)
    (hsem : DQBFTrue dqbf cs → DQBFTrue st.formula (st.clauses.addClause lits).1) :
    CheckState.Correct dqbf cs { st with clauses := (st.clauses.addClause lits).1 } := by
  refine
    { toSound := ?_
      propQueue_empty := hcorr.propQueue_empty
      trail_single_level := hcorr.trail_single_level
      clauses_wf := hcorr.clauses_wf.addClause hlits
      formula_extends := hcorr.formula_extends
      preserves_models := ?_
      formula_sound := hsem
      lookupInternal_sound := hcorr.lookupInternal_sound }
  · exact
      { isAssigned_size := hcorr.toSound.isAssigned_size
        value_size := hcorr.toSound.value_size
        indepKnown_size := hcorr.toSound.indepKnown_size
        indepOf_size := hcorr.toSound.indepOf_size
        externalName_size := hcorr.toSound.externalName_size
        isExistential_size := hcorr.toSound.isExistential_size
        depset_size := hcorr.toSound.depset_size
        clauses_nonempty := by simpa [ClauseStore.addClause] using Nat.succ_pos st.clauses.clauses.size
        trail_nonempty := hcorr.toSound.trail_nonempty
        trail_lits_valid := hcorr.trail_lits_valid
        assigned_iff_in_trail := hcorr.assigned_iff_in_trail }
  · intro v hpos hassign sk σ hmat
    exact hcorr.preserves_models v hpos hassign sk σ
      (matrixValue_addClause_mono st.formula st.clauses lits σ sk hmat)

theorem CheckState.Correct.withDeleteClauseReset
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {cref : CRef}
    (hcorr : CheckState.Correct dqbf cs st) :
    CheckState.Correct dqbf cs
      { st with
        clauses := st.clauses.deleteClause cref
        isAssigned := Array.replicate st.formula.maxVar false
        value := Array.replicate st.formula.maxVar false
        trail := #[#[]]
        propQueue := #[] } := by
  let st' : CheckState :=
    { st with
      clauses := st.clauses.deleteClause cref
      isAssigned := Array.replicate st.formula.maxVar false
      value := Array.replicate st.formula.maxVar false
      trail := #[#[]]
      propQueue := #[] }
  change CheckState.Correct dqbf cs st'
  refine
    { toSound := ?_
      propQueue_empty := rfl
      trail_single_level := rfl
      clauses_wf := hcorr.clauses_wf.deleteClause
      formula_extends := hcorr.formula_extends
      preserves_models := ?_
      formula_sound := ?_
      lookupInternal_sound := hcorr.lookupInternal_sound }
  · refine
      { isAssigned_size := by simp [st']
        value_size := by simp [st']
        indepKnown_size := hcorr.toSound.indepKnown_size
        indepOf_size := hcorr.toSound.indepOf_size
        externalName_size := hcorr.toSound.externalName_size
        isExistential_size := hcorr.toSound.isExistential_size
        depset_size := hcorr.toSound.depset_size
        clauses_nonempty := by
          simpa [st', ClauseStore.deleteClause_clauses_size] using hcorr.toSound.clauses_nonempty
        trail_nonempty := by simp [st']
        trail_lits_valid := ?_
        assigned_iff_in_trail := ?_ }
    · intro i hi l hl
      simp [st'] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp [st'] at hl
    · intro v hpos hle
      have hle' : v ≤ st.formula.maxVar := by simpa [st'] using hle
      have hpred : v - 1 < v := by
        simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hpos)
      have hlt : v - 1 < st.formula.maxVar := Nat.lt_of_lt_of_le hpred hle'
      constructor
      · intro hassign
        simp [st', hlt] at hassign
      · intro htrail
        rcases htrail with ⟨i, hi, l, hl, _⟩
        simp [st'] at hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp [st'] at hl
  · intro v hpos hassign sk σ hmat
    by_cases hlt : v - 1 < st.formula.maxVar
    · simp [st', hlt] at hassign
    · simp [st', hlt] at hassign
  · intro htrue
    exact DQBFTrue.delete_clause st.formula st.clauses cref (hcorr.formula_sound htrue)

theorem CheckState.Correct.withAddDependencyReset
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {of_ on_ : Var}
    (hcorr : CheckState.Correct dqbf cs st)
    (hof : 0 < of_) (hof_le : of_ ≤ st.formula.maxVar) :
    CheckState.Correct dqbf cs
      { st with
        formula := st.formula.addDependencyFormula of_ on_
        isAssigned := Array.replicate st.formula.maxVar false
        value := Array.replicate st.formula.maxVar false
        trail := #[#[]]
        propQueue := #[]
        indepKnown := st.indepKnown.setIfInBounds (on_ - 1) false
        indepOf := st.indepOf.setIfInBounds (on_ - 1) #[] } := by
  let st₁ : CheckState :=
    { st with
      formula := st.formula.addDependencyFormula of_ on_
      indepKnown := st.indepKnown.setIfInBounds (on_ - 1) false
      indepOf := st.indepOf.setIfInBounds (on_ - 1) #[] }
  have hsound₁ : CheckState.Sound st₁ := by
    refine
      { isAssigned_size := by
          simpa [st₁, DQBF.addDependencyFormula] using hcorr.toSound.isAssigned_size
        value_size := by
          simpa [st₁, DQBF.addDependencyFormula] using hcorr.toSound.value_size
        indepKnown_size := by
          simp [st₁, DQBF.addDependencyFormula, Array.size_setIfInBounds,
            hcorr.toSound.indepKnown_size]
        indepOf_size := by
          simp [st₁, DQBF.addDependencyFormula, Array.size_setIfInBounds,
            hcorr.toSound.indepOf_size]
        externalName_size := by
          simpa [st₁, DQBF.addDependencyFormula] using hcorr.toSound.externalName_size
        isExistential_size := by
          simpa [st₁, DQBF.addDependencyFormula] using hcorr.toSound.isExistential_size
        depset_size := by
          simp [st₁, DQBF.addDependencyFormula, Array.size_setIfInBounds,
            hcorr.toSound.depset_size]
        clauses_nonempty := hcorr.toSound.clauses_nonempty
        trail_nonempty := hcorr.toSound.trail_nonempty
        trail_lits_valid := ?_
        assigned_iff_in_trail := ?_ }
    · intro i hi l hl
      rcases hcorr.trail_lits_valid i hi l hl with ⟨hpos, hle⟩
      exact ⟨hpos, by simpa [st₁, DQBF.addDependencyFormula] using hle⟩
    · intro v hpos hle
      have hle_old : v ≤ st.formula.maxVar := by
        simpa [st₁, DQBF.addDependencyFormula] using hle
      exact hcorr.assigned_iff_in_trail v hpos hle_old
  have hclauses₁ : ClausesWellFormed st₁.formula st₁.clauses := by
    simpa [st₁, DQBF.addDependencyFormula] using hcorr.clauses_wf
  have hformula_sound₁ : DQBFTrue dqbf cs → DQBFTrue st₁.formula st₁.clauses := by
    intro htrue
    exact DQBFTrue_addDependencyFormula st.formula st.clauses of_ on_
      hcorr.toSound.depset_size hof hof_le (hcorr.formula_sound htrue)
  have hlookup₁ :
      ∀ ext v, st₁.formula.lookupInternal ext = some v →
        0 < v ∧ v ≤ st₁.formula.maxVar := by
    intro ext v hlookup
    have hlookup_old : st.formula.lookupInternal ext = some v := by
      simpa [st₁, lookupInternal_addDependencyFormula] using hlookup
    rcases hcorr.lookupInternal_sound ext v hlookup_old with ⟨hpos, hle⟩
    exact ⟨hpos, by simpa [st₁, DQBF.addDependencyFormula] using hle⟩
  simpa [st₁, DQBF.addDependencyFormula] using
    (CheckState.Correct.ofResetState
      (st := st₁)
      hsound₁
      hclauses₁
      hcorr.formula_extends
      hformula_sound₁
      hlookup₁)

theorem CheckState.PropStruct.withAddClause
    {st : CheckState} {lits : Array Literal}
    (hprop : CheckState.PropStruct st)
    (hlits : ClauseLitsWellFormed st.formula lits) :
    CheckState.PropStruct { st with clauses := (st.clauses.addClause lits).1 } := by
  refine
    { toSound := ?_
      clauses_wf := hprop.clauses_wf.addClause hlits
      trail_single_level := hprop.trail_single_level }
  exact
    { isAssigned_size := hprop.toSound.isAssigned_size
      value_size := hprop.toSound.value_size
      indepKnown_size := hprop.toSound.indepKnown_size
      indepOf_size := hprop.toSound.indepOf_size
      externalName_size := hprop.toSound.externalName_size
      isExistential_size := hprop.toSound.isExistential_size
      depset_size := hprop.toSound.depset_size
      clauses_nonempty := by simpa [ClauseStore.addClause] using Nat.succ_pos st.clauses.clauses.size
      trail_nonempty := hprop.toSound.trail_nonempty
      trail_lits_valid := hprop.trail_lits_valid
      assigned_iff_in_trail := hprop.assigned_iff_in_trail }

-- ─── Key lemma (sorry'd) ──────────────────────────────────────────────────────

/-- If `negateAndPropagate lits (fun _ => true)` is called from a state
    ConsistentWith (σ, sk) and all lits are model-false under (σ, sk),
    then it returns `false` (no conflict detected).

    Proof sketch: `newDecisionLevel` preserves consistency. For each literal `l` in `lits`,
    `which l = true` so we negate it: `l` is already false in the model, so `l.negate` is
    true. If `l.var` is out of range or `l.negate` is already assigned, we skip safely.
    Otherwise we enqueue `l.negate` (a model-true literal) and run `propagate`. Since the
    model satisfies all clauses, `propagate` never finds a conflict from model-true
    assignments. Hence the foldlM returns `false`. -/
-- ─── Helper: propagation never conflicts when model is consistent ─────────────

-- Helper: if model satisfies all clauses and state is consistent, sat check gives false
-- (model-false literals can't be satisfied in a consistent state)
theorem litValue_of_satisfied'
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (st : CheckState)
    (hassign : ∀ v, 0 < v → st.isAssigned.getD (v - 1) false = true →
        f.varValue σ sk v = st.value.getD (v - 1) false)
    (l : Literal) (hsat : satisfied st l = true) :
    f.litValue σ sk l = true := by
  simp only [satisfied, Bool.and_eq_true, decide_eq_true_iff] at hsat
  obtain ⟨⟨⟨hv_pos, _⟩, hassign_v⟩, hval_eq⟩ := hsat
  have hmodel := (hassign l.var hv_pos hassign_v).trans (beq_iff_eq.mp hval_eq)
  simp only [DQBF.litValue, hmodel]; cases l.isPos <;> simp

-- If clauseValue = true, sat = false, unassigned.size = 1, all lits WF:
-- the unique unassigned lit is model-true
theorem unit_lit_model_true
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (st : CheckState) (hf : st.formula = f) (hcs : st.clauses = cs)
    (hassign : ∀ v, 0 < v → st.isAssigned.getD (v - 1) false = true →
        f.varValue σ sk v = st.value.getD (v - 1) false)
    (clause_lits : Array Literal)
    (hwf_lits : ∀ l ∈ clause_lits.toList, 0 < l.var ∧ l.var ≤ f.maxVar)
    (hclause_val : f.clauseValue σ sk clause_lits = true)
    (hsat_false : clause_lits.any (fun lit =>
        let v := lit.var
        v > 0 && v ≤ st.formula.maxVar &&
        st.isAssigned.getD (v - 1) false &&
        (st.value.getD (v - 1) false == lit.isPos)) = false)
    (unassigned : Array Literal)
    (hunassigned : unassigned = clause_lits.filter (fun lit =>
        let v := lit.var
        v > 0 && v ≤ st.formula.maxVar &&
        !st.isAssigned.getD (v - 1) false))
    (hsize1 : unassigned.size = 1) :
    f.litValue σ sk (unassigned.getD 0 ⟨0⟩) = true := by
  simp only [DQBF.clauseValue, Array.any_eq_true] at hclause_val
  obtain ⟨i, hi, hl_true⟩ := hclause_val
  have hmem_tl := Array.mem_toList_iff.mpr (Array.getElem_mem hi)
  have hwfl := hwf_lits _ hmem_tl
  -- Step 1: clause_lits[i] is NOT assigned (if it were, sat = true contradicts hsat_false)
  have hnotassign : st.isAssigned.getD (clause_lits[i].var - 1) false = false := by
    rcases Bool.eq_false_or_eq_true (st.isAssigned.getD (clause_lits[i].var - 1) false) with h | h
    · exfalso
      have hval := hassign _ hwfl.1 h
      have hvarval : f.varValue σ sk clause_lits[i].var = clause_lits[i].isPos := by
        rcases Bool.eq_false_or_eq_true clause_lits[i].isPos with hpos | hpos <;>
          simp [DQBF.litValue, hpos] at hl_true ⊢ <;> exact hl_true
      have hval_eq : st.value.getD (clause_lits[i].var - 1) false = clause_lits[i].isPos :=
        hval.symm.trans hvarval
      have hsat_one : (fun lit => let v := lit.var; decide (v > 0) && decide (v ≤ st.formula.maxVar) &&
          st.isAssigned.getD (v - 1) false && (st.value.getD (v - 1) false == lit.isPos)) clause_lits[i] = true := by
        simp only [Bool.and_eq_true, gt_iff_lt, decide_eq_true_iff, beq_iff_eq, hf]
        exact ⟨⟨⟨hwfl.1, hwfl.2⟩, h⟩, hval_eq⟩
      have hany : clause_lits.any (fun lit =>
          let v := lit.var
          decide (v > 0) && decide (v ≤ st.formula.maxVar) && st.isAssigned.getD (v - 1) false &&
          (st.value.getD (v - 1) false == lit.isPos)) = true :=
        Array.any_eq_true.mpr ⟨i, hi, hsat_one⟩
      rw [hany] at hsat_false; exact absurd hsat_false (by decide)
    · exact h
  -- Step 2: clause_lits[i] ∈ unassigned
  have hmem_u : clause_lits[i] ∈ unassigned := by
    rw [hunassigned, Array.mem_filter]
    exact ⟨Array.getElem_mem hi, by simp [hf, hwfl.1, hwfl.2, hnotassign]⟩
  -- Step 3: unassigned has only one element at index 0, which is clause_lits[i]
  obtain ⟨j, hj, heqj⟩ := Array.mem_iff_getElem.mp hmem_u
  have hj0 : j = 0 := Nat.lt_one_iff.mp (hsize1 ▸ hj)
  subst hj0
  have h0lt : 0 < unassigned.size := hsize1 ▸ Nat.zero_lt_one
  suffices h : unassigned.getD 0 ⟨0⟩ = clause_lits[i] by rw [h]; exact hl_true
  simp only [Array.getD, dif_pos h0lt]
  exact heqj

-- litValue of the negated literal is the Boolean negation of litValue.
theorem litValue_negate (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (l : Literal) :
    f.litValue σ sk l.negate = !(f.litValue σ sk l) := by
  simp only [DQBF.litValue, Literal.negate, Literal.var, Literal.isPos]
  have hvar : (l.x ^^^ 1) / 2 = l.x / 2 := by
    apply Nat.eq_of_testBit_eq; intro k
    simp only [← Nat.testBit_succ, Nat.testBit_xor]
    have h1 : Nat.testBit 1 (k + 1) = false := by
      rw [Bool.eq_false_iff]
      exact fun h => Nat.succ_ne_zero k (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)
    simp [h1]
  have hpos : ((l.x ^^^ 1) % 2 == 1) = !(l.x % 2 == 1) := by
    have h0 : (l.x ^^^ 1).testBit 0 = !l.x.testBit 0 := by
      rw [Nat.testBit_xor, Nat.testBit_one_zero]; simp [Bool.xor_comm]
    cases hb : l.x.testBit 0
    · have hm : l.x % 2 = 0 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hb
      have hxm : (l.x ^^^ 1) % 2 = 1 := Nat.mod_two_eq_one_iff_testBit_zero.mpr (by rw [h0, hb]; decide)
      simp [hm, hxm]
    · have hm : l.x % 2 = 1 := Nat.mod_two_eq_one_iff_testBit_zero.mpr hb
      have hxm : (l.x ^^^ 1) % 2 = 0 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr (by rw [h0, hb]; decide)
      simp [hm, hxm]
  rw [hvar, hpos]
  cases h : (l.x % 2 == 1) <;> simp

-- If a literal is model-false and the state is consistent, then `satisfied st l = false`.
theorem satisfied_false_of_model_false
    {f : DQBF} {cs : ClauseStore} {σ : UnivAssignment} {sk : SkolemAssignment} {st : CheckState}
    (h_con : CheckState.ConsistentWith f cs σ sk st)
    (l : Literal) (hl : f.litValue σ sk l = false) :
    satisfied st l = false := by
  cases h : satisfied st l
  · rfl
  · exact absurd (litValue_of_satisfied' f σ sk st h_con.assigned_model l h) (by simp [hl])

-- PropInv: state maintains model-consistency including formula/clauses identity
abbrev PropInv (f : DQBF) (cs : ClauseStore)
    (σ : UnivAssignment) (sk : SkolemAssignment) (st : CheckState) : Prop :=
  CheckState.ConsistentWith f cs σ sk st

-- Helper for setIfInBounds getD (positive case)
theorem arraySafeSet_getD_eq' (a : Array Bool) (i : Nat) (v : Bool) (h : i < a.size) :
    (a.setIfInBounds i v).getD i false = v := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD, dif_pos (hsize ▸ h)]
  simp [Array.getElem_setIfInBounds h]

-- Helper for setIfInBounds getD (negative case)
theorem arraySafeSet_getD_ne' (a : Array Bool) (i j : Nat) (v : Bool) (hij : i ≠ j) :
    (a.setIfInBounds i v).getD j false = a.getD j false := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD]
  rcases Nat.lt_or_ge j a.size with hjlt | hjlt
  · rw [dif_pos (hsize ▸ hjlt), dif_pos hjlt]
    exact Array.getElem_setIfInBounds_ne hjlt hij
  · have hjlt' : ¬(j < a.size) := Nat.not_lt.mpr hjlt
    rw [dif_neg (hsize ▸ hjlt'), dif_neg hjlt']

theorem arraySetIfInBounds_getD_eq
    {α : Type} (a : Array α) (i : Nat) (v fallback : α) (h : i < a.size) :
    (a.setIfInBounds i v).getD i fallback = v := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD, dif_pos (hsize ▸ h)]
  simp [Array.getElem_setIfInBounds h]

theorem arraySetIfInBounds_getD_ne
    {α : Type} (a : Array α) (i j : Nat) (v fallback : α) (hij : i ≠ j) :
    (a.setIfInBounds i v).getD j fallback = a.getD j fallback := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD]
  rcases Nat.lt_or_ge j a.size with hjlt | hjlt
  · rw [dif_pos (hsize ▸ hjlt), dif_pos hjlt]
    exact Array.getElem_setIfInBounds_ne hjlt hij
  · have hjlt' : ¬(j < a.size) := Nat.not_lt.mpr hjlt
    rw [dif_neg (hsize ▸ hjlt'), dif_neg hjlt']

theorem enqueue_sound_spec
    (l : Literal) :
    ⦃fun s => ⌜CheckState.Sound s⌝⦄
    (enqueue l : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Sound s'⌝⦄ := by
  unfold enqueue
  mvcgen
  rename_i s_state hsound v_var _ h_valid h_in_bounds _ lastIdx lastLevel
  have htrail_pos : 0 < s_state.trail.size := hsound.trail_nonempty
  have hlast_lt : lastIdx < s_state.trail.size := by
    unfold lastIdx
    omega
  have hv_pos : 0 < v_var := by
    cases Nat.eq_zero_or_pos v_var with
    | inl hv0 =>
      simp [hv0] at h_valid
    | inr hv_pos =>
      exact hv_pos
  have hv_le : v_var ≤ s_state.formula.maxVar := by
    exact Nat.le_of_not_gt (by
      intro hgt
      simp [hgt] at h_valid)
  have hlt : v_var - 1 < s_state.isAssigned.size := Nat.lt_of_not_le h_in_bounds
  refine
    { isAssigned_size := by simp [Array.size_setIfInBounds, hsound.isAssigned_size]
      value_size := by simp [Array.size_setIfInBounds, hsound.value_size]
      indepKnown_size := hsound.indepKnown_size
      indepOf_size := hsound.indepOf_size
      externalName_size := hsound.externalName_size
      isExistential_size := hsound.isExistential_size
      depset_size := hsound.depset_size
      clauses_nonempty := hsound.clauses_nonempty
      trail_nonempty := by
        simp [Array.size_setIfInBounds, hsound.trail_nonempty]
      trail_lits_valid := ?_
      assigned_iff_in_trail := ?_ }
  · intro i hi l' hl'
    by_cases hidx : i = lastIdx
    · subst hidx
      have hget :
          (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD lastIdx #[] =
            lastLevel.push l := by
        exact arraySetIfInBounds_getD_eq s_state.trail lastIdx (lastLevel.push l) #[] hlast_lt
      rw [hget] at hl'
      have hl'' : l' ∈ lastLevel ∨ l' = l := by
        simpa using (Array.mem_push.mp hl')
      rcases hl'' with hl_old | rfl
      · have hlastLevel : lastLevel = s_state.trail.getD lastIdx #[] := by
          simp [lastLevel]
        have hl_old' : l' ∈ s_state.trail.getD lastIdx #[] := by
          rw [← hlastLevel]
          exact hl_old
        exact hsound.trail_lits_valid lastIdx (by simpa using hlast_lt) l' hl_old'
      · exact ⟨hv_pos, hv_le⟩
    · have hget :
          (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD i #[] =
            s_state.trail.getD i #[] := by
        exact arraySetIfInBounds_getD_ne s_state.trail lastIdx i (lastLevel.push l) #[] (by
          intro h
          exact hidx h.symm)
      rw [hget] at hl'
      exact hsound.trail_lits_valid i (by
        simpa [Array.size_setIfInBounds] using hi) l' hl'
  · intro v' hpos' hle'
    constructor
    · intro hass'
      by_cases hveq : v' = v_var
      · refine ⟨lastIdx, by simpa [Array.size_setIfInBounds] using hlast_lt, l, ?_, hveq.symm⟩
        have hget :
            (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD lastIdx #[] =
              lastLevel.push l := by
          exact arraySetIfInBounds_getD_eq s_state.trail lastIdx (lastLevel.push l) #[] hlast_lt
        rw [hget]
        exact Array.mem_push_self
      · have hne : v_var - 1 ≠ v' - 1 := by
          intro heq
          apply hveq
          have h := congrArg (· + 1) heq
          simp only [Nat.sub_add_cancel hv_pos, Nat.sub_add_cancel hpos'] at h
          exact h.symm
        rw [arraySafeSet_getD_ne' _ _ _ _ hne] at hass'
        obtain ⟨i, hi, l'', hl'', hlvar⟩ :=
          (hsound.assigned_iff_in_trail v' hpos' hle').mp hass'
        refine ⟨i, by simpa [Array.size_setIfInBounds] using hi, l'', ?_, hlvar⟩
        by_cases hidx : i = lastIdx
        · subst hidx
          have hget :
              (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD lastIdx #[] =
                lastLevel.push l := by
            exact arraySetIfInBounds_getD_eq s_state.trail lastIdx (lastLevel.push l) #[] hlast_lt
          rw [hget]
          have hlastLevel : lastLevel = s_state.trail.getD lastIdx #[] := by
            simp [lastLevel]
          rw [hlastLevel]
          exact Array.mem_push.mpr (Or.inl hl'')
        · have hget :
              (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD i #[] =
                s_state.trail.getD i #[] := by
            exact arraySetIfInBounds_getD_ne s_state.trail lastIdx i (lastLevel.push l) #[] (by
              intro h
              exact hidx h.symm)
          rw [hget]
          exact hl''
    · intro hmem
      by_cases hveq : v' = v_var
      · subst hveq
        exact arraySafeSet_getD_eq' _ _ _ hlt
      · have hne : v_var - 1 ≠ v' - 1 := by
          intro heq
          apply hveq
          have h := congrArg (· + 1) heq
          simp only [Nat.sub_add_cancel hv_pos, Nat.sub_add_cancel hpos'] at h
          exact h.symm
        rw [arraySafeSet_getD_ne' _ _ _ _ hne]
        apply (hsound.assigned_iff_in_trail v' hpos' hle').mpr
        rcases hmem with ⟨i, hi, l', hl', hlvar⟩
        refine ⟨i, by simpa [Array.size_setIfInBounds] using hi, l', ?_, hlvar⟩
        by_cases hidx : i = lastIdx
        · subst hidx
          have hget :
              (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD lastIdx #[] =
                lastLevel.push l := by
            exact arraySetIfInBounds_getD_eq s_state.trail lastIdx (lastLevel.push l) #[] hlast_lt
          rw [hget] at hl'
          rcases Array.mem_push.mp hl' with hl_old | rfl
          · have hlastLevel : lastLevel = s_state.trail.getD lastIdx #[] := by
              simp [lastLevel]
            rw [← hlastLevel]
            exact hl_old
          · exfalso
            exact hveq hlvar.symm
        · have hget :
              (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD i #[] =
                s_state.trail.getD i #[] := by
            exact arraySetIfInBounds_getD_ne s_state.trail lastIdx i (lastLevel.push l) #[] (by
              intro h
              exact hidx h.symm)
          rw [hget] at hl'
          exact hl'

theorem enqueue_propStruct_spec
    (l : Literal) :
    ⦃fun s => ⌜CheckState.PropStruct s⌝⦄
    (enqueue l : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.PropStruct s'⌝⦄ := by
  unfold enqueue
  mvcgen
  rename_i s_state hprop v_var _ h_valid h_in_bounds h_unassigned lastIdx lastLevel
  have htrail_size : s_state.trail.size = 1 := hprop.trail_single_level
  have hlastIdx : lastIdx = 0 := by
    simp [lastIdx, htrail_size]
  have hlast_lt : lastIdx < s_state.trail.size := by
    rw [hlastIdx, htrail_size]
    decide
  have hv_pos : 0 < v_var := by
    cases Nat.eq_zero_or_pos v_var with
    | inl hv0 =>
      simp [hv0] at h_valid
    | inr hv_pos =>
      exact hv_pos
  have hv_le : v_var ≤ s_state.formula.maxVar := by
    exact Nat.le_of_not_gt (by
      intro hgt
      simp [hgt] at h_valid)
  have hlt : v_var - 1 < s_state.isAssigned.size := Nat.lt_of_not_le h_in_bounds
  have hlt_val : v_var - 1 < s_state.value.size :=
    hprop.toSound.value_size.symm ▸ hprop.toSound.isAssigned_size ▸ hlt
  refine
    { toSound := ?_
      clauses_wf := hprop.clauses_wf
      trail_single_level := by simp [Array.size_setIfInBounds, htrail_size] }
  · refine ⟨?_, ?_, hprop.toSound.indepKnown_size, hprop.toSound.indepOf_size,
      hprop.toSound.externalName_size, hprop.toSound.isExistential_size,
      hprop.toSound.depset_size, hprop.toSound.clauses_nonempty, ?_, ?_, ?_⟩
    · simp [Array.size_setIfInBounds, hprop.toSound.isAssigned_size]
    · simp [Array.size_setIfInBounds, hprop.toSound.value_size]
    · simp [Array.size_setIfInBounds, hprop.toSound.trail_nonempty]
    · intro i hi l' hl'
      have hi0 : i = 0 := by
        rw [show (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).size = 1 by
          simp [Array.size_setIfInBounds, htrail_size]] at hi
        exact Nat.lt_one_iff.mp hi
      subst hi0
      have hget0 :
          (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD 0 #[] =
            lastLevel.push l := by
        simpa [hlastIdx] using
          arraySetIfInBounds_getD_eq s_state.trail lastIdx (lastLevel.push l) #[] hlast_lt
      rw [hget0] at hl'
      have hl'' : l' ∈ lastLevel ∨ l' = l := by
        simpa using (Array.mem_push.mp hl')
      rcases hl'' with hl' | rfl
      · have hlastLevel : lastLevel = s_state.trail.getD 0 #[] := by
          simp [lastLevel, hlastIdx]
        have hl_old : l' ∈ s_state.trail.getD 0 #[] := by
          rw [← hlastLevel]
          exact hl'
        exact hprop.trail_lits_valid 0 (by simpa [htrail_size]) l' hl_old
      · exact ⟨hv_pos, hv_le⟩
    · intro v' hpos' hle'
      constructor
      · intro hass'
        by_cases hveq : v' = v_var
        · refine ⟨0, by simpa [Array.size_setIfInBounds, htrail_size], l, ?_, hveq.symm⟩
          have hget0 :
              (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD 0 #[] =
                lastLevel.push l := by
            simpa [hlastIdx] using
              arraySetIfInBounds_getD_eq s_state.trail lastIdx (lastLevel.push l) #[] hlast_lt
          rw [hget0]
          exact Array.mem_push_self
        · have hne : v_var - 1 ≠ v' - 1 := by
            intro heq
            apply hveq
            have h := congrArg (· + 1) heq
            simp only [Nat.sub_add_cancel hv_pos, Nat.sub_add_cancel hpos'] at h
            exact h.symm
          rw [arraySafeSet_getD_ne' _ _ _ _ hne] at hass'
          obtain ⟨i, hi, l'', hl'', hlvar⟩ := (hprop.assigned_iff_in_trail v' hpos' hle').mp hass'
          have hi0 : i = 0 := by
            rw [htrail_size] at hi
            exact Nat.lt_one_iff.mp hi
          subst hi0
          refine ⟨0, by simpa [Array.size_setIfInBounds, htrail_size], l'', ?_, hlvar⟩
          have hget0 :
              (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD 0 #[] =
                lastLevel.push l := by
            simpa [hlastIdx] using
              arraySetIfInBounds_getD_eq s_state.trail lastIdx (lastLevel.push l) #[] hlast_lt
          rw [hget0]
          have hlastLevel : lastLevel = s_state.trail.getD 0 #[] := by
            simp [lastLevel, hlastIdx]
          rw [hlastLevel]
          exact Array.mem_push.mpr (Or.inl hl'')
      · intro hmem
        rcases hmem with ⟨i, hi, l', hl', hlvar⟩
        have hi0 : i = 0 := by
          rw [show (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).size = 1 by
            simp [Array.size_setIfInBounds, htrail_size]] at hi
          exact Nat.lt_one_iff.mp hi
        subst hi0
        have hget0 :
            (s_state.trail.setIfInBounds lastIdx (lastLevel.push l)).getD 0 #[] =
              lastLevel.push l := by
          simpa [hlastIdx] using
            arraySetIfInBounds_getD_eq s_state.trail lastIdx (lastLevel.push l) #[] hlast_lt
        rw [hget0] at hl'
        have hl'' : l' ∈ lastLevel ∨ l' = l := by
          simpa using (Array.mem_push.mp hl')
        rcases hl'' with hl' | hnew
        · have hass_old := (hprop.assigned_iff_in_trail v' hpos' hle').mpr
            (by
              have hlastLevel : lastLevel = s_state.trail.getD 0 #[] := by
                simp [lastLevel, hlastIdx]
              refine ⟨0, by simpa [htrail_size], l', ?_, hlvar⟩
              rw [← hlastLevel]
              exact hl')
          by_cases hveq : v' = v_var
          · subst hveq
            exact arraySafeSet_getD_eq' _ _ _ hlt
          · have hne : v_var - 1 ≠ v' - 1 := by
              intro heq
              apply hveq
              have h := congrArg (· + 1) heq
              simp only [Nat.sub_add_cancel hv_pos, Nat.sub_add_cancel hpos'] at h
              exact h.symm
            rw [arraySafeSet_getD_ne' _ _ _ _ hne]
            exact hass_old
        · have : v' = v_var := by simpa [hlvar] using congrArg Literal.var hnew
          subst this
          exact arraySafeSet_getD_eq' _ _ _ hlt

theorem enqueue_sameFC_spec (l : Literal) (s₀ : CheckState) :
    ⦃fun s => ⌜SameFC s₀ s⌝⦄
    (enqueue l : CheckM Unit)
    ⦃⇓ _ s' => ⌜SameFC s₀ s'⌝⦄ := by
  mvcgen [enqueue]

-- ─── Hoare-triple specs for propagation primitives ────────────────────────────

section SoundProof
attribute [local spec] enqueue_sound_spec

theorem propagateOne_sound_spec (l : Literal) :
    ⦃fun s => ⌜CheckState.Sound s⌝⦄
    (propagateOne l : CheckM (Option CRef))
    ⦃⇓ _ s' => ⌜CheckState.Sound s'⌝⦄ := by
  mvcgen [propagateOne, enqueue_sound_spec] invariants
  · ⇓⟨_, acc⟩ s => ⌜CheckState.Sound s⌝
    with
  case vc9.post.success => exact id

end SoundProof

section PropStructProof
attribute [local spec] enqueue_propStruct_spec

/-- `propagateOne` preserves `PropStruct`.  No model witness needed.
    Placed before `enqueue_consistent_spec` so mvcgen sees only the structural
    `@[spec] enqueue_propStruct_spec`, not the semantic one. -/
theorem propagateOne_propStruct_spec (l : Literal) :
    ⦃fun s => ⌜CheckState.PropStruct s⌝⦄
    (propagateOne l : CheckM (Option CRef))
    ⦃⇓ _ s' => ⌜CheckState.PropStruct s'⌝⦄ := by
  mvcgen [propagateOne, enqueue_propStruct_spec] invariants
  · ⇓⟨_, acc⟩ s => ⌜CheckState.PropStruct s⌝
    with
  case vc9.post.success => exact id

end PropStructProof

section SameFCProof
attribute [local spec] enqueue_sameFC_spec

theorem propagateOne_sameFC_spec (l : Literal) (s₀ : CheckState) :
    ⦃fun s => ⌜SameFC s₀ s⌝⦄
    (propagateOne l : CheckM (Option CRef))
    ⦃⇓ _ s' => ⌜SameFC s₀ s'⌝⦄ := by
  mvcgen [propagateOne, enqueue_sameFC_spec] invariants
  · ⇓⟨_, acc⟩ s => ⌜SameFC s₀ s⌝
    with all_goals first | assumption | exact sameFC_trans ‹_› ‹_› | exact id

end SameFCProof

private structure TrialState (s₀ st : CheckState) : Prop
    extends CheckState.Sound st where
  sameFC : SameFC s₀ st
  trail_two_levels : st.trail.size = 2
  base_level_eq : st.trail.getD 0 #[] = s₀.trail.getD 0 #[]
  level1_fresh : ∀ l ∈ st.trail.getD 1 #[], s₀.isAssigned.getD (l.var - 1) false = false
  base_values_preserved : ∀ v, 0 < v → s₀.isAssigned.getD (v - 1) false = true →
      st.value.getD (v - 1) false = s₀.value.getD (v - 1) false

private theorem TrialState.baseAssigned_stillAssigned
    {dqbf : DQBF} {cs : ClauseStore} {s₀ s : CheckState}
    (hcorr₀ : CheckState.Correct dqbf cs s₀)
    (htrial : TrialState s₀ s)
    {v : Var}
    (hpos : 0 < v)
    (hassign₀ : s₀.isAssigned.getD (v - 1) false = true) :
    s.isAssigned.getD (v - 1) false = true := by
  have hlt : v - 1 < s₀.isAssigned.size := by
    by_cases hlt : v - 1 < s₀.isAssigned.size
    · exact hlt
    · have : s₀.isAssigned.getD (v - 1) false = false := by
        simp [Array.getD, hlt]
      rw [this] at hassign₀
      cases hassign₀
  have hle₀ : v ≤ s₀.formula.maxVar := by
    rw [hcorr₀.toSound.isAssigned_size] at hlt
    have hle' : v - 1 + 1 ≤ s₀.formula.maxVar := Nat.succ_le_of_lt hlt
    simpa [Nat.sub_add_cancel hpos] using hle'
  have hmem₀ := (hcorr₀.assigned_iff_in_trail v hpos hle₀).mp hassign₀
  rcases hmem₀ with ⟨i, hi, l, hl, hlvar⟩
  have hi0 : i = 0 := by
    simpa [hcorr₀.trail_single_level] using hi
  subst hi0
  have hl' : l ∈ s.trail.getD 0 #[] := by
    simpa [htrial.base_level_eq] using hl
  have hle : v ≤ s.formula.maxVar := by
    rcases htrial.sameFC with ⟨hformula, _⟩
    simpa [hformula] using hle₀
  exact (htrial.assigned_iff_in_trail v hpos hle).mpr
    ⟨0, by simpa [htrial.trail_two_levels], l, hl', hlvar⟩

private theorem TrialState.lastIdx_eq_one
    {s₀ s : CheckState} (htrial : TrialState s₀ s) :
    s.trail.size - 1 = 1 := by
  simpa [htrial.trail_two_levels]

private theorem TrialState.lastIdx_lt
    {s₀ s : CheckState} (htrial : TrialState s₀ s) :
    s.trail.size - 1 < s.trail.size := by
  simpa [htrial.trail_two_levels]

section TrialProof

private theorem enqueue_trial_spec
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState) (l : Literal) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s⌝⦄
    (enqueue l : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s'⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr₀, htrial⟩
  let v := l.var
  by_cases hbad : v = 0 ∨ v > s.formula.maxVar
  · have hguard : l.var = 0 ∨ s.formula.maxVar < l.var := by
      cases hbad with
      | inl h0 =>
          exact Or.inl (by simpa [v] using h0)
      | inr hgt =>
          exact Or.inr (by simpa [v] using hgt)
    have hrun : enqueue l s = .ok () s := by
      simpa using
        (show EStateM.run (enqueue l) s = .ok () s from by
          simp [enqueue, hguard])
    simp [WP.wp, PredTrans.apply, EStateM.run, hrun]
    exact ⟨hcorr₀, htrial⟩
  · have hv0 : v ≠ 0 := by
      intro hv0
      exact hbad (Or.inl hv0)
    have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
    have hvle : v ≤ s.formula.maxVar := by
      exact Nat.le_of_not_gt (by
        intro hgt
        exact hbad (Or.inr hgt))
    have hnotgt : ¬ s.formula.maxVar < l.var := by
      simpa [v] using Nat.not_lt_of_ge hvle
    by_cases hbounds : v - 1 >= s.isAssigned.size
    · have hrun : enqueue l s = .ok () s := by
        simpa using
          (show EStateM.run (enqueue l) s = .ok () s from by
            simp [enqueue, hv0, hvle, hbounds, v])
      simp [WP.wp, PredTrans.apply, EStateM.run, hrun]
      exact ⟨hcorr₀, htrial⟩
    · by_cases hassigned : s.isAssigned.getD (v - 1) false = true
      · have hrun : enqueue l s = .ok () s := by
          have hcond : s.isAssigned[l.var - 1]?.getD false = true := by
            simpa [Array.getD_eq_getD_getElem?, v] using hassigned
          simpa using
            (show EStateM.run (enqueue l) s = .ok () s from by
              simp [enqueue, hv0, hnotgt, hbounds, hcond, v])
        simp [WP.wp, PredTrans.apply, EStateM.run, hrun]
        exact ⟨hcorr₀, htrial⟩
      · have hrun : enqueue l s =
            .ok ()
              { s with
                isAssigned := s.isAssigned.setIfInBounds (v - 1) true
                value := s.value.setIfInBounds (v - 1) l.isPos
                trail := s.trail.setIfInBounds (s.trail.size - 1)
                  ((s.trail.getD (s.trail.size - 1) #[]).push l)
                propQueue := s.propQueue.push l } := by
          simpa using
            (show EStateM.run (enqueue l) s =
              .ok ()
                { s with
                  isAssigned := s.isAssigned.setIfInBounds (v - 1) true
                  value := s.value.setIfInBounds (v - 1) l.isPos
                  trail := s.trail.setIfInBounds (s.trail.size - 1)
                    ((s.trail.getD (s.trail.size - 1) #[]).push l)
                  propQueue := s.propQueue.push l } from by
              have hassigned_false : s.isAssigned.getD (v - 1) false = false := by
                simpa using hassigned
              have hcond_false : s.isAssigned[l.var - 1]?.getD false = false := by
                simpa [Array.getD_eq_getD_getElem?, v] using hassigned_false
              simp [enqueue, hv0, hvle, hnotgt, hbounds, hcond_false, v])
        let s_enq : CheckState :=
          { s with
            isAssigned := s.isAssigned.setIfInBounds (v - 1) true
            value := s.value.setIfInBounds (v - 1) l.isPos
            trail := s.trail.setIfInBounds (s.trail.size - 1)
              ((s.trail.getD (s.trail.size - 1) #[]).push l)
            propQueue := s.propQueue.push l }
        have hrun' : enqueue l s = .ok () s_enq := by
          simpa [s_enq] using hrun
        have hsound : CheckState.Sound s_enq := by
          have hspec := enqueue_sound_spec l
          specialize hspec s htrial.toSound
          simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
          rw [hrun'] at hspec
          exact hspec
        have hsame : SameFC s₀ s_enq := by
          have hspec := enqueue_sameFC_spec l s₀
          specialize hspec s htrial.sameFC
          simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
          rw [hrun'] at hspec
          exact hspec
        have hbase_unassigned : s₀.isAssigned.getD (v - 1) false = false := by
          by_cases hbase : s₀.isAssigned.getD (v - 1) false = true
          · have hs_assigned : s.isAssigned.getD (v - 1) false = true :=
              TrialState.baseAssigned_stillAssigned hcorr₀ htrial hvpos hbase
            have hs_false : s.isAssigned.getD (v - 1) false = false := by
              simpa using hassigned
            rw [hs_false] at hs_assigned
            cases hs_assigned
          · cases hbool : s₀.isAssigned.getD (v - 1) false <;> simp [hbool] at hbase ⊢
        have htrail_two_levels : s_enq.trail.size = 2 := by
          simpa [s_enq, htrial.trail_two_levels] using htrial.trail_two_levels
        have hbase_level_eq : s_enq.trail.getD 0 #[] = s₀.trail.getD 0 #[] := by
          have hneq : s.trail.size - 1 ≠ 0 := by
            simpa [TrialState.lastIdx_eq_one htrial] using (Nat.one_ne_zero : (1 : Nat) ≠ 0)
          have hget0 :
              s_enq.trail.getD 0 #[] = s.trail.getD 0 #[] := by
            simpa [s_enq] using
              (arraySetIfInBounds_getD_ne
                (a := s.trail)
                (i := s.trail.size - 1)
                (j := 0)
                (v := (s.trail.getD (s.trail.size - 1) #[]).push l)
                (fallback := #[])
                hneq)
          exact hget0.trans htrial.base_level_eq
        have hlevel1_eq :
            s_enq.trail.getD 1 #[] = (s.trail.getD 1 #[]).push l := by
          have hlast_lt : s.trail.size - 1 < s.trail.size :=
            TrialState.lastIdx_lt htrial
          have hget_last :
              (s.trail.setIfInBounds (s.trail.size - 1)
                ((s.trail.getD (s.trail.size - 1) #[]).push l)).getD (s.trail.size - 1) #[] =
                (s.trail.getD (s.trail.size - 1) #[]).push l := by
            exact arraySetIfInBounds_getD_eq s.trail (s.trail.size - 1)
              ((s.trail.getD (s.trail.size - 1) #[]).push l) #[] hlast_lt
          simpa [s_enq, TrialState.lastIdx_eq_one htrial] using hget_last
        have htrial' : TrialState s₀ s_enq := by
          refine
            { toSound := hsound
              sameFC := hsame
              trail_two_levels := htrail_two_levels
              base_level_eq := hbase_level_eq
              level1_fresh := ?_
              base_values_preserved := ?_ }
          · intro l' hl'
            have hlpush : l' ∈ (s.trail.getD 1 #[]).push l := by
              simpa [hlevel1_eq] using hl'
            rcases Array.mem_push.mp hlpush with hl_old | rfl
            · exact htrial.level1_fresh l' hl_old
            · exact hbase_unassigned
          · intro v' hv' hassign₀
            by_cases hveq : v' = v
            · subst hveq
              rw [hbase_unassigned] at hassign₀
              cases hassign₀
            · have hneq : v - 1 ≠ v' - 1 := by
                intro heq
                apply hveq
                have h := congrArg (fun n => n + 1) heq
                simp [Nat.sub_add_cancel hvpos, Nat.sub_add_cancel hv'] at h
                exact h.symm
              have hval_set :
                  s_enq.value.getD (v' - 1) false = s.value.getD (v' - 1) false := by
                simpa [s_enq] using
                  (arraySetIfInBounds_getD_ne
                    (a := s.value) (i := v - 1) (j := v' - 1)
                    (v := l.isPos) (fallback := false) hneq)
              exact hval_set.trans (htrial.base_values_preserved v' hv' hassign₀)
        simp [WP.wp, PredTrans.apply, EStateM.run, hrun']
        exact ⟨hcorr₀, htrial'⟩

private theorem propagateOne_trial_spec
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState) (l : Literal) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s⌝⦄
    (propagateOne l : CheckM (Option CRef))
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s'⌝⦄ := by
  mvcgen [propagateOne] invariants
  · ⇓⟨_, acc⟩ s => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s⌝
    with
  case vc5.step.h_2.h_2.isFalse.isFalse.isTrue =>
    rename_i _ _ _ _ _ _ _ _ _ _ s hs _ _ _ _ _ unassigned _ _
    simpa [WP.wp, PredTrans.apply, EStateM.run] using
      (enqueue_trial_spec dqbf cs s₀ (unassigned.getD 0 { x := 0 }) s hs)
  case vc8.post.success =>
    intro hcorr htrial
    exact ⟨hcorr, htrial⟩
  all_goals assumption

end TrialProof

/-- `@[spec]` for `enqueue`: preserves `CheckState.ConsistentWith` when the literal is
    model-true. Because `ConsistentWith` extends `Sound`, this also guarantees all
    structural invariants are preserved. The `isAssigned_size` field inherited from
    `Sound` ensures `setIfInBounds` on `value` is in-bounds whenever the `isAssigned`
    bounds-check passes. -/
@[spec]
theorem enqueue_consistent_spec
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment) (sk : SkolemAssignment)
    (l : Literal) (hl : f.litValue σ sk l = true) :
    ⦃fun s => ⌜CheckState.ConsistentWith f cs σ sk s⌝⦄
    (enqueue l : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.ConsistentWith f cs σ sk s'⌝⦄ := by
  unfold enqueue; mvcgen
  -- mvcgen generates one VC: case vc4.isFalse.isFalse.isFalse
  -- Inaccessible hypotheses (9, in order):
  --   s✝ (CheckState), h✝³ (ConsistentWith), v✝ (Var := l.var), __do_jp✝ (do-cont),
  --   h✝² (var valid), h✝¹ (isAssigned bounds), h✝ (not assigned),
  --   lastIdx✝ (Nat), lastLevel✝ (Array Literal)
  rename_i s_state h_con v_var _ h_valid h_in_bounds _ lastIdx lastLevel
  -- Case split: v_var = 0 contradicts h_valid; v_var > 0 continues the proof
  cases Nat.eq_zero_or_pos v_var with
  | inl hv0 => simp [hv0] at h_valid  -- contradiction: decide (0 = 0) = true
  | inr hv_pos =>
  -- h_in_bounds : ¬v_var - 1 ≥ s_state.isAssigned.size
  have hlt : v_var - 1 < s_state.isAssigned.size := Nat.lt_of_not_le h_in_bounds
  have hlt_val : v_var - 1 < s_state.value.size :=
    h_con.toSound.value_size.symm ▸ h_con.toSound.isAssigned_size ▸ hlt
  -- Key: f.varValue σ sk l.var = l.isPos from hl (v_var = l.var definitionally)
  have hvarval : f.varValue σ sk l.var = l.isPos := by
    simp only [DQBF.litValue] at hl
    rcases Bool.eq_false_or_eq_true l.isPos with h | h <;>
      simp only [h] at hl ⊢ <;> simpa using hl
  -- New state: formula/clauses unchanged; isAssigned/value set at (v_var - 1); propQueue pushed
  -- Provide toSound (all 9 structural fields), then the 5 ConsistentWith-specific fields.
  refine ⟨?_, h_con.formula_eq, h_con.clauses_eq, h_con.clauses_wf, ?_, ?_⟩
  · -- toSound: isAssigned/value sizes change via setIfInBounds (size-preserving);
    --          all other Sound fields are unchanged.
    refine ⟨?_, ?_, h_con.toSound.indepKnown_size, h_con.toSound.indepOf_size,
              h_con.toSound.externalName_size, h_con.toSound.isExistential_size,
              h_con.toSound.depset_size, h_con.toSound.clauses_nonempty,
              by rw [Array.size_setIfInBounds]; exact h_con.toSound.trail_nonempty,
              ?_, ?_⟩
    · simp [Array.size_setIfInBounds, h_con.toSound.isAssigned_size]
    · simp [Array.size_setIfInBounds, h_con.toSound.value_size]
    · simp
      intro i hi lit hlit
      have := h_con.trail_lits_valid i (by lia) lit
      by_cases eq : lastIdx = i
      · rw [← eq] at hlit
        simp [Array.getElem?_setIfInBounds_self] at hlit
        have lt : lastIdx < s_state.trail.size := by
          unfold lastIdx
          have := h_con.trail_nonempty
          lia
        simp only [lt, ↓reduceIte, Option.getD_some, Array.mem_push] at hlit
        cases hlit with
        | inl hin =>
          unfold lastLevel at hin
          rw [eq] at hin
          exact this hin
        | inr liteq =>
          subst liteq
          lia
      · rw [Array.getElem?_setIfInBounds_ne eq] at hlit
        simp at this
        exact this hlit
    · simp
      intro v hv1 hv2
      have := h_con.assigned_iff_in_trail v hv1 hv2
      simp at this
      by_cases eq : v = v_var
      · subst eq
        constructor
        · intro
          have lt : lastIdx < s_state.trail.size := by unfold lastIdx; have := h_con.trail_nonempty; lia
          refine ⟨lastIdx, lt, l, ?_, rfl⟩
          rw [Array.getElem?_setIfInBounds_self, if_pos lt, Option.getD_some]
          exact Array.mem_push.mpr (Or.inr rfl)
        · intro _
          rw [Array.getElem?_setIfInBounds_self, if_pos hlt, Option.getD_some]
      · have neq : v_var-1 ≠ v - 1 := by lia
        rw [Array.getElem?_setIfInBounds_ne neq]
        rw [this]
        constructor
        · rintro ⟨i, hi, lit, lit_in, lit_eq⟩
          exists i, hi, lit
          refine ⟨?_, lit_eq⟩
          by_cases hli : lastIdx = i
          · have lt : lastIdx < s_state.trail.size := hli ▸ hi
            rw [← hli, Array.getElem?_setIfInBounds_self, if_pos lt, Option.getD_some]
            apply Array.mem_push.mpr; left; simpa [lastLevel, Array.getD] using hli ▸ lit_in
          · rw [Array.getElem?_setIfInBounds_ne hli]; exact lit_in
        · rintro ⟨i, hi, lit, lit_in, lit_eq⟩
          refine ⟨i, hi, lit, ?_, lit_eq⟩
          by_cases hli : lastIdx = i
          · have lt : lastIdx < s_state.trail.size := hli ▸ hi
            rw [← hli, Array.getElem?_setIfInBounds_self, if_pos lt, Option.getD_some] at lit_in
            rcases Array.mem_push.mp lit_in with h | rfl
            · simpa [lastLevel, hli] using h
            · exact absurd lit_eq.symm eq
          · rwa [Array.getElem?_setIfInBounds_ne hli] at lit_in
      done
  · -- Assignment consistency
    intro v' hpos' hass'
    by_cases hveq : v' = v_var
    · -- Same variable: newly assigned; value is l.isPos
      rw [hveq, arraySafeSet_getD_eq' _ _ _ hlt_val]
      exact hvarval  -- v_var = l.var definitionally
    · -- Different variable: isAssigned and value unchanged at v' - 1
      -- v' ≠ v_var with both ≥ 1 → v' - 1 ≠ v_var - 1
      have hne : v_var - 1 ≠ v' - 1 := by
        intro heq; apply hveq
        have h := congrArg (· + 1) heq
        simp only [Nat.sub_add_cancel hv_pos, Nat.sub_add_cancel hpos'] at h
        exact h.symm
      rw [arraySafeSet_getD_ne' _ _ _ _ hne] at hass'
      rw [arraySafeSet_getD_ne' _ _ _ _ hne]
      exact h_con.assigned_model v' hpos' hass'
  · -- propQueue: new = old.push l; l is model-true by hl
    intro l' hl'
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl'
    rcases hl' with hl' | rfl
    · exact h_con.queue_model l' hl'
    · exact hl

/-- `@[spec]` for `propagateOne`: preserves `CheckState.ConsistentWith` (hence also
    `Sound`) and always returns `none` (no conflict) when the model satisfies all clauses.
    The conflict branch (`unassigned.isEmpty`) is unreachable: if all literals are
    assigned, at least one must be model-true (since the clause is model-true), and
    under `ConsistentWith` that literal would be `satisfied`, contradicting `sat = false`.
    The unit branch uses `unit_lit_model_true` + `enqueue_consistent_spec`. -/
@[spec]
theorem propagateOne_consistent_spec
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment) (sk : SkolemAssignment)
    (hmat : cs.matrixValue f σ sk = true) (l : Literal) :
    ⦃fun s => ⌜CheckState.ConsistentWith f cs σ sk s⌝⦄
    (propagateOne l : CheckM (Option CRef))
    ⦃⇓ r s' => ⌜CheckState.ConsistentWith f cs σ sk s' ∧ r = none⌝⦄ := by
  mvcgen [propagateOne, enqueue_consistent_spec] invariants
  · ⇓⟨_, acc⟩ s => ⌜CheckState.ConsistentWith f cs σ sk s ∧ acc = none⌝
    with
  case vc4.step.h_2.h_2.isFalse.isTrue =>
    -- Conflict branch: all lits assigned, sat = false, but clause is model-true → False.
    rename_i negL s_outer h_con_outer occs pref cur suff h_list b h_b s_inner clause x_get
             sat jp h_sat_false unassigned h_empty h_con
    exfalso
    -- Get the clause value from the matrix value
    have h_clause_val : f.clauseValue σ sk clause.lits = true :=
      clauseValue_of_matrixValue f cs σ sk cur clause hmat (h_con.clauses_eq ▸ x_get)
    -- Extract a model-satisfying literal
    simp only [DQBF.clauseValue, Array.any_eq_true] at h_clause_val
    obtain ⟨i, hi, hl_true⟩ := h_clause_val
    -- Literal is well-formed
    have hwfl := h_con.clauses_wf cur clause (h_con.clauses_eq ▸ x_get)
        clause.lits[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
    have hle : clause.lits[i].var ≤ s_inner.formula.maxVar := by
      rw [h_con.formula_eq]; exact hwfl.2
    -- Literal is assigned (not in unassigned since unassigned is empty).
    -- `by_contra` is unavailable without Mathlib; split on Bool value instead.
    have hassigned : s_inner.isAssigned.getD (clause.lits[i].var - 1) false = true := by
      rcases Bool.eq_false_or_eq_true (s_inner.isAssigned.getD (clause.lits[i].var - 1) false)
          with hna | hna
      · exact hna  -- value = true, done
      · -- value = false: literal belongs to `unassigned`, contradicting isEmpty
        exfalso
        have hcond : (fun lit =>
            let v := lit.var
            decide (v > 0) && decide (v ≤ s_inner.formula.maxVar) &&
            !s_inner.isAssigned.getD (v - 1) false)
            clause.lits[i] = true := by
          simp only [Bool.and_eq_true, decide_eq_true_iff]; refine ⟨⟨hwfl.1, hle⟩, ?_⟩; simp [hna]
        have hmem : clause.lits[i] ∈ unassigned :=
          Array.mem_filter.mpr ⟨Array.getElem_mem hi, hcond⟩
        have hempty := Array.isEmpty_iff.mp h_empty
        simp [hempty] at hmem
    -- Model value: from assigned_model, value matches varValue
    have hmodel := h_con.assigned_model clause.lits[i].var hwfl.1 hassigned
    -- varValue equals isPos (from litValue = true);
    -- simp_all uses Bool.not_eq_true to handle the negated case.
    have hvarval : f.varValue σ sk clause.lits[i].var = clause.lits[i].isPos := by
      rcases Bool.eq_false_or_eq_true clause.lits[i].isPos with hpos | hpos <;>
        simp [DQBF.litValue, hpos] at hl_true ⊢ <;> exact hl_true
    have hispos : s_inner.value.getD (clause.lits[i].var - 1) false = clause.lits[i].isPos :=
      hmodel.symm.trans hvarval
    -- sat must be true, contradicting h_sat_false.
    -- Use `show` to unfold `sat` (a let-binding) before applying any_eq_true.
    have hsat_true : sat = true := by
      show clause.lits.any (fun lit =>
          have v := lit.var
          decide (v > 0) && decide (v ≤ s_inner.formula.maxVar) &&
          s_inner.isAssigned.getD (v - 1) false &&
          s_inner.value.getD (v - 1) false == lit.isPos) = true
      simp only [Array.any_eq_true]
      refine ⟨i, hi, ?_⟩
      simp only [Bool.and_eq_true, gt_iff_lt, decide_eq_true_iff, beq_iff_eq, h_con.formula_eq]
      exact And.intro (And.intro (And.intro hwfl.1 hwfl.2) hassigned) hispos
    simp [hsat_true] at h_sat_false
  case vc9.hl =>
    -- Unit branch: prove the unique unassigned literal is model-true.
    rename_i negL s_outer h_con_outer occs pref cur suff h_list b h_b s_inner clause x_get
             sat jp h_sat_false unassigned h_not_empty h_size1 h_con
    have hsat_false : sat = false := by
      rcases Bool.eq_false_or_eq_true sat with h | h
      · exact absurd h h_sat_false
      · exact h
    exact unit_lit_model_true f σ sk s_inner
        h_con.formula_eq h_con.clauses_eq h_con.assigned_model
        clause.lits
        (h_con.clauses_wf cur clause (h_con.clauses_eq ▸ x_get))
        (clauseValue_of_matrixValue f cs σ sk cur clause hmat (h_con.clauses_eq ▸ x_get))
        hsat_false unassigned rfl h_size1
  all_goals first | exact ‹_› | exact ⟨‹_›, rfl⟩ | (intro h1 h2; exact ⟨h1, h2⟩)

/-- `propagate.aux` preserves `ConsistentWith` and returns `none`.
    Proved by induction on `n ≥ propQueue.size + isAssigned.count false`.
    At each step: pop from queue (preserves ConsistentWith), run propagateOne
    (preserves ConsistentWith and returns none by `propagateOne_consistent_spec`),
    then recurse (measure decreased by ≥ 1). -/
private theorem propagate_aux_consistent
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment) (sk : SkolemAssignment)
    (hmat : cs.matrixValue f σ sk = true) :
    ∀ (n : Nat) (st : CheckState),
      CheckState.ConsistentWith f cs σ sk st →
      st.propQueue.size + st.isAssigned.count false ≤ n →
      ∃ st', propagate.aux st = .ok none st' ∧
             CheckState.ConsistentWith f cs σ sk st' := by
  intro n
  induction n with
  | zero =>
    intro st h_con hn
    have hempty : st.propQueue.isEmpty = true := by
      simp only [Array.isEmpty_iff_size_eq_zero]; omega
    exact ⟨st, by simp only [propagate.aux, hempty, ↓reduceIte], h_con⟩
  | succ n ih =>
    intro st h_con hn
    by_cases hempty : st.propQueue.isEmpty = true
    · exact ⟨st, by simp only [propagate.aux, hempty, ↓reduceIte], h_con⟩
    · -- Queue non-empty: pop one literal
      simp only [Bool.not_eq_true] at hempty
      -- s₁ (with popped queue) satisfies ConsistentWith
      have h_con₁ : CheckState.ConsistentWith f cs σ sk
          { st with propQueue := st.propQueue.pop } :=
        { h_con with
          queue_model := fun l' hl' => h_con.queue_model l' (by
            rw [Array.toList_pop] at hl'
            exact List.dropLast_subset _ hl') }
      -- Apply propagateOne_consistent_spec (⇓ form) to get result
      have hprop := propagateOne_consistent_spec f cs σ sk hmat
          (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
      specialize hprop { st with propQueue := st.propQueue.pop } h_con₁
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hprop
      -- Case split on propagateOne result
      cases he : (propagateOne (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩))
          { st with propQueue := st.propQueue.pop } with
      | error e s =>
        -- Impossible: propagateOne_consistent_spec is ⇓ (noThrow)
        rw [he] at hprop; exact hprop.elim
      | ok r s₂ =>
        rw [he] at hprop
        obtain ⟨h_con₂, hr⟩ := hprop
        subst hr
        -- Measure: s₂.propQueue.size + s₂.isAssigned.count false ≤ n
        have hmeas := propagateOne_measure_spec
            (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
            ({ st with propQueue := st.propQueue.pop }.propQueue.size +
             { st with propQueue := st.propQueue.pop }.isAssigned.count false)
        specialize hmeas { st with propQueue := st.propQueue.pop } rfl
        simp only [WP.wp, PredTrans.apply, EStateM.run] at hmeas
        simp only [he] at hmeas
        have hpos : 0 < st.propQueue.size := by
          have hne : st.propQueue.size ≠ 0 :=
            fun h => absurd (Array.isEmpty_iff_size_eq_zero.mpr h) (by simp [hempty])
          omega
        have hmeas' : { st with propQueue := st.propQueue.pop }.propQueue.size +
                      { st with propQueue := st.propQueue.pop }.isAssigned.count false =
                      st.propQueue.size - 1 + st.isAssigned.count false := by
          show st.propQueue.pop.size + st.isAssigned.count false =
               st.propQueue.size - 1 + st.isAssigned.count false
          simp [Array.size_pop]
        have hn₂ : s₂.propQueue.size + s₂.isAssigned.count false ≤ n := by
          have hmeas_eq : s₂.propQueue.size + Array.count false s₂.isAssigned =
              st.propQueue.pop.size + Array.count false st.isAssigned := hmeas
          have hpop := @Array.size_pop _ st.propQueue
          omega
        -- Recurse
        obtain ⟨st', haux', h_con'⟩ := ih s₂ h_con₂ hn₂
        refine ⟨st', ?_, h_con'⟩
        -- Unfold propagate.aux one step, zeta-reduce let-bindings, then close
        rw [propagate.aux.eq_def, if_neg (show ¬(st.propQueue.isEmpty = true) by simp [hempty])]
        simp only []  -- zeta/iota reduction for have l := ...; have s₁ := ...
        rw [he]
        exact haux'

private theorem propagate_aux_none_queue_empty :
    ∀ (n : Nat) (st st' : CheckState),
      st.propQueue.size + st.isAssigned.count false ≤ n →
      propagate.aux st = .ok none st' →
      st'.propQueue = #[] := by
  intro n
  induction n with
  | zero =>
    intro st st' hn hrun
    have hcount : 0 ≤ st.isAssigned.count false := Nat.zero_le _
    have hsize : st.propQueue.size = 0 := by omega
    have hempty : st.propQueue.isEmpty = true := by
      simpa [Array.isEmpty_iff_size_eq_zero] using hsize
    rw [propagate.aux.eq_def, if_pos hempty] at hrun
    cases hrun
    simpa [Array.isEmpty_iff_size_eq_zero] using hempty
  | succ n ih =>
    intro st st' hn hrun
    by_cases hempty : st.propQueue.isEmpty = true
    · rw [propagate.aux.eq_def, if_pos hempty] at hrun
      cases hrun
      simpa [Array.isEmpty_iff_size_eq_zero] using hempty
    · rw [propagate.aux.eq_def,
        if_neg (show ¬ st.propQueue.isEmpty = true by simpa using hempty)] at hrun
      simp only [] at hrun
      cases he : (propagateOne (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩))
          { st with propQueue := st.propQueue.pop } with
      | error e s =>
        rw [he] at hrun
        cases hrun
      | ok r s =>
        cases r with
        | some cref =>
          rw [he] at hrun
          cases hrun
        | none =>
          rw [he] at hrun
          have hmeas := propagateOne_measure_spec
              (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
              ({ st with propQueue := st.propQueue.pop }.propQueue.size +
               { st with propQueue := st.propQueue.pop }.isAssigned.count false)
          specialize hmeas { st with propQueue := st.propQueue.pop } rfl
          simp only [WP.wp, PredTrans.apply, EStateM.run] at hmeas
          simp only [he] at hmeas
          have hn₂ : s.propQueue.size + s.isAssigned.count false ≤ n := by
            have hne : st.propQueue.size ≠ 0 :=
              fun h =>
                let hq : st.propQueue = #[] := Array.eq_empty_of_size_eq_zero h
                hempty (by simp [hq])
            have hpos : 0 < st.propQueue.size := Nat.pos_iff_ne_zero.mpr hne
            have hmeas_eq : s.propQueue.size + Array.count false s.isAssigned =
                st.propQueue.pop.size + Array.count false st.isAssigned := hmeas
            have hpop : st.propQueue.pop.size = st.propQueue.size - 1 := by
              simp [Array.size_pop]
            omega
          exact ih s st' hn₂ hrun

theorem propagate_none_queue_empty {st st' : CheckState}
    (hrun : propagate st = .ok none st') :
    st'.propQueue = #[] := by
  exact propagate_aux_none_queue_empty
    (st.propQueue.size + st.isAssigned.count false) st st' (Nat.le_refl _) hrun

private theorem propagate_aux_sound :
    ∀ (n : Nat) (st st' : CheckState),
      CheckState.Sound st →
      st.propQueue.size + st.isAssigned.count false ≤ n →
      propagate.aux st = .ok none st' →
      CheckState.Sound st' := by
  intro n
  induction n with
  | zero =>
    intro st st' hsound hn hrun
    have hempty : st.propQueue.isEmpty = true := by
      simp only [Array.isEmpty_iff_size_eq_zero]
      omega
    rw [propagate.aux.eq_def, if_pos hempty] at hrun
    cases hrun
    exact hsound
  | succ n ih =>
    intro st st' hsound hn hrun
    by_cases hempty : st.propQueue.isEmpty = true
    · rw [propagate.aux.eq_def, if_pos hempty] at hrun
      cases hrun
      exact hsound
    · rw [propagate.aux.eq_def,
        if_neg (show ¬ st.propQueue.isEmpty = true by simpa using hempty)] at hrun
      simp only [] at hrun
      have hsound₁ : CheckState.Sound { st with propQueue := st.propQueue.pop } := by
        refine
          { isAssigned_size := hsound.isAssigned_size
            value_size := hsound.value_size
            indepKnown_size := hsound.indepKnown_size
            indepOf_size := hsound.indepOf_size
            externalName_size := hsound.externalName_size
            isExistential_size := hsound.isExistential_size
            depset_size := hsound.depset_size
            clauses_nonempty := hsound.clauses_nonempty
            trail_nonempty := hsound.trail_nonempty
            trail_lits_valid := hsound.trail_lits_valid
            assigned_iff_in_trail := hsound.assigned_iff_in_trail }
      have hspec := propagateOne_sound_spec
          (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
      specialize hspec { st with propQueue := st.propQueue.pop } hsound₁
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
      cases he : (propagateOne (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩))
          { st with propQueue := st.propQueue.pop } with
      | error e s =>
        rw [he] at hspec
        exact hspec.elim
      | ok r s =>
        rw [he] at hspec
        cases r with
        | some cref =>
          rw [he] at hrun
          cases hrun
        | none =>
          rw [he] at hrun
          simp only [] at hrun
          have hn₂ : s.propQueue.size + s.isAssigned.count false ≤ n := by
            have hmeas := propagateOne_measure_spec
                (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
                ({ st with propQueue := st.propQueue.pop }.propQueue.size +
                 { st with propQueue := st.propQueue.pop }.isAssigned.count false)
            specialize hmeas { st with propQueue := st.propQueue.pop } rfl
            simp only [WP.wp, PredTrans.apply, EStateM.run] at hmeas
            simp only [he] at hmeas
            have hne : st.propQueue.size ≠ 0 :=
              fun h =>
                let hq : st.propQueue = #[] := Array.eq_empty_of_size_eq_zero h
                hempty (by simp [hq])
            have hpos : 0 < st.propQueue.size := Nat.pos_iff_ne_zero.mpr hne
            have hmeas_eq : s.propQueue.size + Array.count false s.isAssigned =
                st.propQueue.pop.size + Array.count false st.isAssigned := hmeas
            have hpop : st.propQueue.pop.size = st.propQueue.size - 1 := by
              simp [Array.size_pop]
            omega
          exact ih s st' hspec hn₂ hrun

theorem propagate_none_sound {st st' : CheckState}
    (hsound : CheckState.Sound st)
    (hrun : propagate st = .ok none st') :
    CheckState.Sound st' := by
  exact propagate_aux_sound
    (st.propQueue.size + st.isAssigned.count false) st st' hsound (Nat.le_refl _) hrun

private theorem propagate_aux_sound_any :
    ∀ (n : Nat) (st : CheckState) (r : Option CRef) (st' : CheckState),
      CheckState.Sound st →
      st.propQueue.size + st.isAssigned.count false ≤ n →
      propagate.aux st = .ok r st' →
      CheckState.Sound st' := by
  intro n
  induction n with
  | zero =>
    intro st r st' hsound hn hrun
    have hempty : st.propQueue.isEmpty = true := by
      simp only [Array.isEmpty_iff_size_eq_zero]
      omega
    rw [propagate.aux.eq_def, if_pos hempty] at hrun
    cases hrun
    exact hsound
  | succ n ih =>
    intro st r st' hsound hn hrun
    by_cases hempty : st.propQueue.isEmpty = true
    · rw [propagate.aux.eq_def, if_pos hempty] at hrun
      cases hrun
      exact hsound
    · rw [propagate.aux.eq_def,
        if_neg (show ¬ st.propQueue.isEmpty = true by simpa using hempty)] at hrun
      simp only [] at hrun
      have hsound₁ : CheckState.Sound { st with propQueue := st.propQueue.pop } := by
        refine
          { isAssigned_size := hsound.isAssigned_size
            value_size := hsound.value_size
            indepKnown_size := hsound.indepKnown_size
            indepOf_size := hsound.indepOf_size
            externalName_size := hsound.externalName_size
            isExistential_size := hsound.isExistential_size
            depset_size := hsound.depset_size
            clauses_nonempty := hsound.clauses_nonempty
            trail_nonempty := hsound.trail_nonempty
            trail_lits_valid := hsound.trail_lits_valid
            assigned_iff_in_trail := hsound.assigned_iff_in_trail }
      have hspec := propagateOne_sound_spec
          (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
      specialize hspec { st with propQueue := st.propQueue.pop } hsound₁
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
      cases he : (propagateOne (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩))
          { st with propQueue := st.propQueue.pop } with
      | error e s =>
        rw [he] at hspec
        exact hspec.elim
      | ok r₁ s =>
        rw [he] at hspec
        cases r₁ with
        | some cref =>
          rw [he] at hrun
          cases hrun
          exact hspec
        | none =>
          rw [he] at hrun
          simp only [] at hrun
          have hn₂ : s.propQueue.size + s.isAssigned.count false ≤ n := by
            have hmeas := propagateOne_measure_spec
                (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
                ({ st with propQueue := st.propQueue.pop }.propQueue.size +
                 { st with propQueue := st.propQueue.pop }.isAssigned.count false)
            specialize hmeas { st with propQueue := st.propQueue.pop } rfl
            simp only [WP.wp, PredTrans.apply, EStateM.run] at hmeas
            simp only [he] at hmeas
            have hne : st.propQueue.size ≠ 0 :=
              fun h =>
                let hq : st.propQueue = #[] := Array.eq_empty_of_size_eq_zero h
                hempty (by simp [hq])
            have hpos : 0 < st.propQueue.size := Nat.pos_iff_ne_zero.mpr hne
            have hmeas_eq : s.propQueue.size + Array.count false s.isAssigned =
                st.propQueue.pop.size + Array.count false st.isAssigned := hmeas
            have hpop : st.propQueue.pop.size = st.propQueue.size - 1 := by
              simp [Array.size_pop]
            omega
          exact ih s r st' hspec hn₂ hrun

theorem propagate_sound_spec :
    ⦃fun s => ⌜CheckState.Sound s⌝⦄
    (propagate : CheckM (Option CRef))
    ⦃⇓? _ s' => ⌜CheckState.Sound s'⌝⦄ := by
  intro st hsound
  cases hrun : propagate st with
  | error e s' =>
    simp only [WP.wp, PredTrans.apply, EStateM.run, hrun]
    trivial
  | ok r s' =>
    simp only [WP.wp, PredTrans.apply, EStateM.run, hrun]
    exact propagate_aux_sound_any
      (st.propQueue.size + st.isAssigned.count false) st r s' hsound (Nat.le_refl _) hrun

private theorem propagate_aux_propStruct :
    ∀ (n : Nat) (st st' : CheckState),
      CheckState.PropStruct st →
      st.propQueue.size + st.isAssigned.count false ≤ n →
      propagate.aux st = .ok none st' →
      CheckState.PropStruct st' := by
  intro n
  induction n with
  | zero =>
    intro st st' hprop hn hrun
    have hempty : st.propQueue.isEmpty = true := by
      simp only [Array.isEmpty_iff_size_eq_zero]
      omega
    rw [propagate.aux.eq_def, if_pos hempty] at hrun
    cases hrun
    exact hprop
  | succ n ih =>
    intro st st' hprop hn hrun
    by_cases hempty : st.propQueue.isEmpty = true
    · rw [propagate.aux.eq_def, if_pos hempty] at hrun
      cases hrun
      exact hprop
    · rw [propagate.aux.eq_def,
        if_neg (show ¬ st.propQueue.isEmpty = true by simpa using hempty)] at hrun
      simp only [] at hrun
      have hprop₁ : CheckState.PropStruct { st with propQueue := st.propQueue.pop } := by
        refine
          { toSound :=
              { isAssigned_size := hprop.toSound.isAssigned_size
                value_size := hprop.toSound.value_size
                indepKnown_size := hprop.toSound.indepKnown_size
                indepOf_size := hprop.toSound.indepOf_size
                externalName_size := hprop.toSound.externalName_size
                isExistential_size := hprop.toSound.isExistential_size
                depset_size := hprop.toSound.depset_size
                clauses_nonempty := hprop.toSound.clauses_nonempty
                trail_nonempty := hprop.toSound.trail_nonempty
                trail_lits_valid := hprop.trail_lits_valid
                assigned_iff_in_trail := hprop.assigned_iff_in_trail }
            clauses_wf := hprop.clauses_wf
            trail_single_level := hprop.trail_single_level }
      have hspec := propagateOne_propStruct_spec
          (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
      specialize hspec { st with propQueue := st.propQueue.pop } hprop₁
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
      cases he : (propagateOne (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩))
          { st with propQueue := st.propQueue.pop } with
      | error e s =>
        rw [he] at hspec
        exact hspec.elim
      | ok r s =>
        rw [he] at hspec
        cases r with
        | some cref =>
          rw [he] at hrun
          cases hrun
        | none =>
          rw [he] at hrun
          simp only [] at hrun
          have hn₂ : s.propQueue.size + s.isAssigned.count false ≤ n := by
            have hmeas := propagateOne_measure_spec
                (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
                ({ st with propQueue := st.propQueue.pop }.propQueue.size +
                 { st with propQueue := st.propQueue.pop }.isAssigned.count false)
            specialize hmeas { st with propQueue := st.propQueue.pop } rfl
            simp only [WP.wp, PredTrans.apply, EStateM.run] at hmeas
            simp only [he] at hmeas
            have hne : st.propQueue.size ≠ 0 :=
              fun h =>
                let hq : st.propQueue = #[] := Array.eq_empty_of_size_eq_zero h
                hempty (by simp [hq])
            have hpos : 0 < st.propQueue.size := Nat.pos_iff_ne_zero.mpr hne
            have hmeas_eq : s.propQueue.size + Array.count false s.isAssigned =
                st.propQueue.pop.size + Array.count false st.isAssigned := hmeas
            have hpop : st.propQueue.pop.size = st.propQueue.size - 1 := by
              simp [Array.size_pop]
            omega
          exact ih s st' hspec hn₂ hrun

theorem propagate_none_propStruct {st st' : CheckState}
    (hprop : CheckState.PropStruct st)
    (hrun : propagate st = .ok none st') :
    CheckState.PropStruct st' := by
  exact propagate_aux_propStruct
    (st.propQueue.size + st.isAssigned.count false) st st' hprop (Nat.le_refl _) hrun

private theorem propagate_aux_sameFC :
    ∀ (n : Nat) (s₀ st st' : CheckState),
      SameFC s₀ st →
      st.propQueue.size + st.isAssigned.count false ≤ n →
      propagate.aux st = .ok none st' →
      SameFC s₀ st' := by
  intro n
  induction n with
  | zero =>
    intro s₀ st st' hsame hn hrun
    have hempty : st.propQueue.isEmpty = true := by
      simp only [Array.isEmpty_iff_size_eq_zero]
      omega
    rw [propagate.aux.eq_def, if_pos hempty] at hrun
    cases hrun
    exact hsame
  | succ n ih =>
    intro s₀ st st' hsame hn hrun
    by_cases hempty : st.propQueue.isEmpty = true
    · rw [propagate.aux.eq_def, if_pos hempty] at hrun
      cases hrun
      exact hsame
    · rw [propagate.aux.eq_def,
        if_neg (show ¬ st.propQueue.isEmpty = true by simpa using hempty)] at hrun
      simp only [] at hrun
      have hsame₁ : SameFC s₀ { st with propQueue := st.propQueue.pop } := by
        simpa [SameFC] using hsame
      have hspec := propagateOne_sameFC_spec
          (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩) s₀
      specialize hspec { st with propQueue := st.propQueue.pop } hsame₁
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
      cases he : (propagateOne (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩))
          { st with propQueue := st.propQueue.pop } with
      | error e s =>
        rw [he] at hspec
        exact hspec.elim
      | ok r s =>
        rw [he] at hspec
        cases r with
        | some cref =>
          rw [he] at hrun
          cases hrun
        | none =>
          rw [he] at hrun
          simp only [] at hrun
          have hn₂ : s.propQueue.size + s.isAssigned.count false ≤ n := by
            have hmeas := propagateOne_measure_spec
                (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
                ({ st with propQueue := st.propQueue.pop }.propQueue.size +
                 { st with propQueue := st.propQueue.pop }.isAssigned.count false)
            specialize hmeas { st with propQueue := st.propQueue.pop } rfl
            simp only [WP.wp, PredTrans.apply, EStateM.run] at hmeas
            simp only [he] at hmeas
            have hne : st.propQueue.size ≠ 0 :=
              fun h =>
                let hq : st.propQueue = #[] := Array.eq_empty_of_size_eq_zero h
                hempty (by simp [hq])
            have hpos : 0 < st.propQueue.size := Nat.pos_iff_ne_zero.mpr hne
            have hmeas_eq : s.propQueue.size + Array.count false s.isAssigned =
                st.propQueue.pop.size + Array.count false st.isAssigned := hmeas
            have hpop : st.propQueue.pop.size = st.propQueue.size - 1 := by
              simp [Array.size_pop]
            omega
          exact ih s₀ s st' hspec hn₂ hrun

theorem propagate_none_sameFC {s₀ st st' : CheckState}
    (hsame : SameFC s₀ st)
    (hrun : propagate st = .ok none st') :
    SameFC s₀ st' := by
  exact propagate_aux_sameFC
    (st.propQueue.size + st.isAssigned.count false) s₀ st st' hsame (Nat.le_refl _) hrun

private theorem propagate_aux_sameFC_any :
    ∀ (n : Nat) (s₀ st : CheckState) (r : Option CRef) (st' : CheckState),
      SameFC s₀ st →
      st.propQueue.size + st.isAssigned.count false ≤ n →
      propagate.aux st = .ok r st' →
      SameFC s₀ st' := by
  intro n
  induction n with
  | zero =>
    intro s₀ st r st' hsame hn hrun
    have hempty : st.propQueue.isEmpty = true := by
      simp only [Array.isEmpty_iff_size_eq_zero]
      omega
    rw [propagate.aux.eq_def, if_pos hempty] at hrun
    cases hrun
    exact hsame
  | succ n ih =>
    intro s₀ st r st' hsame hn hrun
    by_cases hempty : st.propQueue.isEmpty = true
    · rw [propagate.aux.eq_def, if_pos hempty] at hrun
      cases hrun
      exact hsame
    · rw [propagate.aux.eq_def,
        if_neg (show ¬ st.propQueue.isEmpty = true by simpa using hempty)] at hrun
      simp only [] at hrun
      have hsame₁ : SameFC s₀ { st with propQueue := st.propQueue.pop } := by
        simpa [SameFC] using hsame
      have hspec := propagateOne_sameFC_spec
          (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩) s₀
      specialize hspec { st with propQueue := st.propQueue.pop } hsame₁
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
      cases he : (propagateOne (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩))
          { st with propQueue := st.propQueue.pop } with
      | error e s =>
        rw [he] at hspec
        exact hspec.elim
      | ok r₁ s =>
        rw [he] at hspec
        cases r₁ with
        | some cref =>
          rw [he] at hrun
          cases hrun
          exact hspec
        | none =>
          rw [he] at hrun
          simp only [] at hrun
          have hn₂ : s.propQueue.size + s.isAssigned.count false ≤ n := by
            have hmeas := propagateOne_measure_spec
                (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
                ({ st with propQueue := st.propQueue.pop }.propQueue.size +
                 { st with propQueue := st.propQueue.pop }.isAssigned.count false)
            specialize hmeas { st with propQueue := st.propQueue.pop } rfl
            simp only [WP.wp, PredTrans.apply, EStateM.run] at hmeas
            simp only [he] at hmeas
            have hne : st.propQueue.size ≠ 0 :=
              fun h =>
                let hq : st.propQueue = #[] := Array.eq_empty_of_size_eq_zero h
                hempty (by simp [hq])
            have hpos : 0 < st.propQueue.size := Nat.pos_iff_ne_zero.mpr hne
            have hmeas_eq : s.propQueue.size + Array.count false s.isAssigned =
                st.propQueue.pop.size + Array.count false st.isAssigned := hmeas
            have hpop : st.propQueue.pop.size = st.propQueue.size - 1 := by
              simp [Array.size_pop]
            omega
          exact ih s₀ s r st' hspec hn₂ hrun

theorem propagate_sameFC_spec (s₀ : CheckState) :
    ⦃fun s => ⌜SameFC s₀ s⌝⦄
    (propagate : CheckM (Option CRef))
    ⦃⇓? _ s' => ⌜SameFC s₀ s'⌝⦄ := by
  intro st hsame
  cases hrun : propagate st with
  | error e s' =>
    simp only [WP.wp, PredTrans.apply, EStateM.run, hrun]
    trivial
  | ok r s' =>
    simp only [WP.wp, PredTrans.apply, EStateM.run, hrun]
    exact propagate_aux_sameFC_any
      (st.propQueue.size + st.isAssigned.count false) s₀ st r s' hsame (Nat.le_refl _) hrun



/-- `@[spec]` for `propagate`: preserves `CheckState.ConsistentWith` and always returns
    `none` (no conflict) when the model satisfies all clauses.
    Proved by well-founded induction on the propagation measure via
    `propagateOne_consistent_spec`. -/
@[spec]
theorem propagate_consistent_spec
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment) (sk : SkolemAssignment)
    (hmat : cs.matrixValue f σ sk = true) :
    ⦃fun s => ⌜CheckState.ConsistentWith f cs σ sk s⌝⦄
    (propagate : CheckM (Option CRef))
    ⦃⇓ r s' => ⌜CheckState.ConsistentWith f cs σ sk s' ∧ r = none⌝⦄ := by
  intro s h_con
  obtain ⟨st', haux, h_con'⟩ := propagate_aux_consistent f cs σ sk hmat
      (s.propQueue.size + s.isAssigned.count false) s h_con (Nat.le_refl _)
  simp only [WP.wp, PredTrans.apply, EStateM.run, propagate, haux]
  exact ⟨h_con', trivial⟩

@[spec]
theorem newDecisionLevel_consistent_spec
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment) (sk : SkolemAssignment) :
    ⦃fun s => ⌜CheckState.ConsistentWith f cs σ sk s⌝⦄
    (newDecisionLevel : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.ConsistentWith f cs σ sk s'⌝⦄ := by
  intro s h_con
  simp only [WP.wp, PredTrans.apply, EStateM.run, newDecisionLevel, EStateM.modifyGet,
             EStateM.set]
  refine ⟨?_, h_con.formula_eq, h_con.clauses_eq, h_con.clauses_wf, h_con.assigned_model,
            h_con.queue_model⟩
  refine ⟨h_con.toSound.isAssigned_size, h_con.toSound.value_size,
         h_con.toSound.indepKnown_size, h_con.toSound.indepOf_size,
         h_con.toSound.externalName_size, h_con.toSound.isExistential_size,
         h_con.toSound.depset_size, h_con.toSound.clauses_nonempty,
         by simp [Array.size_push], ?_, ?_⟩
  · simp
    intro i hi lit hlit
    by_cases eq : i = s.trail.size
    · simp [eq] at hlit
    · have := h_con.trail_lits_valid i (by lia) lit
      rw [Array.getElem?_push_lt (by lia), Option.getD_some] at hlit
      rw [← Array.getElem_eq_getD] at this
      · exact this hlit
      · lia
  · simp
    intro v hv1 hv2
    have := h_con.assigned_iff_in_trail v hv1 hv2
    simp at this
    rw [this]
    constructor
    · rintro ⟨i, hi, l, hl1, hl2⟩
      exists i
      constructor
      · lia
      · exists l
        rw [Array.getElem?_push_lt (by lia)]
        simp
        rw [← Array.getD_eq_getD_getElem?, ← Array.getElem_eq_getD] at hl1
        · exact ⟨hl1, hl2⟩
        · lia
    · rintro ⟨i, hi, l, hl1, hl2⟩
      by_cases eq : i = s.trail.size
      · simp [eq] at hl1
      · rw [Array.getElem?_push_lt (by lia)] at hl1
        simp at hl1
        exists i
        constructor
        · lia
        · exists l
          rw [Array.getElem?_eq_getElem (by lia)]
          simp
          exact ⟨hl1, hl2⟩

theorem newDecisionLevel_sound_spec :
    ⦃fun s => ⌜CheckState.Sound s⌝⦄
    (newDecisionLevel : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Sound s'⌝⦄ := by
  intro s hsound
  simp only [WP.wp, PredTrans.apply, EStateM.run, newDecisionLevel, EStateM.modifyGet,
             EStateM.set]
  refine
    { isAssigned_size := hsound.isAssigned_size
      value_size := hsound.value_size
      indepKnown_size := hsound.indepKnown_size
      indepOf_size := hsound.indepOf_size
      externalName_size := hsound.externalName_size
      isExistential_size := hsound.isExistential_size
      depset_size := hsound.depset_size
      clauses_nonempty := hsound.clauses_nonempty
      trail_nonempty := by simp [Array.size_push]
      trail_lits_valid := ?_
      assigned_iff_in_trail := ?_ }
  · simp
    intro i hi lit hlit
    by_cases eq : i = s.trail.size
    · simp [eq] at hlit
    · have := hsound.trail_lits_valid i (by lia) lit
      rw [Array.getElem?_push_lt (by lia), Option.getD_some] at hlit
      rw [← Array.getElem_eq_getD] at this
      · exact this hlit
      · lia
  · simp
    intro v hv1 hv2
    have := hsound.assigned_iff_in_trail v hv1 hv2
    simp at this
    rw [this]
    constructor
    · rintro ⟨i, hi, l, hl1, hl2⟩
      exists i
      constructor
      · lia
      · exists l
        rw [Array.getElem?_push_lt (by lia)]
        simp
        rw [← Array.getD_eq_getD_getElem?, ← Array.getElem_eq_getD] at hl1
        · exact ⟨hl1, hl2⟩
        · lia
    · rintro ⟨i, hi, l, hl1, hl2⟩
      by_cases eq : i = s.trail.size
      · simp [eq] at hl1
      · rw [Array.getElem?_push_lt (by lia)] at hl1
        simp at hl1
        exists i
        constructor
        · lia
        · exists l
          rw [Array.getElem?_eq_getElem (by lia)]
          simp
          exact ⟨hl1, hl2⟩

theorem newDecisionLevel_sameFC_spec (s₀ : CheckState) :
    ⦃fun s => ⌜SameFC s₀ s⌝⦄
    (newDecisionLevel : CheckM Unit)
    ⦃⇓ _ s' => ⌜SameFC s₀ s'⌝⦄ := by
  intro s hsame
  rcases hsame with ⟨hformula, hclauses⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run, newDecisionLevel, EStateM.modifyGet,
             EStateM.set, SameFC]
  exact ⟨hformula, hclauses⟩

theorem backtrackBefore_sameFC_spec (level : Nat) (s₀ : CheckState) :
    ⦃fun s => ⌜SameFC s₀ s⌝⦄
    (backtrackBefore level : CheckM Unit)
    ⦃⇓ _ s' => ⌜SameFC s₀ s'⌝⦄ := by
  intro s hsame
  rcases hsame with ⟨hformula, hclauses⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run, backtrackBefore, SameFC]
  exact ⟨hformula, hclauses⟩

/-- `negateAndPropagate lits (fun _ => true)` returns `false` (no conflict) from a
    `CheckState.ConsistentWith` state when all lits are model-false: each negated literal
    is model-true, so `enqueue` + `propagate` find no conflict. -/
theorem negateAndPropagate_consistent_spec
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment) (sk : SkolemAssignment)
    (hmat : cs.matrixValue f σ sk = true)
    (lits : Array Literal) (hlits_false : ∀ l ∈ lits.toList, f.litValue σ sk l = false) :
    ⦃fun s => ⌜CheckState.ConsistentWith f cs σ sk s⌝⦄
    (negateAndPropagate lits (fun _ => true) : CheckM Bool)
    ⦃⇓ r s' => ⌜CheckState.ConsistentWith f cs σ sk s' ∧ r = false⌝⦄ := by
  mvcgen [negateAndPropagate] invariants
  · ⇓⟨_xs, b⟩ s => ⌜b = false ∧ CheckState.ConsistentWith f cs σ sk s⌝
    with simp_all [litValue_negate, satisfied_false_of_model_false,
                   List.mem_append, List.mem_cons]
  -- vc12: satisfied cur = true — contradiction (cur is model-false under ConsistentWith)
  case vc12.isFalse.isFalse.isFalse.isTrue =>
    rename_i _ _ _ _ cur _ _ _ _ _ _ _ _ _ _ h_inv _ h_sat
    simp [satisfied_false_of_model_false h_inv.2 cur
            (hlits_false cur (Or.inr (Or.inl rfl)))] at h_sat

-- ─── Main theorem ────────────────────────────────────────────────────────────

/-- **RUP soundness**: if `negateAndPropagate lits (fun _ => true)` detects a conflict
    (returns `true`) from a valid state, then adding `lits` to a true formula preserves truth.

    The hypothesis `hrup` is a Hoare triple: starting from state `st`, the computation
    returns `true`. This avoids referencing `EStateM.run` directly.

    Proof: by contradiction against `negateAndPropagate_consistent_spec`. If `lits` were
    false under some model (sk, σ) satisfying the matrix, build `ConsistentWith` and apply
    the spec: it says the computation returns `false`. But `hrup` says `true`. Contradiction. -/
theorem RUP_soundness (st : CheckState) (lits : Array Literal)
    (hsound : CheckState.Sound st)
    (hvalid : StatePreservesModels st)
    (hwf : ClausesWellFormed st.formula st.clauses)
    (hpq : st.propQueue = #[])
    (hrup : ⦃fun s => ⌜s = st⌝⦄
            (negateAndPropagate lits (fun _ => true) : CheckM Bool)
            ⦃⇓? r _ => ⌜r = true⌝⦄)
    (h : DQBFTrue st.formula st.clauses) :
    DQBFTrue st.formula (st.clauses.addClause lits).1 := by
  apply SemanticConsequence_soundness _ _ _ _ h
  intro sk σ hmat
  rcases Bool.eq_false_or_eq_true (st.formula.clauseValue σ sk lits) with h_true | h_false
  · exact h_true
  · exfalso
    -- All literals in lits are false under (σ, sk)
    have hlits_false : ∀ l ∈ lits.toList, st.formula.litValue σ sk l = false := by
      intro l hl
      rcases Bool.eq_false_or_eq_true (st.formula.litValue σ sk l) with hl_true | hl_false
      · exfalso
        have hmem : l ∈ lits := Array.mem_toList_iff.mp hl
        have ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hmem
        have hclause_true : st.formula.clauseValue σ sk lits = true := by
          simp only [DQBF.clauseValue]
          exact Array.any_eq_true.mpr ⟨i, hi, heq ▸ hl_true⟩
        rw [hclause_true] at h_false; exact absurd h_false (by decide)
      · exact hl_false
    -- Build ConsistentWith from the validity hypotheses
    have hcon : CheckState.ConsistentWith st.formula st.clauses σ sk st :=
      { toSound      := hsound
        formula_eq   := rfl
        clauses_eq   := rfl
        clauses_wf   := hwf
        assigned_model := fun v hpos hassign => hvalid v hpos hassign sk σ hmat
        queue_model  := by simp [hpq] }
    -- negateAndPropagate_consistent_spec (⇓): from ConsistentWith, returns false
    have hspec := negateAndPropagate_consistent_spec
        st.formula st.clauses σ sk hmat lits hlits_false
    specialize hspec st hcon
    simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
    -- hrup: from st, the computation returns true
    specialize hrup st rfl
    simp only [WP.wp, PredTrans.apply, EStateM.run] at hrup
    -- Case split on the computation result; spec says false, hrup says true
    cases hr : (negateAndPropagate lits (fun _ => true)) st with
    | error e s => rw [hr] at hspec; exact hspec.elim
    | ok r s    =>
      rw [hr] at hspec; rw [hr] at hrup
      exact absurd (hrup.symm.trans hspec.2) (by decide)

/-- The outer clause of clause `D` with respect to existential literal `y`:
    all literals `l ∈ D` such that `l.var` is an outer variable of `y.var`. -/
def outerClause (f : DQBF) (D : Array Literal) (y : Literal) : Array Literal :=
  D.filter fun l => f.isVarOuterOfExivar l.var y.var

/-- DQRAT_e condition (placeholder): clause C has the DQRAT existential property
    with pivot `y ∈ C` if for every blocker clause D containing `¬y`,
    the clause `(C \ {y}) ∪ outerClause(D, y)` is a RUP consequence of the formula. -/
def DQRAT_e_Condition (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (pivot : Literal) : Prop :=
  f.isVarExistential pivot.var
  -- TODO: formalize "∀ blocker D containing ¬pivot, (lits\{pivot}) ∪ OC(D, pivot) is RUP"

/-- **DQRATE soundness** (sorry'd):
    If C has the DQRAT_e property w.r.t. the formula, then adding C preserves truth. -/
theorem DQRATE_soundness (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (pivot : Literal)
    (_ : DQRAT_e_Condition f cs lits pivot)
    (h : DQBFTrue f cs) : DQBFTrue f (cs.addClause lits).1 := by
  sorry

/-- **DQRATU soundness** (sorry'd):
    If C has the DQRAT_u property (Mixed-EUR / D^pure variant), adding C preserves truth. -/
theorem DQRATU_soundness (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (pivot : Literal)
    (_ : URCondition f lits pivot) -- simplified; full condition involves D^pure path
    (h : DQBFTrue f cs) : DQBFTrue f (cs.addClause lits).1 := by
  sorry

private theorem checkAddUniversalStep_correct_spec
    (dqbf : DQBF) (cs : ClauseStore) (lineNum : Nat) (cv : Int)
    (r : MProd (Option (Option ProofResult)) PUnit) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (checkAddUniversalStep lineNum cv r)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
  intro s hcorr
  have hget_formula :
      (((fun x => x.formula) <$> (get : CheckM CheckState)) s) = .ok s.formula s := by
    rfl
  by_cases hneg : cv < 0
  · by_cases hex_neg : s.formula.externalVarExists (-cv).toNat = true
    · simp [checkAddUniversalStep, hneg, hex_neg, WP.wp, PredTrans.apply, EStateM.run,
        Bind.bind, EStateM.bind, hget_formula]
      exact hcorr
    · simp [checkAddUniversalStep, hneg, hex_neg, WP.wp, PredTrans.apply, EStateM.run,
        Bind.bind, EStateM.bind, hget_formula]
      exact hcorr
  ·
    by_cases hex : s.formula.externalVarExists cv.toNat = true
    · simp [checkAddUniversalStep, hneg, hex, WP.wp, PredTrans.apply, EStateM.run,
        Bind.bind, EStateM.bind, hget_formula]
      exact hcorr
    · have hex_false : s.formula.externalVarExists cv.toNat = false := by
        cases hval : s.formula.externalVarExists cv.toNat <;> simp_all
      have hadd := addVarForall_correct_spec dqbf cs cv.toNat s ⟨hcorr, hex_false⟩
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hadd
      cases hrun : addVarForall cv.toNat s with
      | error e s' =>
          rw [hrun] at hadd
          exact hadd.elim
      | ok v s' =>
          rw [hrun] at hadd
          rcases hadd with ⟨hcorr', _⟩
          simpa [checkAddUniversalStep, hneg, hex_false, WP.wp, PredTrans.apply, EStateM.run,
            Bind.bind, EStateM.bind, hget_formula, hrun] using hcorr'

private theorem checkAddUniversalLoop_correct_spec
    (dqbf : DQBF) (cs : ClauseStore) (lineNum : Nat) (extVars : List Int) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (forIn extVars (MProd.mk (none : Option (Option ProofResult)) PUnit.unit)
      (checkAddUniversalStep lineNum) :
      CheckM (MProd (Option (Option ProofResult)) PUnit))
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
  refine (Spec.forIn_list_const_inv
    (xs := extVars)
    (init := MProd.mk (none : Option (Option ProofResult)) PUnit.unit)
    (f := checkAddUniversalStep lineNum)
    (inv := (⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝))
    ?_)
  intro cv r
  exact Triple.entails_wp_of_post
    (h := checkAddUniversalStep_correct_spec dqbf cs lineNum cv r)
    (by
      simp [PostCond.entails, SPred.entails, ExceptConds.entails]
      intro a s hs
      cases a <;> simpa using hs)

@[spec]
theorem checkAddUniversal_correct_spec (dqbf : DQBF) (cs : ClauseStore)
    (lineNum : Nat) (extVars : List Int) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkAddUniversal lineNum extVars
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
  intro s hcorr
  simp only [WP.wp, PredTrans.apply, EStateM.run, checkAddUniversal, Bind.bind, EStateM.bind]
  cases hloop_run :
      (forIn extVars (MProd.mk (none : Option (Option ProofResult)) PUnit.unit)
        (checkAddUniversalStep lineNum)) s with
  | error e s' =>
      have hloop := checkAddUniversalLoop_correct_spec dqbf cs lineNum extVars s hcorr
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hloop
      rw [hloop_run] at hloop
      exact hloop.elim
  | ok r s' =>
      have hloop := checkAddUniversalLoop_correct_spec dqbf cs lineNum extVars s hcorr
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hloop
      rw [hloop_run] at hloop
      cases hres : r.fst with
      | none =>
          have hreset := resetPropagationState_correct_spec dqbf cs s' hloop
          simp only [WP.wp, PredTrans.apply, EStateM.run] at hreset
          simp [WP.wp, PredTrans.apply, EStateM.run, Bind.bind, EStateM.bind,
            EStateM.pure]
          simpa [hres] using hreset
      | some res =>
          simp [WP.wp, PredTrans.apply, EStateM.run, Bind.bind, EStateM.bind,
            EStateM.pure]
          simpa [hres] using hloop

@[spec]
theorem checkDeleteClause_correct_spec (dqbf : DQBF) (cs : ClauseStore)
    (lineNum : Nat) (extLits : List Int) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkDeleteClause lineNum extLits
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
  intro s hcorr
  have htrans := translateExistingLits_spec dqbf cs extLits s hcorr
  simp only [WP.wp, PredTrans.apply, EStateM.run] at htrans
  cases hrunTrans : translateExistingLits extLits s with
  | error e s' =>
      rw [hrunTrans] at htrans
      exact htrans.elim
  | ok lits s₁ =>
      rw [hrunTrans] at htrans
      rcases htrans with ⟨hcorr₁, hlits⟩
      have hget : (get : CheckM CheckState) = EStateM.get := rfl
      simp only [WP.wp, PredTrans.apply, EStateM.run, checkDeleteClause, Bind.bind,
        EStateM.bind, hrunTrans, hget]
      cases hfind : s₁.clauses.findSortedClause (ClauseStore.sortLits lits) with
      | none =>
          simp [hfind, EStateM.get, EStateM.pure]
          exact hcorr₁
      | some cref =>
          simp [hfind, EStateM.get, EStateM.pure, resetPropagationState_run]
          exact CheckState.Correct.withDeleteClauseReset hcorr₁

-- ─── Section 7: Overall Checker Soundness Stub (full checker, all rules) ────

-- ─── Section 7: Overall Checker Soundness Stub ───────────────────────────────

/-- **Main soundness theorem** (sorry'd):
    If `processProof` returns `.Verified`, then the input formula is false.

    This connects the imperative checker (`CheckState`, `processProof`) to the
    semantic definitions (`DQBFFalse`, `DQBFTrue`).

    The full proof would proceed by induction on the proof steps and appeal to:
    - `DQBFTrue.delete_clause` for DEL steps
    - `UR_soundness` for UR steps
    - `DQRATE_soundness` / `DQRATU_soundness` for DQRATE / DQRATU steps
    - `DQBFFalse.of_empty_clause` for the final refutation step. -/
theorem processProof_sound (st : CheckState) (proofContent : String) (n : Nat) :
    processProof st proofContent = .Verified n →
    DQBFFalse st.formula st.clauses := by
  sorry

-- ─── Checker soundness theorems ───────────────────────────────────────────────

/-- **Single-action soundness** (sorry'd):
    `checkAction` preserves `Correct` and, when it returns `Verified`, witnesses
    that the current formula is unsatisfiable.

    Proof plan: case-split on the constructor of `action`; for each case:
    - Structural parts of `Correct` follow from the `@[spec]` lemmas for the primitives.
    - `formula_sound` follows from the appropriate soundness theorem
      (DEL: `DQBFTrue.delete_clause`; RUP: `RUP_soundness`; UR: `DQRATU_soundness`;
       DQRATE: `DQRATE_soundness`).
    - `Verified` is only returned when `addClause` detects an empty clause by UP,
      giving `DQBFFalse` via `DQBFFalse.of_empty_clause`. -/
theorem checkAction_sound (dqbf : DQBF) (cs : ClauseStore) (action : DQRatAction) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkAction action
    ⦃⇓ res s' => ⌜CheckState.Correct dqbf cs s' ∧
                  ((∃ n, res = some (.Verified n)) → DQBFFalse s'.formula s'.clauses)⌝⦄ := by
  sorry

/-- **Action-list soundness** (sorry'd):
    `checkActions` preserves `Correct` by induction on the action list,
    with the `Verified` case propagating `DQBFFalse` from `checkAction_sound`. -/
theorem checkActions_sound (dqbf : DQBF) (cs : ClauseStore) (actions : List DQRatAction) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkActions actions
    ⦃⇓ r s' => ⌜CheckState.Correct dqbf cs s' ∧
                (∃ n, r = .Verified n → DQBFFalse s'.formula s'.clauses)⌝⦄ := by
  sorry

/-- **Initial state is Correct** (sorry'd):
    The `CheckState` returned by `parseDQDIMACS` satisfies `Correct` with respect
    to its own formula and clauses, whenever parsing succeeds (no UP conflict). -/
theorem parseDQDIMACS_correct (content : String) (st : CheckState)
    (h : parseDQDIMACS content = .ok (some st)) :
    CheckState.Correct st.formula st.clauses st := by
  sorry

/-- **Improved main soundness theorem** (sorry'd):
    If the checker verifies a proof, the input formula is unsatisfiable.

    This now follows from `checkActions_sound` + `parseDQDIMACS_correct`:
    1. `parseDQDIMACS` gives `Correct st.formula st.clauses st`.
    2. `checkActions_sound` shows `Correct` is maintained and `Verified` → `DQBFFalse`.
    3. `DQBFFalse st.formula st.clauses` is the desired conclusion. -/
theorem processProof_sound' (content formulaContent : String) (n : Nat)
    (st : CheckState) (hparse : parseDQDIMACS formulaContent = .ok (some st))
    (hverify : processProof st content = .Verified n) :
    DQBFFalse st.formula st.clauses := by
  sorry

-- ─── Section 8: Soundness of `checkActionsBasic` ─────────────────────────────

/-!
## Section 8: Soundness of `checkActionsBasic` (RUP + simple UR only)

Proves `checkActionsBasic` sound via Hoare triples maintaining `CheckState.Correct`
as the loop invariant. The main theorem is `checkActionsBasic_sound`.

Proof architecture (two-level invariant):
- **Inter-action**: `CheckState.Correct dqbf cs st` — maintained at entry/exit of each action
- **Intra-action**: `CheckState.ConsistentWith f cs σ sk st` — used inside `addClause` to
  show UP cannot conflict when the model satisfies all clauses.

Key helper specs:
- **H1** `negateAndPropagate_rup_spec`: RUP soundness as `@[spec]`
- **H2** `negateAndPropagate_backtrack_correct`: after `negateAndPropagate + backtrackBefore 1`,
  `Correct` is restored
- **H3** `ConsistentWith.of_addClause_lits`: `ConsistentWith` preserved when adding a
  model-true clause
- **H4** `addClause_sound_spec`: result-dependent soundness for `addClause`
-/

private theorem newDecisionLevel_trial_spec
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState) :
    ⦃fun s => ⌜s = s₀ ∧ CheckState.Correct dqbf cs s⌝⦄
    (newDecisionLevel : CheckM Unit)
    ⦃⇓ _ s' => ⌜TrialState s₀ s'⌝⦄ := by
  intro s hs
  rcases hs with ⟨rfl, hcorr⟩
  have hsound := (newDecisionLevel_sound_spec (s := s) hcorr.toSound)
  have hsame := (newDecisionLevel_sameFC_spec s (s := s) ⟨rfl, rfl⟩)
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hsound hsame
  refine
    { toSound := hsound
      sameFC := hsame
      trail_two_levels := by simpa [hcorr.trail_single_level]
      base_level_eq := by
        rw [Array.getD_eq_getD_getElem?]
        rw [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_push_lt (by simpa [hcorr.trail_single_level])]
        rw [Array.getElem?_eq_getElem (by simpa [hcorr.trail_single_level])]
      level1_fresh := ?_
      base_values_preserved := ?_ }
  · intro l hl
    have hempty : (s.trail.push #[]).getD 1 #[] = (#[] : Array Literal) := by
      rw [Array.getD_eq_getD_getElem?]
      simpa [hcorr.trail_single_level] using
        (Array.getElem?_push_size (xs := s.trail) (x := (#[] : Array Literal)))
    have : l ∈ (#[] : Array Literal) := by simpa [hempty] using hl
    simp at this
  · intro v hpos hassign
    rfl

private def clearAssigned (ia : Array Bool) (l : Literal) : Array Bool :=
  let v := l.var
  if v > 0 then ia.setIfInBounds (v - 1) false else ia

private theorem clearAssigned_getD_ne
    (ia : Array Bool) (l : Literal) {v : Var}
    (hv : 0 < v) (hneq : l.var ≠ v) :
    (clearAssigned ia l).getD (v - 1) false = ia.getD (v - 1) false := by
  unfold clearAssigned
  by_cases hpos : 0 < l.var
  · have hsubneq : l.var - 1 ≠ v - 1 := by
      intro h
      apply hneq
      have h' := congrArg (fun n => n + 1) h
      simpa [Nat.sub_add_cancel hpos, Nat.sub_add_cancel hv] using h'
    simpa [hpos] using arraySafeSet_getD_ne' ia (l.var - 1) (v - 1) false hsubneq
  · simp [hpos]

private theorem clearAssigned_getD_eq_false
    (ia : Array Bool) (l : Literal) {v : Var}
    (hv : 0 < v) (heq : l.var = v) :
    (clearAssigned ia l).getD (v - 1) false = false := by
  unfold clearAssigned
  subst heq
  by_cases hlt : l.var - 1 < ia.size
  · rw [if_pos hv]
    exact arraySetIfInBounds_getD_eq ia (l.var - 1) false false hlt
  · rw [if_pos hv]
    simp [Array.getD, hlt, Array.setIfInBounds_def]

private theorem clearAssigned_size
    (ia : Array Bool) (l : Literal) :
    (clearAssigned ia l).size = ia.size := by
  unfold clearAssigned
  by_cases hpos : 0 < l.var
  · simp [hpos, Array.size_setIfInBounds]
  · simp [hpos]

private theorem clearLevel_size
    (lvl : List Literal) (ia : Array Bool) :
    (lvl.foldl clearAssigned ia).size = ia.size := by
  induction lvl generalizing ia with
  | nil =>
      rfl
  | cons l ls ih =>
      rw [List.foldl_cons, ih, clearAssigned_size]

private theorem clearLevel_preserves_false
    (lvl : List Literal) (ia : Array Bool) {v : Var}
    (hv : 0 < v) (hinit : ia.getD (v - 1) false = false) :
    (lvl.foldl clearAssigned ia).getD (v - 1) false = false := by
  induction lvl generalizing ia with
  | nil =>
      simpa using hinit
  | cons l ls ih =>
      rw [List.foldl_cons]
      have hnext : (clearAssigned ia l).getD (v - 1) false = false := by
        by_cases heq : l.var = v
        · exact clearAssigned_getD_eq_false ia l hv heq
        · rw [clearAssigned_getD_ne ia l hv heq]
          exact hinit
      exact ih _ hnext

private theorem clearLevel_getD_of_not_mem
    (lvl : List Literal) (ia : Array Bool) {v : Var}
    (hv : 0 < v)
    (hnot : ∀ l ∈ lvl, l.var ≠ v) :
    (lvl.foldl clearAssigned ia).getD (v - 1) false = ia.getD (v - 1) false := by
  induction lvl generalizing ia with
  | nil =>
      rfl
  | cons l ls ih =>
      rw [List.foldl_cons]
      have hneq : l.var ≠ v := hnot l (by simp)
      have hnot' : ∀ l' ∈ ls, l'.var ≠ v := by
        intro l' hl'
        exact hnot l' (by simp [hl'])
      rw [ih (clearAssigned ia l) hnot']
      exact clearAssigned_getD_ne ia l hv hneq

private theorem clearLevel_getD_false_of_mem
    (lvl : List Literal) (ia : Array Bool) {v : Var}
    (hv : 0 < v)
    (hmem : ∃ l, l ∈ lvl ∧ l.var = v) :
    (lvl.foldl clearAssigned ia).getD (v - 1) false = false := by
  induction lvl generalizing ia with
  | nil =>
      rcases hmem with ⟨_, hmem, _⟩
      simp at hmem
  | cons a ls ih =>
      rw [List.foldl_cons]
      rcases hmem with ⟨l', hlmem, hlvar⟩
      simp at hlmem
      rcases hlmem with hhead | htail
      · have hfirst : (clearAssigned ia a).getD (v - 1) false = false :=
          by
            subst l'
            exact clearAssigned_getD_eq_false ia a hv hlvar
        exact clearLevel_preserves_false ls (clearAssigned ia a) hv hfirst
      · exact ih (clearAssigned ia a) ⟨l', htail, hlvar⟩

private theorem TrialState.clearedAssigned_iff_baseAssigned
    {dqbf : DQBF} {cs : ClauseStore} {s₀ s : CheckState}
    (hcorr₀ : CheckState.Correct dqbf cs s₀)
    (htrial : TrialState s₀ s)
    {v : Var} (hpos : 0 < v) :
    ((s.trail.getD 1 #[]).foldl clearAssigned s.isAssigned).getD (v - 1) false = true ↔
      s₀.isAssigned.getD (v - 1) false = true := by
  constructor
  · intro hclear
    by_cases hmem1 : ∃ l, l ∈ (s.trail.getD 1 #[]).toList ∧ l.var = v
    · have hfalse :
          ((s.trail.getD 1 #[]).foldl clearAssigned s.isAssigned).getD (v - 1) false = false := by
        rw [← Array.foldl_toList]
        exact clearLevel_getD_false_of_mem ((s.trail.getD 1 #[]).toList) s.isAssigned hpos hmem1
      rw [hfalse] at hclear
      cases hclear
    · have hnot1 : ∀ l ∈ (s.trail.getD 1 #[]).toList, l.var ≠ v := by
        intro l hl hv
        exact hmem1 ⟨l, hl, hv⟩
      have hassigned : s.isAssigned.getD (v - 1) false = true := by
        have hsame :
            ((s.trail.getD 1 #[]).foldl clearAssigned s.isAssigned).getD (v - 1) false =
              s.isAssigned.getD (v - 1) false := by
          rw [← Array.foldl_toList]
          exact clearLevel_getD_of_not_mem ((s.trail.getD 1 #[]).toList) s.isAssigned hpos hnot1
        rw [hsame] at hclear
        exact hclear
      have hlt : v - 1 < s.isAssigned.size := arrayGetD_true_imp_lt (a := s.isAssigned) hassigned
      have hle : v ≤ s.formula.maxVar := by
        rw [htrial.toSound.isAssigned_size] at hlt
        have hle' : v - 1 + 1 ≤ s.formula.maxVar := Nat.succ_le_of_lt hlt
        simpa [Nat.sub_add_cancel hpos] using hle'
      obtain ⟨i, hi, l, hl, hlvar⟩ := (htrial.assigned_iff_in_trail v hpos hle).mp hassigned
      have hi01 : i = 0 ∨ i = 1 := by
        rw [htrial.trail_two_levels] at hi
        omega
      cases hi01 with
      | inl hi0 =>
          subst hi0
          have hl₀ : l ∈ s₀.trail.getD 0 #[] := by
            simpa [htrial.base_level_eq] using hl
          have hle₀ : v ≤ s₀.formula.maxVar := by
            rcases htrial.sameFC with ⟨hformula, _⟩
            simpa [hformula] using hle
          exact (hcorr₀.assigned_iff_in_trail v hpos hle₀).mpr
            ⟨0, by simpa [hcorr₀.trail_single_level], l, hl₀, hlvar⟩
      | inr hi1 =>
          subst hi1
          exact False.elim <| hmem1 ⟨l, Array.mem_toList_iff.mpr hl, hlvar⟩
  · intro hassign₀
    have hassigned : s.isAssigned.getD (v - 1) false = true :=
      TrialState.baseAssigned_stillAssigned hcorr₀ htrial hpos hassign₀
    have hnot1 : ∀ l ∈ (s.trail.getD 1 #[]).toList, l.var ≠ v := by
      intro l hl hv
      have hfresh := htrial.level1_fresh l (Array.mem_toList_iff.mp hl)
      rw [hv, hassign₀] at hfresh
      cases hfresh
    have hsame :
        ((s.trail.getD 1 #[]).foldl clearAssigned s.isAssigned).getD (v - 1) false =
          s.isAssigned.getD (v - 1) false := by
      rw [← Array.foldl_toList]
      exact clearLevel_getD_of_not_mem ((s.trail.getD 1 #[]).toList) s.isAssigned hpos hnot1
    rw [hsame]
    exact hassigned

private theorem backtrackBefore_trial_correct_spec
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s⌝⦄
    (backtrackBefore 1 : CheckM Unit)
    ⦃⇓ _ s' => ⌜CheckState.Correct dqbf cs s' ∧ SameFC s₀ s'⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr₀, htrial⟩
  let s' : CheckState :=
    { s with
      trail := s.trail.pop
      isAssigned := (s.trail.getD 1 #[]).foldl clearAssigned s.isAssigned
      propQueue := #[] }
  have hclearLevels :
      backtrackBefore.clearLevels 1 s.trail s.isAssigned =
        (s.trail.pop, (s.trail.getD 1 #[]).foldl clearAssigned s.isAssigned) := by
    rw [backtrackBefore.clearLevels.eq_def]
    have hstop₀ : ¬ s.trail.size ≤ 1 := by
      simpa [htrial.trail_two_levels]
    rw [if_neg hstop₀]
    rw [backtrackBefore.clearLevels.eq_def]
    have hstop₁ : s.trail.pop.size ≤ 1 := by
      simpa [htrial.trail_two_levels]
    rw [if_pos hstop₁]
    have hlast : s.trail.getD (s.trail.size - 1) #[] = s.trail.getD 1 #[] := by
      simpa [htrial.trail_two_levels]
    simp [hlast]
    have hclearFun :
        (fun acc (l : Literal) =>
          if 0 < l.var then acc.setIfInBounds (l.var - 1) false else acc) = clearAssigned := by
      funext acc l
      simp [clearAssigned]
    rw [hclearFun]
  have hrun : backtrackBefore 1 s = .ok () s' := by
    simpa using
      (show EStateM.run (backtrackBefore 1) s = .ok () s' from by
        simp [backtrackBefore, s', hclearLevels])
  have hsame' := backtrackBefore_sameFC_spec 1 s₀
  specialize hsame' s htrial.sameFC
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hsame'
  rw [hrun] at hsame'
  rcases hsame' with ⟨hformula', hclauses'⟩
  have hpop0 : s.trail.pop.getD 0 #[] = s.trail.getD 0 #[] := by
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
    simp [htrial.trail_two_levels]
  have hcorr' : CheckState.Correct dqbf cs s' := by
    refine
      { toSound := ?_
        propQueue_empty := by simp [s']
        trail_single_level := by simp [s', htrial.trail_two_levels]
        clauses_wf := by simpa [hformula', hclauses'] using hcorr₀.clauses_wf
        formula_extends := by simpa [hformula'] using hcorr₀.formula_extends
        preserves_models := ?_
        formula_sound := ?_
        lookupInternal_sound := ?_ }
    · refine
        { isAssigned_size := by
            rw [show ((s.trail.getD 1 #[]).foldl clearAssigned s.isAssigned).size = s.isAssigned.size by
              rw [← Array.foldl_toList]
              exact clearLevel_size ((s.trail.getD 1 #[]).toList) s.isAssigned]
            exact htrial.toSound.isAssigned_size
          value_size := by
            simp [s', htrial.toSound.value_size]
          indepKnown_size := by
            simp [s', htrial.toSound.indepKnown_size]
          indepOf_size := by
            simp [s', htrial.toSound.indepOf_size]
          externalName_size := by
            simpa [hformula'] using hcorr₀.toSound.externalName_size
          isExistential_size := by
            simpa [hformula'] using hcorr₀.toSound.isExistential_size
          depset_size := by
            simpa [hformula'] using hcorr₀.toSound.depset_size
          clauses_nonempty := by
            simpa [hclauses'] using hcorr₀.toSound.clauses_nonempty
          trail_nonempty := by
            simp [s', htrial.trail_two_levels]
          trail_lits_valid := ?_
          assigned_iff_in_trail := ?_ }
      · intro i hi l hl
        have hi0 : i = 0 := by
          simpa [s', htrial.trail_two_levels] using hi
        subst hi0
        have hl0 : l ∈ s.trail.getD 0 #[] := by
          simpa [s', hpop0] using hl
        exact htrial.trail_lits_valid 0 (by simpa [htrial.trail_two_levels]) l hl0
      · intro v hpos hle
        have hle₀ : v ≤ s₀.formula.maxVar := by
          simpa [hformula'] using hle
        constructor
        · intro hassign
          have hassign₀ :=
            (TrialState.clearedAssigned_iff_baseAssigned hcorr₀ htrial hpos).mp <| by
              simpa [s'] using hassign
          obtain ⟨i, hi, l, hl, hlvar⟩ := (hcorr₀.assigned_iff_in_trail v hpos hle₀).mp hassign₀
          have hi0 : i = 0 := by
            simpa [hcorr₀.trail_single_level] using hi
          subst hi0
          have hl_s : l ∈ s.trail.getD 0 #[] := by
            simpa [htrial.base_level_eq] using hl
          refine ⟨0, by simpa [s', htrial.trail_two_levels], l, ?_, hlvar⟩
          simpa [s', hpop0] using hl_s
        · intro hmem
          rcases hmem with ⟨i, hi, l, hl, hlvar⟩
          have hi0 : i = 0 := by
            simpa [s', htrial.trail_two_levels] using hi
          subst hi0
          have hl_s : l ∈ s.trail.getD 0 #[] := by
            simpa [s', hpop0] using hl
          have hl₀ : l ∈ s₀.trail.getD 0 #[] := by
            simpa [htrial.base_level_eq] using hl_s
          have hassign₀ := (hcorr₀.assigned_iff_in_trail v hpos hle₀).mpr
            ⟨0, by simpa [hcorr₀.trail_single_level], l, hl₀, hlvar⟩
          have hassign :=
            (TrialState.clearedAssigned_iff_baseAssigned hcorr₀ htrial hpos).mpr hassign₀
          simpa [s'] using hassign
    · intro v hpos hassign sk σ hmat
      have hassign₀ :=
        (TrialState.clearedAssigned_iff_baseAssigned hcorr₀ htrial hpos).mp <| by
          simpa [s'] using hassign
      have hmat₀ : s₀.clauses.matrixValue s₀.formula σ sk = true := by
        simpa [hformula', hclauses'] using hmat
      have hmodel₀ := hcorr₀.preserves_models v hpos hassign₀ sk σ hmat₀
      have hvalue : s.value.getD (v - 1) false = s₀.value.getD (v - 1) false :=
        htrial.base_values_preserved v hpos hassign₀
      simpa [s', htrial.sameFC.1, hvalue] using hmodel₀
    · intro htrue
      simpa [hformula', hclauses'] using hcorr₀.formula_sound htrue
    · intro ext v hlookup
      have hlookup₀ : s₀.formula.lookupInternal ext = some v := by
        simpa [hformula'] using hlookup
      simpa [hformula'] using hcorr₀.lookupInternal_sound ext v hlookup₀
  simp only [WP.wp, PredTrans.apply, EStateM.run, hrun]
  exact ⟨hcorr', ⟨hformula', hclauses'⟩⟩

private theorem enqueue_from_trial_sound_sameFC
    (s₀ : CheckState) (l : Literal) (s s' : CheckState)
    (htrial : TrialState s₀ s)
    (hrun : enqueue l s = .ok () s') :
    CheckState.Sound s' ∧ SameFC s₀ s' := by
  have hsound := enqueue_sound_spec l
  specialize hsound s htrial.toSound
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hsound
  rw [hrun] at hsound
  have hsame := enqueue_sameFC_spec l s₀
  specialize hsame s htrial.sameFC
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hsame
  rw [hrun] at hsame
  exact ⟨hsound, hsame⟩

private theorem TrialState.withPoppedQueue
    {s₀ s : CheckState} (htrial : TrialState s₀ s) :
    TrialState s₀ { s with propQueue := s.propQueue.pop } := by
  exact
    { toSound :=
        { isAssigned_size := htrial.toSound.isAssigned_size
          value_size := htrial.toSound.value_size
          indepKnown_size := htrial.toSound.indepKnown_size
          indepOf_size := htrial.toSound.indepOf_size
          externalName_size := htrial.toSound.externalName_size
          isExistential_size := htrial.toSound.isExistential_size
          depset_size := htrial.toSound.depset_size
          clauses_nonempty := htrial.toSound.clauses_nonempty
          trail_nonempty := htrial.toSound.trail_nonempty
          trail_lits_valid := htrial.toSound.trail_lits_valid
          assigned_iff_in_trail := htrial.toSound.assigned_iff_in_trail }
      sameFC := htrial.sameFC
      trail_two_levels := htrial.trail_two_levels
      base_level_eq := htrial.base_level_eq
      level1_fresh := htrial.level1_fresh
      base_values_preserved := htrial.base_values_preserved }

private theorem propagate_aux_trial_any
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState) :
    ∀ (n : Nat) (st : CheckState) (r : Option CRef) (st' : CheckState),
      CheckState.Correct dqbf cs s₀ →
      TrialState s₀ st →
      st.propQueue.size + st.isAssigned.count false ≤ n →
      propagate.aux st = .ok r st' →
      TrialState s₀ st' := by
  intro n
  induction n with
  | zero =>
      intro st r st' hcorr₀ htrial hn hrun
      have hempty : st.propQueue.isEmpty = true := by
        simp only [Array.isEmpty_iff_size_eq_zero]
        omega
      rw [propagate.aux.eq_def, if_pos hempty] at hrun
      cases hrun
      exact htrial
  | succ n ih =>
      intro st r st' hcorr₀ htrial hn hrun
      by_cases hempty : st.propQueue.isEmpty = true
      · rw [propagate.aux.eq_def, if_pos hempty] at hrun
        cases hrun
        exact htrial
      · rw [propagate.aux.eq_def,
          if_neg (show ¬ st.propQueue.isEmpty = true by simpa using hempty)] at hrun
        simp only [] at hrun
        have htrial₁ : TrialState s₀ { st with propQueue := st.propQueue.pop } :=
          htrial.withPoppedQueue
        have hspec := propagateOne_trial_spec dqbf cs s₀
            (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
        specialize hspec { st with propQueue := st.propQueue.pop } ⟨hcorr₀, htrial₁⟩
        simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
        cases he : (propagateOne (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩))
            { st with propQueue := st.propQueue.pop } with
        | error e s =>
            rw [he] at hspec
            exact hspec.elim
        | ok r₁ s =>
            rw [he] at hspec
            rcases hspec with ⟨_, htrial₂⟩
            cases r₁ with
            | some cref =>
                rw [he] at hrun
                cases hrun
                exact htrial₂
            | none =>
                rw [he] at hrun
                simp only [] at hrun
                have hn₂ : s.propQueue.size + s.isAssigned.count false ≤ n := by
                  have hmeas := propagateOne_measure_spec
                      (st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩)
                      ({ st with propQueue := st.propQueue.pop }.propQueue.size +
                       { st with propQueue := st.propQueue.pop }.isAssigned.count false)
                  specialize hmeas { st with propQueue := st.propQueue.pop } rfl
                  simp only [WP.wp, PredTrans.apply, EStateM.run] at hmeas
                  simp only [he] at hmeas
                  have hne : st.propQueue.size ≠ 0 :=
                    fun h =>
                      let hq : st.propQueue = #[] := Array.eq_empty_of_size_eq_zero h
                      hempty (by simp [hq])
                  have hpos : 0 < st.propQueue.size := Nat.pos_iff_ne_zero.mpr hne
                  have hmeas_eq : s.propQueue.size + Array.count false s.isAssigned =
                      st.propQueue.pop.size + Array.count false st.isAssigned := hmeas
                  have hpop : st.propQueue.pop.size = st.propQueue.size - 1 := by
                    simp [Array.size_pop]
                  omega
                exact ih s r st' hcorr₀ htrial₂ hn₂ hrun

private theorem propagate_trial_spec
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s⌝⦄
    (propagate : CheckM (Option CRef))
    ⦃⇓? _ s' => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s'⌝⦄ := by
  intro st hs
  rcases hs with ⟨hcorr₀, htrial⟩
  cases hrun : propagate st with
  | error e s' =>
      simp only [WP.wp, PredTrans.apply, EStateM.run, hrun]
      trivial
  | ok r s' =>
      simp only [WP.wp, PredTrans.apply, EStateM.run, hrun]
      exact ⟨hcorr₀,
        propagate_aux_trial_any dqbf cs s₀
          (st.propQueue.size + st.isAssigned.count false) st r s'
          hcorr₀ htrial (Nat.le_refl _) hrun⟩

section NegateTrialProof

private def negateAndPropagateTrueStep (conflict : Bool) (l : Literal) : CheckM Bool := do
  if conflict then
    return true
  let st ← get
  let v := l.var
  if v = 0 || v > st.formula.maxVar then
    return false
  if satisfied st l then
    return true
  else if satisfied st l.negate then
    return false
  else
    enqueue l.negate
    let cref ← propagate
    return cref.isSome

private theorem negateAndPropagateTrueStep_trial_spec
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState)
    (conflict : Bool) (l : Literal) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s⌝⦄
    (negateAndPropagateTrueStep conflict l : CheckM Bool)
    ⦃⇓? _ s' => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s'⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr₀, htrial⟩
  have hget : (get : CheckM CheckState) = EStateM.get := rfl
  cases conflict with
  | true =>
      have hrun : negateAndPropagateTrueStep true l s = .ok true s := by
        simp [negateAndPropagateTrueStep, hget, Bind.bind, EStateM.bind, Pure.pure,
          EStateM.pure]
      simp [WP.wp, PredTrans.apply, EStateM.run]
      rw [hrun]
      simp
      exact ⟨hcorr₀, htrial⟩
  | false =>
      by_cases hbad : l.var = 0 ∨ l.var > s.formula.maxVar
      · have hguard : l.var = 0 ∨ s.formula.maxVar < l.var := by
          cases hbad with
          | inl h0 => exact Or.inl h0
          | inr hgt => exact Or.inr (by simpa using hgt)
        have hrun : negateAndPropagateTrueStep false l s = .ok false s := by
          simp [negateAndPropagateTrueStep, hget, hguard, Bind.bind, EStateM.bind,
            Pure.pure, EStateM.pure, EStateM.get]
        simp [WP.wp, PredTrans.apply, EStateM.run]
        rw [hrun]
        simp
        exact ⟨hcorr₀, htrial⟩
      · have hguard : ¬ (l.var = 0 ∨ s.formula.maxVar < l.var) := by
          intro h
          apply hbad
          cases h with
          | inl h0 => exact Or.inl h0
          | inr hlt => exact Or.inr (by simpa using hlt)
        by_cases hsat : satisfied s l = true
        · have hrun : negateAndPropagateTrueStep false l s = .ok true s := by
            simp [negateAndPropagateTrueStep, hget, hguard, hsat, Bind.bind, EStateM.bind,
              Pure.pure, EStateM.pure, EStateM.get]
          simp [WP.wp, PredTrans.apply, EStateM.run]
          rw [hrun]
          simp
          exact ⟨hcorr₀, htrial⟩
        · by_cases hsatNeg : satisfied s l.negate = true
          · have hrun : negateAndPropagateTrueStep false l s = .ok false s := by
              simp [negateAndPropagateTrueStep, hget, hguard, hsat, hsatNeg, Bind.bind,
                EStateM.bind, Pure.pure, EStateM.pure, EStateM.get]
            simp [WP.wp, PredTrans.apply, EStateM.run]
            rw [hrun]
            simp
            exact ⟨hcorr₀, htrial⟩
          · have henq := enqueue_trial_spec dqbf cs s₀ l.negate s ⟨hcorr₀, htrial⟩
            simp only [WP.wp, PredTrans.apply, EStateM.run] at henq
            cases henq_run : enqueue l.negate s with
            | error e s' =>
                rw [henq_run] at henq
                exact henq.elim
            | ok _ s₁ =>
                rw [henq_run] at henq
                rcases henq with ⟨hcorr₀', htrial₁⟩
                have hprop := propagate_trial_spec dqbf cs s₀ s₁ ⟨hcorr₀', htrial₁⟩
                simp only [WP.wp, PredTrans.apply, EStateM.run] at hprop
                cases hprop_run : propagate s₁ with
                | error e s' =>
                    rw [hprop_run] at hprop
                    have hrun : negateAndPropagateTrueStep false l s = .error e s' := by
                      simp [negateAndPropagateTrueStep, hget, hguard, hsat, hsatNeg, henq_run,
                        hprop_run, Bind.bind, EStateM.bind, EStateM.get, Pure.pure,
                        EStateM.pure]
                    simp [WP.wp, PredTrans.apply, EStateM.run]
                    rw [hrun]
                    simp
                | ok r s₂ =>
                    rw [hprop_run] at hprop
                    rcases hprop with ⟨hcorr₀'', htrial₂⟩
                    have hrun : negateAndPropagateTrueStep false l s = .ok r.isSome s₂ := by
                      simp [negateAndPropagateTrueStep, hget, hguard, hsat, hsatNeg, henq_run,
                        hprop_run, Bind.bind, EStateM.bind, EStateM.get, Pure.pure,
                        EStateM.pure]
                    simp [WP.wp, PredTrans.apply, EStateM.run]
                    rw [hrun]
                    simp
                    exact ⟨hcorr₀'', htrial₂⟩

private theorem negateAndPropagateTrueFold_trial_spec
    (dqbf : DQBF) (cs : ClauseStore) (s₀ : CheckState) (lits : Array Literal) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s⌝⦄
    (lits.foldlM negateAndPropagateTrueStep false : CheckM Bool)
    ⦃⇓? _ s' => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s'⌝⦄ := by
  simpa using
    (show
      ⦃fun s => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s⌝⦄
      (lits.toList.foldlM negateAndPropagateTrueStep false : CheckM Bool)
      ⦃⇓? _ s' => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s'⌝⦄ from by
        refine (Spec.foldlM_list_const_inv
          (xs := lits.toList)
          (init := false)
          (f := negateAndPropagateTrueStep)
          (inv := (⇓? _ s' => ⌜CheckState.Correct dqbf cs s₀ ∧ TrialState s₀ s'⌝))
          ?_)
        intro hd b
        simpa using
          (negateAndPropagateTrueStep_trial_spec
            (dqbf := dqbf) (cs := cs) (s₀ := s₀) (conflict := b) (l := hd)))

end NegateTrialProof

-- ─── Formula/clauses preservation lemmas ─────────────────────────────────────

-- ─── H3: ConsistentWith preserved when adding a model-true clause ─────────────

/-- **H3**: Extending the clause store with a clause that the model satisfies
    preserves `ConsistentWith`.

    When `addClause` modifies `st.clauses` to `(cs.addClause lits).1`, if the model
    `(σ, sk)` satisfies `lits` (i.e., `f.clauseValue σ sk lits = true`), then the
    new state is consistent with `(σ, sk)` for the extended clause store.

    Proof: straightforward from `ConsistentWith` fields.
    - `formula_eq`, `clauses_eq`, `assigned_model`, `queue_model` are transferred directly.
    - `clauses_eq` becomes `st.clauses = (cs.addClause lits).1` by assumption.
    - The matrix value for the extended store holds because old clauses are satisfied
      (by `hcon.clauses_eq ▸ hmat`) and the new clause is satisfied (`hclause`). -/
theorem CheckState.ConsistentWith.of_addClause_lits
    (f : DQBF) (cs : ClauseStore) (lits : Array Literal)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hclause : f.clauseValue σ sk lits = true)
    (hwf : ClausesWellFormed f (cs.addClause lits).1)
    (hcon : CheckState.ConsistentWith f cs σ sk st) :
    CheckState.ConsistentWith f (cs.addClause lits).1 σ sk
      { st with clauses := (cs.addClause lits).1 } := by
  refine ⟨?_, hcon.formula_eq, rfl, hwf, hcon.assigned_model, hcon.queue_model⟩
  exact { isAssigned_size := hcon.toSound.isAssigned_size, value_size := hcon.toSound.value_size,
          indepKnown_size := hcon.toSound.indepKnown_size, indepOf_size := hcon.toSound.indepOf_size,
          externalName_size := hcon.toSound.externalName_size,
          isExistential_size := hcon.toSound.isExistential_size,
          depset_size := hcon.toSound.depset_size,
          clauses_nonempty := by simpa [ClauseStore.addClause] using Nat.succ_pos cs.clauses.size,
          trail_nonempty := hcon.toSound.trail_nonempty,
          trail_lits_valid := hcon.trail_lits_valid,
          assigned_iff_in_trail := hcon.assigned_iff_in_trail }

-- ─── H4: result-dependent soundness specs for the basic checker ──────────────

/-- Postcondition for `addClause`: a successful insertion returns to the
    action-boundary invariant, while `none` means the original formula is false. -/
def AddClausePost (dqbf : DQBF) (cs : ClauseStore)
    (r : Option CRef) (s' : CheckState) : Prop :=
  match r with
  | some _ => CheckState.Correct dqbf cs s'
  | none   => DQBFFalse dqbf cs

@[simp] theorem addClausePost_some
    (dqbf : DQBF) (cs : ClauseStore) (cref : CRef) (s' : CheckState) :
    AddClausePost dqbf cs (some cref) s' ↔ CheckState.Correct dqbf cs s' := by
  rfl

@[simp] theorem addClausePost_none
    (dqbf : DQBF) (cs : ClauseStore) (s' : CheckState) :
    AddClausePost dqbf cs none s' ↔ DQBFFalse dqbf cs := by
  rfl

theorem addClausePost_of_empty_sameFC
    {dqbf : DQBF} {cs : ClauseStore}
    {s₀ s₁ : CheckState} {lits : Array Literal}
    (hcorr : CheckState.Correct dqbf cs s₁)
    (hsame : SameFC s₀ s₁)
    (hsem : DQBFTrue dqbf cs → DQBFTrue s₀.formula (s₀.clauses.addClause lits).1)
    (hempty : lits.isEmpty = true) :
    AddClausePost dqbf cs none { s₁ with clauses := (s₁.clauses.addClause lits).1 } := by
  rw [addClausePost_none]
  apply DQBFFalse.of_sound_extension (addClause_semantics_of_sameFC hsame hsem)
  have hpos : 1 ≤ s₁.clauses.clauses.size :=
    Nat.succ_le_of_lt hcorr.toSound.clauses_nonempty
  have hsize : s₁.clauses.clauses.size < (s₁.clauses.addClause lits).1.clauses.size := by
    simp [ClauseStore.addClause]
  have hget :=
    ClauseStore.getClause_addClause_new s₁.clauses lits hcorr.toSound.clauses_nonempty
  have hlits_empty : lits = #[] := Array.isEmpty_iff.mp hempty
  refine DQBFFalse.of_empty_clause s₁.formula (s₁.clauses.addClause lits).1
    s₁.clauses.clauses.size hpos hsize ?_
  refine ⟨{ lits := lits, deleted := false }, hget, ?_⟩
  simpa [hlits_empty]

theorem addClausePost_of_store_only_sameFC
    {dqbf : DQBF} {cs : ClauseStore}
    {s₀ s₁ : CheckState} {lits : Array Literal} {cref : CRef}
    (hcorr : CheckState.Correct dqbf cs s₁)
    (hsame : SameFC s₀ s₁)
    (hlits : ClauseLitsWellFormed s₀.formula lits)
    (hsem : DQBFTrue dqbf cs → DQBFTrue s₀.formula (s₀.clauses.addClause lits).1) :
    AddClausePost dqbf cs (some cref) { s₁ with clauses := (s₁.clauses.addClause lits).1 } := by
  rw [addClausePost_some]
  refine CheckState.Correct.withAddClause hcorr
    (clauseLitsWellFormed_of_sameFC hsame hlits)
    (addClause_semantics_of_sameFC hsame hsem)

theorem clauseValue_false_of_sat_false_unassigned_empty
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {lits : Array Literal} {σ : UnivAssignment} {sk : SkolemAssignment}
    (hcorr : CheckState.Correct dqbf cs st)
    (hwf : ClauseLitsWellFormed st.formula lits)
    (hsat_false : lits.any (fun lit =>
        let v := lit.var
        v > 0 && v ≤ st.formula.maxVar &&
        st.isAssigned.getD (v - 1) false &&
        (st.value.getD (v - 1) false == lit.isPos)) = false)
    (hunassigned_empty : (lits.filter fun lit =>
        let v := lit.var
        v > 0 && v ≤ st.formula.maxVar &&
        !st.isAssigned.getD (v - 1) false).isEmpty = true)
    (hmat : st.clauses.matrixValue st.formula σ sk = true) :
    st.formula.clauseValue σ sk lits = false := by
  by_cases hclause : st.formula.clauseValue σ sk lits = false
  · exact hclause
  · exfalso
    have hclause_true : st.formula.clauseValue σ sk lits = true := by
      cases hcv : st.formula.clauseValue σ sk lits <;> simp [hcv] at hclause ⊢
    have htrue : lits.any (st.formula.litValue σ sk) = true := by
      simpa [DQBF.clauseValue] using hclause_true
    simp only [Array.any_eq_true] at htrue
    obtain ⟨i, hi, hlit_true⟩ := htrue
    have hwfl := hwf _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
    have hassigned : st.isAssigned.getD (lits[i].var - 1) false = true := by
      rcases Bool.eq_false_or_eq_true (st.isAssigned.getD (lits[i].var - 1) false) with
          hassign | hassign
      · exact hassign
      · exfalso
        have hmem : lits[i] ∈ lits.filter (fun lit =>
            let v := lit.var
            v > 0 && v ≤ st.formula.maxVar &&
            !st.isAssigned.getD (v - 1) false) := by
          exact Array.mem_filter.mpr
            ⟨Array.getElem_mem hi, by simp [hwfl.1, hwfl.2, hassign]⟩
        have hempty : lits.filter (fun lit =>
            let v := lit.var
            v > 0 && v ≤ st.formula.maxVar &&
            !st.isAssigned.getD (v - 1) false) = #[] :=
          Array.isEmpty_iff.mp hunassigned_empty
        rw [hempty] at hmem
        simp at hmem
    have hmodel := hcorr.preserves_models lits[i].var hwfl.1 hassigned sk σ hmat
    have hvarval : st.formula.varValue σ sk lits[i].var = lits[i].isPos := by
      rcases Bool.eq_false_or_eq_true lits[i].isPos with hpos | hpos <;>
        simp [DQBF.litValue, hpos] at hlit_true ⊢ <;> exact hlit_true
    have hval_eq : st.value.getD (lits[i].var - 1) false = lits[i].isPos :=
      hmodel.symm.trans hvarval
    have hsat_one : (fun lit =>
        let v := lit.var
        v > 0 && v ≤ st.formula.maxVar &&
        st.isAssigned.getD (v - 1) false &&
        (st.value.getD (v - 1) false == lit.isPos)) lits[i] = true := by
      simp [hwfl.1, hwfl.2, hassigned, hval_eq]
    have hany : lits.any (fun lit =>
        let v := lit.var
        v > 0 && v ≤ st.formula.maxVar &&
        st.isAssigned.getD (v - 1) false &&
        (st.value.getD (v - 1) false == lit.isPos)) = true :=
      Array.any_eq_true.mpr ⟨i, hi, hsat_one⟩
    rw [hany] at hsat_false
    cases hsat_false

theorem addClausePost_of_all_false_sameFC
    {dqbf : DQBF} {cs : ClauseStore}
    {s₀ s₁ : CheckState} {lits : Array Literal}
    (hcorr : CheckState.Correct dqbf cs s₁)
    (hsame : SameFC s₀ s₁)
    (hlits : ClauseLitsWellFormed s₀.formula lits)
    (hsem : DQBFTrue dqbf cs → DQBFTrue s₀.formula (s₀.clauses.addClause lits).1)
    (hsat_false : lits.any (fun lit =>
        let v := lit.var
        v > 0 && v ≤ s₁.formula.maxVar &&
        s₁.isAssigned.getD (v - 1) false &&
        (s₁.value.getD (v - 1) false == lit.isPos)) = false)
    (hunassigned_empty : (lits.filter fun lit =>
        let v := lit.var
        v > 0 && v ≤ s₁.formula.maxVar &&
        !s₁.isAssigned.getD (v - 1) false).isEmpty = true) :
    AddClausePost dqbf cs none { s₁ with clauses := (s₁.clauses.addClause lits).1 } := by
  rw [addClausePost_none]
  apply DQBFFalse.of_sound_extension (addClause_semantics_of_sameFC hsame hsem)
  intro sk
  by_cases hex : ∃ σ, s₁.clauses.matrixValue s₁.formula σ sk = false
  · rcases hex with ⟨σ, hσ⟩
    exact ⟨σ, matrixValue_addClause_false_of_old_false s₁.formula s₁.clauses lits σ sk hσ⟩
  · have hall : ∀ σ, s₁.clauses.matrixValue s₁.formula σ sk = true := by
      intro σ
      cases h : s₁.clauses.matrixValue s₁.formula σ sk <;> simp at h ⊢
      exact False.elim (hex ⟨σ, h⟩)
    let σ : UnivAssignment := fun _ => true
    have hclause_false : s₁.formula.clauseValue σ sk lits = false :=
      clauseValue_false_of_sat_false_unassigned_empty hcorr
        (clauseLitsWellFormed_of_sameFC hsame hlits)
        hsat_false hunassigned_empty (hall σ)
    refine ⟨σ, matrixValue_addClause_false_of_new_false
      s₁.formula s₁.clauses lits σ sk hcorr.toSound.clauses_nonempty hclause_false⟩

theorem addClausePost_of_unit_conflict_sameFC
    {dqbf : DQBF} {cs : ClauseStore}
    {s₀ s₁ s_enq s₂ : CheckState} {lits unassigned : Array Literal} {conflict : CRef}
    (hcorr : CheckState.Correct dqbf cs s₁)
    (hsame : SameFC s₀ s₁)
    (hlits : ClauseLitsWellFormed s₀.formula lits)
    (hsem : DQBFTrue dqbf cs → DQBFTrue s₀.formula (s₀.clauses.addClause lits).1)
    (hunassigned : unassigned = lits.filter (fun lit =>
        let v := lit.var
        v > 0 && v ≤ s₁.formula.maxVar &&
        !s₁.isAssigned.getD (v - 1) false))
    (hsat_false : lits.any (fun lit =>
        let v := lit.var
        v > 0 && v ≤ s₁.formula.maxVar &&
        s₁.isAssigned.getD (v - 1) false &&
        (s₁.value.getD (v - 1) false == lit.isPos)) = false)
    (hsize1 : unassigned.size = 1)
    (henq_run :
      enqueue (unassigned.getD 0 ⟨0⟩)
        { s₁ with clauses := (s₁.clauses.addClause lits).1 } = .ok () s_enq)
    (hprop_run : propagate s_enq = .ok (some conflict) s₂) :
    AddClausePost dqbf cs none s₂ := by
  rw [addClausePost_none]
  apply DQBFFalse.of_not_true
  intro htrue
  have htrue_ext : DQBFTrue s₁.formula (s₁.clauses.addClause lits).1 :=
    addClause_semantics_of_sameFC hsame hsem htrue
  obtain ⟨sk, hsk⟩ := htrue_ext
  let σ : UnivAssignment := fun _ => true
  have hmat_added : (s₁.clauses.addClause lits).1.matrixValue s₁.formula σ sk = true := hsk σ
  have hmat_old : s₁.clauses.matrixValue s₁.formula σ sk = true := by
    cases h : s₁.clauses.matrixValue s₁.formula σ sk <;> simp at h ⊢
    have hfalse :=
      matrixValue_addClause_false_of_old_false s₁.formula s₁.clauses lits σ sk h
    rw [hmat_added] at hfalse
    cases hfalse
  have hget :=
    ClauseStore.getClause_addClause_new s₁.clauses lits hcorr.toSound.clauses_nonempty
  have hclause_true :
      s₁.formula.clauseValue σ sk lits = true :=
    clauseValue_of_matrixValue s₁.formula (s₁.clauses.addClause lits).1 σ sk
      s₁.clauses.clauses.size { lits := lits, deleted := false } hmat_added hget
  have hcon_old : CheckState.ConsistentWith s₁.formula s₁.clauses σ sk s₁ :=
    hcorr.to_consistentWith σ sk hmat_old
  have hcon_added :
      CheckState.ConsistentWith s₁.formula (s₁.clauses.addClause lits).1 σ sk
        { s₁ with clauses := (s₁.clauses.addClause lits).1 } := by
    apply CheckState.ConsistentWith.of_addClause_lits s₁.formula s₁.clauses lits σ sk
      hclause_true
    exact hcorr.clauses_wf.addClause (clauseLitsWellFormed_of_sameFC hsame hlits)
    exact hcon_old
  have hunit_true :
      s₁.formula.litValue σ sk (unassigned.getD 0 ⟨0⟩) = true := by
    apply unit_lit_model_true s₁.formula σ sk s₁ rfl rfl
    · intro v hpos hassign
      exact hcorr.preserves_models v hpos hassign sk σ hmat_old
    · exact clauseLitsWellFormed_of_sameFC hsame hlits
    · exact hclause_true
    · exact hsat_false
    · exact hunassigned
    · exact hsize1
  have henq :=
    enqueue_consistent_spec s₁.formula (s₁.clauses.addClause lits).1 σ sk
      (unassigned.getD 0 ⟨0⟩) hunit_true
  specialize henq { s₁ with clauses := (s₁.clauses.addClause lits).1 } hcon_added
  simp only [WP.wp, PredTrans.apply, EStateM.run] at henq
  rw [henq_run] at henq
  have hprop :=
    propagate_consistent_spec s₁.formula (s₁.clauses.addClause lits).1 σ sk hmat_added
  specialize hprop s_enq henq
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hprop
  rw [hprop_run] at hprop
  cases hprop.2

theorem addClausePost_of_unit_success_sameFC
    {dqbf : DQBF} {cs : ClauseStore}
    {s₀ s₁ s_enq s₂ : CheckState} {lits unassigned : Array Literal} {cref : CRef}
    (hcorr : CheckState.Correct dqbf cs s₁)
    (hsame : SameFC s₀ s₁)
    (hlits : ClauseLitsWellFormed s₀.formula lits)
    (hsem : DQBFTrue dqbf cs → DQBFTrue s₀.formula (s₀.clauses.addClause lits).1)
    (hunassigned : unassigned = lits.filter (fun lit =>
        let v := lit.var
        v > 0 && v ≤ s₁.formula.maxVar &&
        !s₁.isAssigned.getD (v - 1) false))
    (hsat_false : lits.any (fun lit =>
        let v := lit.var
        v > 0 && v ≤ s₁.formula.maxVar &&
        s₁.isAssigned.getD (v - 1) false &&
        (s₁.value.getD (v - 1) false == lit.isPos)) = false)
    (hsize1 : unassigned.size = 1)
    (henq_run :
      enqueue (unassigned.getD 0 ⟨0⟩)
        { s₁ with clauses := (s₁.clauses.addClause lits).1 } = .ok () s_enq)
    (hprop_run : propagate s_enq = .ok none s₂) :
    AddClausePost dqbf cs (some cref) s₂ := by
  rw [addClausePost_some]
  let s_added : CheckState := { s₁ with clauses := (s₁.clauses.addClause lits).1 }
  have hprop_added : CheckState.PropStruct s_added := by
    dsimp [s_added]
    exact CheckState.PropStruct.withAddClause hcorr.toPropStruct
      (clauseLitsWellFormed_of_sameFC hsame hlits)
  have henq_prop := enqueue_propStruct_spec (unassigned.getD 0 ⟨0⟩)
  specialize henq_prop s_added hprop_added
  simp only [WP.wp, PredTrans.apply, EStateM.run] at henq_prop
  rw [henq_run] at henq_prop
  have hprop₂ : CheckState.PropStruct s₂ :=
    propagate_none_propStruct henq_prop hprop_run
  have henq_same := enqueue_sameFC_spec (unassigned.getD 0 ⟨0⟩) s_added
  specialize henq_same s_added (by exact ⟨rfl, rfl⟩)
  simp only [WP.wp, PredTrans.apply, EStateM.run] at henq_same
  rw [henq_run] at henq_same
  have hsame₂ : SameFC s_added s₂ :=
    propagate_none_sameFC henq_same hprop_run
  rcases hsame₂ with ⟨hformula₂, hclauses₂⟩
  refine
    { toSound := hprop₂.toSound
      propQueue_empty := propagate_none_queue_empty hprop_run
      trail_single_level := hprop₂.trail_single_level
      clauses_wf := hprop₂.clauses_wf
      formula_extends := by
        simpa [s_added, hformula₂] using hcorr.formula_extends
      preserves_models := ?_
      formula_sound := ?_
      lookupInternal_sound := ?_ }
  · intro v hpos hassign sk σ hmat₂
    have hmat_added : (s₁.clauses.addClause lits).1.matrixValue s₁.formula σ sk = true := by
      simpa [s_added, hformula₂, hclauses₂] using hmat₂
    have hmat_old : s₁.clauses.matrixValue s₁.formula σ sk = true := by
      cases h : s₁.clauses.matrixValue s₁.formula σ sk <;> simp at h ⊢
      have hfalse :=
        matrixValue_addClause_false_of_old_false s₁.formula s₁.clauses lits σ sk h
      rw [hmat_added] at hfalse
      cases hfalse
    have hget :=
      ClauseStore.getClause_addClause_new s₁.clauses lits hcorr.toSound.clauses_nonempty
    have hclause_true :
        s₁.formula.clauseValue σ sk lits = true :=
      clauseValue_of_matrixValue s₁.formula (s₁.clauses.addClause lits).1 σ sk
        s₁.clauses.clauses.size { lits := lits, deleted := false } hmat_added hget
    have hcon_old : CheckState.ConsistentWith s₁.formula s₁.clauses σ sk s₁ :=
      hcorr.to_consistentWith σ sk hmat_old
    have hcon_added :
        CheckState.ConsistentWith s₁.formula (s₁.clauses.addClause lits).1 σ sk s_added := by
      dsimp [s_added]
      apply CheckState.ConsistentWith.of_addClause_lits s₁.formula s₁.clauses lits σ sk
        hclause_true
      · exact hcorr.clauses_wf.addClause (clauseLitsWellFormed_of_sameFC hsame hlits)
      · exact hcon_old
    have hunit_true :
        s₁.formula.litValue σ sk (unassigned.getD 0 ⟨0⟩) = true := by
      apply unit_lit_model_true s₁.formula σ sk s₁ rfl rfl
      · intro w hwpos hassign'
        exact hcorr.preserves_models w hwpos hassign' sk σ hmat_old
      · exact clauseLitsWellFormed_of_sameFC hsame hlits
      · exact hclause_true
      · exact hsat_false
      · exact hunassigned
      · exact hsize1
    have henq :=
      enqueue_consistent_spec s₁.formula (s₁.clauses.addClause lits).1 σ sk
        (unassigned.getD 0 ⟨0⟩) hunit_true
    specialize henq s_added hcon_added
    simp only [WP.wp, PredTrans.apply, EStateM.run] at henq
    rw [henq_run] at henq
    have hprop :=
      propagate_consistent_spec s₁.formula (s₁.clauses.addClause lits).1 σ sk hmat_added
    specialize hprop s_enq henq
    simp only [WP.wp, PredTrans.apply, EStateM.run] at hprop
    rw [hprop_run] at hprop
    rcases hprop with ⟨hcon₂, _⟩
    simpa [hcon₂.formula_eq] using hcon₂.assigned_model v hpos hassign
  · intro htrue
    have htrue_added : DQBFTrue s₁.formula (s₁.clauses.addClause lits).1 :=
      addClause_semantics_of_sameFC hsame hsem htrue
    simpa [s_added, hformula₂, hclauses₂] using htrue_added
  · intro ext v hlookup
    have hlookup₁ : s₁.formula.lookupInternal ext = some v := by
      simpa [s_added, hformula₂] using hlookup
    have hv := hcorr.lookupInternal_sound ext v hlookup₁
    simpa [s_added, hformula₂] using hv

/-- Postcondition for a single basic checker step.

    Continuing (`none`) or failing leaves the checker in a boundary state.
    A `Verified` result establishes falsity of the original formula. -/
def BasicStepPost (dqbf : DQBF) (cs : ClauseStore)
    (r : Option ProofResult) (s' : CheckState) : Prop :=
  match r with
  | none => CheckState.Correct dqbf cs s'
  | some (.Verified _) => DQBFFalse dqbf cs
  | some (.Failed ..)  => CheckState.Correct dqbf cs s'
  | some .Unknown      => CheckState.Correct dqbf cs s'

@[simp] theorem basicStepPost_none
    (dqbf : DQBF) (cs : ClauseStore) (s' : CheckState) :
    BasicStepPost dqbf cs none s' ↔ CheckState.Correct dqbf cs s' := by
  rfl

@[simp] theorem basicStepPost_verified
    (dqbf : DQBF) (cs : ClauseStore) (n : Nat) (s' : CheckState) :
    BasicStepPost dqbf cs (some (.Verified n)) s' ↔ DQBFFalse dqbf cs := by
  rfl

@[simp] theorem basicStepPost_failed
    (dqbf : DQBF) (cs : ClauseStore)
    (line : Nat) (rules : Array String) (info : Array Int) (blocker : Option CRef)
    (s' : CheckState) :
    BasicStepPost dqbf cs (some (.Failed line rules info blocker)) s' ↔
      CheckState.Correct dqbf cs s' := by
  rfl

@[simp] theorem basicStepPost_unknown
    (dqbf : DQBF) (cs : ClauseStore) (s' : CheckState) :
    BasicStepPost dqbf cs (some .Unknown) s' ↔ CheckState.Correct dqbf cs s' := by
  rfl

/-- Postcondition for the basic action-list runner. -/
def BasicRunPost (dqbf : DQBF) (cs : ClauseStore)
    (r : ProofResult) (s' : CheckState) : Prop :=
  match r with
  | .Unknown      => CheckState.Correct dqbf cs s'
  | .Verified _   => DQBFFalse dqbf cs
  | .Failed ..    => CheckState.Correct dqbf cs s'

@[simp] theorem basicRunPost_unknown
    (dqbf : DQBF) (cs : ClauseStore) (s' : CheckState) :
    BasicRunPost dqbf cs .Unknown s' ↔ CheckState.Correct dqbf cs s' := by
  rfl

@[simp] theorem basicRunPost_verified
    (dqbf : DQBF) (cs : ClauseStore) (n : Nat) (s' : CheckState) :
    BasicRunPost dqbf cs (.Verified n) s' ↔ DQBFFalse dqbf cs := by
  rfl

@[simp] theorem basicRunPost_failed
    (dqbf : DQBF) (cs : ClauseStore)
    (line : Nat) (rules : Array String) (info : Array Int) (blocker : Option CRef)
    (s' : CheckState) :
    BasicRunPost dqbf cs (.Failed line rules info blocker) s' ↔
      CheckState.Correct dqbf cs s' := by
  rfl

/-- **H4**: `addClause lits` has a result-dependent postcondition.

    The precondition bundles:
    1. `Correct dqbf cs s` — the invariant holds
    2. `ClauseLitsWellFormed s.formula lits` — the inserted clause mentions only
       valid variables of the current formula
    3. `DQBFTrue dqbf cs → DQBFTrue s.formula (s.clauses.addClause lits).1` — the
       semantic precondition that adding `lits` preserves truth (the RUP/UR condition)

    When `addClause` returns `none`, one of these cases arose (all contradicting the
    semantic precondition):
    - `lits.isEmpty`: empty clause added → `DQBFFalse.of_empty_clause`
    - `unassigned.isEmpty`: all lits false under current assignment.  By
      `Correct.preserves_models` these assignments match every model, so the new
      clause is false under every model → `DQBFFalse`
    - UP conflict after unit: `propagate_consistent_spec` guarantees no conflict from
      a `ConsistentWith` state (built via H3 + model-true unit literal from H3 / `unit_lit_model_true`)
      → contradiction.

    When `addClause` returns `some cref`, `Correct dqbf cs s'` holds:
    - `formula_sound`: `DQBFTrue dqbf cs → DQBFTrue s'.formula s'.clauses` follows
      from the semantic precondition and monotonicity (`DQBFTrue.of_addClause`).
    - Structural fields: `addClause` adds exactly one clause and propagates at level 0;
      `trail_single_level`, `propQueue_empty` are preserved.
    - `preserves_models`: newly enqueued unit literal is model-forced (all other lits
      in the clause are false under model-forced assignment → only this can satisfy it). -/
theorem addClauseAfterCache_sound_spec
    (dqbf : DQBF) (cs : ClauseStore) (lits : Array Literal) (s₀ : CheckState) :
    ⦃fun s =>
      ⌜CheckState.Correct dqbf cs s ∧
       SameFC s₀ s ∧
       ClauseLitsWellFormed s₀.formula lits ∧
       (DQBFTrue dqbf cs → DQBFTrue s₀.formula (s₀.clauses.addClause lits).1)⌝⦄
    (addClauseAfterCache lits : CheckM (Option CRef))
    ⦃⇓? r s' => ⌜AddClausePost dqbf cs r s'⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr, hsame, hlits, hsem⟩
  let s_added : CheckState := { s with clauses := (s.clauses.addClause lits).1 }
  let cref : CRef := s_added.clauses.clauses.size - 1
  by_cases hempty : lits.isEmpty = true
  · simp only [WP.wp, PredTrans.apply, EStateM.run, addClauseAfterCache, hempty]
    simpa [s_added] using addClausePost_of_empty_sameFC hcorr hsame hsem hempty
  · by_cases hsat : lits.any (fun lit =>
        let v := lit.var
        v > 0 && v ≤ s.formula.maxVar &&
        s.isAssigned.getD (v - 1) false &&
        (s.value.getD (v - 1) false == lit.isPos)) = true
    · simp only [WP.wp, PredTrans.apply, EStateM.run, addClauseAfterCache, hempty, hsat]
      simpa [s_added, cref] using
        addClausePost_of_store_only_sameFC (cref := cref) hcorr hsame hlits hsem
    · have hsat_false : lits.any (fun lit =>
          let v := lit.var
          v > 0 && v ≤ s.formula.maxVar &&
          s.isAssigned.getD (v - 1) false &&
          (s.value.getD (v - 1) false == lit.isPos)) = false := by
        cases hbool : lits.any (fun lit =>
            let v := lit.var
            v > 0 && v ≤ s.formula.maxVar &&
            s.isAssigned.getD (v - 1) false &&
            (s.value.getD (v - 1) false == lit.isPos)) with
        | false =>
            simpa [hbool]
        | true =>
            exact False.elim (hsat hbool)
      by_cases hunempty : (lits.filter fun lit =>
          let v := lit.var
          v > 0 && v ≤ s.formula.maxVar &&
          !s.isAssigned.getD (v - 1) false).isEmpty = true
      ·
        simp only [WP.wp, PredTrans.apply, EStateM.run, addClauseAfterCache, hempty, hsat, hunempty]
        simpa [s_added] using
          addClausePost_of_all_false_sameFC hcorr hsame hlits hsem hsat_false hunempty
      · by_cases hsize1 : (lits.filter fun lit =>
            let v := lit.var
            v > 0 && v ≤ s.formula.maxVar &&
            !s.isAssigned.getD (v - 1) false).size = 1
        · let unassigned : Array Literal := lits.filter fun lit =>
              let v := lit.var
              v > 0 && v ≤ s.formula.maxVar &&
              !s.isAssigned.getD (v - 1) false
          have hunassigned' : unassigned = lits.filter (fun lit =>
              let v := lit.var
              v > 0 && v ≤ s.formula.maxVar &&
              !s.isAssigned.getD (v - 1) false) := by
            rfl
          have hsize1' : unassigned.size = 1 := by
            simpa [unassigned] using hsize1
          simp only [WP.wp, PredTrans.apply, EStateM.run, addClauseAfterCache, hempty, hsat, hunempty, hsize1]
          cases henq_run :
              enqueue ((lits.filter fun lit =>
                  let v := lit.var
                  v > 0 && v ≤ s.formula.maxVar &&
                  !s.isAssigned.getD (v - 1) false).getD 0 ⟨0⟩)
                { s with clauses := (s.clauses.addClause lits).1 } with
          | error e s_err =>
              simp [henq_run]
          | ok _ s_enq =>
              cases hprop_run : propagate s_enq with
              | error e s_err =>
                  simp [henq_run, hprop_run]
              | ok conflict s₂ =>
                  cases conflict with
                  | none =>
                      simp [henq_run, hprop_run]
                      simpa [unassigned] using
                        addClausePost_of_unit_success_sameFC
                          (cref := cref) (s₁ := s) (s_enq := s_enq) (s₂ := s₂)
                          (unassigned := unassigned)
                          hcorr hsame hlits hsem hunassigned' hsat_false hsize1'
                          (by simpa [unassigned] using henq_run)
                          hprop_run
                  | some conflict =>
                      simp [henq_run, hprop_run]
                      simpa [unassigned] using
                        addClausePost_of_unit_conflict_sameFC
                          (s₁ := s) (s_enq := s_enq) (s₂ := s₂)
                          (unassigned := unassigned) (conflict := conflict)
                          hcorr hsame hlits hsem hunassigned' hsat_false hsize1'
                          (by simpa [unassigned] using henq_run)
                          hprop_run
        · simp only [WP.wp, PredTrans.apply, EStateM.run, addClauseAfterCache, hempty, hsat, hunempty, hsize1]
          simpa [s_added, cref] using
            addClausePost_of_store_only_sameFC (cref := cref) hcorr hsame hlits hsem

theorem addClause_sound_spec (dqbf : DQBF) (cs : ClauseStore) (lits : Array Literal) :
    ⦃fun s =>
      ⌜CheckState.Correct dqbf cs s ∧
       ClauseLitsWellFormed s.formula lits ∧
       (DQBFTrue dqbf cs → DQBFTrue s.formula (s.clauses.addClause lits).1)⌝⦄
    (addClause lits : CheckM (Option CRef))
    ⦃⇓? r s' => ⌜AddClausePost dqbf cs r s'⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr, hlits, hsem⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run]
  have hadd :
      addClause lits s =
        match invalidateDepCaches lits s with
        | .ok _ s' => addClauseAfterCache lits s'
        | .error e s' => .error e s' := by
    unfold addClause
    cases h : invalidateDepCaches lits s with
    | ok a s' =>
        change EStateM.bind (invalidateDepCaches lits) (fun x => addClauseAfterCache lits) s =
          addClauseAfterCache lits s'
        simpa [EStateM.bind, h]
    | error e s' =>
        change EStateM.bind (invalidateDepCaches lits) (fun x => addClauseAfterCache lits) s =
          EStateM.Result.error e s'
        simpa [EStateM.bind, h]
  rw [hadd]
  have hcache := invalidateDepCaches_correct_sameFC_spec dqbf cs lits s
  specialize hcache s ⟨hcorr, by exact ⟨rfl, rfl⟩⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hcache
  cases hrun : invalidateDepCaches lits s with
  | error e s' =>
      simp [hrun]
  | ok _ s' =>
      rw [hrun] at hcache
      rcases hcache with ⟨hcorr', hsame'⟩
      have hafter := addClauseAfterCache_sound_spec dqbf cs lits s
      specialize hafter s' ⟨hcorr', hsame', hlits, hsem⟩
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hafter
      simpa [hrun] using hafter

private theorem runRupTrial_post_of_trial
    {dqbf : DQBF} {cs : ClauseStore}
    {s s₁ s₂ : CheckState} {lits : Array Literal} {isRup : Bool}
    (hcorr : CheckState.Correct dqbf cs s)
    (hlits : ClauseLitsWellFormed s.formula lits)
    (hneg_run : negateAndPropagate lits (fun _ => true) s = .ok isRup s₁)
    (htrial : TrialState s s₁)
    (hback_run : backtrackBefore 1 s₁ = .ok () s₂) :
    CheckState.Correct dqbf cs s₂ ∧
      ClauseLitsWellFormed s₂.formula lits ∧
      (isRup = true → DQBFTrue dqbf cs → DQBFTrue s₂.formula (s₂.clauses.addClause lits).1) := by
  have hback := backtrackBefore_trial_correct_spec dqbf cs s
  specialize hback s₁ ⟨hcorr, htrial⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hback
  rw [hback_run] at hback
  rcases hback with ⟨hcorr₂, hsame₂⟩
  refine ⟨hcorr₂, clauseLitsWellFormed_of_sameFC hsame₂ hlits, ?_⟩
  intro hisRup htrue
  have hrup :
      ⦃fun st => ⌜st = s⌝⦄
      (negateAndPropagate lits (fun _ => true) : CheckM Bool)
      ⦃⇓? r _ => ⌜r = true⌝⦄ := by
    intro st hst
    subst hst
    simp only [WP.wp, PredTrans.apply, EStateM.run, hneg_run]
    exact hisRup
  have htrue_s : DQBFTrue s.formula s.clauses := hcorr.formula_sound htrue
  have htrue_added : DQBFTrue s.formula (s.clauses.addClause lits).1 :=
    RUP_soundness s lits hcorr.toSound hcorr.preserves_models hcorr.clauses_wf
      hcorr.propQueue_empty hrup htrue_s
  simpa [hsame₂.1, hsame₂.2] using htrue_added

@[spec] theorem runRupTrial_spec
    (dqbf : DQBF) (cs : ClauseStore) (lits : Array Literal) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s ∧ ClauseLitsWellFormed s.formula lits⌝⦄
    (runRupTrial lits : CheckM Bool)
    ⦃⇓? r s' => ⌜CheckState.Correct dqbf cs s' ∧
        ClauseLitsWellFormed s'.formula lits ∧
        (r = true → DQBFTrue dqbf cs → DQBFTrue s'.formula (s'.clauses.addClause lits).1)⌝⦄ := by
  intro s hs
  rcases hs with ⟨hcorr, hlits⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run, runRupTrial, Bind.bind, EStateM.bind]
  cases hneg_run : negateAndPropagate lits (fun _ => true) s with
  | error e s' =>
      simp [hneg_run]
  | ok isRup s₁ =>
      have hnew := newDecisionLevel_trial_spec dqbf cs s s ⟨rfl, hcorr⟩
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hnew
      have hfold :=
        negateAndPropagateTrueFold_trial_spec dqbf cs s lits
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hfold
      simp only [WP.wp, PredTrans.apply, EStateM.run, negateAndPropagate,
        Bind.bind, EStateM.bind] at hneg_run
      cases hnew_run : newDecisionLevel s with
      | error e s' =>
          rw [hnew_run] at hnew
          exact hnew.elim
      | ok _ s_mid =>
          rw [hnew_run] at hnew
          have hfold' := hfold s_mid ⟨hcorr, hnew⟩
          simp only [WP.wp, PredTrans.apply, EStateM.run] at hfold'
          have hfold_run :
              (lits.foldlM negateAndPropagateTrueStep false : CheckM Bool) s_mid =
                EStateM.Result.ok isRup s₁ := by
            have hfold_run' :
                (lits.foldlM
                    (fun conflict (l : Literal) => do
                      if conflict then
                        return true
                      let st : CheckState ← get
                      let v := l.var
                      if v = 0 || v > st.formula.maxVar then
                        return false
                      if satisfied st l then
                        return true
                      else if satisfied st l.negate then
                        return false
                      else
                        enqueue l.negate
                        let cref ← propagate
                        return cref.isSome)
                    false : CheckM Bool) s_mid = EStateM.Result.ok isRup s₁ := by
              simpa [hnew_run, negateAndPropagate, Bind.bind, EStateM.bind] using hneg_run
            simpa [negateAndPropagateTrueStep, Bind.bind, EStateM.bind,
              Pure.pure, EStateM.pure, EStateM.get] using hfold_run'
          rw [hfold_run] at hfold'
          rcases hfold' with ⟨_, htrial⟩
          cases hback_run : backtrackBefore 1 s₁ with
          | error e s' =>
              simp [hback_run]
          | ok _ s₂ =>
              simp [hback_run]
              exact runRupTrial_post_of_trial hcorr hlits hneg_run htrial hback_run

-- ─── Checker function soundness theorems ──────────────────────────────────────

/-- **RUP step soundness**: `checkRatClauseBasic` has a result-dependent basic-step
    postcondition.

    Proof sketch:
    1. Translate external literals to internal (no state change).
    2. Run `negateAndPropagate lits true` — apply `negateAndPropagate_rup_spec` to
       capture: `r = true → DQBFTrue dqbf cs → DQBFTrue s.formula (s.clauses.addClause lits).1`
    3. Run `backtrackBefore 1` — apply `negateAndPropagate_backtrack_correct` to
       recover `Correct dqbf cs` for the restored state.
    4. If `!isRup`: return `Failed` (no semantic obligation; `Correct` already holds).
    5. Run `addClause lits` — apply `addClause_sound_spec` with the semantic precondition
       from step 2. Yields: `Correct dqbf cs s'` and `(r = none → DQBFFalse dqbf cs)`.
    6. If `r.isNone`: return `Verified` and produce `DQBFFalse dqbf cs` from step 5. -/
theorem checkRatClauseBasic_sound (dqbf : DQBF) (cs : ClauseStore)
    (lineNum : Nat) (extLits : List Int) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkRatClauseBasic lineNum extLits
    ⦃⇓? r s' => ⌜BasicStepPost dqbf cs r s'⌝⦄ := by
  intro s hcorr
  simp only [WP.wp, PredTrans.apply, EStateM.run, checkRatClauseBasic, Bind.bind, EStateM.bind]
  have htrans := translateRatLitsBasic_spec dqbf cs extLits s hcorr
  simp only [WP.wp, PredTrans.apply, EStateM.run] at htrans
  cases hrunTrans : translateRatLitsBasic extLits s with
  | error e s' =>
      simp
  | ok lits s₁ =>
      rw [hrunTrans] at htrans
      rcases htrans with ⟨hcorr₁, hlits₁⟩
      have htrial := runRupTrial_spec dqbf cs lits s₁ ⟨hcorr₁, hlits₁⟩
      simp only [WP.wp, PredTrans.apply, EStateM.run] at htrial
      cases hrunTrial : runRupTrial lits s₁ with
      | error e s' =>
          rw [hrunTrial] at htrial
          simpa [hrunTrial]
      | ok isRup s₂ =>
          rw [hrunTrial] at htrial
          rcases htrial with ⟨hcorr₂, hlits₂, hrup₂⟩
          cases hisRup : isRup with
          | false =>
              simpa [BasicStepPost, hisRup, hrunTrial] using hcorr₂
          | true =>
              have hsem :
                  DQBFTrue dqbf cs → DQBFTrue s₂.formula (s₂.clauses.addClause lits).1 :=
                hrup₂ hisRup
              have hadd := addClause_sound_spec dqbf cs lits s₂ ⟨hcorr₂, hlits₂, hsem⟩
              simp only [WP.wp, PredTrans.apply, EStateM.run] at hadd
              cases hrunAdd : addClause lits s₂ with
              | error e s' =>
                  rw [hrunAdd] at hadd
                  simpa [hrunTrial, hisRup, Bind.bind, EStateM.bind, Pure.pure,
                    EStateM.pure, hrunAdd, BasicStepPost]
              | ok r s₃ =>
                  rw [hrunAdd] at hadd
                  cases hr : r with
                  | none =>
                      simpa [hrunTrial, hisRup, Bind.bind, EStateM.bind, Pure.pure,
                        EStateM.pure, hrunAdd, hr, BasicStepPost]
                        using hadd
                  | some cref =>
                      simpa [hrunTrial, hisRup, Bind.bind, EStateM.bind, Pure.pure,
                        EStateM.pure, hrunAdd, hr, BasicStepPost]
                        using hadd

/-- **UR step soundness**: `checkUniversalReductionBasic` has a result-dependent
    basic-step postcondition.

    Proof sketch:
    1. Translate literals (no state change).
    2. Check that pivot is universal and reducible — uses `URCondition`.
    3. Call `addClause (lits.filter (· ≠ pivot))` — apply `addClause_sound_spec`
       with semantic precondition from `UR_soundness` (already proved):
       `URCondition → clause in store → DQBFTrue → DQBFTrue of reduced clause`.
    4. `addClause` returning `none` gives `DQBFFalse dqbf cs` from `addClause_sound_spec`. -/
theorem checkUniversalReductionBasic_sound (dqbf : DQBF) (cs : ClauseStore)
    (lineNum : Nat) (extLits : List Int) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkUniversalReductionBasic lineNum extLits
    ⦃⇓? r s' => ⌜BasicStepPost dqbf cs r s'⌝⦄ := by
  mvcgen [checkUniversalReductionBasic, translateExistingLits_spec, addClause_sound_spec]
  case vc4.post.success.isTrue =>
    rename_i _ _ lits _ _ s hs
    exact hs.1
  case vc5.post.success.isFalse =>
    rename_i _ _ lits _ _ s hs pivot rest
    rcases hs with ⟨hcorr, hlits⟩
    by_cases hexi : s.formula.isVarExistential pivot.var = true
    · simp [hexi, BasicStepPost]
      exact hcorr
    · have hexi_false : s.formula.isVarExistential pivot.var = false := by
        cases hbool : s.formula.isVarExistential pivot.var <;> simp_all
      let reduced := lits.filter (· ≠ pivot)
      let urAfterLocate : CheckM (Option ProofResult) := do
        let f2 ← (·.formula) <$> get
        let pivotReducible := !lits.any (· = pivot.negate) && lits.all (fun l =>
          !f2.isVarExistential l.var || !f2.isVarOuterOfExivar pivot.var l.var)
        if pivotReducible then
          let r ← addClause reduced
          if r.isNone then
            return some (.Verified lineNum)
        else
          return some (.Failed lineNum #["UR"] #[] none)
        return none
      simp [hexi_false, rest, WP.wp, PredTrans.apply, EStateM.run]
      have hget : (MonadStateOf.get : CheckM CheckState) = EStateM.get := rfl
      cases hfind : s.clauses.findSortedClause (ClauseStore.sortLits lits) with
      | none =>
          simpa [WP.wp, PredTrans.apply, EStateM.run, hget, Bind.bind, EStateM.bind,
            EStateM.get, EStateM.pure, hfind, BasicStepPost] using hcorr
      | some cref =>
          simp only [WP.wp, PredTrans.apply, EStateM.run, hget, Bind.bind, EStateM.bind,
            EStateM.get, EStateM.pure, hfind]
          by_cases hpivotReducible :
              (∀ i (x : i < lits.size), ¬lits[i] = pivot.negate) ∧
              ∀ i (x : i < lits.size),
                s.formula.isVarExistential lits[i].var = false ∨
                  s.formula.isVarOuterOfExivar pivot.var lits[i].var = false
          · simp only [hpivotReducible, ↓reduceDIte]
            have hcond : URCondition s.formula lits pivot :=
              urCondition_of_pivotReducible_prop hexi_false hpivotReducible
            have hfind' := ClauseStore.findSortedClause_spec hfind
            rcases hfind' with ⟨c, hget, hsorted⟩
            have hperm_sorted : Array.Perm (ClauseStore.sortLits c.lits) lits := by
              rw [hsorted]
              exact ClauseStore.sortLits_perm lits
            have hperm : Array.Perm c.lits lits :=
              (Array.Perm.symm (ClauseStore.sortLits_perm c.lits)).trans hperm_sorted
            have hfilter : Array.filter (fun x => !decide (x = pivot)) lits = reduced := by
              simpa [reduced, decide_not]
            have hsem :
                DQBFTrue dqbf cs → DQBFTrue s.formula (s.clauses.addClause reduced).1 := by
              intro htrue
              simpa [reduced] using
                (UR_soundness_perm s.formula s.clauses lits pivot hcond
                  ⟨cref, c, hget, hperm⟩ (hcorr.formula_sound htrue))
            have hadd := addClause_sound_spec dqbf cs reduced s
              ⟨hcorr, ClauseLitsWellFormed.filter hlits, hsem⟩
            simp only [WP.wp, PredTrans.apply, EStateM.run] at hadd
            cases hrunAdd : addClause reduced s with
            | error e s' =>
                rw [hfilter]
                simpa [EStateM.bind, hrunAdd]
            | ok r s' =>
                rw [hrunAdd] at hadd
                cases hr : r with
                | none =>
                    rw [hfilter]
                    simpa [EStateM.bind, EStateM.pure, hrunAdd, hr,
                      BasicStepPost] using hadd
                | some cref' =>
                    rw [hfilter]
                    simpa [EStateM.bind, EStateM.pure, hrunAdd, hr,
                      BasicStepPost] using hadd
          · simpa [hpivotReducible, BasicStepPost] using hcorr

/-- **Single basic action soundness**: `checkActionBasic` has a result-dependent
    basic-step postcondition.

    Proof: immediate case split on the action constructor:
    - `AddUniversal`, `ModifyExistential`, `DeleteClause`: `throw` in basic mode;
      the postcondition for error states is vacuously true via `⇓?`.
    - `UniversalReduction`: apply `checkUniversalReductionBasic_sound`.
    - `RatClause`: apply `checkRatClauseBasic_sound`. -/
theorem checkActionBasic_sound (dqbf : DQBF) (cs : ClauseStore)
    (action : DQRatAction) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkActionBasic action
    ⦃⇓? r s' => ⌜BasicStepPost dqbf cs r s'⌝⦄ := by
  mvcgen [checkActionBasic, checkUniversalReductionBasic_sound, checkRatClauseBasic_sound]

/-- **Action-list soundness** (main theorem): `checkActionsBasic` has a
    result-dependent run postcondition.

    Proof: induction on `actions`. Base case: `checkActionsBasic [] = return .Unknown`,
    trivially satisfies the spec. Inductive step: head action may return `Verified`
    (delegate to `checkActionBasic_sound`) or `none` (continue; apply IH on tail). -/
theorem checkActionsBasic_sound (dqbf : DQBF) (cs : ClauseStore)
    (actions : List DQRatAction) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkActionsBasic actions
    ⦃⇓? r s' => ⌜BasicRunPost dqbf cs r s'⌝⦄ := by
  induction actions with
  | nil =>
      mvcgen [checkActionsBasic]
  | cons action actions ih =>
      mvcgen [checkActionsBasic, checkActionBasic_sound, ih]
      case vc4.cons.post.success.h_1 =>
        rename_i _ _ _ _ r _ _ hpost
        cases r <;> simpa [BasicRunPost, BasicStepPost] using hpost
      case vc5.cons.post.success.h_2 =>
        rename_i _ _ _ _ opt hnone _ _ hpost
        cases hx : opt with
        | none =>
            simpa [BasicStepPost, hx] using hpost
        | some r =>
            exact False.elim (hnone r hx)

/-- **Top-level soundness for basic checker**: if `checkActionsBasic` on parsed proof
    actions returns `Verified`, the input formula is `DQBFFalse`.

    Follows from `checkActionsBasic_sound` plus the fact that `Correct` holds initially
    (here taken as a hypothesis; see `parseDQDIMACS_correct` for the full checker). -/
theorem processProofBasic_sound (st : CheckState) (proofContent : String) (n : Nat)
    (hcorrect : CheckState.Correct st.formula st.clauses st)
    (hverify : ∃ st', (checkActionsBasic (parseProofActions proofContent)).run st
               = .ok (.Verified n) st') :
    DQBFFalse st.formula st.clauses := by
  rcases hverify with ⟨st', hrun⟩
  have hspec :=
    checkActionsBasic_sound st.formula st.clauses (parseProofActions proofContent)
  have hpost := hspec st hcorrect
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hpost
  have hrun' :
      checkActionsBasic (parseProofActions proofContent) st = .ok (.Verified n) st' := by
    simpa using hrun
  rw [hrun'] at hpost
  simpa [BasicRunPost] using hpost
