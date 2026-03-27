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
  /-- There is always at least one decision level (level 0). -/
  trail_nonempty : 0 < st.trail.size

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
  /-- Every literal recorded in the trail refers to a valid variable.
      (Moved here from `Sound`: only needed at action boundaries for `backtrackBefore`.) -/
  trail_lits_valid : ∀ i, i < st.trail.size →
      ∀ l ∈ st.trail.getD i #[], 0 < l.var ∧ l.var ≤ st.formula.maxVar
  /-- A variable is assigned iff it appears in some trail level.
      This is the key invariant that makes `backtrackBefore` correct.
      (Moved here from `Sound`: only needed at action boundaries.) -/
  assigned_iff_in_trail : ∀ v : Var, 0 < v → v ≤ st.formula.maxVar →
      (st.isAssigned.getD (v - 1) false = true ↔
       ∃ i, i < st.trail.size ∧ ∃ l ∈ st.trail.getD i #[], l.var = v)

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

-- ─── Hoare-triple specs for propagation primitives ────────────────────────────

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
  -- Provide toSound (all 8 structural fields), then the 5 ConsistentWith-specific fields.
  refine ⟨?_, h_con.formula_eq, h_con.clauses_eq, h_con.clauses_wf, ?_, ?_⟩
  · -- toSound: isAssigned/value sizes change via setIfInBounds (size-preserving);
    --          all other Sound fields are unchanged.
    refine ⟨?_, ?_, h_con.toSound.indepKnown_size, h_con.toSound.indepOf_size,
              h_con.toSound.externalName_size, h_con.toSound.isExistential_size,
              h_con.toSound.depset_size,
              by rw [Array.size_setIfInBounds]; exact h_con.toSound.trail_nonempty⟩
    · simp [Array.size_setIfInBounds, h_con.toSound.isAssigned_size]
    · simp [Array.size_setIfInBounds, h_con.toSound.value_size]
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
  exact ⟨h_con.toSound.isAssigned_size, h_con.toSound.value_size,
         h_con.toSound.indepKnown_size, h_con.toSound.indepOf_size,
         h_con.toSound.externalName_size, h_con.toSound.isExistential_size,
         h_con.toSound.depset_size,
         by simp [Array.size_push]⟩

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
- **H4** `addClause_sound_spec`: `addClause` maintains `Correct`; `none` → `DQBFFalse`
-/

-- ─── Formula/clauses preservation lemmas ─────────────────────────────────────

/-- `enqueue` never modifies `formula` or `clauses`. -/
theorem enqueue_fc (f : DQBF) (c : ClauseStore) (l : Literal) :
    ⦃fun s => ⌜s.formula = f ∧ s.clauses = c⌝⦄
    (enqueue l : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.formula = f ∧ s'.clauses = c⌝⦄ := by
  intro s ⟨hf, hc⟩; unfold enqueue; mvcgen

/-- `propagateOne` never modifies `formula` or `clauses`. -/
@[spec]
theorem propagateOne_fc (f : DQBF) (c : ClauseStore) (l : Literal) :
    ⦃fun s => ⌜s.formula = f ∧ s.clauses = c⌝⦄
    (propagateOne l : CheckM (Option CRef))
    ⦃⇓? _ s' => ⌜s'.formula = f ∧ s'.clauses = c⌝⦄ := by
  mvcgen [propagateOne, enqueue_fc] invariants
  · ⇓?⟨_, _⟩ s => ⌜s.formula = f ∧ s.clauses = c⌝
    with all_goals assumption

/-- `propagate.aux` preserves `formula` and `clauses`. -/
theorem propagate_aux_fc (f : DQBF) (c : ClauseStore) :
    ∀ (n : Nat) (st : CheckState),
      st.formula = f ∧ st.clauses = c →
      st.propQueue.size + st.isAssigned.count false ≤ n →
      ∀ (r : Option CRef) (s' : CheckState),
      propagate.aux st = .ok r s' →
      s'.formula = f ∧ s'.clauses = c := by
  intro n
  induction n with
  | zero =>
    intro st ⟨hf, hc⟩ hn r s' h
    have hempty : st.propQueue.isEmpty = true := by
      simp only [Array.isEmpty_iff_size_eq_zero]; omega
    simp only [propagate.aux, hempty, ↓reduceIte] at h
    simp only [EStateM.Result.ok.injEq] at h
    exact ⟨h.2 ▸ hf, h.2 ▸ hc⟩
  | succ n ih =>
    intro st ⟨hf, hc⟩ hn r s' h
    by_cases hempty : st.propQueue.isEmpty = true
    · simp only [propagate.aux, hempty, ↓reduceIte] at h
      simp only [EStateM.Result.ok.injEq] at h
      exact ⟨h.2 ▸ hf, h.2 ▸ hc⟩
    · simp only [Bool.not_eq_true] at hempty
      rw [propagate.aux.eq_def, if_neg (show ¬(st.propQueue.isEmpty = true) by simp [hempty])] at h
      simp only [] at h
      -- h : match (propagateOne l) s₁ with ...
      set l := st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩
      set s₁ := { st with propQueue := st.propQueue.pop }
      have hfc₁ : s₁.formula = f ∧ s₁.clauses = c := ⟨hf, hc⟩
      cases he : (propagateOne l) s₁ with
      | error e s => rw [he] at h; exact absurd h (by simp)
      | ok r₂ s₂ =>
        rw [he] at h
        -- propagateOne preserves formula/clauses
        have hfc₂ := propagateOne_fc f c l s₁ r₂ s₂ hfc₁ he
        cases r₂ with
        | some cref =>
          simp only [EStateM.Result.ok.injEq] at h
          exact ⟨h.2 ▸ hfc₂.1, h.2 ▸ hfc₂.2⟩
        | none =>
          -- recurse: aux s₂
          have hmeas := propagateOne_measure_spec l
              (s₁.propQueue.size + s₁.isAssigned.count false)
          specialize hmeas s₁ rfl
          simp only [WP.wp, PredTrans.apply, EStateM.run, he] at hmeas
          have hpos : 0 < st.propQueue.size := by
            have hne : st.propQueue.size ≠ 0 :=
              fun hh => absurd (Array.isEmpty_iff_size_eq_zero.mpr hh) (by simp [hempty])
            omega
          have hn₂ : s₂.propQueue.size + s₂.isAssigned.count false ≤ n := by
            have : s₁.propQueue.size = st.propQueue.size - 1 := by simp [s₁, Array.size_pop]
            have : s₁.isAssigned.count false = st.isAssigned.count false := rfl
            omega
          exact ih s₂ hfc₂ hn₂ r s' h

/-- `propagate` preserves `formula` and `clauses`. -/
@[spec]
theorem propagate_fc (f : DQBF) (c : ClauseStore) :
    ⦃fun s => ⌜s.formula = f ∧ s.clauses = c⌝⦄
    (propagate : CheckM (Option CRef))
    ⦃⇓? _ s' => ⌜s'.formula = f ∧ s'.clauses = c⌝⦄ := by
  intro s ⟨hf, hc⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run, propagate]
  cases h : propagate.aux s with
  | error e s' => simp only []
  | ok r s' =>
    simp only []
    exact propagate_aux_fc f c (s.propQueue.size + s.isAssigned.count false) s ⟨hf, hc⟩
        (Nat.le_refl _) r s' h

/-- `negateAndPropagate` preserves `formula` and `clauses`. -/
@[spec]
theorem negateAndPropagate_fc (f : DQBF) (c : ClauseStore)
    (lits : Array Literal) (which : Literal → Bool) :
    ⦃fun s => ⌜s.formula = f ∧ s.clauses = c⌝⦄
    (negateAndPropagate lits which : CheckM Bool)
    ⦃⇓? _ s' => ⌜s'.formula = f ∧ s'.clauses = c⌝⦄ := by
  mvcgen [negateAndPropagate, newDecisionLevel, enqueue_fc, propagate_fc] invariants
  · ⇓?⟨_, _⟩ s => ⌜s.formula = f ∧ s.clauses = c⌝
    with all_goals (first | assumption | exact ⟨rfl, rfl⟩)

-- ─── H1: RUP soundness as @[spec] ────────────────────────────────────────────

/-- **H1**: `negateAndPropagate` with "negate all" filter is sound for RUP.

    If the computation returns `true` from a `Correct` state, and the original
    formula is true, then adding `lits` preserves truth of the *current* formula.

    Proof: by contradiction via `negateAndPropagate_consistent_spec`.
    If `DQBFTrue dqbf cs`, then `formula_sound` gives `DQBFTrue s.formula s.clauses`.
    Take a satisfying model `(σ, sk)`. For any `σ'` with all lits false, build
    `ConsistentWith s.formula s.clauses σ' sk s` and apply the consistent spec to
    get `r = false` — contradicting `r = true`. Hence all lits are model-true under
    every satisfying assignment → `IsSemanticConsequence` → `SemanticConsequence_soundness`.
    The fact that `negateAndPropagate` preserves `s'.formula = s.formula` and
    `s'.clauses = s.clauses` follows from `newDecisionLevel`, `enqueue`, `propagate`
    not touching formula or clauses. -/
@[spec]
theorem negateAndPropagate_rup_spec (dqbf : DQBF) (cs : ClauseStore)
    (lits : Array Literal) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (negateAndPropagate lits (fun _ => true) : CheckM Bool)
    ⦃⇓? r s' =>
      ⌜r = true →
       DQBFTrue dqbf cs →
       DQBFTrue s'.formula (s'.clauses.addClause lits).1⌝⦄ := by
  sorry

-- ─── H2: negateAndPropagate + backtrackBefore 1 restores Correct ──────────────

/-- **H2**: After `negateAndPropagate lits which` followed by `backtrackBefore 1`,
    starting from a `Correct` state (with single trail level), `Correct` is restored.

    Proof sketch:
    - `negateAndPropagate` calls `newDecisionLevel` (pushes level 1), then assigns
      literals at level 1 (via `enqueue`). It does NOT touch `formula`, `clauses`,
      `value`, or level-0 trail content.
    - `backtrackBefore 1` pops all levels ≥ 1, un-assigning their literals.
      Since `enqueue` only assigns literals not already assigned (guards on
      `isAssigned.getD (v-1) false`), level-1 assignments are disjoint from level-0.
      Un-assigning them restores `isAssigned` to exactly the level-0 state.
    - After backtracking: trail.size = 1 (level 0 only), propQueue = #[], and
      isAssigned matches trail[0]. All `Correct` fields are restored because:
      * `formula`, `clauses`, `value` are unchanged
      * trail[0] and isAssigned are restored to pre-`negateAndPropagate` state
      * `Correct.preserves_models`, `Correct.formula_sound`, etc. all hold for
        the restored state since they held before -/
theorem negateAndPropagate_backtrack_correct
    (dqbf : DQBF) (cs : ClauseStore)
    (lits : Array Literal) (which : Literal → Bool) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    (do let r ← negateAndPropagate lits which; backtrackBefore 1; return r)
    ⦃⇓? r s' => ⌜CheckState.Correct dqbf cs s'⌝⦄ := by
  sorry

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
          depset_size := hcon.toSound.depset_size, trail_nonempty := hcon.toSound.trail_nonempty }

-- ─── H4: addClause maintains Correct and none → DQBFFalse ────────────────────

/-- **H4**: `addClause lits` maintains `Correct dqbf cs` and returns `none` only if
    the original formula is false.

    The precondition bundles:
    1. `Correct dqbf cs s` — the invariant holds
    2. `DQBFTrue dqbf cs → DQBFTrue s.formula (s.clauses.addClause lits).1` — the
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
@[spec]
theorem addClause_sound_spec (dqbf : DQBF) (cs : ClauseStore) (lits : Array Literal) :
    ⦃fun s =>
      ⌜CheckState.Correct dqbf cs s ∧
       (DQBFTrue dqbf cs → DQBFTrue s.formula (s.clauses.addClause lits).1)⌝⦄
    (addClause lits : CheckM (Option CRef))
    ⦃⇓? r s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       (r = none → DQBFFalse dqbf cs)⌝⦄ := by
  sorry

-- ─── Checker function soundness theorems ──────────────────────────────────────

/-- **RUP step soundness**: `checkRatClauseBasic` preserves `Correct` and, when it
    returns `Verified`, the original formula is `DQBFFalse`.

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
    ⦃⇓? r s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       ((∃ n, r = some (.Verified n)) → DQBFFalse dqbf cs)⌝⦄ := by
  sorry

/-- **UR step soundness**: `checkUniversalReductionBasic` preserves `Correct` and,
    when it returns `Verified`, the original formula is `DQBFFalse`.

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
    ⦃⇓? r s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       ((∃ n, r = some (.Verified n)) → DQBFFalse dqbf cs)⌝⦄ := by
  sorry

/-- **Single basic action soundness**: `checkActionBasic` preserves `Correct` and,
    when it returns `Verified`, the original formula is `DQBFFalse`.

    Proof: immediate case split on the action constructor:
    - `AddUniversal`, `ModifyExistential`, `DeleteClause`: `throw` in basic mode;
      the postcondition for error states is vacuously true via `⇓?`.
    - `UniversalReduction`: apply `checkUniversalReductionBasic_sound`.
    - `RatClause`: apply `checkRatClauseBasic_sound`. -/
theorem checkActionBasic_sound (dqbf : DQBF) (cs : ClauseStore)
    (action : DQRatAction) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkActionBasic action
    ⦃⇓? r s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       ((∃ n, r = some (.Verified n)) → DQBFFalse dqbf cs)⌝⦄ := by
  sorry

/-- **Action-list soundness** (main theorem): `checkActionsBasic` preserves `Correct`
    and, when it returns `Verified`, the original formula is `DQBFFalse`.

    Proof: induction on `actions`. Base case: `checkActionsBasic [] = return .Unknown`,
    trivially satisfies the spec. Inductive step: head action may return `Verified`
    (delegate to `checkActionBasic_sound`) or `none` (continue; apply IH on tail). -/
theorem checkActionsBasic_sound (dqbf : DQBF) (cs : ClauseStore)
    (actions : List DQRatAction) :
    ⦃fun s => ⌜CheckState.Correct dqbf cs s⌝⦄
    checkActionsBasic actions
    ⦃⇓ r s' =>
      ⌜CheckState.Correct dqbf cs s' ∧
       (∃ n, r = .Verified n → DQBFFalse dqbf cs)⌝⦄ := by
  sorry

/-- **Top-level soundness for basic checker**: if `checkActionsBasic` on parsed proof
    actions returns `Verified`, the input formula is `DQBFFalse`.

    Follows from `checkActionsBasic_sound` plus the fact that `Correct` holds initially
    (here taken as a hypothesis; see `parseDQDIMACS_correct` for the full checker). -/
theorem processProofBasic_sound (st : CheckState) (proofContent : String) (n : Nat)
    (hcorrect : CheckState.Correct st.formula st.clauses st)
    (hverify : ∃ st', (checkActionsBasic (parseProofActions proofContent)).run st
               = .ok (.Verified n) st') :
    DQBFFalse st.formula st.clauses := by
  sorry
