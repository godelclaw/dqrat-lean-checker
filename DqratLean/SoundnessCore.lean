import DqratLean.Semantics
import DqratLean.Checker

/-!
# Soundness Core: checker-state invariants

Definitions of the state-validity predicates (`CheckState.Sound`,
`CheckState.Correct`, `CheckState.FullCorrect`) plus small generic literal
and array helpers shared by the soundness development.

Trust status: certified proof module on the default non-watched path.
-/
open Std.Do

/-- The variable of a constructed literal: `mkLit v pos` has variable `v`, for either polarity. -/
theorem mkLit_var_early (v : Var) (pos : Bool) :
    (mkLit v pos).var = v := by
  unfold Literal.var mkLit
  by_cases hpos : pos
  · simp [hpos]
    rw [Nat.add_comm (v * 2) 1]
    rw [Nat.add_mul_div_right 1 v (by decide)]
    simp
  · simp [hpos]

/-- Every literal equals the literal rebuilt from its own variable and polarity. -/
theorem literal_eq_mkLit_var_isPos (l : Literal) :
    l = mkLit l.var l.isPos := by
  cases l with
  | mk x =>
      unfold mkLit Literal.var Literal.isPos
      have hdecomp : x / 2 * 2 + x % 2 = x := by
        simpa [Nat.mul_comm] using Nat.div_add_mod x 2
      rcases Nat.mod_two_eq_zero_or_one x with hmod | hmod
      · simp [hmod]
        omega
      · simp [hmod]
        omega

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

/-- If a defaulted read of a Boolean array (default `false`) returns `true`, the index is in
    bounds. -/
theorem arrayGetD_true_imp_lt (a : Array Bool) {i : Nat}
    (h : a.getD i false = true) :
    i < a.size := by
  by_cases hi : i < a.size
  · exact hi
  · simp [Array.getD, hi] at h

/-- The positive literal on a variable `v` evaluates to the value of `v` itself. -/
theorem litValue_mkLit_true
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (v : Var) :
    f.litValue σ sk (mkLit v true) = f.varValue σ sk v := by
  unfold DQBF.litValue
  rw [mkLit_var_early]
  simp [Literal.isPos, mkLit]

/-- The negative literal on a variable `v` evaluates to the Boolean negation of the value
    of `v`. -/
theorem litValue_mkLit_false
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (v : Var) :
    f.litValue σ sk (mkLit v false) = !(f.varValue σ sk v) := by
  unfold DQBF.litValue
  rw [mkLit_var_early]
  simp [Literal.isPos, mkLit]

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

/-- Action-boundary invariant plus the executable clause-store completeness property
    needed by the full DQRATE argument. -/
structure CheckState.FullCorrect (dqbf : DQBF) (cs : ClauseStore) (st : CheckState) : Prop where
  toCorrect : CheckState.Correct dqbf cs st
  liveOccurrencesComplete : ClauseStore.LiveOccurrencesComplete st.clauses

/-- The empty checker state satisfies the action-boundary invariant `Correct` relative to its own
    (empty) formula and clause store. -/
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
        simp [ClauseStore.getClause, CRef_Undef, hzero] at hget
      exact this.elim
    · have : False := by
        have hne0 : cref ≠ 0 := by
          simpa [CRef_Undef] using hzero
        have hnone :
            (if cref = 0 then some Clause.dummy else none) = none := by
          simp [hne0]
        simp [CheckState.empty, ClauseStore.getClause, ClauseStore.getClauseAt, CRef_Undef,
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

/-- The empty checker state satisfies the prefix-loading invariant `PrefixState`. -/
theorem PrefixState.empty : PrefixState CheckState.empty := by
  refine ⟨CheckState.empty_correct, rfl, ?_⟩
  intro v hpos hle
  have : False := by
    have hle0 : v ≤ 0 := by simpa [CheckState.empty] using hle
    exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hpos hle0)
  exact False.elim this

/-- Writing within bounds and then reading back the same index returns the written value,
    whatever the fallback. -/
theorem arraySetIfInBounds_getD_eq
    {α : Type} (a : Array α) (i : Nat) (v fallback : α) (h : i < a.size) :
    (a.setIfInBounds i v).getD i fallback = v := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD, dif_pos (hsize ▸ h)]
  simp [Array.getElem_setIfInBounds h]

/-- A bounds-checked write at one index leaves the defaulted read at any other index
    unchanged. -/
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

/-- A clause returned by the live lookup `getClause` is also present in the raw store, with its
    deletion flag unset. -/
theorem getClauseRaw_deleted_of_getClause
    {cs : ClauseStore} {cref : CRef} {c : Clause}
    (hget : cs.getClause cref = some c) :
    cs.getClauseRaw cref = some c ∧ c.deleted = false := by
  have hne : cref ≠ CRef_Undef :=
    ClauseStore.getClause_some_imp_ne_undef cs cref c hget
  unfold ClauseStore.getClause at hget
  cases hraw : cs.getClauseAt cref with
  | none =>
      simp [hne, hraw] at hget
  | some c' =>
      have hget' : c'.deleted = false ∧ c' = c := by
        simpa [ClauseStore.getClauseRaw, hne, hraw] using hget
      rcases hget' with ⟨hdeleted, hc⟩
      cases hc
      simp [ClauseStore.getClauseRaw, hne, hraw, hdeleted]

/-- Conversely, a clause found in the raw store whose deletion flag is unset is returned by the
    live lookup `getClause`. -/
theorem getClause_of_getClauseRaw_not_deleted
    {cs : ClauseStore} {cref : CRef} {c : Clause}
    (hraw : cs.getClauseRaw cref = some c)
    (hdeleted : c.deleted = false) :
    cs.getClause cref = some c := by
  have hne : cref ≠ CRef_Undef := by
    intro hzero
    simp [ClauseStore.getClauseRaw, hzero] at hraw
  unfold ClauseStore.getClauseRaw at hraw
  cases hgetAt : cs.getClauseAt cref with
  | none =>
      simp [hne, hgetAt] at hraw
  | some c' =>
      have hc : c' = c := by
        simpa [hne, hgetAt] using hraw
      subst hc
      simp [ClauseStore.getClause, hne, hgetAt, hdeleted]
