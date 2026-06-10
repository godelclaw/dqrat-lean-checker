import DqratLean.SoundnessCore

/-!
# Deletion Semantics

Semantic layer for the dependency-deletion (negative-`e`) rule:
`forceDelDep(s)` weakening, `ExhibitsDeleteIndependence(Set)`, the
`DeleteIndependenceBridge`/`SetBridge` model-repair interface, the
`flipUniv` characterization lemma family, and the witness lift/project
chain culminating in `DQBFTrue_forceDelDeps_of_setBridge`.
-/
open Std.Do

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

theorem litValue_negate_early
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (l : Literal) :
    f.litValue σ sk l.negate = !(f.litValue σ sk l) := by
  simp only [DQBF.litValue, Literal.negate, Literal.var, Literal.isPos]
  have hvar : (l.x ^^^ 1) / 2 = l.x / 2 := by
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [← Nat.testBit_succ, Nat.testBit_xor]
    have h1 : Nat.testBit 1 (k + 1) = false := by
      rw [Bool.eq_false_iff]
      exact fun h => Nat.succ_ne_zero k (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)
    simp [h1]
  have hpos : ((l.x ^^^ 1) % 2 == 1) = !(l.x % 2 == 1) := by
    have h0 : (l.x ^^^ 1).testBit 0 = !l.x.testBit 0 := by
      rw [Nat.testBit_xor, Nat.testBit_one_zero]
      simp [Bool.xor_comm]
    cases hb : l.x.testBit 0
    · have hm : l.x % 2 = 0 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hb
      have hxm : (l.x ^^^ 1) % 2 = 1 := Nat.mod_two_eq_one_iff_testBit_zero.mpr (by rw [h0, hb]; decide)
      simp [hm, hxm]
    · have hm : l.x % 2 = 1 := Nat.mod_two_eq_one_iff_testBit_zero.mpr hb
      have hxm : (l.x ^^^ 1) % 2 = 0 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr (by rw [h0, hb]; decide)
      simp [hm, hxm]
  rw [hvar, hpos]
  cases h : (l.x % 2 == 1) <;> simp

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

/-- Well-formedness of a clause literal array against a formula. -/
def ClauseLitsWellFormed (f : DQBF) (lits : Array Literal) : Prop :=
  ∀ l ∈ lits.toList, 0 < l.var ∧ l.var ≤ f.maxVar

theorem ClauseLitsWellFormed.filter
    {f : DQBF} {lits : Array Literal} {p : Literal → Bool}
    (hwf : ClauseLitsWellFormed f lits) :
    ClauseLitsWellFormed f (lits.filter p) := by
  intro l hl
  exact hwf l (Array.mem_filter.mp (Array.mem_toList_iff.mp hl) |>.1 |> Array.mem_toList_iff.mpr)

def deleteDepArgs
    (f : DQBF) (of_ on_ : Var) (σ : UnivAssignment) : Array Bool :=
  ((f.depset.getD of_ #[]).filter (· ≠ on_)).map σ

/-- Two universal assignments agree on the dependency set of `of_` with `on_` removed. -/
def AgreeOnDeleteDeps
    (f : DQBF) (of_ on_ : Var) (σ₁ σ₂ : UnivAssignment) : Prop :=
  ∀ u ∈ (f.depset.getD of_ #[]).filter (· ≠ on_), σ₁ u = σ₂ u

/-- A Skolem witness exhibits deletion-independence for `of_` from `on_` if
    the value assigned to `of_` depends only on the reduced dependency pattern. -/
def ExhibitsDeleteIndependence
    (f : DQBF) (of_ on_ : Var) (sk : SkolemAssignment) : Prop :=
  ∀ σ₁ σ₂, AgreeOnDeleteDeps f of_ on_ σ₁ σ₂ →
    f.varValue σ₁ sk of_ = f.varValue σ₂ sk of_

def DeleteIndependenceBridge
    (st : CheckState) (of_ on_ : Var) : Prop :=
  DQBFTrue st.formula st.clauses →
    ∃ sk,
      (∀ σ, st.clauses.matrixValue st.formula σ sk = true) ∧
      ExhibitsDeleteIndependence st.formula of_ on_ sk

def ExhibitsDeleteIndependenceSet
    (f : DQBF) (vars : Array Var) (on_ : Var) (sk : SkolemAssignment) : Prop :=
  ∀ of_ ∈ vars.toList, ExhibitsDeleteIndependence f of_ on_ sk

def DeleteIndependenceSetBridge
    (st : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  DQBFTrue st.formula st.clauses →
    ∃ sk,
      (∀ σ, st.clauses.matrixValue st.formula σ sk = true) ∧
      ExhibitsDeleteIndependenceSet st.formula vars on_ sk

theorem deleteDepArgs_eq_of_dep_agree
    (f : DQBF) (of_ on_ : Var) (σ₁ σ₂ : UnivAssignment)
    (hagree : AgreeOnDeleteDeps f of_ on_ σ₁ σ₂) :
    deleteDepArgs f of_ on_ σ₁ = deleteDepArgs f of_ on_ σ₂ := by
  unfold deleteDepArgs
  apply Array.ext (by simp [Array.size_map])
  intro i hi₁ _
  simp only [Array.getElem_map]
  have hi :
      i < ((f.depset.getD of_ #[]).filter (· ≠ on_)).size := by
    simpa [Array.size_map] using hi₁
  have hmem :
      (((f.depset.getD of_ #[]).filter (· ≠ on_))[i]) ∈
        (f.depset.getD of_ #[]).filter (· ≠ on_) :=
    Array.getElem_mem hi
  exact hagree _ hmem

/-- Full dependency argument vector supplied to the original Skolem witness. -/
def fullDepArgs
    (f : DQBF) (of_ : Var) (σ : UnivAssignment) : Array Bool :=
  (f.depset.getD of_ #[]).map σ

def flipUniv (u : Var) (σ : UnivAssignment) : UnivAssignment :=
  fun w => if w == u then !σ w else σ w

theorem agreeOnDeleteDeps_flipUniv
    (f : DQBF) (of_ on_ : Var) (σ : UnivAssignment) :
    AgreeOnDeleteDeps f of_ on_ σ (flipUniv on_ σ) := by
  intro u hu
  have hne : u ≠ on_ := by
    simpa using (Array.mem_filter.mp hu).2
  simp [flipUniv, hne]

theorem varValue_eq_of_fullDepArgs_eq
    (f : DQBF) (of_ : Var) (σ₁ σ₂ : UnivAssignment)
    (sk : SkolemAssignment)
    (hexi : f.isVarExistential of_ = true)
    (hargs : fullDepArgs f of_ σ₁ = fullDepArgs f of_ σ₂) :
    f.varValue σ₁ sk of_ = f.varValue σ₂ sk of_ := by
  simpa [DQBF.varValue, hexi, DQBF.exiValue, fullDepArgs] using
    congrArg (sk of_) hargs

theorem fullDepArgs_eq_of_agreeOnDeleteDeps_same_on
    (f : DQBF) (of_ on_ : Var) (σ₁ σ₂ : UnivAssignment)
    (hagree : AgreeOnDeleteDeps f of_ on_ σ₁ σ₂)
    (hon : σ₁ on_ = σ₂ on_) :
    fullDepArgs f of_ σ₁ = fullDepArgs f of_ σ₂ := by
  unfold fullDepArgs
  apply Array.ext (by simp [Array.size_map])
  intro i hi₁ _
  simp only [Array.getElem_map]
  have hi : i < (f.depset.getD of_ #[]).size := by
    simpa [Array.size_map] using hi₁
  have hu_mem : (f.depset.getD of_ #[])[i] ∈ f.depset.getD of_ #[] := by
    exact Array.getElem_mem hi
  by_cases hu : (f.depset.getD of_ #[])[i] = on_
  · calc
      σ₁ ((f.depset.getD of_ #[])[i]) = σ₁ on_ := by
        simpa using congrArg σ₁ hu
      _ = σ₂ on_ := hon
      _ = σ₂ ((f.depset.getD of_ #[])[i]) := by
        simpa using congrArg σ₂ hu.symm
  · have hu_filter :
        (f.depset.getD of_ #[])[i] ∈ (f.depset.getD of_ #[]).filter (· ≠ on_) := by
      exact Array.mem_filter.mpr ⟨hu_mem, by simpa using hu⟩
    exact hagree _ hu_filter

theorem fullDepArgs_flipUniv_eq_of_agreeOnDeleteDeps
    (f : DQBF) (of_ on_ : Var) (σ₁ σ₂ : UnivAssignment)
    (hagree : AgreeOnDeleteDeps f of_ on_ σ₁ σ₂)
    (hneq : σ₁ on_ ≠ σ₂ on_) :
    fullDepArgs f of_ (flipUniv on_ σ₁) = fullDepArgs f of_ σ₂ := by
  unfold fullDepArgs
  apply Array.ext (by simp [Array.size_map])
  intro i hi₁ _
  simp only [Array.getElem_map]
  have hi : i < (f.depset.getD of_ #[]).size := by
    simpa [Array.size_map] using hi₁
  have hu_mem : (f.depset.getD of_ #[])[i] ∈ f.depset.getD of_ #[] := by
    exact Array.getElem_mem hi
  by_cases hu : (f.depset.getD of_ #[])[i] = on_
  · have hon' : σ₂ on_ = !σ₁ on_ := by
      cases h₁ : σ₁ on_ <;> cases h₂ : σ₂ on_
      · exfalso
        exact hneq (by simp [h₁, h₂])
      · simp [h₁, h₂]
      · simp [h₁, h₂]
      · exfalso
        exact hneq (by simp [h₁, h₂])
    calc
      (flipUniv on_ σ₁) ((f.depset.getD of_ #[])[i]) = (flipUniv on_ σ₁) on_ := by
        simpa using congrArg (flipUniv on_ σ₁) hu
      _ = !σ₁ on_ := by
          unfold flipUniv
          have hone : (on_ == on_) = true := by simp
          rw [if_pos hone]
      _ = σ₂ on_ := hon'.symm
      _ = σ₂ ((f.depset.getD of_ #[])[i]) := by
        simpa using congrArg σ₂ hu.symm
  · have hu_filter :
        (f.depset.getD of_ #[])[i] ∈ (f.depset.getD of_ #[]).filter (· ≠ on_) := by
      exact Array.mem_filter.mpr ⟨hu_mem, by simpa using hu⟩
    calc
      (flipUniv on_ σ₁) ((f.depset.getD of_ #[])[i]) =
          σ₁ ((f.depset.getD of_ #[])[i]) := by
            unfold flipUniv
            have hbeq : ¬ ((f.depset.getD of_ #[])[i] == on_) = true := by
              simpa using hu
            rw [if_neg hbeq]
      _ = σ₂ ((f.depset.getD of_ #[])[i]) := hagree _ hu_filter

theorem fullDepArgs_eq_flipUniv_of_not_contains
    (f : DQBF) (of_ on_ : Var) (σ : UnivAssignment)
    (hcontains : (f.depset.getD of_ #[]).contains on_ = false) :
    fullDepArgs f of_ (flipUniv on_ σ) = fullDepArgs f of_ σ := by
  unfold fullDepArgs flipUniv
  apply Array.ext (by simp [Array.size_map])
  intro i hi₁ _
  simp only [Array.getElem_map]
  have hi : i < (f.depset.getD of_ #[]).size := by
    simpa [Array.size_map] using hi₁
  have hne : (f.depset.getD of_ #[])[i] ≠ on_ := by
    intro heq
    have hmem_on : on_ ∈ (f.depset.getD of_ #[]) := by
      exact Array.mem_iff_getElem.mpr ⟨i, hi, heq⟩
    have hcontains' : (f.depset.getD of_ #[]).contains on_ = true := by
      exact Array.contains_iff_mem.mpr hmem_on
    rw [hcontains'] at hcontains
    cases hcontains
  let w := (f.depset.getD of_ #[])[i]
  have hw : w = (f.depset.getD of_ #[])[i] := rfl
  have hne' : w ≠ on_ := by simpa [hw] using hne
  have hbeq : (w == on_) = false := by
    simp [hne']
  change (if w == on_ then !σ w else σ w) = σ w
  simp [hbeq]

theorem varValue_flipUniv_eq_of_contains_false
    (f : DQBF) (v on_ : Var) (σ : UnivAssignment) (sk : SkolemAssignment)
    (hexi : f.isVarExistential v = true)
    (hcontains : (f.depset.getD v #[]).contains on_ = false) :
    f.varValue (flipUniv on_ σ) sk v = f.varValue σ sk v := by
  rw [DQBF.varValue, hexi, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
  exact congrArg (sk v) (fullDepArgs_eq_flipUniv_of_not_contains f v on_ σ hcontains)

theorem varValue_flipUniv_eq_of_universal_ne
    (f : DQBF) (v on_ : Var) (σ : UnivAssignment) (sk : SkolemAssignment)
    (huniv : f.isVarExistential v = false)
    (hneq : v ≠ on_) :
    f.varValue (flipUniv on_ σ) sk v = f.varValue σ sk v := by
  rw [DQBF.varValue, huniv, DQBF.varValue, huniv]
  simp [flipUniv, hneq]

theorem litValue_flipUniv_eq_of_universal_ne
    (f : DQBF) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (l : Literal)
    (huniv : f.isVarExistential l.var = false)
    (hne : l.var ≠ on_) :
    f.litValue (flipUniv on_ σ) sk l = f.litValue σ sk l := by
  simp [DQBF.litValue,
    varValue_flipUniv_eq_of_universal_ne f l.var on_ σ sk huniv hne]

theorem litValue_flipUniv_eq_of_existential_not_contains
    (f : DQBF) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (l : Literal)
    (hexi : f.isVarExistential l.var = true)
    (hcontains : (f.depset.getD l.var #[]).contains on_ = false) :
    f.litValue (flipUniv on_ σ) sk l = f.litValue σ sk l := by
  simp [DQBF.litValue,
    varValue_flipUniv_eq_of_contains_false f l.var on_ σ sk hexi hcontains]

theorem exhibitsDeleteIndependence_iff_flipUniv
    (f : DQBF) (of_ on_ : Var) (sk : SkolemAssignment)
    (hexi : f.isVarExistential of_ = true) :
    ExhibitsDeleteIndependence f of_ on_ sk ↔
      ∀ σ, f.varValue σ sk of_ = f.varValue (flipUniv on_ σ) sk of_ := by
  constructor
  · intro hexhibit σ
    exact hexhibit σ (flipUniv on_ σ) (agreeOnDeleteDeps_flipUniv f of_ on_ σ)
  · intro hflip σ₁ σ₂ hagree
    by_cases hon : σ₁ on_ = σ₂ on_
    · exact varValue_eq_of_fullDepArgs_eq
        f of_ σ₁ σ₂ sk hexi
        (fullDepArgs_eq_of_agreeOnDeleteDeps_same_on f of_ on_ σ₁ σ₂ hagree hon)
    · calc
        f.varValue σ₁ sk of_ = f.varValue (flipUniv on_ σ₁) sk of_ := hflip σ₁
        _ = f.varValue σ₂ sk of_ := by
            exact varValue_eq_of_fullDepArgs_eq
              f of_ (flipUniv on_ σ₁) σ₂ sk hexi
              (fullDepArgs_flipUniv_eq_of_agreeOnDeleteDeps f of_ on_ σ₁ σ₂ hagree hon)

theorem litValue_false_true_flip_universal_eq_on
    (f : DQBF) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (l : Literal)
    (huniv : f.isVarExistential l.var = false)
    (hfalse : f.litValue σ sk l = false)
    (htrue : f.litValue (flipUniv on_ σ) sk l = true) :
    l.var = on_ := by
  by_cases hEq : l.var = on_
  · exact hEq
  · have hsame :=
      litValue_flipUniv_eq_of_universal_ne f on_ σ sk l huniv hEq
    rw [hsame, hfalse] at htrue
    cases htrue

theorem litValue_false_true_flip_existential_contains
    (f : DQBF) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (l : Literal)
    (hexi : f.isVarExistential l.var = true)
    (hfalse : f.litValue σ sk l = false)
    (htrue : f.litValue (flipUniv on_ σ) sk l = true) :
    (f.depset.getD l.var #[]).contains on_ = true := by
  cases hcontains : (f.depset.getD l.var #[]).contains on_ with
  | false =>
      have hsame :=
        litValue_flipUniv_eq_of_existential_not_contains
          f on_ σ sk l hexi hcontains
      rw [hsame, hfalse] at htrue
      cases htrue
  | true =>
      rfl

theorem fullDepArgs_eq_implies_on_eq_of_contains
    (f : DQBF) (of_ on_ : Var) (σ σ₀ : UnivAssignment)
    (hcontains : (f.depset.getD of_ #[]).contains on_ = true)
    (hfull : fullDepArgs f of_ σ = fullDepArgs f of_ σ₀) :
    σ on_ = σ₀ on_ := by
  rcases Array.mem_iff_getElem.mp (Array.contains_iff_mem.mp hcontains) with
    ⟨i, hi, hi_on⟩
  have hi₁ : i < (fullDepArgs f of_ σ).size := by
    simpa [fullDepArgs] using hi
  have hi₂ : i < (fullDepArgs f of_ σ₀).size := by
    simpa [fullDepArgs] using hi
  have hget :
      (fullDepArgs f of_ σ).getD i false =
        (fullDepArgs f of_ σ₀).getD i false :=
    congrArg (fun a => a.getD i false) hfull
  rw [← Array.getElem_eq_getD (h := hi₁),
      ← Array.getElem_eq_getD (h := hi₂)] at hget
  simp only [fullDepArgs, Array.getElem_map, hi] at hget
  calc
    σ on_ = σ ((f.depset.getD of_ #[])[i]) := by rw [hi_on]
    _ = σ₀ ((f.depset.getD of_ #[])[i]) := hget
    _ = σ₀ on_ := by rw [hi_on]

theorem lit_eq_mkLit_varValue_of_var_and_true
    (f : DQBF) (of_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (l : Literal)
    (hvar : l.var = of_)
    (htrue : f.litValue σ sk l = true) :
    l = mkLit of_ (f.varValue σ sk of_) := by
  cases hval : f.varValue σ sk of_
  · have hsame_var : l.var = (mkLit of_ false).var := by
      simpa [mkLit_var_early] using hvar
    rcases literal_eq_or_negate_of_same_var l (mkLit of_ false) hsame_var with hEq | hNeg
    · simpa [hval] using hEq
    · rw [hNeg, litValue_negate_early, litValue_mkLit_false, hval] at htrue
      cases htrue
  · have hsame_var : l.var = (mkLit of_ true).var := by
      simpa [mkLit_var_early] using hvar
    rcases literal_eq_or_negate_of_same_var l (mkLit of_ true) hsame_var with hEq | hNeg
    · simpa [hval] using hEq
    · rw [hNeg, litValue_negate_early, litValue_mkLit_true, hval] at htrue
      cases htrue

theorem matrixValue_false_implies_exists_false_clause
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment)
    (sk : SkolemAssignment)
    (hfalse : cs.matrixValue f σ sk = false) :
    ∃ cref c, cs.getClause cref = some c ∧
      f.clauseValue σ sk c.lits = false := by
  simp only [ClauseStore.matrixValue, List.all_eq_false, List.mem_range] at hfalse
  rcases hfalse with ⟨i, hi, hnot⟩
  cases hget : cs.getClause (i + 1) with
  | none =>
      simp [hget] at hnot
  | some c =>
      have hclause : f.clauseValue σ sk c.lits = false := by
        cases hval : f.clauseValue σ sk c.lits <;> simp [hget, hval] at hnot ⊢
      exact ⟨i + 1, c, hget, hclause⟩

theorem matrixValue_false_of_false_clause
    (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment)
    (sk : SkolemAssignment) {cref : CRef} {c : Clause}
    (hget : cs.getClause cref = some c)
    (hfalse : f.clauseValue σ sk c.lits = false) :
    cs.matrixValue f σ sk = false := by
  cases hmat : cs.matrixValue f σ sk with
  | false => rfl
  | true =>
      have htrue : f.clauseValue σ sk c.lits = true :=
        clauseValue_of_matrixValue f cs σ sk cref c hmat hget
      rw [hfalse] at htrue
      cases htrue

/-- Project the old dependency-argument vector by dropping the slot for `on_`. -/
def projectDeleteArgs
    (deps : Array Var) (on_ : Var) (args : Array Bool) : Array Bool :=
  (((List.zip deps.toList args.toList).filterMap fun
      | (u, b) => if u = on_ then none else some b)).toArray

theorem projectDeleteArgs_of_map
    (deps : Array Var) (on_ : Var) (σ : UnivAssignment) :
    projectDeleteArgs deps on_ (deps.map σ) = (deps.filter (· ≠ on_)).map σ := by
  apply Array.ext'
  simp [projectDeleteArgs, Array.toList_map, Array.toList_filter]
  induction deps.toList with
  | nil =>
      simp
  | cons u us ih =>
      by_cases hu : u = on_
      · simp [hu, ih]
      · simp [hu, ih]

/-- Delete one universal dependency from every existential in `vars`. This is the
    one-universal / many-existentials shape used by the D^forall-pure paper proof. -/
def forceDelDepsList
    (f : DQBF) (vars : List Var) (on_ : Var) : DQBF :=
  vars.foldl (fun g of_ => g.forceDelDep of_ on_) f

def forceDelDeps
    (f : DQBF) (vars : Array Var) (on_ : Var) : DQBF :=
  forceDelDepsList f vars.toList on_

/-- Lift a witness for the formula with `on_` deleted from every variable in `vars`
    back to the original formula by projecting those argument vectors. -/
def liftForceDelDepsWitnessList
    (f : DQBF) (vars : List Var) (on_ : Var) (sk : SkolemAssignment) :
    SkolemAssignment :=
  fun v args =>
    if v ∈ vars then
      sk v (projectDeleteArgs (f.depset.getD v #[]) on_ args)
    else
      sk v args

def liftForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (sk : SkolemAssignment) :
    SkolemAssignment :=
  liftForceDelDepsWitnessList f vars.toList on_ sk

theorem array_filter_ne_idem (xs : Array Var) (on_ : Var) :
    (xs.filter (· ≠ on_)).filter (· ≠ on_) = xs.filter (· ≠ on_) := by
  apply Array.ext'
  simp [Array.toList_filter, List.filter_filter]

theorem forceDelDep_depset_getD_self
    (f : DQBF) (of_ on_ : Var) :
    (f.forceDelDep of_ on_).depset.getD of_ #[] =
      (f.depset.getD of_ #[]).filter (· ≠ on_) := by
  unfold DQBF.forceDelDep
  by_cases hlt : of_ < f.depset.size
  · simp [Array.setIfInBounds_def, hlt]
  · simp [Array.setIfInBounds_def, hlt]

theorem forceDelDep_depset_getD_of_ne
    (f : DQBF) (of_ on_ v : Var) (hneq : v ≠ of_) :
    (f.forceDelDep of_ on_).depset.getD v #[] = f.depset.getD v #[] := by
  unfold DQBF.forceDelDep
  by_cases hlt : of_ < f.depset.size
  · simp [Array.setIfInBounds_def, hlt]
    rw [Array.getElem?_set_ne hlt (Ne.symm hneq)]
  · simp [Array.setIfInBounds_def, hlt]

theorem forceDelDepsList_isVarExistential
    (f : DQBF) (vars : List Var) (on_ v : Var) :
    (forceDelDepsList f vars on_).isVarExistential v = f.isVarExistential v := by
  induction vars generalizing f with
  | nil =>
      simp [forceDelDepsList]
  | cons of_ vars ih =>
      simpa [forceDelDepsList, DQBF.forceDelDep, DQBF.isVarExistential] using
        ih (f := f.forceDelDep of_ on_)

theorem forceDelDeps_isVarExistential
    (f : DQBF) (vars : Array Var) (on_ v : Var) :
    (forceDelDeps f vars on_).isVarExistential v = f.isVarExistential v := by
  simp [forceDelDeps, forceDelDepsList_isVarExistential]

theorem forceDelDepsList_depset_getD
    (f : DQBF) (vars : List Var) (on_ v : Var) :
    (forceDelDepsList f vars on_).depset.getD v #[] =
      if v ∈ vars then (f.depset.getD v #[]).filter (· ≠ on_) else f.depset.getD v #[] := by
  induction vars generalizing f with
  | nil =>
      simp [forceDelDepsList]
  | cons of_ vars ih =>
      by_cases hov : v = of_
      · subst hov
        by_cases hmem : v ∈ vars
        · have hih := ih (f := f.forceDelDep v on_)
          rw [if_pos hmem] at hih
          rw [forceDelDep_depset_getD_self] at hih
          simpa [forceDelDepsList, List.mem_cons, hmem,
            array_filter_ne_idem] using hih
        · have hih := ih (f := f.forceDelDep v on_)
          rw [if_neg hmem] at hih
          rw [forceDelDep_depset_getD_self] at hih
          simpa [forceDelDepsList, List.mem_cons, hmem] using hih
      · by_cases hmem : v ∈ vars
        · have hih := ih (f := f.forceDelDep of_ on_)
          rw [if_pos hmem] at hih
          rw [forceDelDep_depset_getD_of_ne _ _ _ _ hov] at hih
          simpa [forceDelDepsList, List.mem_cons, hov, hmem,
            array_filter_ne_idem] using hih
        · have hih := ih (f := f.forceDelDep of_ on_)
          rw [if_neg hmem] at hih
          rw [forceDelDep_depset_getD_of_ne _ _ _ _ hov] at hih
          simpa [forceDelDepsList, List.mem_cons, hov, hmem] using hih

theorem forceDelDeps_depset_getD
    (f : DQBF) (vars : Array Var) (on_ v : Var) :
    (forceDelDeps f vars on_).depset.getD v #[] =
      if v ∈ vars.toList then (f.depset.getD v #[]).filter (· ≠ on_) else f.depset.getD v #[] := by
  simpa [forceDelDeps] using forceDelDepsList_depset_getD f vars.toList on_ v

theorem varValue_liftForceDelDepsWitnessList
    (f : DQBF) (vars : List Var) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (v : Var) :
    f.varValue σ (liftForceDelDepsWitnessList f vars on_ sk) v =
      (forceDelDepsList f vars on_).varValue σ sk v := by
  by_cases hex : f.isVarExistential v = true
  · have hex' : (forceDelDepsList f vars on_).isVarExistential v = true := by
      simpa [forceDelDepsList_isVarExistential] using hex
    rw [DQBF.varValue, DQBF.varValue, hex, hex']
    by_cases hmem : v ∈ vars
    · simp [DQBF.exiValue, forceDelDepsList_depset_getD f vars on_ v,
        liftForceDelDepsWitnessList, hmem, projectDeleteArgs_of_map]
    · simp [DQBF.exiValue, forceDelDepsList_depset_getD f vars on_ v,
        liftForceDelDepsWitnessList, hmem]
  · have hex' : (forceDelDepsList f vars on_).isVarExistential v = false := by
      simpa [forceDelDepsList_isVarExistential] using hex
    simp [DQBF.varValue, hex, hex']

theorem varValue_liftForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (v : Var) :
    f.varValue σ (liftForceDelDepsWitness f vars on_ sk) v =
      (forceDelDeps f vars on_).varValue σ sk v := by
  simpa [forceDelDeps, liftForceDelDepsWitness] using
    varValue_liftForceDelDepsWitnessList f vars.toList on_ σ sk v

theorem litValue_liftForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (l : Literal) :
    f.litValue σ (liftForceDelDepsWitness f vars on_ sk) l =
      (forceDelDeps f vars on_).litValue σ sk l := by
  simp [DQBF.litValue, varValue_liftForceDelDepsWitness f vars on_ σ sk l.var]

theorem clauseValue_liftForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment) (lits : Array Literal) :
    f.clauseValue σ (liftForceDelDepsWitness f vars on_ sk) lits =
      (forceDelDeps f vars on_).clauseValue σ sk lits := by
  unfold DQBF.clauseValue
  simpa using
    (Array.any_congr (w := rfl)
      (h := fun l => litValue_liftForceDelDepsWitness f vars on_ σ sk l)
      (wstart := rfl) (wstop := rfl))

theorem matrixValue_liftForceDelDepsWitness
    (f : DQBF) (cs : ClauseStore) (vars : Array Var) (on_ : Var)
    (σ : UnivAssignment) (sk : SkolemAssignment) :
    cs.matrixValue f σ (liftForceDelDepsWitness f vars on_ sk) =
      cs.matrixValue (forceDelDeps f vars on_) σ sk := by
  unfold ClauseStore.matrixValue
  apply List.all_congr rfl
  intro i
  cases hclause : cs.getClause (i + 1) with
  | none =>
      simp [hclause]
  | some c =>
      simp [hclause, clauseValue_liftForceDelDepsWitness f vars on_ σ sk c.lits]

theorem exhibitsDeleteIndependenceSet_liftForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (sk : SkolemAssignment)
    (hexi : ∀ of_ ∈ vars.toList, f.isVarExistential of_ = true) :
    ExhibitsDeleteIndependenceSet f vars on_ (liftForceDelDepsWitness f vars on_ sk) := by
  intro of_ hof
  intro σ₁ σ₂ hagree
  have hargs :
      deleteDepArgs f of_ on_ σ₁ = deleteDepArgs f of_ on_ σ₂ :=
    deleteDepArgs_eq_of_dep_agree f of_ on_ σ₁ σ₂ hagree
  have hexi_of : f.isVarExistential of_ = true := hexi of_ hof
  simpa [DQBF.varValue, DQBF.exiValue, hexi_of, liftForceDelDepsWitness,
    liftForceDelDepsWitnessList, hof, projectDeleteArgs_of_map, deleteDepArgs] using
    congrArg (sk of_) hargs

theorem exhibitsDeleteIndependence_liftForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (sk : SkolemAssignment)
    {of_ : Var}
    (hmem : of_ ∈ vars.toList)
    (hexi : f.isVarExistential of_ = true) :
    ExhibitsDeleteIndependence f of_ on_ (liftForceDelDepsWitness f vars on_ sk) := by
  intro σ₁ σ₂ hagree
  have hargs :
      deleteDepArgs f of_ on_ σ₁ = deleteDepArgs f of_ on_ σ₂ :=
    deleteDepArgs_eq_of_dep_agree f of_ on_ σ₁ σ₂ hagree
  simpa [DQBF.varValue, DQBF.exiValue, hexi, liftForceDelDepsWitness,
    liftForceDelDepsWitnessList, hmem, projectDeleteArgs_of_map, deleteDepArgs] using
    congrArg (sk of_) hargs

theorem deleteIndependenceBridge_of_forceDelDepsTrue
    (f : DQBF) (cs : ClauseStore) (vars : Array Var) (of_ on_ : Var)
    (hmem : of_ ∈ vars.toList)
    (hexi : f.isVarExistential of_ = true)
    (htrueDel : DQBFTrue (forceDelDeps f vars on_) cs) :
    DQBFTrue f cs →
      ∃ sk,
        (∀ σ, cs.matrixValue f σ sk = true) ∧
        ExhibitsDeleteIndependence f of_ on_ sk := by
  intro _
  rcases htrueDel with ⟨sk, hsk⟩
  refine ⟨liftForceDelDepsWitness f vars on_ sk, ?_, ?_⟩
  · intro σ
    rw [matrixValue_liftForceDelDepsWitness]
    exact hsk σ
  · exact exhibitsDeleteIndependence_liftForceDelDepsWitness
      f vars on_ sk hmem hexi

theorem deleteIndependenceSetBridge_of_forceDelDepsTrue
    (f : DQBF) (cs : ClauseStore) (vars : Array Var) (on_ : Var)
    (hexi : ∀ of_ ∈ vars.toList, f.isVarExistential of_ = true)
    (htrueDel : DQBFTrue (forceDelDeps f vars on_) cs) :
    DQBFTrue f cs →
      ∃ sk,
        (∀ σ, cs.matrixValue f σ sk = true) ∧
        ExhibitsDeleteIndependenceSet f vars on_ sk := by
  intro _
  rcases htrueDel with ⟨sk, hsk⟩
  refine ⟨liftForceDelDepsWitness f vars on_ sk, ?_, ?_⟩
  · intro σ
    rw [matrixValue_liftForceDelDepsWitness]
    exact hsk σ
  · exact exhibitsDeleteIndependenceSet_liftForceDelDepsWitness f vars on_ sk hexi

theorem DeleteIndependenceSetBridge.of_forceDelDepsTrue
    {st : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ of_ ∈ vars.toList, st.formula.isVarExistential of_ = true)
    (htrueDel : DQBFTrue (forceDelDeps st.formula vars on_) st.clauses) :
    DeleteIndependenceSetBridge st vars on_ :=
  deleteIndependenceSetBridge_of_forceDelDepsTrue
    st.formula st.clauses vars on_ hexi htrueDel

theorem DeleteIndependenceBridge.of_forceDelDepsTrue
    {st : CheckState} {vars : Array Var} {of_ on_ : Var}
    (hmem : of_ ∈ vars.toList)
    (hexi : st.formula.isVarExistential of_ = true)
    (htrueDel : DQBFTrue (forceDelDeps st.formula vars on_) st.clauses) :
    DeleteIndependenceBridge st of_ on_ :=
  deleteIndependenceBridge_of_forceDelDepsTrue
    st.formula st.clauses vars of_ on_ hmem hexi htrueDel

/-- Reinsert a canonical `false` value for the deleted dependency `on_`. -/
def insertDeleteArgsList : List Var → Var → List Bool → List Bool
  | [], _, _ => []
  | u :: us, on_, args =>
      if u = on_ then
        false :: insertDeleteArgsList us on_ args
      else
        match args with
        | [] => false :: insertDeleteArgsList us on_ []
        | b :: bs => b :: insertDeleteArgsList us on_ bs

def insertDeleteArgs
    (deps : Array Var) (on_ : Var) (args : Array Bool) : Array Bool :=
  (insertDeleteArgsList deps.toList on_ args.toList).toArray

theorem insertDeleteArgsList_of_filter_map
    (deps : List Var) (on_ : Var) (σ : UnivAssignment) :
    insertDeleteArgsList deps on_ ((deps.filter fun x => !decide (x = on_)).map σ) =
      deps.map (fun u => (!decide (u = on_)) && σ u) := by
  induction deps with
  | nil =>
      simp [insertDeleteArgsList]
  | cons u us ih =>
      by_cases hu : u = on_
      · simp [insertDeleteArgsList, hu, ih]
      · simp [insertDeleteArgsList, hu, ih]

theorem insertDeleteArgs_of_filter_map
    (deps : Array Var) (on_ : Var) (σ : UnivAssignment) :
    insertDeleteArgs deps on_ ((deps.filter (· ≠ on_)).map σ) =
      deps.map (fun u => (!decide (u = on_)) && σ u) := by
  apply Array.ext'
  simpa [insertDeleteArgs, Array.toList_map] using
    insertDeleteArgsList_of_filter_map deps.toList on_ σ

/-- Project a witness for the original formula down to the formula where `on_`
    has been deleted from every existential in `vars`, using `false` as a
    canonical value for the removed dependency slot. -/
def projectForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (sk : SkolemAssignment) :
    SkolemAssignment :=
  fun v args =>
    if v ∈ vars.toList then
      sk v (insertDeleteArgs (f.depset.getD v #[]) on_ args)
    else
      sk v args

theorem varValue_projectForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment)
    (hexhibit : ExhibitsDeleteIndependenceSet f vars on_ sk)
    (v : Var) :
    (forceDelDeps f vars on_).varValue σ
      (projectForceDelDepsWitness f vars on_ sk) v =
      f.varValue σ sk v := by
  by_cases hex : f.isVarExistential v = true
  · have hex' : (forceDelDeps f vars on_).isVarExistential v = true := by
      simpa [hex] using forceDelDeps_isVarExistential f vars on_ v
    rw [DQBF.varValue, DQBF.varValue, hex', hex]
    by_cases hmem : v ∈ vars.toList
    · have hdeps :
          (forceDelDeps f vars on_).depset.getD v #[] =
            (f.depset.getD v #[]).filter (· ≠ on_) := by
        simpa [hmem] using forceDelDeps_depset_getD f vars on_ v
      rw [DQBF.exiValue, DQBF.exiValue, hdeps]
      have hargs :
          insertDeleteArgs (f.depset.getD v #[]) on_
              (((f.depset.getD v #[]).filter (· ≠ on_)).map σ) =
            (f.depset.getD v #[]).map (fun u => (!decide (u = on_)) && σ u) := by
        simpa using insertDeleteArgs_of_filter_map (f.depset.getD v #[]) on_ σ
      have hagree :
          AgreeOnDeleteDeps f v on_
            (fun u => (!decide (u = on_)) && σ u) σ := by
        intro u hu
        have hu_ne : u ≠ on_ := by
          simpa using (Array.mem_filter.mp hu).2
        simp [hu_ne]
      have hindep :=
        hexhibit v hmem (fun u => (!decide (u = on_)) && σ u) σ hagree
      have happ :
          projectForceDelDepsWitness f vars on_ sk v
              (((f.depset.getD v #[]).filter (· ≠ on_)).map σ) =
            sk v ((f.depset.getD v #[]).map (fun u => (!decide (u = on_)) && σ u)) := by
        unfold projectForceDelDepsWitness
        rw [if_pos hmem]
        simpa using congrArg (sk v) hargs
      rw [happ]
      simpa [DQBF.varValue, hex, DQBF.exiValue] using hindep
    · have hdeps :
          (forceDelDeps f vars on_).depset.getD v #[] = f.depset.getD v #[] := by
        simpa [hmem] using forceDelDeps_depset_getD f vars on_ v
      rw [DQBF.exiValue, DQBF.exiValue, hdeps]
      simp [projectForceDelDepsWitness, hmem]
  · have hex' : (forceDelDeps f vars on_).isVarExistential v = false := by
      simpa [hex] using forceDelDeps_isVarExistential f vars on_ v
    simp [DQBF.varValue, hex', hex]

theorem litValue_projectForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment)
    (hexhibit : ExhibitsDeleteIndependenceSet f vars on_ sk)
    (l : Literal) :
    (forceDelDeps f vars on_).litValue σ
      (projectForceDelDepsWitness f vars on_ sk) l =
      f.litValue σ sk l := by
  simp [DQBF.litValue, varValue_projectForceDelDepsWitness f vars on_ σ sk hexhibit l.var]

theorem clauseValue_projectForceDelDepsWitness
    (f : DQBF) (vars : Array Var) (on_ : Var) (σ : UnivAssignment)
    (sk : SkolemAssignment)
    (hexhibit : ExhibitsDeleteIndependenceSet f vars on_ sk)
    (lits : Array Literal) :
    (forceDelDeps f vars on_).clauseValue σ
      (projectForceDelDepsWitness f vars on_ sk) lits =
      f.clauseValue σ sk lits := by
  unfold DQBF.clauseValue
  simpa using
    (Array.any_congr
      (w := rfl)
      (h := fun l => litValue_projectForceDelDepsWitness f vars on_ σ sk hexhibit l)
      (wstart := rfl) (wstop := rfl))

theorem matrixValue_projectForceDelDepsWitness
    (f : DQBF) (cs : ClauseStore) (vars : Array Var) (on_ : Var)
    (σ : UnivAssignment) (sk : SkolemAssignment)
    (hexhibit : ExhibitsDeleteIndependenceSet f vars on_ sk) :
    cs.matrixValue (forceDelDeps f vars on_) σ
      (projectForceDelDepsWitness f vars on_ sk) =
      cs.matrixValue f σ sk := by
  unfold ClauseStore.matrixValue
  apply List.all_congr rfl
  intro i
  cases hclause : cs.getClause (i + 1) with
  | none =>
      simp [hclause]
  | some c =>
      simp [hclause, clauseValue_projectForceDelDepsWitness f vars on_ σ sk hexhibit c.lits]

theorem DQBFTrue_forceDelDeps_of_setBridge
    {st : CheckState} {vars : Array Var} {on_ : Var}
    (hbridge : DeleteIndependenceSetBridge st vars on_)
    (htrue : DQBFTrue st.formula st.clauses) :
    DQBFTrue (forceDelDeps st.formula vars on_) st.clauses := by
  rcases hbridge htrue with ⟨sk, hall, hexhibit⟩
  refine ⟨projectForceDelDepsWitness st.formula vars on_ sk, ?_⟩
  intro σ
  rw [matrixValue_projectForceDelDepsWitness st.formula st.clauses vars on_ σ sk hexhibit]
  exact hall σ

theorem varValue_forceDelDeps_filter_existential_eq
    (f : DQBF) (vars : Array Var) (on_ : Var)
    (σ : UnivAssignment) (sk : SkolemAssignment) (v : Var) :
    (forceDelDeps f vars on_).varValue σ sk v =
      (forceDelDeps f (vars.filter f.isVarExistential) on_).varValue σ sk v := by
  by_cases hex : f.isVarExistential v = true
  · have hex_all : (forceDelDeps f vars on_).isVarExistential v = true := by
      simpa [forceDelDeps_isVarExistential] using hex
    have hex_exi :
        (forceDelDeps f (vars.filter f.isVarExistential) on_).isVarExistential v = true := by
      simpa [forceDelDeps_isVarExistential] using hex
    rw [DQBF.varValue, DQBF.varValue, hex_all, hex_exi]
    have hdeps_all :
        (forceDelDeps f vars on_).depset.getD v #[] =
          if v ∈ vars.toList then
            (f.depset.getD v #[]).filter (· ≠ on_)
          else
            f.depset.getD v #[] := by
      simpa using forceDelDeps_depset_getD f vars on_ v
    have hdeps_exi :
        (forceDelDeps f (vars.filter f.isVarExistential) on_).depset.getD v #[] =
          if v ∈ (vars.filter f.isVarExistential).toList then
            (f.depset.getD v #[]).filter (· ≠ on_)
          else
            f.depset.getD v #[] := by
      simpa using forceDelDeps_depset_getD
        f (vars.filter f.isVarExistential) on_ v
    by_cases hmem : v ∈ vars.toList
    · have hmem_exi : v ∈ (vars.filter f.isVarExistential).toList := by
        exact Array.mem_toList_iff.mpr <|
          Array.mem_filter.mpr ⟨Array.mem_toList_iff.mp hmem, hex⟩
      simp [DQBF.exiValue, hdeps_all, hdeps_exi, hmem, hex]
    · have hnot_mem_exi : v ∉ (vars.filter f.isVarExistential).toList := by
        intro hmem_exi
        exact hmem (Array.mem_toList_iff.mpr (Array.mem_filter.mp
          (Array.mem_toList_iff.mp hmem_exi)).1)
      simp [DQBF.exiValue, hdeps_all, hdeps_exi, hmem, hnot_mem_exi, hex]
  · have hex_all : (forceDelDeps f vars on_).isVarExistential v = false := by
      simpa [forceDelDeps_isVarExistential] using hex
    have hex_exi :
        (forceDelDeps f (vars.filter f.isVarExistential) on_).isVarExistential v = false := by
      simpa [forceDelDeps_isVarExistential] using hex
    simp [DQBF.varValue, hex_all, hex_exi]

theorem litValue_forceDelDeps_filter_existential_eq
    (f : DQBF) (vars : Array Var) (on_ : Var)
    (σ : UnivAssignment) (sk : SkolemAssignment) (l : Literal) :
    (forceDelDeps f vars on_).litValue σ sk l =
      (forceDelDeps f (vars.filter f.isVarExistential) on_).litValue σ sk l := by
  simp [DQBF.litValue, varValue_forceDelDeps_filter_existential_eq
    f vars on_ σ sk l.var]

theorem clauseValue_forceDelDeps_filter_existential_eq
    (f : DQBF) (vars : Array Var) (on_ : Var)
    (σ : UnivAssignment) (sk : SkolemAssignment) (lits : Array Literal) :
    (forceDelDeps f vars on_).clauseValue σ sk lits =
      (forceDelDeps f (vars.filter f.isVarExistential) on_).clauseValue σ sk lits := by
  unfold DQBF.clauseValue
  simpa using
    (Array.any_congr
      (w := rfl)
      (h := fun l => litValue_forceDelDeps_filter_existential_eq f vars on_ σ sk l)
      (wstart := rfl) (wstop := rfl))

theorem matrixValue_forceDelDeps_filter_existential_eq
    (f : DQBF) (cs : ClauseStore) (vars : Array Var) (on_ : Var)
    (σ : UnivAssignment) (sk : SkolemAssignment) :
    cs.matrixValue (forceDelDeps f vars on_) σ sk =
      cs.matrixValue (forceDelDeps f (vars.filter f.isVarExistential) on_) σ sk := by
  unfold ClauseStore.matrixValue
  apply List.all_congr rfl
  intro i
  cases hclause : cs.getClause (i + 1) with
  | none =>
      simp [hclause]
  | some c =>
      simp [hclause, clauseValue_forceDelDeps_filter_existential_eq
        f vars on_ σ sk c.lits]

theorem DQBFTrue_forceDelDeps_filter_existential_iff
    (f : DQBF) (cs : ClauseStore) (vars : Array Var) (on_ : Var) :
    DQBFTrue (forceDelDeps f vars on_) cs ↔
      DQBFTrue (forceDelDeps f (vars.filter f.isVarExistential) on_) cs := by
  constructor
  · intro htrue
    rcases htrue with ⟨sk, hall⟩
    refine ⟨sk, ?_⟩
    intro σ
    simpa [matrixValue_forceDelDeps_filter_existential_eq f cs vars on_ σ sk]
      using hall σ
  · intro htrue
    rcases htrue with ⟨sk, hall⟩
    refine ⟨sk, ?_⟩
    intro σ
    simpa [matrixValue_forceDelDeps_filter_existential_eq f cs vars on_ σ sk]
      using hall σ

theorem clauseValue_false_implies_all_lits_false_early
    (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (lits : Array Literal)
    (hfalse : f.clauseValue σ sk lits = false) :
    ∀ l ∈ lits.toList, f.litValue σ sk l = false := by
  intro l hl
  rcases Bool.eq_false_or_eq_true (f.litValue σ sk l) with hl_true | hl_false
  · exfalso
    have hmem : l ∈ lits := Array.mem_toList_iff.mp hl
    rcases Array.mem_iff_getElem.mp hmem with ⟨i, hi, rfl⟩
    have hclause_true : f.clauseValue σ sk lits = true := by
      simp only [DQBF.clauseValue, Array.any_eq_true]
      exact ⟨i, hi, hl_true⟩
    rw [hclause_true] at hfalse
    cases hfalse
  · exact hl_false

theorem clauseValue_true_false_implies_exists_true_false_lit
    (f : DQBF) (σ : UnivAssignment)
    (skTrue skFalse : SkolemAssignment)
    (lits : Array Literal)
    (htrue : f.clauseValue σ skTrue lits = true)
    (hfalse : f.clauseValue σ skFalse lits = false) :
    ∃ l ∈ lits.toList,
      f.litValue σ skTrue l = true ∧
      f.litValue σ skFalse l = false := by
  have hfalse_lits :
      ∀ l ∈ lits.toList, f.litValue σ skFalse l = false :=
    clauseValue_false_implies_all_lits_false_early f σ skFalse lits hfalse
  simp only [DQBF.clauseValue, Array.any_eq_true] at htrue
  rcases htrue with ⟨i, hi, hli_true⟩
  refine ⟨lits[i], Array.mem_toList_iff.mpr (Array.getElem_mem hi), hli_true, ?_⟩
  exact hfalse_lits _ (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
