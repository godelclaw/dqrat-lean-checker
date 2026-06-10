import DqratLean.DeletionSemantics
import DqratLean.DeletionPaths

/-!
# Deletion Exhibition (open frontier)

Full exhibition of the reflexive resolution-path dependency scheme,
transcribed from:

> O. Beyersdorff, J. Blinkhorn, L. Chew, R. Schmidt, M. Suda,
> **"Reinterpreting Dependency Schemes: Soundness Meets Incompleteness in
> DQBF"**, Journal of Automated Reasoning 63 (2019) 597–623,
> DOI 10.1007/s10817-018-9482-4 (open access, CC-BY).
> Local copy: `docs/papers/beyersdorff-blinkhorn-chew-schmidt-suda-jar2019-*`.

Alignment map (paper § 6 → this file):

| Paper                                  | Here                                  |
|----------------------------------------|---------------------------------------|
| Def. 9 (resolution path)               | `DeletePurePath` (DeletionPaths.lean) |
| Def. 10 (Drrs: paired opposite paths)  | `NoDeleteCrossPaths` (negated form)   |
| Def. 11 (assignment tree, model)       | `SkolemAssignment` + `∀ σ, matrixValue`|
| Def. 12 (reformed path `ref(P,M,u)`)   | `reformLeft` / `reformRight` bodies   |
| Def. 13 (left/right reform, `ref(M,u)`)| `reformLeft`, `reformRight`, `reformSkolem` |
| Lemma 2 (reformed paths satisfy ϕ)     | `reformLeft_matrix_true`, `reformRight_matrix_true` |
| Lemma 3 (reform is a model)            | automatic in Skolem form (functions of own deps) |
| Lemma 4 (reform exhibits independence) | `reformSkolem_exhibits_mem`           |
| Lemma 5 (reforms preserve exhibitions) | not needed: one universal per checker step |
| Thm 8 / Wimmer et al. Thm 11           | `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet` |

Paper paths `P` with `P[u] = ¬u` correspond to assignments `σ` with
`σ on_ = false`; the complementary path `comp(P,M,u)` is `flipUniv on_ σ`
evaluated in the same Skolem assignment. The paper's refusal condition
`(¬l, ¬l′) ∈ C_Φ` (Def. 12) becomes a `DeletePurePath` test from the
appropriate `on_`-literal — stated as a `Prop` and decided classically, so
only the (already proved) *completeness* direction of the `getReachable`
BFS specification is ever needed, never its soundness direction.

Iterate here: `lake build DqratLean.DeletionExhibition` (sub-second).
-/

open Std.Do

/-- `σ` with the `on_`-coordinate forced to `c`. -/
def pinUniv (on_ : Var) (c : Bool) (σ : UnivAssignment) : UnivAssignment :=
  fun w => if w == on_ then c else σ w

theorem pinUniv_flipUniv (on_ : Var) (c : Bool) (σ : UnivAssignment) :
    pinUniv on_ c (flipUniv on_ σ) = pinUniv on_ c σ := by
  funext w
  by_cases h : w == on_
  · simp [pinUniv, h]
  · simp [pinUniv, flipUniv, h]

theorem pinUniv_eq_self_of_eq {on_ : Var} {c : Bool} {σ : UnivAssignment}
    (hσ : σ on_ = c) : pinUniv on_ c σ = σ := by
  funext w
  by_cases h : w == on_
  · have : w = on_ := by simpa using h
    simp [pinUniv, h, this, hσ]
  · simp [pinUniv, h]

theorem flipUniv_eq_pinUniv_of_eq {on_ : Var} {b : Bool} {σ : UnivAssignment}
    (hσ : σ on_ = b) : flipUniv on_ σ = pinUniv on_ (!b) σ := by
  funext w
  by_cases h : w == on_
  · have hw : w = on_ := by simpa using h
    simp [flipUniv, pinUniv, h, hw, hσ]
  · simp [flipUniv, pinUniv, h]

/-- Dep-vector analogue of `pinUniv`: overwrite every coordinate of `args`
    that belongs to `on_` in the dependency list of `z` by `c`.
    Duplicate-safe (positional zip, not index search). -/
def pinDepArgs (f : DQBF) (v on_ : Var) (c : Bool) (args : Array Bool) :
    Array Bool :=
  (f.depset.getD v #[]).zipWith (fun u a => if u == on_ then c else a) args

theorem fullDepArgs_pinUniv (f : DQBF) (v on_ : Var) (c : Bool)
    (σ : UnivAssignment) :
    fullDepArgs f v (pinUniv on_ c σ) =
      pinDepArgs f v on_ c (fullDepArgs f v σ) := by
  unfold fullDepArgs pinDepArgs pinUniv
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp [Array.getElem_zipWith, Array.getElem_map]

/-- On the image of `fullDepArgs`, pinning the `on_`-coordinate to `c` is a
    no-op exactly when `σ` already assigns `c` to `on_` (provided `on_`
    genuinely occurs in the dependency list). This is how the reform
    definitions below read "which half-space is `args` on" without an
    index search. -/
theorem pinDepArgs_fullDepArgs_eq_self_iff
    (f : DQBF) (z on_ : Var) (c : Bool) (σ : UnivAssignment)
    (hcontains : (f.depset.getD z #[]).contains on_ = true) :
    pinDepArgs f z on_ c (fullDepArgs f z σ) = fullDepArgs f z σ ↔
      σ on_ = c := by
  constructor
  · intro hpin
    have hmem : on_ ∈ f.depset.getD z #[] := by
      simpa [Array.contains_iff_mem] using hcontains
    rcases Array.mem_iff_getElem.mp hmem with ⟨i, hi, hgi⟩
    have hpinsize : i < (pinDepArgs f z on_ c (fullDepArgs f z σ)).size := by
      simp only [pinDepArgs, fullDepArgs, Array.size_zipWith, Array.size_map]
      omega
    have hfullsize : i < (fullDepArgs f z σ).size := by
      simp only [fullDepArgs, Array.size_map]
      omega
    have hq := congrArg (fun a : Array Bool => a[i]?) hpin
    simp only at hq
    rw [Array.getElem?_eq_getElem hpinsize,
      Array.getElem?_eq_getElem hfullsize] at hq
    have hpv : (pinDepArgs f z on_ c (fullDepArgs f z σ))[i]'hpinsize = c := by
      unfold pinDepArgs
      rw [Array.getElem_zipWith, hgi]
      simp
    have hfv : (fullDepArgs f z σ)[i]'hfullsize = σ on_ := by
      unfold fullDepArgs
      rw [Array.getElem_map, hgi]
    rw [hpv, hfv] at hq
    exact (Option.some.inj hq).symm
  · intro hσ
    rw [← fullDepArgs_pinUniv, pinUniv_eq_self_of_eq hσ]

/-!
## The reform (paper Definitions 12 and 13, single universal `on_`)

Paper Def. 12, for a left path `P` (`P[u] = ¬u`, so `l = ¬u`, `¬l = u`):

> `ref(P,M,u)[z] = comp(P,M,u)[z]` if `z` is existential and
> `(¬l, ¬l′) ∉ C_Φ`; `P[z]` otherwise, where `l′ = comp(P,M,u)[z]`.

In Skolem form, with `v := sk z (args pinned to the `on_ := true` side)`
the complementary value, the true literal of `z` on the complementary path
is `mkLit z v`, so `¬l′ = mkLit z (!v)` and the refusal test is a
resolution path from `u` (= `mkLit on_ true`) to `mkLit z (!v)`.
-/

open Classical in
/-- Paper Def. 13 (left reform): paths containing `¬u` (here: argument
    vectors on the `on_ = false` half-space) are reformed; everything else
    is preserved. -/
noncomputable def reformLeft (st : CheckState) (on_ : Var)
    (sk : SkolemAssignment) : SkolemAssignment :=
  fun z args =>
    if (st.formula.depset.getD z #[]).contains on_ = false then sk z args
    else if pinDepArgs st.formula z on_ true args = args then sk z args
    else if DeletePurePath st on_ (mkLit on_ true)
        (mkLit z (!(sk z (pinDepArgs st.formula z on_ true args)))) then
      sk z args
    else sk z (pinDepArgs st.formula z on_ true args)

open Classical in
/-- Paper Def. 13 (right reform): paths containing `u` (argument vectors on
    the `on_ = true` half-space) are reformed, over an arbitrary base
    (instantiated with the left reform). For right paths `l = u`, so the
    refusal test starts from `¬u` (= `mkLit on_ false`). -/
noncomputable def reformRight (st : CheckState) (on_ : Var)
    (sk : SkolemAssignment) : SkolemAssignment :=
  fun z args =>
    if (st.formula.depset.getD z #[]).contains on_ = false then sk z args
    else if pinDepArgs st.formula z on_ false args = args then sk z args
    else if DeletePurePath st on_ (mkLit on_ false)
        (mkLit z (!(sk z (pinDepArgs st.formula z on_ false args)))) then
      sk z args
    else sk z (pinDepArgs st.formula z on_ false args)

/-- Paper Def. 13 (reformed model): right reform of the left reform. -/
noncomputable def reformSkolem (st : CheckState) (on_ : Var)
    (sk : SkolemAssignment) : SkolemAssignment :=
  reformRight st on_ (reformLeft st on_ sk)

/-!
## Evaluation rules for the reform (the computational content of Def. 12)
-/

theorem varValue_reformLeft_of_not_contains
    (st : CheckState) (on_ : Var) (sk : SkolemAssignment)
    (σ : UnivAssignment) {z : Var}
    (hnc : (st.formula.depset.getD z #[]).contains on_ = false) :
    st.formula.varValue σ (reformLeft st on_ sk) z =
      st.formula.varValue σ sk z := by
  by_cases hexi : st.formula.isVarExistential z = true
  · rw [DQBF.varValue, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
    show reformLeft st on_ sk z (fullDepArgs st.formula z σ) =
      sk z (fullDepArgs st.formula z σ)
    unfold reformLeft
    rw [if_pos hnc]
  · have hexi' : st.formula.isVarExistential z = false := by simpa using hexi
    rw [DQBF.varValue, DQBF.varValue, hexi']
    simp

theorem varValue_reformLeft_of_on_true
    (st : CheckState) (on_ : Var) (sk : SkolemAssignment)
    {σ : UnivAssignment} {z : Var}
    (hσ : σ on_ = true) :
    st.formula.varValue σ (reformLeft st on_ sk) z =
      st.formula.varValue σ sk z := by
  by_cases hexi : st.formula.isVarExistential z = true
  · by_cases hnc : (st.formula.depset.getD z #[]).contains on_ = false
    · exact varValue_reformLeft_of_not_contains st on_ sk σ hnc
    · have hcont : (st.formula.depset.getD z #[]).contains on_ = true := by
        simpa using hnc
      have hpin :
          pinDepArgs st.formula z on_ true (fullDepArgs st.formula z σ) =
            fullDepArgs st.formula z σ :=
        (pinDepArgs_fullDepArgs_eq_self_iff st.formula z on_ true σ hcont).2 hσ
      rw [DQBF.varValue, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
      show reformLeft st on_ sk z (fullDepArgs st.formula z σ) =
        sk z (fullDepArgs st.formula z σ)
      unfold reformLeft
      rw [if_neg (by rw [hcont]; simp), if_pos hpin]
  · have hexi' : st.formula.isVarExistential z = false := by simpa using hexi
    rw [DQBF.varValue, DQBF.varValue, hexi']
    simp

/-- Left half-space, refusal triggered (paper: `(¬l, ¬l′) ∈ C_Φ`): the
    reform keeps the original value. -/
theorem varValue_reformLeft_refused
    (st : CheckState) (on_ : Var) (sk : SkolemAssignment)
    {σ : UnivAssignment} {z : Var}
    (hexi : st.formula.isVarExistential z = true)
    (hcont : (st.formula.depset.getD z #[]).contains on_ = true)
    (hσ : σ on_ = false)
    (hpath : DeletePurePath st on_ (mkLit on_ true)
      (mkLit z (!(st.formula.varValue (flipUniv on_ σ) sk z)))) :
    st.formula.varValue σ (reformLeft st on_ sk) z =
      st.formula.varValue σ sk z := by
  have hflip : fullDepArgs st.formula z (flipUniv on_ σ) =
      pinDepArgs st.formula z on_ true (fullDepArgs st.formula z σ) := by
    rw [flipUniv_eq_pinUniv_of_eq hσ]
    exact fullDepArgs_pinUniv st.formula z on_ true σ
  have hnotpin :
      ¬ pinDepArgs st.formula z on_ true (fullDepArgs st.formula z σ) =
        fullDepArgs st.formula z σ := by
    rw [pinDepArgs_fullDepArgs_eq_self_iff st.formula z on_ true σ hcont]
    simp [hσ]
  have hv : st.formula.varValue (flipUniv on_ σ) sk z =
      sk z (pinDepArgs st.formula z on_ true (fullDepArgs st.formula z σ)) := by
    rw [DQBF.varValue, hexi, DQBF.exiValue, ← hflip]
    rfl
  rw [hv] at hpath
  rw [DQBF.varValue, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
  show reformLeft st on_ sk z (fullDepArgs st.formula z σ) =
    sk z (fullDepArgs st.formula z σ)
  unfold reformLeft
  rw [if_neg (by rw [hcont]; simp), if_neg hnotpin, if_pos hpath]

/-- Left half-space, reform performed (paper: `(¬l, ¬l′) ∉ C_Φ`): the value
    is copied from the complementary path. -/
theorem varValue_reformLeft_reformed
    (st : CheckState) (on_ : Var) (sk : SkolemAssignment)
    {σ : UnivAssignment} {z : Var}
    (hexi : st.formula.isVarExistential z = true)
    (hcont : (st.formula.depset.getD z #[]).contains on_ = true)
    (hσ : σ on_ = false)
    (hno : ¬ DeletePurePath st on_ (mkLit on_ true)
      (mkLit z (!(st.formula.varValue (flipUniv on_ σ) sk z)))) :
    st.formula.varValue σ (reformLeft st on_ sk) z =
      st.formula.varValue (flipUniv on_ σ) sk z := by
  have hflip : fullDepArgs st.formula z (flipUniv on_ σ) =
      pinDepArgs st.formula z on_ true (fullDepArgs st.formula z σ) := by
    rw [flipUniv_eq_pinUniv_of_eq hσ]
    exact fullDepArgs_pinUniv st.formula z on_ true σ
  have hnotpin :
      ¬ pinDepArgs st.formula z on_ true (fullDepArgs st.formula z σ) =
        fullDepArgs st.formula z σ := by
    rw [pinDepArgs_fullDepArgs_eq_self_iff st.formula z on_ true σ hcont]
    simp [hσ]
  have hv : st.formula.varValue (flipUniv on_ σ) sk z =
      sk z (pinDepArgs st.formula z on_ true (fullDepArgs st.formula z σ)) := by
    rw [DQBF.varValue, hexi, DQBF.exiValue, ← hflip]
    rfl
  rw [hv] at hno
  rw [hv, DQBF.varValue, hexi, DQBF.exiValue]
  show reformLeft st on_ sk z (fullDepArgs st.formula z σ) =
    sk z (pinDepArgs st.formula z on_ true (fullDepArgs st.formula z σ))
  unfold reformLeft
  rw [if_neg (by rw [hcont]; simp), if_neg hnotpin, if_neg hno]

theorem varValue_reformRight_of_not_contains
    (st : CheckState) (on_ : Var) (sk : SkolemAssignment)
    (σ : UnivAssignment) {z : Var}
    (hnc : (st.formula.depset.getD z #[]).contains on_ = false) :
    st.formula.varValue σ (reformRight st on_ sk) z =
      st.formula.varValue σ sk z := by
  by_cases hexi : st.formula.isVarExistential z = true
  · rw [DQBF.varValue, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
    show reformRight st on_ sk z (fullDepArgs st.formula z σ) =
      sk z (fullDepArgs st.formula z σ)
    unfold reformRight
    rw [if_pos hnc]
  · have hexi' : st.formula.isVarExistential z = false := by simpa using hexi
    rw [DQBF.varValue, DQBF.varValue, hexi']
    simp

theorem varValue_reformRight_of_on_false
    (st : CheckState) (on_ : Var) (sk : SkolemAssignment)
    {σ : UnivAssignment} {z : Var}
    (hσ : σ on_ = false) :
    st.formula.varValue σ (reformRight st on_ sk) z =
      st.formula.varValue σ sk z := by
  by_cases hexi : st.formula.isVarExistential z = true
  · by_cases hnc : (st.formula.depset.getD z #[]).contains on_ = false
    · exact varValue_reformRight_of_not_contains st on_ sk σ hnc
    · have hcont : (st.formula.depset.getD z #[]).contains on_ = true := by
        simpa using hnc
      have hpin :
          pinDepArgs st.formula z on_ false (fullDepArgs st.formula z σ) =
            fullDepArgs st.formula z σ :=
        (pinDepArgs_fullDepArgs_eq_self_iff st.formula z on_ false σ hcont).2 hσ
      rw [DQBF.varValue, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
      show reformRight st on_ sk z (fullDepArgs st.formula z σ) =
        sk z (fullDepArgs st.formula z σ)
      unfold reformRight
      rw [if_neg (by rw [hcont]; simp), if_pos hpin]
  · have hexi' : st.formula.isVarExistential z = false := by simpa using hexi
    rw [DQBF.varValue, DQBF.varValue, hexi']
    simp

theorem varValue_reformRight_refused
    (st : CheckState) (on_ : Var) (sk : SkolemAssignment)
    {σ : UnivAssignment} {z : Var}
    (hexi : st.formula.isVarExistential z = true)
    (hcont : (st.formula.depset.getD z #[]).contains on_ = true)
    (hσ : σ on_ = true)
    (hpath : DeletePurePath st on_ (mkLit on_ false)
      (mkLit z (!(st.formula.varValue (flipUniv on_ σ) sk z)))) :
    st.formula.varValue σ (reformRight st on_ sk) z =
      st.formula.varValue σ sk z := by
  have hflip : fullDepArgs st.formula z (flipUniv on_ σ) =
      pinDepArgs st.formula z on_ false (fullDepArgs st.formula z σ) := by
    rw [flipUniv_eq_pinUniv_of_eq hσ]
    exact fullDepArgs_pinUniv st.formula z on_ false σ
  have hnotpin :
      ¬ pinDepArgs st.formula z on_ false (fullDepArgs st.formula z σ) =
        fullDepArgs st.formula z σ := by
    rw [pinDepArgs_fullDepArgs_eq_self_iff st.formula z on_ false σ hcont]
    simp [hσ]
  have hv : st.formula.varValue (flipUniv on_ σ) sk z =
      sk z (pinDepArgs st.formula z on_ false (fullDepArgs st.formula z σ)) := by
    rw [DQBF.varValue, hexi, DQBF.exiValue, ← hflip]
    rfl
  rw [hv] at hpath
  rw [DQBF.varValue, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
  show reformRight st on_ sk z (fullDepArgs st.formula z σ) =
    sk z (fullDepArgs st.formula z σ)
  unfold reformRight
  rw [if_neg (by rw [hcont]; simp), if_neg hnotpin, if_pos hpath]

theorem varValue_reformRight_reformed
    (st : CheckState) (on_ : Var) (sk : SkolemAssignment)
    {σ : UnivAssignment} {z : Var}
    (hexi : st.formula.isVarExistential z = true)
    (hcont : (st.formula.depset.getD z #[]).contains on_ = true)
    (hσ : σ on_ = true)
    (hno : ¬ DeletePurePath st on_ (mkLit on_ false)
      (mkLit z (!(st.formula.varValue (flipUniv on_ σ) sk z)))) :
    st.formula.varValue σ (reformRight st on_ sk) z =
      st.formula.varValue (flipUniv on_ σ) sk z := by
  have hflip : fullDepArgs st.formula z (flipUniv on_ σ) =
      pinDepArgs st.formula z on_ false (fullDepArgs st.formula z σ) := by
    rw [flipUniv_eq_pinUniv_of_eq hσ]
    exact fullDepArgs_pinUniv st.formula z on_ false σ
  have hnotpin :
      ¬ pinDepArgs st.formula z on_ false (fullDepArgs st.formula z σ) =
        fullDepArgs st.formula z σ := by
    rw [pinDepArgs_fullDepArgs_eq_self_iff st.formula z on_ false σ hcont]
    simp [hσ]
  have hv : st.formula.varValue (flipUniv on_ σ) sk z =
      sk z (pinDepArgs st.formula z on_ false (fullDepArgs st.formula z σ)) := by
    rw [DQBF.varValue, hexi, DQBF.exiValue, ← hflip]
    rfl
  rw [hv] at hno
  rw [hv, DQBF.varValue, hexi, DQBF.exiValue]
  show reformRight st on_ sk z (fullDepArgs st.formula z σ) =
    sk z (pinDepArgs st.formula z on_ false (fullDepArgs st.formula z σ))
  unfold reformRight
  rw [if_neg (by rw [hcont]; simp), if_neg hnotpin, if_neg hno]

/-!
## Paper Lemma 2: reformed paths satisfy every clause

> **Lemma 2** Let M be a model for a DQBF Φ, let P be a path in M and let u
> be a universal variable appearing in Φ. Then ref(P,M,u) satisfies every
> clause in the matrix of Φ.

Paper proof (verbatim structure, left stage; `σ on_ = false`, comp = flip):

1. Suppose `ref(P)` falsifies clause `C`; show `comp(P) = (flipUniv on_ σ, sk)`
   falsifies `C`, contradicting the model property at `flipUniv on_ σ`.
2. "Since P satisfies C, there exists an existential variable x appearing in
   C on which P and ref(P,M,u) disagree." — from `hall σ` get a literal
   `lx ∈ C` true under `(σ, sk)`, false under `(σ, ref)`. Its variable `x`
   is existential (universals keep their values), `on_`-dependent and
   *reformed* (else its value is unchanged), so with
   `v := varValue (flip σ) sk x` the refusal test failed:
   `(1)  ¬ DeletePurePath st on_ (mkLit on_ true) (mkLit x (!v))`,
   and `lx = mkLit x (!v)` (true under sk at σ, false under the reformed
   value `v`), and `litValue (flip σ) sk lx = false` (its value there is `v`).
3. "we cannot have u ∈ C": `mkLit on_ false ∈ C` is impossible (true under
   `(σ, ref)` since `σ on_ = false`); `mkLit on_ true ∈ C` gives the
   one-clause path `DeletePurePath.first` from `mkLit on_ true` to `lx`
   (side conditions: `mkLit on_ false ∉ C`, `x` existential and dependent),
   contradicting (1). Universal literals (≠ on_) of C keep their (false)
   values under the flip.
4. Existential `ly ∈ C`, `var ly = y ≠ x`, `on_ ∉ depset y`: value unchanged
   under both the reform and the flip — still false.
5. Existential `ly ∈ C`, `y ≠ x`, `on_ ∈ depset y` (paper step "(u,¬l) ∉ C_Φ"):
   if `litValue (flip σ) sk ly = true` then `ly = mkLit y vy` with
   `vy := varValue (flip σ) sk y`, and the refusal literal for `y` at `σ` is
   `mkLit y (!vy) = ¬ly`. A path `mkLit on_ true → ¬ly` would extend through
   `C` (via `deletePurePath_step_from_opposite_target_tail`-style step with
   connector `¬ly`, endpoint `lx`; `mkLit on_ false ∉ C` from step 3) to a
   path `mkLit on_ true → lx`, contradicting (1). So no such path, the
   reform of `y` at `σ` fires (`varValue_reformLeft_reformed`), giving
   `litValue σ ref ly = true` — contradicting "ref falsifies C".
   Hence `litValue (flip σ) sk ly = false`.
6. All literals of `C` are false under `(flipUniv on_ σ, sk)`:
   `matrixValue_false_of_false_clause` contradicts `hall (flipUniv on_ σ)`. ∎
-/
theorem reformLeft_matrix_true
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    {sk : SkolemAssignment}
    (hall : ∀ σ, st.clauses.matrixValue st.formula σ sk = true) :
    ∀ σ, st.clauses.matrixValue st.formula σ (reformLeft st on_ sk) = true := by
  sorry

/-- Mirror of `reformLeft_matrix_true` for the right stage (paper Lemma 2
    applied to right paths: start literal `mkLit on_ false`, half-space
    `σ on_ = true`). The proof is the same with polarities swapped. -/
theorem reformRight_matrix_true
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    {sk : SkolemAssignment}
    (hall : ∀ σ, st.clauses.matrixValue st.formula σ sk = true) :
    ∀ σ, st.clauses.matrixValue st.formula σ (reformRight st on_ sk) = true := by
  sorry

/-!
## Paper Lemma 4: the reformed model exhibits the independence

> **Lemma 4** ... For each j with uᵢ ∉ Sⱼ′, ref(M,uᵢ) exhibits the
> independence of xⱼ on uᵢ.

Paper proof (verbatim structure; `A := varValue σ sk of_` at `σ on_ = false`,
`B := varValue (flip σ) sk of_`; `P′ := reformLeft` values,
`P″/Q″ := reformSkolem` values; left reform preserves the `u`-side, right
reform preserves the `¬u`-side):

1. Case `A = B`: the left reform of `of_` at `σ` returns the same value in
   both branches (`v = B = A`), so `P′ = A`; the right reform of the flip
   side has candidate value `P′ = A` and original `B = A`, so `Q″ = A = P″`
   "unconditionally".
2. Case `A ≠ B` (WLOG by `cases` on `A`): by `NoDeleteCrossPaths` (Def. 10),
   for the literal pairing `(mkLit on_ true → mkLit of_ (!B))` /
   `(mkLit on_ false → mkLit of_ B)` at least one path is absent
   (`noDeleteCrossPathsSet_not_deletePurePath_pair_of_fullCorrect` after
   array-completeness):
   - 2a. If `¬ DeletePurePath … (mkLit on_ true) (mkLit of_ (!B))`: the left
     reform fires (`varValue_reformLeft_reformed`), `P′ = B`; now the two
     sides agree and case-1 reasoning gives `P″ = Q″ = B`.
   - 2b. Else that path exists, so the left reform is refused
     (`varValue_reformLeft_refused`), `P′ = A`; cross-freedom then denies
     `DeletePurePath … (mkLit on_ false) (mkLit of_ B)`. Note `B = !A`
     here, so the right-reform refusal literal for the flip side,
     `mkLit of_ (!P′) = mkLit of_ (!A) = mkLit of_ B`, has no path: the
     right reform fires (`varValue_reformRight_reformed`) and
     `Q″ = P′ = A = P″`. ∎
-/
private theorem flipUniv_flipUniv (on_ : Var) (σ : UnivAssignment) :
    flipUniv on_ (flipUniv on_ σ) = σ := by
  funext w
  by_cases h : w == on_ <;> simp [flipUniv, h]

/-- The core of paper Lemma 4, for one variable and one assignment on the
    `¬u` half-space; see the case analysis transcribed above. -/
private theorem reformSkolem_flip_eq_of_on_false
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    (sk : SkolemAssignment) {of_ : Var} (hof : of_ ∈ vars.toList)
    (hexi_of : st.formula.isVarExistential of_ = true)
    (hcont_of : (st.formula.depset.getD of_ #[]).contains on_ = true)
    {σ : UnivAssignment} (hσ : σ on_ = false) :
    st.formula.varValue σ (reformSkolem st on_ sk) of_ =
      st.formula.varValue (flipUniv on_ σ) (reformSkolem st on_ sk) of_ := by
  have hσf : (flipUniv on_ σ) on_ = true := by simp [flipUniv, hσ]
  have hff : flipUniv on_ (flipUniv on_ σ) = σ := flipUniv_flipUniv on_ σ
  -- right reform preserves the ¬u side: LHS is the left-reform value P′
  have hLHS : st.formula.varValue σ (reformSkolem st on_ sk) of_ =
      st.formula.varValue σ (reformLeft st on_ sk) of_ :=
    varValue_reformRight_of_on_false st on_ (reformLeft st on_ sk) hσ
  -- left reform preserves the u side: Q′ = Q (value B)
  have hB : st.formula.varValue (flipUniv on_ σ) (reformLeft st on_ sk) of_ =
      st.formula.varValue (flipUniv on_ σ) sk of_ :=
    varValue_reformLeft_of_on_true st on_ sk hσf
  by_cases hR : DeletePurePath st on_ (mkLit on_ false)
      (mkLit of_ (!(st.formula.varValue (flipUniv on_ (flipUniv on_ σ))
        (reformLeft st on_ sk) of_)))
  · -- right reform refused: Q″ = Q′ = B; show P′ = B
    have hQ : st.formula.varValue (flipUniv on_ σ) (reformSkolem st on_ sk) of_ =
        st.formula.varValue (flipUniv on_ σ) (reformLeft st on_ sk) of_ :=
      varValue_reformRight_refused st on_ (reformLeft st on_ sk)
        hexi_of hcont_of hσf hR
    by_cases hL : DeletePurePath st on_ (mkLit on_ true)
        (mkLit of_ (!(st.formula.varValue (flipUniv on_ σ) sk of_)))
    · -- both refused: P′ = A; either A = B, or cross paths contradict
      have hP : st.formula.varValue σ (reformLeft st on_ sk) of_ =
          st.formula.varValue σ sk of_ :=
        varValue_reformLeft_refused st on_ sk hexi_of hcont_of hσ hL
      rw [hLHS, hP, hQ, hB]
      by_cases hAB : st.formula.varValue σ sk of_ =
          st.formula.varValue (flipUniv on_ σ) sk of_
      · exact hAB
      · exfalso
        have hBA : st.formula.varValue (flipUniv on_ σ) sk of_ =
            !(st.formula.varValue σ sk of_) := by
          revert hAB
          cases st.formula.varValue σ sk of_ <;>
            cases st.formula.varValue (flipUniv on_ σ) sk of_ <;> simp
        rw [hff, hP] at hR
        rw [hBA, Bool.not_not] at hL
        exact noDeleteCrossPathsSet_not_deletePurePath_pair_of_fullCorrect
          hfull hon_le hon_univ hpaths hof hL hR
    · -- left reform fired: P′ = B directly
      have hP : st.formula.varValue σ (reformLeft st on_ sk) of_ =
          st.formula.varValue (flipUniv on_ σ) sk of_ :=
        varValue_reformLeft_reformed st on_ sk hexi_of hcont_of hσ hL
      rw [hLHS, hP, hQ, hB]
  · -- right reform fired: Q″ takes the value from the ¬u side, i.e. P′
    have hQ : st.formula.varValue (flipUniv on_ σ) (reformSkolem st on_ sk) of_ =
        st.formula.varValue (flipUniv on_ (flipUniv on_ σ))
          (reformLeft st on_ sk) of_ :=
      varValue_reformRight_reformed st on_ (reformLeft st on_ sk)
        hexi_of hcont_of hσf hR
    rw [hLHS, hQ, hff]

theorem reformSkolem_exhibits_mem
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hexi : ∀ of_ ∈ vars.toList, st.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (st.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    (sk : SkolemAssignment) :
    ExhibitsDeleteIndependenceSet st.formula vars on_
      (reformSkolem st on_ sk) := by
  intro of_ hof
  rw [exhibitsDeleteIndependence_iff_flipUniv st.formula of_ on_ _
    (hexi of_ hof)]
  intro σ
  cases hσ : σ on_ with
  | false =>
      exact reformSkolem_flip_eq_of_on_false hfull hon_le hon_univ hpaths sk
        hof (hexi of_ hof) (hcontains of_ hof) hσ
  | true =>
      have hσf : (flipUniv on_ σ) on_ = false := by simp [flipUniv, hσ]
      have h := reformSkolem_flip_eq_of_on_false hfull hon_le hon_univ hpaths
        sk hof (hexi of_ hof) (hcontains of_ hof) hσf
      rw [flipUniv_flipUniv] at h
      exact h.symm

/-!
## Paper Theorem 8 / Wimmer et al. Theorem 11 (single-universal instance)
-/

/-- **Full exhibition of the reflexive resolution-path dependency scheme.**

If no variable of `vars` is connected to both polarities of the universal
`on_` by `on_`-pure resolution paths (`NoDeleteCrossPathsSet`, certified by
the executable `getReachable` BFS), then any model of the formula can be
repaired into a model whose Skolem functions for every `of_ ∈ vars` are
simultaneously independent of `on_` (`DeleteIndependenceSetBridge`).

Known true: Beyersdorff–Blinkhorn–Chew–Schmidt–Suda (JAR 2019), Theorem 8,
via Wimmer–Wimmer–Scholl–Becker (SAT 2016), Theorems 3–4; see the module
header and `docs/papers/`. The witness is the two-stage reformed model
`reformSkolem`; the obligations are the Lemma 2 analogues
(`reformLeft_matrix_true`, `reformRight_matrix_true`) and the Lemma 4
analogue (`reformSkolem_exhibits_mem`). -/
theorem deleteIndependenceSetBridge_of_noDeleteCrossPathsSet
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, st.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (st.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet st vars on_) :
    DeleteIndependenceSetBridge st vars on_ := by
  intro htrue
  rcases htrue with ⟨sk, hall⟩
  exact ⟨reformSkolem st on_ sk,
    reformRight_matrix_true hfull hon_le hon_univ
      (reformLeft_matrix_true hfull hon_le hon_univ hall),
    reformSkolem_exhibits_mem hfull hon_le hon_univ hexi hcontains hpaths sk⟩
