import DqratLean.DeletionSemantics
import DqratLean.DeletionPaths

/-!
# Deletion Exhibition (open frontier)

This leaf module contains the single open theorem of the development:
full exhibition of the reflexive resolution-path dependency scheme.
Iterate here: `lake build DqratLean.DeletionExhibition` rebuilds only this
file against the compiled support modules.

The construction (see `docs/deletion_exhibition_proof.md`): repair a model
by *pinning* — each `v ∈ vars` reads its Skolem value from the assignment
whose `on_`-coordinate is forced to a per-variable constant. Exhibition
(flip-invariance) is mechanical and proved below for any polarity choice;
the open obligation is `pinSkolem_matrix_true`, the clause-truth transfer,
which is where `NoDeleteCrossPathsSet` does its work.
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

/-- Dep-vector analogue of `pinUniv`: overwrite every coordinate of `args`
    that belongs to `on_` in the dependency list of `v` by `c`.
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

/-- The repaired Skolem assignment: members of `vars` read the `cpol`-pinned
    half-space; everything else is untouched. -/
def pinSkolem (f : DQBF) (vars : Array Var) (on_ : Var) (cpol : Var → Bool)
    (sk : SkolemAssignment) : SkolemAssignment :=
  fun v args =>
    if vars.contains v then sk v (pinDepArgs f v on_ (cpol v) args)
    else sk v args

theorem varValue_pinSkolem_of_mem
    (f : DQBF) (vars : Array Var) (on_ : Var) (cpol : Var → Bool)
    (sk : SkolemAssignment) (σ : UnivAssignment) {v : Var}
    (hmem : v ∈ vars.toList)
    (hexi : f.isVarExistential v = true) :
    f.varValue σ (pinSkolem f vars on_ cpol sk) v =
      f.varValue (pinUniv on_ (cpol v) σ) sk v := by
  have hcontains : vars.contains v = true := by
    simpa [Array.contains_iff_mem] using hmem
  rw [DQBF.varValue, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
  show pinSkolem f vars on_ cpol sk v (fullDepArgs f v σ) =
    sk v (fullDepArgs f v (pinUniv on_ (cpol v) σ))
  rw [fullDepArgs_pinUniv]
  simp only [pinSkolem, hcontains]
  simp

theorem varValue_pinSkolem_of_not_mem
    (f : DQBF) (vars : Array Var) (on_ : Var) (cpol : Var → Bool)
    (sk : SkolemAssignment) (σ : UnivAssignment) {v : Var}
    (hmem : v ∉ vars.toList) :
    f.varValue σ (pinSkolem f vars on_ cpol sk) v = f.varValue σ sk v := by
  have hcontains : vars.contains v = false := by
    by_cases h : vars.contains v = true
    · exact absurd (by simpa [Array.contains_iff_mem] using h) hmem
    · simpa using h
  by_cases hexi : f.isVarExistential v = true
  · rw [DQBF.varValue, DQBF.varValue, hexi, DQBF.exiValue, DQBF.exiValue]
    show pinSkolem f vars on_ cpol sk v (fullDepArgs f v σ) =
      sk v (fullDepArgs f v σ)
    simp only [pinSkolem, hcontains, Bool.false_eq_true]
    simp
  · have hexi' : f.isVarExistential v = false := by
      simpa using hexi
    rw [DQBF.varValue, DQBF.varValue, hexi']
    simp

/-- Exhibition is mechanical for the pinned witness: pinned variables read
    only the pinned half-space, so their value is flip-invariant. Holds for
    ANY polarity choice `cpol`. -/
theorem pinSkolem_exhibits
    (f : DQBF) (vars : Array Var) (on_ : Var) (cpol : Var → Bool)
    (sk : SkolemAssignment)
    (hexi : ∀ of_ ∈ vars.toList, f.isVarExistential of_ = true) :
    ExhibitsDeleteIndependenceSet f vars on_
      (pinSkolem f vars on_ cpol sk) := by
  intro of_ hof
  rw [exhibitsDeleteIndependence_iff_flipUniv f of_ on_ _ (hexi of_ hof)]
  intro σ
  rw [varValue_pinSkolem_of_mem f vars on_ cpol sk σ hof (hexi of_ hof),
    varValue_pinSkolem_of_mem f vars on_ cpol sk (flipUniv on_ σ) hof
      (hexi of_ hof),
    pinUniv_flipUniv]

/-- Polarity choice: pin `v` to `true` (the `on_ := true` half-space) exactly
    when the negative reach cone touches `v`. Cross-path freedom for
    `vars`-members makes this the side their cone structure permits.
    (Subject to revision while `pinSkolem_matrix_true` is developed.) -/
def negConeTouch (st : CheckState) (on_ : Var) (v : Var) : Bool :=
  (getReachable st (mkLit on_ false)).getD (v * 2) false ||
    (getReachable st (mkLit on_ false)).getD (v * 2 + 1) false

/-- **The open obligation: clause-truth transfer for the pinned witness.**

A clause false under the pinned witness at `σ` must contain, in each
half-space, a true literal whose class analysis (see
`docs/deletion_exhibition_proof.md`) forces `on_`-pure resolution paths from
both polarities of `on_` to some `of_ ∈ vars` at opposite literal
polarities — killed by `noDeleteCrossPathsSet_not_deletePurePath_pair`.
The value-oriented path-extension lemmas live in `DeletionPaths.lean`
(`noDeleteCrossPathsSet_orients_seed`,
`deletePurePath_step_from_opposite_target_tail`,
`oriented_dependent_tail_forces_next_old_lit_nonpath`). -/
private theorem pinSkolem_matrix_true
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, st.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (st.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet st vars on_)
    {sk : SkolemAssignment}
    (hall : ∀ σ, st.clauses.matrixValue st.formula σ sk = true) :
    ∀ σ, st.clauses.matrixValue st.formula σ
      (pinSkolem st.formula vars on_ (negConeTouch st on_) sk) = true := by
  sorry

/-- **Full exhibition of the reflexive resolution-path dependency scheme.**

If no variable of `vars` is connected to both polarities of the universal
`on_` by `on_`-pure resolution paths (`NoDeleteCrossPathsSet`, certified by
the executable `getReachable` BFS), then any model of the formula can be
repaired into a model whose Skolem functions for every `of_ ∈ vars` are
simultaneously independent of `on_` (`DeleteIndependenceSetBridge`).

This statement is known to be true: the reflexive resolution-path dependency
scheme is *fully exhibited* for DQBF. See R. Wimmer, K. Wimmer, C. Scholl,
B. Becker, "Dependency Schemes for DQBF" (SAT 2016), and O. Beyersdorff,
J. Blinkhorn, "Reinterpreting Dependency Schemes: Soundness Meets
Incompleteness in DQBF" (J. Automated Reasoning, 2019). The repair is the
pinning construction above; the open obligation is `pinSkolem_matrix_true`. -/
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
  exact ⟨pinSkolem st.formula vars on_ (negConeTouch st on_) sk,
    pinSkolem_matrix_true hfull hon_le hon_univ hgt hexi hcontains hpaths hall,
    pinSkolem_exhibits st.formula vars on_ (negConeTouch st on_) sk hexi⟩
