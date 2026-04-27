import DqratLean.Soundness

/-!
This file contains Lean bookkeeping for the residual case in the dependency
removal proof.

The main narrative proof follows the TeX argument: after a failed repair-pool
candidate, patch another witness and get a strictly smaller candidate.  Lean
also has to track what remains if the two-patch candidate is still not a model.
Those residual facts are collected here so the narrative file can stay close
to the mathematical proof.
-/

/-!
When a two-patch candidate is still not a model, the proof needs to remember
more than the fact that some clause is false.  It needs the concrete changed
literal in that false clause, and which of the two patch fibers caused the
change.
-/

abbrev DependencyRemovalTwoPatchChangedClause
    (s : CheckState) (on_ : Var)
    (skBase skNext : SkolemAssignment)
    (leftLit rightLit : Literal) (σ τ : UnivAssignment) : Prop :=
  ∃ cref c l,
    s.clauses.getClause cref = some c ∧
    s.formula.clauseValue τ skNext c.lits = false ∧
    l ∈ c.lits.toList ∧
    ((l.var = leftLit.var ∧
        s.formula.litValue τ skBase l = true ∧
        s.formula.litValue τ
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase) l =
            false ∧
        PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
          skBase) ∨
      (l.var = rightLit.var ∧
        s.formula.litValue τ
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase) l =
            true ∧
        s.formula.litValue τ skNext l = false ∧
        PatchChangedFiber s.formula s.clauses rightLit.var on_
          (flipUniv on_ σ) τ
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase)))

/-!
The residual branch should not split into two unrelated existential packages:
one saying which two witnesses were patched, and another saying which patched
literal changed in a still-false matrix.  This exact package ties them
together.  The same `leftLit`, `rightLit`, and `τ` feed both the concrete
two-patch residual and the changed-clause fact.
-/

abbrev DependencyRemovalExactTwoPatchResidual
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment)
    (σ : UnivAssignment) : Prop :=
  ∃ cref c leftLit rightLit τ,
    s.clauses.getClause cref = some c ∧
    leftLit ∈ c.lits.toList ∧
    rightLit ∈ c.lits.toList ∧
    leftLit.var ∈ vars.toList ∧
    rightLit.var ∈ vars.toList ∧
    leftLit.var ≠ rightLit.var ∧
    DeleteDepWitness s.formula leftLit.var on_ skBase σ ∧
    ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ ∧
    DeleteDepWitness s.formula rightLit.var on_ skBase
      (flipUniv on_ σ) ∧
    ¬ DeleteDepWitness s.formula rightLit.var on_ skCand
      (flipUniv on_ σ) ∧
    ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
      (mkLit leftLit.var (s.formula.varValue σ skBase leftLit.var)) ∧
    let sk₁ := patchDeleteWitnessAt s.formula leftLit.var σ skBase
    ¬ DeletePurePath s on_ (mkLit on_ (!((flipUniv on_ σ) on_)))
      (mkLit rightLit.var
        (s.formula.varValue (flipUniv on_ σ) sk₁ rightLit.var)) ∧
    s.clauses.matrixValue s.formula τ skNext = false ∧
    skNext =
      patchDeleteWitnessAt s.formula rightLit.var (flipUniv on_ σ)
        (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
    DependencyRemovalTwoPatchChangedClause
      s on_ skBase skNext leftLit rightLit σ τ ∧
    ((PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
          skBase ∧
        ¬ DeleteDepWitness s.formula leftLit.var on_ skNext τ) ∨
      (PatchChangedFiber s.formula s.clauses rightLit.var on_
          (flipUniv on_ σ) τ
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
        ¬ DeleteDepWitness s.formula rightLit.var on_ skNext τ))

theorem dependencyRemoval_exactTwoPatchResidual_concreteResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    FlexibleRepairSameClauseTwoPatchConcreteResidual
      s vars on_ skBase skCand skNext σ := by
  rcases hexact with
    ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem, hrightMem,
      hleftVar, hrightVar, hdistinct, hleftBase, hleftNotCand,
      hrightBase, hrightNotCand, _hleftNoPath, _hrightNoPath,
      hfalse, _hshape, _hchanged, hremoved⟩
  exact ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem,
    hrightMem, hleftVar, hrightVar, hdistinct, hleftBase,
    hleftNotCand, hrightBase, hrightNotCand, hfalse, hremoved⟩

theorem dependencyRemoval_exactTwoPatchResidual_falseMatrix
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ τ, s.clauses.matrixValue s.formula τ skNext = false := by
  rcases hexact with
    ⟨_cref, _c, _leftLit, _rightLit, τ, _hget, _hleftMem,
      _hrightMem, _hleftVar, _hrightVar, _hdistinct, _hleftBase,
      _hleftNotCand, _hrightBase, _hrightNotCand, _hleftNoPath,
      _hrightNoPath, hfalse, _hshape, _hchanged, _hremoved⟩
  exact ⟨τ, hfalse⟩

/-!
The next proof steps need the exact residual contents in a direct form.  This
projection exposes the concrete false clause, the literal that changed, and
the fact that `skNext` is exactly the two-patch Skolem set.
-/

theorem dependencyRemoval_exactTwoPatchResidual_changedLiteral
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ leftLit : Literal, ∃ rightLit : Literal, ∃ τ : UnivAssignment,
    ∃ cref : CRef, ∃ c : Clause, ∃ l : Literal,
      leftLit.var ∈ vars.toList ∧
      rightLit.var ∈ vars.toList ∧
      leftLit.var ≠ rightLit.var ∧
      skNext =
        patchDeleteWitnessAt s.formula rightLit.var (flipUniv on_ σ)
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
      s.clauses.getClause cref = some c ∧
      s.formula.clauseValue τ skNext c.lits = false ∧
      l ∈ c.lits.toList ∧
      ((l.var = leftLit.var ∧
          s.formula.litValue τ skBase l = true ∧
          s.formula.litValue τ
            (patchDeleteWitnessAt s.formula leftLit.var σ skBase) l =
              false ∧
          PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
            skBase) ∨
        (l.var = rightLit.var ∧
          s.formula.litValue τ
            (patchDeleteWitnessAt s.formula leftLit.var σ skBase) l =
              true ∧
          s.formula.litValue τ skNext l = false ∧
          PatchChangedFiber s.formula s.clauses rightLit.var on_
            (flipUniv on_ σ) τ
            (patchDeleteWitnessAt s.formula leftLit.var σ skBase))) := by
  rcases hexact with
    ⟨_seedCref, _seedClause, leftLit, rightLit, τ, _hseedGet,
      _hleftMem, _hrightMem, hleftVar, hrightVar, hdistinct,
      _hleftBase, _hleftNotCand, _hrightBase, _hrightNotCand,
      _hleftNoPath, _hrightNoPath, _hfalse, hshape, hchanged,
      _hremoved⟩
  rcases hchanged with
    ⟨cref, c, l, hget, hclauseFalse, hlmem, hside⟩
  exact ⟨leftLit, rightLit, τ, cref, c, l, hleftVar, hrightVar,
    hdistinct, hshape, hget, hclauseFalse, hlmem, hside⟩

theorem dependencyRemoval_exactTwoPatchResidual_patchFiber
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ leftLit : Literal, ∃ rightLit : Literal, ∃ τ : UnivAssignment,
      leftLit.var ∈ vars.toList ∧
      rightLit.var ∈ vars.toList ∧
      leftLit.var ≠ rightLit.var ∧
      skNext =
        patchDeleteWitnessAt s.formula rightLit.var (flipUniv on_ σ)
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
      (PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
          skBase ∨
        PatchChangedFiber s.formula s.clauses rightLit.var on_
          (flipUniv on_ σ) τ
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase)) := by
  rcases
      dependencyRemoval_exactTwoPatchResidual_changedLiteral
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ) hexact with
    ⟨leftLit, rightLit, τ, _cref, _c, _l, hleftVar, hrightVar,
      hdistinct, hshape, _hget, _hclauseFalse, _hlmem, hside⟩
  refine ⟨leftLit, rightLit, τ, hleftVar, hrightVar, hdistinct,
    hshape, ?_⟩
  rcases hside with hleft | hright
  · exact Or.inl hleft.2.2.2
  · exact Or.inr hright.2.2.2

/-!
If the residual case occurs, the two-patch Skolem set still falsifies the
matrix under some universal assignment.  This is the direct Lean form of
"the candidate is not yet a model."
-/

theorem dependencyRemoval_concreteResidual_falseMatrix
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ τ, s.clauses.matrixValue s.formula τ skNext = false := by
  rcases hresidual with
    ⟨_cref, _c, _leftLit, _rightLit, τ, _hget, _hleftMem,
      _hrightMem, _hleftVar, _hrightVar, _hdistinct,
      _hleftBase, _hleftNotLive, _hrightBase, _hrightNotLive,
      hfalse, _hremoved⟩
  exact ⟨τ, hfalse⟩

/-!
The residual remembers the left witness removed by the two-patch construction.
If that witness is absent from the current candidate, then either the original
side or the flipped side must be a real footprint where the current candidate
differs from the original satisfying Skolem functions.
-/

theorem dependencyRemoval_concreteResidual_leftFootprint
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (htracked :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ leftVar σSide,
      leftVar ∈ vars.toList ∧
      (σSide = σ ∨ σSide = flipUniv on_ σ) ∧
      DeleteDepWitness s.formula leftVar on_ skBase σSide ∧
      s.formula.varValue σSide skCand leftVar ≠
        s.formula.varValue σSide skBase leftVar ∧
      ∀ τ,
        deleteDepArgs s.formula leftVar on_ τ =
          deleteDepArgs s.formula leftVar on_ σSide →
        s.formula.varValue τ skCand leftVar ≠
          s.formula.varValue τ skBase leftVar →
        fullDepArgs s.formula leftVar τ =
          fullDepArgs s.formula leftVar σSide := by
  rcases hresidual with
    ⟨_cref, _c, leftLit, _rightLit, _τ, _hget, _hleftMem,
      _hrightMem, hleftVar, _hrightVar, _hdistinct, hleftBase,
      hleftNotLive, _hrightBase, _hrightNotLive, _hfalse,
      _hremoved⟩
  rcases
      flexibleRepairPoolTracked_removed_baseWitness_changed_footprint
        (s := s) (vars := vars) (on_ := on_) (of_ := leftLit.var)
        (skBase := skBase) (skCand := skCand) (σ := σ)
        htracked hleftVar hleftBase hleftNotLive with
    ⟨σSide, hside, hof, hwitBase, hchanged, hfiber⟩
  exact ⟨leftLit.var, σSide, hof, hside, hwitBase, hchanged,
    hfiber⟩

/-!
The same footprint statement holds for the right witness.  Its distinguished
side starts at $\gamma^u$, so the two possible sides are listed in the opposite
order.
-/

theorem dependencyRemoval_concreteResidual_rightFootprint
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (htracked :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ rightVar σSide,
      rightVar ∈ vars.toList ∧
      (σSide = flipUniv on_ σ ∨ σSide = σ) ∧
      DeleteDepWitness s.formula rightVar on_ skBase σSide ∧
      s.formula.varValue σSide skCand rightVar ≠
        s.formula.varValue σSide skBase rightVar ∧
      ∀ τ,
        deleteDepArgs s.formula rightVar on_ τ =
          deleteDepArgs s.formula rightVar on_ σSide →
        s.formula.varValue τ skCand rightVar ≠
          s.formula.varValue τ skBase rightVar →
        fullDepArgs s.formula rightVar τ =
          fullDepArgs s.formula rightVar σSide := by
  rcases hresidual with
    ⟨_cref, _c, _leftLit, rightLit, _τ, _hget, _hleftMem,
      _hrightMem, _hleftVar, hrightVar, _hdistinct, _hleftBase,
      _hleftNotLive, hrightBase, hrightNotLive, _hfalse,
      _hremoved⟩
  rcases
      flexibleRepairPoolTracked_removed_baseWitness_changed_footprint
        (s := s) (vars := vars) (on_ := on_) (of_ := rightLit.var)
        (skBase := skBase) (skCand := skCand)
        (σ := flipUniv on_ σ)
        htracked hrightVar hrightBase hrightNotLive with
    ⟨σSide, hside, hof, hwitBase, hchanged, hfiber⟩
  have hside' :
      σSide = flipUniv on_ σ ∨ σSide = σ := by
    rcases hside with hsame | hflip
    · exact Or.inl hsame
    · right
      rw [hflip]
      funext v
      by_cases hv : v = on_
      · subst v
        simp [flipUniv]
      · simp [flipUniv, hv]
  exact ⟨rightLit.var, σSide, hof, hside', hwitBase, hchanged,
    hfiber⟩

/-!
If every dependency witness of the current candidate is also present in the
two-patch candidate, then a witness missing from the two-patch candidate is
already missing from the current candidate.  This lets the residual talk about
the same blocked witness from either candidate.
-/

theorem dependencyRemoval_concreteResidual_missingCandidateSide
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    (∃ leftVar τ,
      leftVar ∈ vars.toList ∧
      PatchChangedFiber s.formula s.clauses leftVar on_ σ τ
        skBase ∧
      ¬ DeleteDepWitness s.formula leftVar on_ skCand τ) ∨
    ∃ leftVar rightVar τ,
      leftVar ∈ vars.toList ∧
      rightVar ∈ vars.toList ∧
      let sk₁ := patchDeleteWitnessAt s.formula leftVar σ skBase
      PatchChangedFiber s.formula s.clauses rightVar on_
        (flipUniv on_ σ) τ sk₁ ∧
      ¬ DeleteDepWitness s.formula rightVar on_ skCand τ := by
  rcases hresidual with
    ⟨_cref, _c, leftLit, rightLit, τ, _hget, _hleftMem,
      _hrightMem, hleftVar, hrightVar, _hdistinct, _hleftBase,
      _hleftNotLive, _hrightBase, _hrightNotLive, _hfalse,
      hremoved⟩
  rcases hremoved with hleft | hright
  · left
    rcases hleft with ⟨hfiber, hnotNext⟩
    have hnotCand :
        ¬ DeleteDepWitness s.formula leftLit.var on_ skCand τ :=
      deleteWitnessFiberSetSubset_not_deleteDepWitness
        (f := s.formula) (vars := vars) (on_ := on_)
        (of_ := leftLit.var) (skSmall := skCand)
        (skBig := skNext) (σ := τ)
        (hexi leftLit.var hleftVar) hsubsetCandNext hleftVar
        hnotNext
    exact ⟨leftLit.var, τ, hleftVar, hfiber, hnotCand⟩
  · right
    rcases hright with ⟨hfiber, hnotNext⟩
    have hnotCand :
        ¬ DeleteDepWitness s.formula rightLit.var on_ skCand τ :=
      deleteWitnessFiberSetSubset_not_deleteDepWitness
        (f := s.formula) (vars := vars) (on_ := on_)
        (of_ := rightLit.var) (skSmall := skCand)
        (skBig := skNext) (σ := τ)
        (hexi rightLit.var hrightVar) hsubsetCandNext hrightVar
        hnotNext
    exact ⟨leftLit.var, rightLit.var, τ, hleftVar, hrightVar,
      hfiber, hnotCand⟩

/-!
The same conversion can be stated without losing the concrete clause carried
by the residual.  This named frontier keeps the two same-clause seed literals,
the false assignment for the two-patch candidate, and the patch fiber that is
already absent from the current candidate.
-/

abbrev DependencyRemovalCurrentResidualFrontier
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment)
    (σ : UnivAssignment) : Prop :=
  ∃ cref c leftLit rightLit τ,
    s.clauses.getClause cref = some c ∧
    leftLit ∈ c.lits.toList ∧
    rightLit ∈ c.lits.toList ∧
    leftLit.var ∈ vars.toList ∧
    rightLit.var ∈ vars.toList ∧
    leftLit.var ≠ rightLit.var ∧
    DeleteDepWitness s.formula leftLit.var on_ skBase σ ∧
    ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ ∧
    DeleteDepWitness s.formula rightLit.var on_ skBase
      (flipUniv on_ σ) ∧
    ¬ DeleteDepWitness s.formula rightLit.var on_ skCand
      (flipUniv on_ σ) ∧
    s.clauses.matrixValue s.formula τ skNext = false ∧
    ((PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
          skBase ∧
        ¬ DeleteDepWitness s.formula leftLit.var on_ skCand τ) ∨
      (PatchChangedFiber s.formula s.clauses rightLit.var on_
          (flipUniv on_ σ) τ
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
        ¬ DeleteDepWitness s.formula rightLit.var on_ skCand τ))

theorem dependencyRemoval_concreteResidual_currentFrontier
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ := by
  rcases hresidual with
    ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem, hrightMem,
      hleftVar, hrightVar, hdistinct, hleftBase, hleftNotLive,
      hrightBase, hrightNotLive, hfalse, hremoved⟩
  have hremovedCand :
      (PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
            skBase ∧
          ¬ DeleteDepWitness s.formula leftLit.var on_ skCand τ) ∨
        (PatchChangedFiber s.formula s.clauses rightLit.var on_
            (flipUniv on_ σ) τ
            (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
          ¬ DeleteDepWitness s.formula rightLit.var on_ skCand τ) := by
    rcases hremoved with hleft | hright
    · left
      rcases hleft with ⟨hfiber, hnotNext⟩
      exact ⟨hfiber,
        deleteWitnessFiberSetSubset_not_deleteDepWitness
          (f := s.formula) (vars := vars) (on_ := on_)
          (of_ := leftLit.var) (skSmall := skCand)
          (skBig := skNext) (σ := τ)
          (hexi leftLit.var hleftVar) hsubsetCandNext hleftVar
          hnotNext⟩
    · right
      rcases hright with ⟨hfiber, hnotNext⟩
      exact ⟨hfiber,
        deleteWitnessFiberSetSubset_not_deleteDepWitness
          (f := s.formula) (vars := vars) (on_ := on_)
          (of_ := rightLit.var) (skSmall := skCand)
          (skBig := skNext) (σ := τ)
          (hexi rightLit.var hrightVar) hsubsetCandNext hrightVar
          hnotNext⟩
  exact ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem,
    hrightMem, hleftVar, hrightVar, hdistinct, hleftBase,
    hleftNotLive, hrightBase, hrightNotLive, hfalse, hremovedCand⟩

theorem dependencyRemoval_exactTwoPatchResidual_currentFrontier
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ :=
  dependencyRemoval_concreteResidual_currentFrontier
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (skNext := skNext) (σ := σ)
    hexi hsubsetCandNext
    (dependencyRemoval_exactTwoPatchResidual_concreteResidual
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ) hexact)

/-!
If a dependency witness is present at one full dependency argument vector, it
is present at any other assignment with the same full dependency argument
vector.  Lean needs this small transport lemma when a false residual clause
points to a patch fiber at assignment \(\tau\), while the seed witness was
recorded at \(\sigma\).
-/

theorem dependencyRemoval_deleteDepWitness_of_fullDepArgs_eq
    (f : DQBF) (of_ on_ : Var) (σ σ₀ : UnivAssignment)
    (sk : SkolemAssignment)
    (hexi : f.isVarExistential of_ = true)
    (hfull : fullDepArgs f of_ σ = fullDepArgs f of_ σ₀)
    (hwit : DeleteDepWitness f of_ on_ sk σ₀) :
    DeleteDepWitness f of_ on_ sk σ := by
  unfold DeleteDepWitness at hwit ⊢
  have hval :
      f.varValue σ sk of_ = f.varValue σ₀ sk of_ :=
    varValue_eq_of_fullDepArgs_eq f of_ σ σ₀ sk hexi hfull
  have hfullFlip :
      fullDepArgs f of_ (flipUniv on_ σ) =
        fullDepArgs f of_ (flipUniv on_ σ₀) := by
    unfold fullDepArgs
    apply Array.ext (by simp [Array.size_map])
    intro i hi₁ _
    simp only [Array.getElem_map]
    have hi : i < (f.depset.getD of_ #[]).size := by
      simpa [Array.size_map] using hi₁
    have hget :
        (fullDepArgs f of_ σ).getD i false =
          (fullDepArgs f of_ σ₀).getD i false :=
      congrArg (fun a => a.getD i false) hfull
    have hi_left : i < (fullDepArgs f of_ σ).size := by
      simpa [fullDepArgs] using hi
    have hi_right : i < (fullDepArgs f of_ σ₀).size := by
      simpa [fullDepArgs] using hi
    rw [← Array.getElem_eq_getD (h := hi_left),
      ← Array.getElem_eq_getD (h := hi_right)] at hget
    simp only [fullDepArgs, Array.getElem_map] at hget
    unfold flipUniv
    by_cases hdep : (f.depset.getD of_ #[])[i] = on_
    · rw [if_pos hdep, if_pos hdep, hget]
    · rw [if_neg hdep, if_neg hdep, hget]
  have hflip :
      f.varValue (flipUniv on_ σ) sk of_ =
        f.varValue (flipUniv on_ σ₀) sk of_ :=
    varValue_eq_of_fullDepArgs_eq
      f of_ (flipUniv on_ σ) (flipUniv on_ σ₀) sk hexi
      hfullFlip
  intro heq
  exact hwit
    (by
      calc
        f.varValue σ₀ sk of_ = f.varValue σ sk of_ := hval.symm
        _ = f.varValue (flipUniv on_ σ) sk of_ := heq
        _ = f.varValue (flipUniv on_ σ₀) sk of_ := hflip)

/-!
A `PatchChangedFiber` says that the assignment \(\tau\) lies in the same full
dependency fiber as the seed assignment.  Therefore a seed dependency witness
can be read at \(\tau\) as well.
-/

theorem dependencyRemoval_deleteDepWitness_of_patchChangedFiber
    (f : DQBF) (cs : ClauseStore) {of_ on_ : Var}
    {σ₀ τ : UnivAssignment} {sk : SkolemAssignment}
    (hexi : f.isVarExistential of_ = true)
    (hwit : DeleteDepWitness f of_ on_ sk σ₀)
    (hfiber : PatchChangedFiber f cs of_ on_ σ₀ τ sk) :
    DeleteDepWitness f of_ on_ sk τ :=
  dependencyRemoval_deleteDepWitness_of_fullDepArgs_eq
    f of_ on_ τ σ₀ sk hexi hfiber.2.1 hwit

/-!
The residual false clause now has the exact form needed for the next chase
step: one patch fiber is absent from the current candidate, but it is still a
real witness of the original satisfying Skolem functions.  Since the current
candidate is tracked, that absence forces a concrete changed footprint between
the current candidate and the original one.
-/

abbrev DependencyRemovalCurrentResidualPatchFootprint
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand _skNext : SkolemAssignment)
    (_σ : UnivAssignment) : Prop :=
  ∃ patched τ σSide,
    patched ∈ vars.toList ∧
    ¬ DeleteDepWitness s.formula patched on_ skCand τ ∧
    DeleteDepWitness s.formula patched on_ skBase τ ∧
    (σSide = τ ∨ σSide = flipUniv on_ τ) ∧
    DeleteDepWitness s.formula patched on_ skBase σSide ∧
    s.formula.varValue σSide skCand patched ≠
      s.formula.varValue σSide skBase patched ∧
    ∀ ρ,
      deleteDepArgs s.formula patched on_ ρ =
        deleteDepArgs s.formula patched on_ σSide →
      s.formula.varValue ρ skCand patched ≠
        s.formula.varValue ρ skBase patched →
      fullDepArgs s.formula patched ρ =
        fullDepArgs s.formula patched σSide

theorem dependencyRemoval_currentResidual_patchFootprint
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hcurrent :
      DependencyRemovalCurrentResidualFrontier
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalCurrentResidualPatchFootprint
      s vars on_ skBase skCand skNext σ := by
  rcases hcurrent with
    ⟨_cref, _c, leftLit, rightLit, τ, _hget, _hleftMem,
      _hrightMem, hleftVar, hrightVar, hdistinct, hleftBase,
      _hleftNotLive, hrightBase, _hrightNotLive, _hfalse,
      hremoved⟩
  rcases hremoved with hleft | hright
  · rcases hleft with ⟨hfiber, hnotCand⟩
    have hbaseτ :
        DeleteDepWitness s.formula leftLit.var on_ skBase τ :=
      dependencyRemoval_deleteDepWitness_of_patchChangedFiber
        s.formula s.clauses (hexi leftLit.var hleftVar) hleftBase
        hfiber
    rcases
        flexibleRepairPoolTracked_removed_baseWitness_changed_footprint
          (s := s) (vars := vars) (on_ := on_)
          (of_ := leftLit.var) (skBase := skBase)
          (skCand := skCand) (σ := τ)
          htracked hleftVar hbaseτ hnotCand with
      ⟨σSide, hside, _hof, hwitSide, hchanged, hfiberSide⟩
    exact ⟨leftLit.var, τ, σSide, hleftVar, hnotCand, hbaseτ,
      hside, hwitSide, hchanged, hfiberSide⟩
  · rcases hright with ⟨hfiber, hnotCand⟩
    let sk₁ := patchDeleteWitnessAt s.formula leftLit.var σ skBase
    have hrightBase₁ :
        DeleteDepWitness s.formula rightLit.var on_ sk₁
          (flipUniv on_ σ) := by
      dsimp [sk₁]
      exact
        (deleteDepWitness_patchDeleteWitnessAt_iff_of_ne
          s.formula leftLit.var rightLit.var on_ σ
          (flipUniv on_ σ) skBase (Ne.symm hdistinct)).2
          hrightBase
    have hbaseτ₁ :
        DeleteDepWitness s.formula rightLit.var on_ sk₁ τ :=
      dependencyRemoval_deleteDepWitness_of_patchChangedFiber
        s.formula s.clauses (hexi rightLit.var hrightVar)
        hrightBase₁ (by simpa [sk₁] using hfiber)
    have hbaseτ :
        DeleteDepWitness s.formula rightLit.var on_ skBase τ := by
      dsimp [sk₁] at hbaseτ₁
      exact
        (deleteDepWitness_patchDeleteWitnessAt_iff_of_ne
          s.formula leftLit.var rightLit.var on_ σ τ skBase
          (Ne.symm hdistinct)).1 hbaseτ₁
    rcases
        flexibleRepairPoolTracked_removed_baseWitness_changed_footprint
          (s := s) (vars := vars) (on_ := on_)
          (of_ := rightLit.var) (skBase := skBase)
          (skCand := skCand) (σ := τ)
          htracked hrightVar hbaseτ hnotCand with
      ⟨σSide, hside, _hof, hwitSide, hchanged, hfiberSide⟩
    exact ⟨rightLit.var, τ, σSide, hrightVar, hnotCand, hbaseτ,
      hside, hwitSide, hchanged, hfiberSide⟩

/-!
Conversely, if every dependency witness of the two-patch candidate is also
present in the current candidate, the seed witnesses missing from the current
candidate are still missing from the two-patch candidate.
-/

theorem dependencyRemoval_concreteResidual_seedMissingNextSide
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ leftVar rightVar,
      leftVar ∈ vars.toList ∧
      rightVar ∈ vars.toList ∧
      ¬ DeleteDepWitness s.formula leftVar on_ skNext σ ∧
      ¬ DeleteDepWitness s.formula rightVar on_ skNext
        (flipUniv on_ σ) := by
  rcases hresidual with
    ⟨_cref, _c, leftLit, rightLit, _τ, _hget, _hleftMem,
      _hrightMem, hleftVar, hrightVar, _hdistinct, _hleftBase,
      hleftNotLive, _hrightBase, hrightNotLive, _hfalse,
      _hremoved⟩
  have hleftNotNext :
      ¬ DeleteDepWitness s.formula leftLit.var on_ skNext σ :=
    deleteWitnessFiberSetSubset_not_deleteDepWitness
      (f := s.formula) (vars := vars) (on_ := on_)
      (of_ := leftLit.var) (skSmall := skNext)
      (skBig := skCand) (σ := σ)
      (hexi leftLit.var hleftVar) hsubsetNextCand hleftVar
      hleftNotLive
  have hrightNotNext :
      ¬ DeleteDepWitness s.formula rightLit.var on_ skNext
        (flipUniv on_ σ) :=
    deleteWitnessFiberSetSubset_not_deleteDepWitness
      (f := s.formula) (vars := vars) (on_ := on_)
      (of_ := rightLit.var) (skSmall := skNext)
      (skBig := skCand) (σ := flipUniv on_ σ)
      (hexi rightLit.var hrightVar) hsubsetNextCand hrightVar
      hrightNotLive
  exact ⟨leftLit.var, rightLit.var, hleftVar, hrightVar,
    hleftNotNext, hrightNotNext⟩

/-!
When the current candidate and the two-patch candidate have equivalent
dependency-witness footprints, the residual can be read as a single frontier:
the seed witnesses are absent on both sides, and the false assignment points
to a patch fiber already absent from the current candidate.
-/

theorem dependencyRemoval_concreteResidual_equivalentFrontier
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    ∃ cref c leftLit rightLit τ,
      s.clauses.getClause cref = some c ∧
      leftLit ∈ c.lits.toList ∧
      rightLit ∈ c.lits.toList ∧
      leftLit.var ∈ vars.toList ∧
      rightLit.var ∈ vars.toList ∧
      leftLit.var ≠ rightLit.var ∧
      DeleteDepWitness s.formula leftLit.var on_ skBase σ ∧
      ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ ∧
      ¬ DeleteDepWitness s.formula leftLit.var on_ skNext σ ∧
      DeleteDepWitness s.formula rightLit.var on_ skBase
        (flipUniv on_ σ) ∧
      ¬ DeleteDepWitness s.formula rightLit.var on_ skCand
        (flipUniv on_ σ) ∧
      ¬ DeleteDepWitness s.formula rightLit.var on_ skNext
        (flipUniv on_ σ) ∧
      s.clauses.matrixValue s.formula τ skNext = false ∧
      ((PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
            skBase ∧
          ¬ DeleteDepWitness s.formula leftLit.var on_ skCand τ) ∨
        (PatchChangedFiber s.formula s.clauses rightLit.var on_
            (flipUniv on_ σ) τ
            (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
          ¬ DeleteDepWitness s.formula rightLit.var on_ skCand τ)) := by
  rcases hresidual with
    ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem,
      hrightMem, hleftVar, hrightVar, hdistinct, hleftBase,
      hleftNotLive, hrightBase, hrightNotLive, hfalse,
      hremoved⟩
  have hleftNotNext :
      ¬ DeleteDepWitness s.formula leftLit.var on_ skNext σ :=
    deleteWitnessFiberSetSubset_not_deleteDepWitness
      (f := s.formula) (vars := vars) (on_ := on_)
      (of_ := leftLit.var) (skSmall := skNext)
      (skBig := skCand) (σ := σ)
      (hexi leftLit.var hleftVar) hsubsetNextCand hleftVar
      hleftNotLive
  have hrightNotNext :
      ¬ DeleteDepWitness s.formula rightLit.var on_ skNext
        (flipUniv on_ σ) :=
    deleteWitnessFiberSetSubset_not_deleteDepWitness
      (f := s.formula) (vars := vars) (on_ := on_)
      (of_ := rightLit.var) (skSmall := skNext)
      (skBig := skCand) (σ := flipUniv on_ σ)
      (hexi rightLit.var hrightVar) hsubsetNextCand hrightVar
      hrightNotLive
  have hremovedCand :
      (PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
            skBase ∧
          ¬ DeleteDepWitness s.formula leftLit.var on_ skCand τ) ∨
        (PatchChangedFiber s.formula s.clauses rightLit.var on_
            (flipUniv on_ σ) τ
            (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
          ¬ DeleteDepWitness s.formula rightLit.var on_ skCand τ) := by
    rcases hremoved with hleft | hright
    · left
      rcases hleft with ⟨hfiber, hnotNext⟩
      exact ⟨hfiber,
        deleteWitnessFiberSetSubset_not_deleteDepWitness
          (f := s.formula) (vars := vars) (on_ := on_)
          (of_ := leftLit.var) (skSmall := skCand)
          (skBig := skNext) (σ := τ)
          (hexi leftLit.var hleftVar) hsubsetCandNext hleftVar
          hnotNext⟩
    · right
      rcases hright with ⟨hfiber, hnotNext⟩
      exact ⟨hfiber,
        deleteWitnessFiberSetSubset_not_deleteDepWitness
          (f := s.formula) (vars := vars) (on_ := on_)
          (of_ := rightLit.var) (skSmall := skCand)
          (skBig := skNext) (σ := τ)
          (hexi rightLit.var hrightVar) hsubsetCandNext hrightVar
          hnotNext⟩
  exact ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem,
    hrightMem, hleftVar, hrightVar, hdistinct, hleftBase,
    hleftNotLive, hleftNotNext, hrightBase, hrightNotLive,
    hrightNotNext, hfalse, hremovedCand⟩

/-!
In the proper-growth residual case, \(f''\) has at least one dependency
witness fiber that \(f'\) does not have.  Such a newly present live witness in
\(f''\) must already come from the original satisfying Skolem functions, and
the current candidate \(f'\) must differ from the original on one of the two
\(u\)-sides of that fiber.
-/

theorem dependencyRemoval_properGrowth_missingChangedFootprint
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htrackedCand :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hproperCandNext :
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skNext) :
    ∃ of_ σ σSide,
      of_ ∈ vars.toList ∧
      DeleteDepWitness s.formula of_ on_ skNext σ ∧
      ¬ DeleteDepWitness s.formula of_ on_ skCand σ ∧
      (σSide = σ ∨ σSide = flipUniv on_ σ) ∧
      DeleteDepWitness s.formula of_ on_ skBase σSide ∧
      s.formula.varValue σSide skCand of_ ≠
        s.formula.varValue σSide skBase of_ ∧
      ∀ τ,
        deleteDepArgs s.formula of_ on_ τ =
          deleteDepArgs s.formula of_ on_ σSide →
        s.formula.varValue τ skCand of_ ≠
          s.formula.varValue τ skBase of_ →
        fullDepArgs s.formula of_ τ =
          fullDepArgs s.formula of_ σSide := by
  rcases deleteWitnessFiberSet_missingAssignment_of_properSubset
      (f := s.formula) (vars := vars) (on_ := on_)
      (skSmall := skCand) (skBig := skNext) hproperCandNext with
    ⟨of_, hof, σ, hwitNext, hnotCand⟩
  rcases
      flexibleRepairPoolTracked_missing_liveWitness_changed_footprint
        (s := s) (vars := vars) (on_ := on_) (of_ := of_)
        (skBase := skBase) (skCand := skCand) (skNext := skNext)
        (σ := σ) (hexi of_ hof) htrackedCand htrackedNext hof
        hwitNext hnotCand with
    ⟨σSide, hside, _hof', hwitBase, hchanged, hfiber⟩
  exact ⟨of_, σ, σSide, hof, hwitNext, hnotCand, hside, hwitBase,
    hchanged, hfiber⟩

/-!
Combining proper growth with the residual record gives all three footprints
that remain for the mathematical argument:

\[
\begin{array}{ll}
  \text{growth:} & \text{a newly present witness of } f'',\\
  \text{left seed:} & \text{the left same-clause witness removed by } f',\\
  \text{right seed:} & \text{the right same-clause witness removed by } f'.
\end{array}
\]

The final disjunct records which two-patch fiber is still absent from the
current candidate, together with the concrete clause where that residual was
observed.
-/

theorem dependencyRemoval_concreteResidual_properGrowthFrontier
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htrackedCand :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hproperCandNext :
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skNext)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    (∃ of_ σGrow σSide,
      of_ ∈ vars.toList ∧
      DeleteDepWitness s.formula of_ on_ skNext σGrow ∧
      ¬ DeleteDepWitness s.formula of_ on_ skCand σGrow ∧
      (σSide = σGrow ∨ σSide = flipUniv on_ σGrow) ∧
      DeleteDepWitness s.formula of_ on_ skBase σSide ∧
      s.formula.varValue σSide skCand of_ ≠
        s.formula.varValue σSide skBase of_ ∧
      ∀ τ,
        deleteDepArgs s.formula of_ on_ τ =
          deleteDepArgs s.formula of_ on_ σSide →
        s.formula.varValue τ skCand of_ ≠
          s.formula.varValue τ skBase of_ →
        fullDepArgs s.formula of_ τ =
          fullDepArgs s.formula of_ σSide) ∧
    (∃ leftVar σSide,
      leftVar ∈ vars.toList ∧
      (σSide = σ ∨ σSide = flipUniv on_ σ) ∧
      DeleteDepWitness s.formula leftVar on_ skBase σSide ∧
      s.formula.varValue σSide skCand leftVar ≠
        s.formula.varValue σSide skBase leftVar ∧
      ∀ τ,
        deleteDepArgs s.formula leftVar on_ τ =
          deleteDepArgs s.formula leftVar on_ σSide →
        s.formula.varValue τ skCand leftVar ≠
          s.formula.varValue τ skBase leftVar →
        fullDepArgs s.formula leftVar τ =
          fullDepArgs s.formula leftVar σSide) ∧
    (∃ rightVar σSide,
      rightVar ∈ vars.toList ∧
      (σSide = flipUniv on_ σ ∨ σSide = σ) ∧
      DeleteDepWitness s.formula rightVar on_ skBase σSide ∧
      s.formula.varValue σSide skCand rightVar ≠
        s.formula.varValue σSide skBase rightVar ∧
      ∀ τ,
        deleteDepArgs s.formula rightVar on_ τ =
          deleteDepArgs s.formula rightVar on_ σSide →
        s.formula.varValue τ skCand rightVar ≠
          s.formula.varValue τ skBase rightVar →
        fullDepArgs s.formula rightVar τ =
          fullDepArgs s.formula rightVar σSide) ∧
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ := by
  exact
    ⟨dependencyRemoval_properGrowth_missingChangedFootprint
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext)
        hexi htrackedCand htrackedNext hproperCandNext,
      dependencyRemoval_concreteResidual_leftFootprint
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        htrackedCand hresidual,
      dependencyRemoval_concreteResidual_rightFootprint
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        htrackedCand hresidual,
      dependencyRemoval_concreteResidual_currentFrontier
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hexi hproperCandNext.1 hresidual⟩

/-!
For the next layer of the proof, it is helpful to name the exact data exposed
by the equivalent-footprint residual.  This is only a type abbreviation: it
does not add a new assumption or hide any proof obligation.
-/

abbrev DependencyRemovalEquivalentFootprintFrontier
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment)
    (σ : UnivAssignment) : Prop :=
  ∃ cref c leftLit rightLit τ,
    s.clauses.getClause cref = some c ∧
    leftLit ∈ c.lits.toList ∧
    rightLit ∈ c.lits.toList ∧
    leftLit.var ∈ vars.toList ∧
    rightLit.var ∈ vars.toList ∧
    leftLit.var ≠ rightLit.var ∧
    DeleteDepWitness s.formula leftLit.var on_ skBase σ ∧
    ¬ DeleteDepWitness s.formula leftLit.var on_ skCand σ ∧
    ¬ DeleteDepWitness s.formula leftLit.var on_ skNext σ ∧
    DeleteDepWitness s.formula rightLit.var on_ skBase
      (flipUniv on_ σ) ∧
    ¬ DeleteDepWitness s.formula rightLit.var on_ skCand
      (flipUniv on_ σ) ∧
    ¬ DeleteDepWitness s.formula rightLit.var on_ skNext
      (flipUniv on_ σ) ∧
    s.clauses.matrixValue s.formula τ skNext = false ∧
    ((PatchChangedFiber s.formula s.clauses leftLit.var on_ σ τ
          skBase ∧
        ¬ DeleteDepWitness s.formula leftLit.var on_ skCand τ) ∨
      (PatchChangedFiber s.formula s.clauses rightLit.var on_
          (flipUniv on_ σ) τ
          (patchDeleteWitnessAt s.formula leftLit.var σ skBase) ∧
        ¬ DeleteDepWitness s.formula rightLit.var on_ skCand τ))

theorem dependencyRemoval_concreteResidual_equivalentFrontier_data
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalEquivalentFootprintFrontier
      s vars on_ skBase skCand skNext σ :=
  dependencyRemoval_concreteResidual_equivalentFrontier
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (skNext := skNext) (σ := σ)
    hexi hsubsetCandNext hsubsetNextCand hresidual

theorem dependencyRemoval_exactTwoPatchResidual_equivalentFrontier_data
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hsubsetNextCand :
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalEquivalentFootprintFrontier
      s vars on_ skBase skCand skNext σ :=
  dependencyRemoval_concreteResidual_equivalentFrontier_data
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (skNext := skNext) (σ := σ)
    hexi hsubsetCandNext hsubsetNextCand
    (dependencyRemoval_exactTwoPatchResidual_concreteResidual
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ) hexact)

/-!
The proper-growth frontier is the analogous named package for the case where
the two-patch candidate has a genuinely larger current-to-next witness
footprint.  The first component is the newly present witness; the next two are
the original left and right same-clause footprints; the final component keeps
the concrete residual clause and missing patch fiber.
-/

abbrev DependencyRemovalProperGrowthFrontier
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand skNext : SkolemAssignment)
    (σ : UnivAssignment) : Prop :=
  (∃ of_ σGrow σSide,
    of_ ∈ vars.toList ∧
    DeleteDepWitness s.formula of_ on_ skNext σGrow ∧
    ¬ DeleteDepWitness s.formula of_ on_ skCand σGrow ∧
    (σSide = σGrow ∨ σSide = flipUniv on_ σGrow) ∧
    DeleteDepWitness s.formula of_ on_ skBase σSide ∧
    s.formula.varValue σSide skCand of_ ≠
      s.formula.varValue σSide skBase of_ ∧
    ∀ τ,
      deleteDepArgs s.formula of_ on_ τ =
        deleteDepArgs s.formula of_ on_ σSide →
      s.formula.varValue τ skCand of_ ≠
        s.formula.varValue τ skBase of_ →
      fullDepArgs s.formula of_ τ =
        fullDepArgs s.formula of_ σSide) ∧
  (∃ leftVar σSide,
    leftVar ∈ vars.toList ∧
    (σSide = σ ∨ σSide = flipUniv on_ σ) ∧
    DeleteDepWitness s.formula leftVar on_ skBase σSide ∧
    s.formula.varValue σSide skCand leftVar ≠
      s.formula.varValue σSide skBase leftVar ∧
    ∀ τ,
      deleteDepArgs s.formula leftVar on_ τ =
        deleteDepArgs s.formula leftVar on_ σSide →
      s.formula.varValue τ skCand leftVar ≠
        s.formula.varValue τ skBase leftVar →
      fullDepArgs s.formula leftVar τ =
        fullDepArgs s.formula leftVar σSide) ∧
  (∃ rightVar σSide,
    rightVar ∈ vars.toList ∧
    (σSide = flipUniv on_ σ ∨ σSide = σ) ∧
    DeleteDepWitness s.formula rightVar on_ skBase σSide ∧
    s.formula.varValue σSide skCand rightVar ≠
      s.formula.varValue σSide skBase rightVar ∧
    ∀ τ,
      deleteDepArgs s.formula rightVar on_ τ =
        deleteDepArgs s.formula rightVar on_ σSide →
      s.formula.varValue τ skCand rightVar ≠
        s.formula.varValue τ skBase rightVar →
      fullDepArgs s.formula rightVar τ =
        fullDepArgs s.formula rightVar σSide) ∧
  DependencyRemovalCurrentResidualFrontier
    s vars on_ skBase skCand skNext σ

theorem dependencyRemoval_concreteResidual_properGrowthFrontier_data
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htrackedCand :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hproperCandNext :
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skNext)
    (hresidual :
      FlexibleRepairSameClauseTwoPatchConcreteResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalProperGrowthFrontier
      s vars on_ skBase skCand skNext σ :=
  dependencyRemoval_concreteResidual_properGrowthFrontier
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (skNext := skNext) (σ := σ)
    hexi htrackedCand htrackedNext hproperCandNext hresidual

theorem dependencyRemoval_exactTwoPatchResidual_properGrowthFrontier_data
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htrackedCand :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (htrackedNext :
      FlexibleRepairPoolTracked s vars on_ skBase skNext)
    (hproperCandNext :
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skNext)
    (hexact :
      DependencyRemovalExactTwoPatchResidual
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalProperGrowthFrontier
      s vars on_ skBase skCand skNext σ :=
  dependencyRemoval_concreteResidual_properGrowthFrontier_data
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (skNext := skNext) (σ := σ)
    hexi htrackedCand htrackedNext hproperCandNext
    (dependencyRemoval_exactTwoPatchResidual_concreteResidual
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ) hexact)

/-!
Both residual frontier cases now expose the same concrete patch footprint.
The proper-growth package already carries a `DependencyRemovalCurrentResidualFrontier`.
The equivalent-footprint package has the same residual data, plus extra facts
saying the seed witnesses are also absent from the two-patch candidate.
-/

theorem dependencyRemoval_equivalentFrontier_currentResidual
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hfrontier :
      DependencyRemovalEquivalentFootprintFrontier
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ := by
  rcases hfrontier with
    ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem,
      hrightMem, hleftVar, hrightVar, hdistinct, hleftBase,
      hleftNotCand, _hleftNotNext, hrightBase, hrightNotCand,
      _hrightNotNext, hfalse, hremoved⟩
  exact ⟨cref, c, leftLit, rightLit, τ, hget, hleftMem,
    hrightMem, hleftVar, hrightVar, hdistinct, hleftBase,
    hleftNotCand, hrightBase, hrightNotCand, hfalse, hremoved⟩

theorem dependencyRemoval_properGrowthFrontier_patchFootprint
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfrontier :
      DependencyRemovalProperGrowthFrontier
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalCurrentResidualPatchFootprint
      s vars on_ skBase skCand skNext σ := by
  exact
    dependencyRemoval_currentResidual_patchFootprint
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hfrontier.2.2.2

theorem dependencyRemoval_equivalentFrontier_patchFootprint
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (htracked :
      FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfrontier :
      DependencyRemovalEquivalentFootprintFrontier
        s vars on_ skBase skCand skNext σ) :
    DependencyRemovalCurrentResidualPatchFootprint
      s vars on_ skBase skCand skNext σ := by
  exact
    dependencyRemoval_currentResidual_patchFootprint
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked
      (dependencyRemoval_equivalentFrontier_currentResidual
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (skNext := skNext) (σ := σ)
        hfrontier)
