import DqratLean.DependencyRemovalNarrative
open Std.Do

/-!
# Dependency-Removal `computeDeps` Frontier

This module hosts the cached active-set consumer layer for dependency
removal.

The TeX-interleaved proof stack now lives below it in
`DependencyRemovalCore` and `DependencyRemovalNarrative`. The remaining task
here is to instantiate that proof story for the active cached set produced by
`computeDeps`, without dragging the old `Soundness.lean` monolith back into
this proof boundary.
-/

/-!
For the checker-level `computeDeps` integration, the semantic target is not yet
the one-variable deletion statement.  The cached `indepOf[on_ - 1]` set first
produces a whole-set deletion statement, and only then do we project back to a
single variable.

The remaining open bridge below is exactly the point where the paper-side
dependency-removal argument still has to be instantiated for the cached active
set produced by `computeDeps`.
-/

/-!
The active cached set already supplies the three data families used throughout
the dependency-removal proof:

* every cached variable is existential,
* every cached variable is later than `on_`,
* every cached variable still contains `on_` in its dependency set.

What is still missing is the dynamic part: starting from any failed repair
candidate in this cached active set, show that the repair loop can continue.
This is the semantic point where the cached-set `computeDeps` invariants must
be matched against the repair-pool frontier analysis.
-/
private theorem computeDeps_activeDeletion_externalDiagnostic_of_existential
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_)
    (hnotMem : of_ ∉ vars.toList)
    (hexi : s.formula.isVarExistential of_ = true)
    (hcontains : (s.formula.depset.getD of_ #[]).contains on_ = true) :
    ¬ on_ < of_ ∨
      ∃ pos : Bool,
        (getReachable s (mkLit on_ true)).getD
            (mkLit of_ pos).x false = true ∧
        (getReachable s (mkLit on_ false)).getD
            (mkLit of_ (!pos)).x false = true := by
  rcases externalDiagnostic_of_noCrossDepClosedSet_not_mem
      hnoCrossClosed hnotMem hcontains with
    hnotExivar | hrest
  · exfalso
    exact hnotExivar (exivars_complete_of_FullCorrect hfull of_ hexi)
  · exact hrest

private theorem computeDeps_activeDeletion_reachPair_of_existential_gt
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_)
    (hnotMem : of_ ∉ vars.toList)
    (hexi : s.formula.isVarExistential of_ = true)
    (hgt : on_ < of_)
    (hcontains : (s.formula.depset.getD of_ #[]).contains on_ = true) :
    ∃ pos : Bool,
      (getReachable s (mkLit on_ true)).getD
          (mkLit of_ pos).x false = true ∧
      (getReachable s (mkLit on_ false)).getD
          (mkLit of_ (!pos)).x false = true := by
  rcases computeDeps_activeDeletion_externalDiagnostic_of_existential
      dqbf cs hfull hnoCrossClosed hnotMem hexi hcontains with
    hnotGt | hpair
  · exact False.elim (hnotGt hgt)
  · exact hpair

private theorem computeDeps_activeDeletion_noForbiddenPair
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hpaths : NoDeleteCrossPathsSet s vars on_) :
    ∀ {badOf : Var} {pos : Bool},
      badOf ∈ vars.toList →
      DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
      DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
      False := by
  intro badOf pos hof hposPath hnegPath
  exact noDeleteCrossPathsSet_forbids_deletePurePath_pair
    (dqbf := dqbf) (cs := cs) (st := s) (vars := vars)
    (on_ := on_) (of_ := badOf) (pos := pos)
    hfull hon_le hon_univ hpaths hof hposPath hnegPath

private theorem computeDeps_activeDeletion_currentWitness_trackedStrictStep
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ of_ : Var}
    {skBase skCand : SkolemAssignment} {σ₀ : UnivAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hof : of_ ∈ vars.toList)
    (hwit : DeleteDepWitness s.formula of_ on_ skCand σ₀) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand :=
  dependencyRemoval_currentWitness_trackedStrictStep_of_noForbiddenPair
    (s := s) (vars := vars) (on_ := on_) (of_ := of_)
    (skBase := skBase) (skCand := skCand) (σ₀ := σ₀)
    hexi hcontains
    (computeDeps_activeDeletion_noForbiddenPair
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      hfull hon_le hon_univ hpaths)
    htracked hof hwit

private theorem computeDeps_activeDeletion_pathBranch_trackedStrictStep
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hbranch : FlexibleRepairPathBranch s vars on_ skBase skCand σ) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand :=
  dependencyRemoval_pathBranch_trackedStrictStep
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    (skBase := skBase) (skCand := skCand) (σ := σ)
    hfull hon_le hon_univ hexi hcontains hpaths htracked hbranch

private theorem computeDeps_activeDeletion_blockedPathBranch_trackedStrictStep
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {startPos : Bool} {skBase skCand : SkolemAssignment}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hbranch :
      PatchPoolBlockedPathBranch s vars on_ startPos skBase skCand) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand :=
  dependencyRemoval_blockedPathBranch_trackedStrictStep
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
    (startPos := startPos) (skBase := skBase) (skCand := skCand)
    hfull hon_le hon_univ hexi hcontains hpaths htracked hbranch

/-!
For the cached active-set continuation, the external branch only needs the
honest diagnostic split produced by `DeleteDependencyNoCrossDepClosedSet`:

* either `flipVar` is not later than `on_`, or
* there is a two-sided reach pair witnessing the forbidden external
  interaction.

Under `FullCorrect`, the dummy `flipVar ∉ exivars` case in the older
external-diagnostic interface is impossible, so we normalize to this smaller
handler shape before feeding the cached local-frontier assembly.
-/
private abbrev ComputeDepsActiveDeletionExternalDiagnosticLocalContinuation
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand : SkolemAssignment} {σ τ : UnivAssignment}
    {flipVar : Var},
    (∀ ρ, s.clauses.matrixValue s.formula ρ skBase = true) →
    FlexibleRepairPoolCandidate s vars on_ skBase skCand →
    flipVar ∉ vars.toList →
    s.formula.varValue σ skCand flipVar =
      s.formula.varValue σ skBase flipVar →
    DeleteDepWitness s.formula flipVar on_ skCand σ →
    DeleteDepWitness s.formula flipVar on_ skBase σ →
    s.formula.isVarExistential flipVar = true →
    (s.formula.depset.getD flipVar #[]).contains on_ = true →
    ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
      (mkLit flipVar (s.formula.varValue σ skCand flipVar)) →
    ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
      (mkLit flipVar (s.formula.varValue σ skBase flipVar)) →
    (¬ on_ < flipVar ∨
      ∃ pos : Bool,
        (getReachable s (mkLit on_ true)).getD
            (mkLit flipVar pos).x false = true ∧
        (getReachable s (mkLit on_ false)).getD
            (mkLit flipVar (!pos)).x false = true) →
    TargetRepairProgressCandidate s vars on_ skBase
      (patchDeleteWitnessAt s.formula flipVar σ skCand) →
    s.clauses.matrixValue s.formula τ
      (patchDeleteWitnessAt s.formula flipVar σ skCand) = false →
    DeleteIndependenceDescentOutcome s vars on_ skBase

private theorem computeDeps_activeDeletion_externalPatchFailureContinuation_of_diagnostic
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_)
    (hexternal :
      ComputeDepsActiveDeletionExternalDiagnosticLocalContinuation
        s vars on_) :
    FlexibleRepairExternalPatchFailureContinuation s vars on_ := by
  intro skBase skCand σ τ flipVar hall hpool hnotMem hvalEq hwitCand
    hwitBase hexiFlip hcontainsFlip hnoPathCand hnoPathBase hprogress
    hfalse
  have hdiag :
      ¬ on_ < flipVar ∨
        ∃ pos : Bool,
          (getReachable s (mkLit on_ true)).getD
              (mkLit flipVar pos).x false = true ∧
          (getReachable s (mkLit on_ false)).getD
              (mkLit flipVar (!pos)).x false = true :=
    computeDeps_activeDeletion_externalDiagnostic_of_existential
      dqbf cs hfull hnoCrossClosed hnotMem hexiFlip hcontainsFlip
  exact hexternal hall hpool hnotMem hvalEq hwitCand hwitBase hexiFlip
    hcontainsFlip hnoPathCand hnoPathBase hdiag hprogress hfalse

/-!
For the same-clause restartable-failure branch, the exact missing local packet
is the cached current-frontier handler.  This is the point where the two-patch
same-clause residual has already been unpacked into one concrete current
frontier, and the proof must continue from that named frontier data rather than
from the older closed-set wrapper.
-/
private abbrev ComputeDepsActiveDeletionSameClauseCurrentFrontierHandler
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  DependencyRemovalSameClauseConcreteCurrentFrontierHandler s vars on_

private abbrev
    ComputeDepsActiveDeletionCurrentFrontierRemovedWitnessLowPhaseProgress
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  DependencyRemovalCurrentFrontierRemovedWitnessLowPhaseProgressDischarge
    s vars on_

private theorem
    computeDeps_activeDeletion_currentFrontierHandler_of_removedWitnessLowPhase
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ of_ ∈ vars.toList,
      s.formula.isVarExistential of_ = true)
    (hlow :
      ComputeDepsActiveDeletionCurrentFrontierRemovedWitnessLowPhaseProgress
        s vars on_) :
    ComputeDepsActiveDeletionSameClauseCurrentFrontierHandler s vars on_ := by
  intro skBase skCand skNext σ hallBase htracked hfalse htwo
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hcurrent hexact
  have hobs :
      DependencyRemovalRemovedCurrentWitnessFrontierObservation
        s vars on_ skBase skCand :=
    dependencyRemoval_removedCurrentWitnessFrontierObservation_of_currentFrontier
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked hcurrent
  rcases hlow hallBase htracked hfalse htwo hproperCand htrackedNext
      hltNextBase hproperNext hsubsetCandNext hcurrent hexact hobs with
    hlocal | hrank
  · exact hlocal
  · rcases hrank with ⟨phaseNext, hltRank⟩
    exact Or.inr
      ⟨skNext, htrackedNext,
        dependencyRemoval_twoTierLowPhase_lt_to_count_lt
          (s := s) (vars := vars) (on_ := on_)
          (phaseNext := phaseNext) (skBase := skBase)
          (skCand := skCand) (skNext := skNext) hltRank⟩

private abbrev
    ComputeDepsActiveDeletionExternalInternalChangedLiteralHandoff
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand : SkolemAssignment} {σ τ : UnivAssignment}
    {flipVar : Var} {cref : CRef} {c : Clause} {l : Literal},
    (∀ ρ, s.clauses.matrixValue s.formula ρ skBase = true) →
    FlexibleRepairPoolCandidate s vars on_ skBase skCand →
    flipVar ∉ vars.toList →
    s.formula.varValue σ skCand flipVar =
      s.formula.varValue σ skBase flipVar →
    DeleteDepWitness s.formula flipVar on_ skCand σ →
    DeleteDepWitness s.formula flipVar on_ skBase σ →
    s.formula.isVarExistential flipVar = true →
    (s.formula.depset.getD flipVar #[]).contains on_ = true →
    ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
      (mkLit flipVar (s.formula.varValue σ skCand flipVar)) →
    ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
      (mkLit flipVar (s.formula.varValue σ skBase flipVar)) →
    (¬ on_ < flipVar ∨
      ∃ pos : Bool,
        (getReachable s (mkLit on_ true)).getD
            (mkLit flipVar pos).x false = true ∧
        (getReachable s (mkLit on_ false)).getD
            (mkLit flipVar (!pos)).x false = true) →
    TargetRepairProgressCandidate s vars on_ skBase
      (patchDeleteWitnessAt s.formula flipVar σ skCand) →
    s.clauses.matrixValue s.formula τ
      (patchDeleteWitnessAt s.formula flipVar σ skCand) = false →
    s.clauses.getClause cref = some c →
    s.formula.clauseValue τ skCand c.lits = false →
    l ∈ c.lits.toList →
    l.var ∈ vars.toList →
    s.formula.litValue τ skBase l = true →
    s.formula.litValue τ skCand l = false →
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) l →
    DeleteIndependenceDescentOutcome s vars on_ skBase

private abbrev
    ComputeDepsActiveDeletionExternalFlipDiagnosticContinuation
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand : SkolemAssignment} {σ τ : UnivAssignment}
    {flipVar : Var} {cref : CRef} {c : Clause} {l : Literal},
    (∀ ρ, s.clauses.matrixValue s.formula ρ skBase = true) →
    FlexibleRepairPoolCandidate s vars on_ skBase skCand →
    flipVar ∉ vars.toList →
    s.formula.varValue σ skCand flipVar =
      s.formula.varValue σ skBase flipVar →
    DeleteDepWitness s.formula flipVar on_ skCand σ →
    DeleteDepWitness s.formula flipVar on_ skBase σ →
    s.formula.isVarExistential flipVar = true →
    (s.formula.depset.getD flipVar #[]).contains on_ = true →
    ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
      (mkLit flipVar (s.formula.varValue σ skCand flipVar)) →
    ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
      (mkLit flipVar (s.formula.varValue σ skBase flipVar)) →
    (¬ on_ < flipVar ∨
      ∃ pos : Bool,
        (getReachable s (mkLit on_ true)).getD
            (mkLit flipVar pos).x false = true ∧
        (getReachable s (mkLit on_ false)).getD
            (mkLit flipVar (!pos)).x false = true) →
    TargetRepairProgressCandidate s vars on_ skBase
      (patchDeleteWitnessAt s.formula flipVar σ skCand) →
    s.clauses.matrixValue s.formula τ
      (patchDeleteWitnessAt s.formula flipVar σ skCand) = false →
    s.clauses.getClause cref = some c →
    s.formula.clauseValue τ
      (patchDeleteWitnessAt s.formula flipVar σ skCand) c.lits =
        false →
    l ∈ c.lits.toList →
    l.var = flipVar →
    s.formula.litValue τ skCand l = true →
    s.formula.litValue τ
      (patchDeleteWitnessAt s.formula flipVar σ skCand) l = false →
    ¬ DeletePurePath s on_ (mkLit on_ (!(τ on_))) l →
    DeleteIndependenceDescentOutcome s vars on_ skBase

private theorem
    computeDeps_activeDeletion_externalDiagnosticLocalContinuation_of_branchHandoffs
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hinternal :
      ComputeDepsActiveDeletionExternalInternalChangedLiteralHandoff
        s vars on_)
    (hflip :
      ComputeDepsActiveDeletionExternalFlipDiagnosticContinuation
        s vars on_) :
    ComputeDepsActiveDeletionExternalDiagnosticLocalContinuation
      s vars on_ := by
  intro skBase skCand σ τ flipVar hall hpool hnotMem hvalEq
    hwitCand hwitBase hexiFlip hcontainsFlip hnoPathCand hnoPathBase
    hdiag hprogress hfalse
  rcases
      flexibleRepairPoolCandidate_external_patch_false_matrix_internal_or_flip
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σSeed := σ) (τ := τ)
        (flipVar := flipVar)
        hpool hall hexiFlip hcontainsFlip hnoPathCand hfalse with
    hinternalBranch | hflipBranch
  · rcases hinternalBranch with
      ⟨cref, c, l, hget, hclauseFalseCand, hlmem, hlvar,
        hltrue, hlfalse, hnoPathLit⟩
    exact hinternal hall hpool hnotMem hvalEq hwitCand hwitBase
      hexiFlip hcontainsFlip hnoPathCand hnoPathBase hdiag hprogress
      hfalse hget hclauseFalseCand hlmem hlvar hltrue hlfalse
      hnoPathLit
  · rcases hflipBranch with
      ⟨cref, c, l, hget, hclauseFalsePatch, hlmem, hlvar,
        hltrue, hlfalse, hnoPathLit⟩
    exact hflip hall hpool hnotMem hvalEq hwitCand hwitBase
      hexiFlip hcontainsFlip hnoPathCand hnoPathBase hdiag hprogress
      hfalse hget hclauseFalsePatch hlmem hlvar hltrue hlfalse
      hnoPathLit

/-!
The last checker-side handoff now splits cleanly into two reusable packets:

* the cached same-clause current-frontier handler used by the residual
  pipeline, and
* the external diagnostic continuation used for the culprit flip branch.

The remaining work is precisely to connect the non-culprit
`matrix_internal_or_flip` subcase back into this cached current-frontier
packet.  Keeping that seam here leaves the local repair theorem below as pure
orchestration.
-/
private theorem
    computeDeps_activeDeletion_removedWitnessLowPhase_externalBranchHandoffs
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (s.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_) :
    ComputeDepsActiveDeletionCurrentFrontierRemovedWitnessLowPhaseProgress
        s vars on_ ∧
      ComputeDepsActiveDeletionExternalInternalChangedLiteralHandoff
        s vars on_ ∧
      ComputeDepsActiveDeletionExternalFlipDiagnosticContinuation
        s vars on_ := by
  /-
  Smaller remaining seam:

  * the current-frontier same-clause branch has been reduced to the existing
    removed-witness low-phase narrative discharge; and
  * the external patch-false diagnostic branch has been split by
    `flexibleRepairPoolCandidate_external_patch_false_matrix_internal_or_flip`.

  The internal-literal side is now exactly the missing candidate-to-tracked
  frontier handoff.  The culprit-flip side remains the explicit reduced
  diagnostic continuation; no opaque theorem hides either branch.
  -/
  sorry

private theorem
    computeDeps_activeDeletion_removedWitnessLowPhase_externalDiagnosticHandoff
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (s.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_) :
    ComputeDepsActiveDeletionCurrentFrontierRemovedWitnessLowPhaseProgress
        s vars on_ ∧
      ComputeDepsActiveDeletionExternalDiagnosticLocalContinuation
        s vars on_ := by
  rcases
      computeDeps_activeDeletion_removedWitnessLowPhase_externalBranchHandoffs
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
        hfull hon_le hon_univ hgt hexi hcontains hpaths hnoCrossClosed with
    ⟨hlow, hinternal, hflip⟩
  exact
    ⟨hlow,
      computeDeps_activeDeletion_externalDiagnosticLocalContinuation_of_branchHandoffs
        (s := s) (vars := vars) (on_ := on_) hinternal hflip⟩

private theorem
    computeDeps_activeDeletion_cachedCurrentFrontierHandoff
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (s.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_) :
    ComputeDepsActiveDeletionSameClauseCurrentFrontierHandler s vars on_ ∧
      ComputeDepsActiveDeletionExternalDiagnosticLocalContinuation
        s vars on_ := by
  rcases
      computeDeps_activeDeletion_removedWitnessLowPhase_externalDiagnosticHandoff
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
        hfull hon_le hon_univ hgt hexi hcontains hpaths hnoCrossClosed with
    ⟨hlow, hexternal⟩
  exact
    ⟨computeDeps_activeDeletion_currentFrontierHandler_of_removedWitnessLowPhase
        (s := s) (vars := vars) (on_ := on_) hexi hlow,
      hexternal⟩

/-!
For the cached `computeDeps` consumer, the remaining semantic packet is kept at
the tracked repair-pool level used by the narrative proof.  The proof still
has to account for the same two semantic frontier shapes

* a same-clause restart for tracked repair candidates already inside the
  cached active set;
* an external patch whose failure exposes either the reduced diagnostic or a
  new cached current-frontier state.

But those cases are no longer re-exposed through a generic
`FlexibleRepairPoolContinuation` wrapper.  The checker-side bridge below should
consume one tracked false-restart theorem, obtained from a local strict-false
step theorem and nothing stronger.
-/

/-!
\paragraph{TeX guide to the remaining frontier.}

Let `vars` be the cached active set returned by `computeDeps`.  The static
part of the dependency-removal proof is already done for this set:

* every member of `vars` is existential,
* every member of `vars` lies strictly after `on_`,
* every member of `vars` still contains `on_` in its dependency set.

So the only remaining task is dynamic.  Starting from a failed initial patch
candidate, show that the repair search can continue.

There are exactly two frontier shapes that still need mathematical content
inside the tracked repair loop:

* a same-clause failure for a tracked repair candidate already in the cached
  active set;
* an external patch whose second patch also fails.

For the external branch, `DeleteDependencyNoCrossDepClosedSet` gives the
reduced diagnostic

* `¬ on_ < flipVar`, or
* a two-sided reach pair from `on_` to `flipVar`.

The old dummy branch `flipVar ∉ exivars` is ruled out here by `FullCorrect`.

The subtle point is that a failed external patch need not mean the patched
literal itself caused the new false clause.  The local core split allows a
second possibility: the patched candidate was already false on some internal
cached literal.  That is a genuine current-frontier restart state, not an
immediate contradiction.  Therefore the theorem below must be read as the
exact tracked local-step packet:

* same-clause failures must continue inside the cached active set;
* external patch failures must either finish directly from the reduced
  diagnostic, or hand the proof back to the cached current-frontier restart.

This is the point where the narrative current-frontier argument has to be
instantiated for the cached `computeDeps` active set without climbing back to
the old generic pool wrapper.
-/
private theorem
    computeDeps_activeDeletion_failedTrackedCandidate_trackedStrictStep_or_external_or_sameClauseFailure
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (s.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false) :
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand ∨
      (∃ flipVar,
        flipVar ∉ vars.toList ∧
        s.formula.varValue σ skCand flipVar =
          s.formula.varValue σ skBase flipVar ∧
        DeleteDepWitness s.formula flipVar on_ skCand σ ∧
        DeleteDepWitness s.formula flipVar on_ skBase σ ∧
        s.formula.isVarExistential flipVar = true ∧
        (s.formula.depset.getD flipVar #[]).contains on_ = true ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
          (mkLit flipVar (s.formula.varValue σ skCand flipVar)) ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
          (mkLit flipVar (s.formula.varValue σ skBase flipVar)) ∧
        TargetRepairProgressCandidate s vars on_ skBase
          (patchDeleteWitnessAt s.formula flipVar σ skCand)) ∨
      FlexibleRepairSameClauseFlipFailure s vars on_ skBase skCand σ := by
  rcases
      flexibleRepairPoolTracked_false_matrix_step_or_pathBranch_or_external_or_sameClauseFlipFailure
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand)
        hon_univ hgt hexi hcontains htracked hallBase hfalse with
    hstrict | hrest
  · exact Or.inl hstrict
  · rcases hrest with hpath | hrest
    · exact Or.inl
        (computeDeps_activeDeletion_pathBranch_trackedStrictStep
          (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
          hfull hon_le hon_univ hexi hcontains hpaths htracked hpath)
    · rcases hrest with hexternal | hsame
      · right
        left
        rcases hexternal with
          ⟨flipVar, hnotMem, hvalEq, hwitCand, hwitBase, hexiFlip,
            hcontainsFlip, hnoPathCand, hnoPathBase, hprogress⟩
        exact ⟨flipVar, hnotMem, hvalEq, hwitCand, hwitBase, hexiFlip,
          hcontainsFlip, hnoPathCand, hnoPathBase, hprogress⟩
      · exact Or.inr (Or.inr hsame)

/-!
After the tracked-candidate split, the only open local repair packet is the
honest hard residual:

* either the current tracked candidate fails on the same clause after flipping
  `on_`, or
* an external patch also fails after the target-progress step.

All immediate strict steps, path branches, and immediately successful external
patches are discharged before this theorem is invoked.
-/
private theorem
    computeDeps_activeDeletion_sameClause_or_externalPatchFalseLocalRepair
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (s.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_)
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hproper :
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false)
    (hhard :
      FlexibleRepairSameClauseFlipFailure s vars on_ skBase skCand σ ∨
      ∃ τ flipVar,
        flipVar ∉ vars.toList ∧
        s.formula.varValue σ skCand flipVar =
          s.formula.varValue σ skBase flipVar ∧
        DeleteDepWitness s.formula flipVar on_ skCand σ ∧
        DeleteDepWitness s.formula flipVar on_ skBase σ ∧
        s.formula.isVarExistential flipVar = true ∧
        (s.formula.depset.getD flipVar #[]).contains on_ = true ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
          (mkLit flipVar (s.formula.varValue σ skCand flipVar)) ∧
        ¬ DeletePurePath s on_ (mkLit on_ (!(σ on_)))
          (mkLit flipVar (s.formula.varValue σ skBase flipVar)) ∧
        TargetRepairProgressCandidate s vars on_ skBase
          (patchDeleteWitnessAt s.formula flipVar σ skCand) ∧
        s.clauses.matrixValue s.formula τ
          (patchDeleteWitnessAt s.formula flipVar σ skCand) = false) :
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand := by
  rcases
      computeDeps_activeDeletion_cachedCurrentFrontierHandoff
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
        hfull hon_le hon_univ hgt hexi hcontains hpaths hnoCrossClosed with
    ⟨hcurrent, hexternal_local⟩
  have hsame_from_current :
      ComputeDepsActiveDeletionSameClauseCurrentFrontierHandler s vars on_ →
      FlexibleRepairSameClauseFlipFailure s vars on_ skBase skCand σ →
      DependencyRemovalLocalRepairResult s vars on_ skBase skCand := by
    intro hcurrent hsame
    exact
      dependencyRemoval_sameClauseFailure_currentStrictStep_or_outcome_of_residualHandler
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ)
        hexi hcontains
        (dependencyRemoval_sameClauseConcreteNondecreasingResidualHandler_of_current
          (s := s) (vars := vars) (on_ := on_) hexi hcurrent)
        hallBase htracked hproper hfalse hsame
  have hexternal_cont :
      FlexibleRepairExternalPatchFailureContinuation s vars on_ :=
    computeDeps_activeDeletion_externalPatchFailureContinuation_of_diagnostic
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      hfull hnoCrossClosed hexternal_local
  rcases hhard with hsame | hexternal_fail
  · exact hsame_from_current hcurrent hsame
  · rcases hexternal_fail with
      ⟨τ, flipVar, hnotMem, hvalEq, hwitCand, hwitBase, hexiFlip,
        hcontainsFlip, hnoPathCand, hnoPathBase, hprogress, hfalsePatch⟩
    exact Or.inl
      (hexternal_cont hallBase htracked.1 hnotMem hvalEq hwitCand hwitBase
        hexiFlip hcontainsFlip hnoPathCand hnoPathBase hprogress hfalsePatch)

private theorem computeDeps_activeDeletion_trackedStrictFalseStep
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (s.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_) :
    DependencyRemovalTrackedStrictFalseStep s vars on_ := by
  intro skBase skCand σ hallBase htracked hproper hfalse
  rcases
      computeDeps_activeDeletion_failedTrackedCandidate_trackedStrictStep_or_external_or_sameClauseFailure
        (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
        hfull hon_le hon_univ hgt hexi hcontains hpaths hallBase htracked
        hfalse with
    hstrict | hrest
  · exact Or.inr hstrict
  · rcases hrest with hexternal | hsame
    · rcases hexternal with
        ⟨flipVar, hnotMem, hvalEq, hwitCand, hwitBase, hexiFlip,
          hcontainsFlip, hnoPathCand, hnoPathBase, hprogress⟩
      by_cases hfail :
          ∃ τ,
            s.clauses.matrixValue s.formula τ
              (patchDeleteWitnessAt s.formula flipVar σ skCand) = false
      · rcases hfail with ⟨τ, hfalsePatch⟩
        exact
          computeDeps_activeDeletion_sameClause_or_externalPatchFalseLocalRepair
            (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
            hfull hon_le hon_univ hgt hexi hcontains hpaths hnoCrossClosed
            hallBase htracked hproper hfalse
            (Or.inr
              ⟨τ, flipVar, hnotMem, hvalEq, hwitCand, hwitBase, hexiFlip,
                hcontainsFlip, hnoPathCand, hnoPathBase, hprogress,
                hfalsePatch⟩)
      · refine Or.inl ?_
        left
        refine ⟨patchDeleteWitnessAt s.formula flipVar σ skCand, ?_, hprogress.1⟩
        intro τ
        cases hval :
            s.clauses.matrixValue s.formula τ
              (patchDeleteWitnessAt s.formula flipVar σ skCand) with
        | false =>
            exact False.elim (hfail ⟨τ, hval⟩)
        | true =>
            exact rfl
    · exact
        computeDeps_activeDeletion_sameClause_or_externalPatchFalseLocalRepair
          (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
          hfull hon_le hon_univ hgt hexi hcontains hpaths hnoCrossClosed
          hallBase htracked hproper hfalse (Or.inl hsame)

private theorem computeDeps_activeDeletion_trackedFalseRestart
    (dqbf : DQBF) (cs : ClauseStore)
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (s.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hnoCrossClosed : DeleteDependencyNoCrossDepClosedSet s vars on_) :
    DependencyRemovalTrackedFalseRestart s vars on_ :=
  dependencyRemoval_trackedFalseRestart_of_trackedStrictFalseStep
    (s := s) (vars := vars) (on_ := on_)
    (computeDeps_activeDeletion_trackedStrictFalseStep
      dqbf cs hfull hon_le hon_univ hgt hexi hcontains hpaths
      hnoCrossClosed)

private theorem computeDeps_activeDeletionSetBridge
    (dqbf : DQBF) (cs : ClauseStore)
    {s s₁ : CheckState} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon : 0 < on_)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hrun : computeDeps on_ s = .ok () s₁) :
    DeleteIndependenceSetBridge s₁
      (computeDepsActiveDeletionVars s₁ on_) on_ := by
  classical
  let vars := computeDepsActiveDeletionVars s₁ on_
  have hfacts :
      ComputeDepsActiveDeletionFacts s s₁ vars on_ :=
    computeDeps_activeDeletionFacts_filter_contains
      dqbf cs hfull hon hon_le hon_univ hrun
  have hsame : SameFC s s₁ := hfacts.sameFC
  have hexiVars :
      ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true := by
    simpa [hsame.1] using hfacts.hexi
  have hgtVars : ∀ of_ ∈ vars.toList, on_ < of_ := hfacts.gt_on
  have hcontainsVars :
      ∀ of_ ∈ vars.toList,
        (s.formula.depset.getD of_ #[]).contains on_ = true := by
    simpa [hsame.1] using hfacts.contains_on
  have hpathsVars : NoDeleteCrossPathsSet s vars on_ :=
    hfacts.no_cross_paths
  have hnoCrossClosed :
      DeleteDependencyNoCrossDepClosedSet s vars on_ :=
    hfacts.no_cross_dep_closed
  have hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False := by
    exact computeDeps_activeDeletion_noForbiddenPair
      (dqbf := dqbf) (cs := cs) (s := s) (vars := vars) (on_ := on_)
      hfull hon_le hon_univ hpathsVars
  have hrestart :
      DependencyRemovalTrackedFalseRestart s vars on_ :=
    computeDeps_activeDeletion_trackedFalseRestart
      dqbf cs hfull hon_le hon_univ hgtVars hexiVars hcontainsVars
      hpathsVars hnoCrossClosed
  have hbridge_s : DeleteIndependenceSetBridge s vars on_ := by
    exact
      dependencyRemovalBridge_of_initialPatchRestart
        (s := s) (vars := vars) (on_ := on_)
        hexiVars hcontainsVars hnoPair
        (by
          intro of_ sk σ₀ hall hof hwit
          exact dependencyRemoval_selectSeed_of_noForbiddenPair
            (s := s) (vars := vars) (on_ := on_) (of_ := of_)
            (sk := sk) (σ₀ := σ₀) hnoPair hof hwit)
        hrestart
  simpa [vars] using
    (DeleteIndependenceSetBridge.of_sameFC hbridge_s hsame)

/-!
Once the cached active set has a deletion bridge, the set-level force-delete
formula is immediately sound: lower any satisfying witness for the original
formula through the bridge and reuse the generic `forceDelDeps` compression
lemma.
-/
private theorem computeDeps_forceDelDeps_formula_sound
    (dqbf : DQBF) (cs : ClauseStore)
    {s s₁ : CheckState} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon : 0 < on_)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hrun : computeDeps on_ s = .ok () s₁)
    (htrue : DQBFTrue s₁.formula s₁.clauses) :
    DQBFTrue
      (forceDelDeps s₁.formula (computeDepsActiveDeletionVars s₁ on_) on_)
      s₁.clauses := by
  classical
  let vars := computeDepsActiveDeletionVars s₁ on_
  have hfacts :
      ComputeDepsActiveDeletionFacts s s₁ vars on_ :=
    computeDeps_activeDeletionFacts_filter_contains
      dqbf cs hfull hon hon_le hon_univ hrun
  have hexiVars :
      ∀ of_ ∈ vars.toList, s₁.formula.isVarExistential of_ = true :=
    hfacts.hexi
  exact DQBFTrue_forceDelDeps_of_setBridge
    hexiVars
    (computeDeps_activeDeletionSetBridge
      dqbf cs hfull hon hon_le hon_univ hrun)
    htrue

/-!
This is the paper-side projection step: after proving truth for the formula
where every cached active existential drops `on_`, we recover the individual
bridge for any chosen member of that cached set.
-/
private theorem computeDeps_deleteIndependenceBridge_of_member_contains
    (dqbf : DQBF) (cs : ClauseStore)
    {s s₁ : CheckState} {of_ on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon : 0 < on_)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hexi : s.formula.isVarExistential of_ = true)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hrun : computeDeps on_ s = .ok () s₁)
    (hmem : of_ ∈ (s₁.indepOf.getD (on_ - 1) #[]).toList)
    (hcontains : (s₁.formula.depset.getD of_ #[]).contains on_ = true) :
    DeleteIndependenceBridge s₁ of_ on_ := by
  classical
  intro htrue
  have hsame := computeDeps_sameFC_spec on_ s s ⟨rfl, rfl⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hsame
  rw [hrun] at hsame
  rcases hsame with ⟨hformula, _⟩
  have hexi' : s₁.formula.isVarExistential of_ = true := by
    simpa [hformula] using hexi
  have hmemActive :
      of_ ∈ (computeDepsActiveDeletionVars s₁ on_).toList := by
    apply Array.mem_toList_iff.mpr
    unfold computeDepsActiveDeletionVars
    exact Array.mem_filter.mpr
      ⟨Array.mem_toList_iff.mp hmem, hcontains⟩
  have htrueDel :
      DQBFTrue
        (forceDelDeps s₁.formula (computeDepsActiveDeletionVars s₁ on_) on_)
        s₁.clauses :=
    computeDeps_forceDelDeps_formula_sound
      dqbf cs hfull hon hon_le hon_univ hrun htrue
  exact
    (DeleteIndependenceBridge.of_forceDelDepsTrue
      hmemActive hexi' htrueDel) htrue

private theorem computeDeps_forceDelDep_formula_sound_of_member_contains
    (dqbf : DQBF) (cs : ClauseStore)
    {s s₁ : CheckState} {of_ on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon : 0 < on_)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hexi : s.formula.isVarExistential of_ = true)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hrun : computeDeps on_ s = .ok () s₁)
    (hmem : of_ ∈ (s₁.indepOf.getD (on_ - 1) #[]).toList)
    (_hcontains : (s₁.formula.depset.getD of_ #[]).contains on_ = true)
    (htrue : DQBFTrue s₁.formula s₁.clauses) :
    DQBFTrue (s₁.formula.forceDelDep of_ on_) s₁.clauses := by
  have hsame := computeDeps_sameFC_spec on_ s s ⟨rfl, rfl⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hsame
  rw [hrun] at hsame
  rcases hsame with ⟨hformula, _⟩
  have hexi' : s₁.formula.isVarExistential of_ = true := by
    simpa [hformula] using hexi
  exact DQBFTrue_forceDelDep_of_exhibiting_bridge
    s₁.formula s₁.clauses of_ on_ hexi'
    (computeDeps_deleteIndependenceBridge_of_member_contains
      dqbf cs hfull hon hon_le hexi hon_univ hrun hmem _hcontains)
    htrue

private theorem computeDeps_forceDelDep_formula_sound_of_member
    (dqbf : DQBF) (cs : ClauseStore)
    {s s₁ : CheckState} {of_ on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon : 0 < on_)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hexi : s.formula.isVarExistential of_ = true)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hrun : computeDeps on_ s = .ok () s₁)
    (hmem : of_ ∈ (s₁.indepOf.getD (on_ - 1) #[]).toList)
    (htrue : DQBFTrue s₁.formula s₁.clauses) :
    DQBFTrue (s₁.formula.forceDelDep of_ on_) s₁.clauses := by
  cases hcontains : (s₁.formula.depset.getD of_ #[]).contains on_ with
  | true =>
      exact computeDeps_forceDelDep_formula_sound_of_member_contains
        dqbf cs hfull hon hon_le hexi hon_univ hrun hmem hcontains htrue
  | false =>
      exact DQBFTrue_forceDelDep_of_not_contains
        s₁.formula s₁.clauses of_ on_ hcontains htrue

private theorem computeDeps_deleteIndependenceBridge_of_member
    (dqbf : DQBF) (cs : ClauseStore)
    {s s₁ : CheckState} {of_ on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon : 0 < on_)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hexi : s.formula.isVarExistential of_ = true)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hrun : computeDeps on_ s = .ok () s₁)
    (hmem : of_ ∈ (s₁.indepOf.getD (on_ - 1) #[]).toList) :
    DeleteIndependenceBridge s₁ of_ on_ := by
  have hsame := computeDeps_sameFC_spec on_ s s ⟨rfl, rfl⟩
  simp only [WP.wp, PredTrans.apply, EStateM.run] at hsame
  rw [hrun] at hsame
  rcases hsame with ⟨hformula, _⟩
  have hexi' : s₁.formula.isVarExistential of_ = true := by
    simpa [hformula] using hexi
  cases hcontains : (s₁.formula.depset.getD of_ #[]).contains on_ with
  | true =>
      exact computeDeps_deleteIndependenceBridge_of_member_contains
        dqbf cs hfull hon hon_le hexi hon_univ hrun hmem hcontains
  | false =>
      intro htrue
      exact (DeleteIndependenceBridge.of_forceDelDepTrue hexi'
        (DQBFTrue_forceDelDep_of_not_contains
          s₁.formula s₁.clauses of_ on_ hcontains htrue)) htrue

private theorem notDependsOn_true_deleteIndependenceBridge
    (dqbf : DQBF) (cs : ClauseStore)
    {s s₁ : CheckState} {of_ on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon : 0 < on_)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hexi : s.formula.isVarExistential of_ = true)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hrun : notDependsOn of_ on_ s = .ok true s₁) :
    DeleteIndependenceBridge s₁ of_ on_ := by
  unfold notDependsOn at hrun
  cases hdeps : computeDeps on_ s with
  | error e s₂ =>
      simp [Bind.bind, EStateM.bind, hdeps] at hrun
  | ok _ s₂ =>
      have hrun' := hrun
      simp [Bind.bind, EStateM.bind, hdeps, EStateM.get, EStateM.pure, Pure.pure] at hrun'
      injection hrun' with _ hs
      subst hs
      exact computeDeps_deleteIndependenceBridge_of_member
        dqbf cs hfull hon hon_le hexi hon_univ hdeps
        (notDependsOn_true_member_indepOf hrun)
