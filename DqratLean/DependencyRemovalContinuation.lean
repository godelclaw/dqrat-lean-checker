import DqratLean.DependencyRemovalDescent

/-!
This file contains the continuation bookkeeping behind the finite descent
paragraph of the dependency-removal proof.

The narrative proof follows the TeX argument directly.  The lemmas here make
one proof-engineering point explicit: once a failed tracked repair candidate
can be replaced by a strictly smaller tracked repair candidate, finite descent
turns that local step into a global outcome.
-/

/-!
In the TeX proof, the induction step says:

\[
  \text{if } f' \in \mathcal{M} \text{ is not a model, then there is }
  f'' \in \mathcal{M}
  \text{ with a proper subset of the remaining } u\text{-witnesses.}
\]

Lean separates the local step from the finite-descent wrapper.  A local repair
result is exactly the TeX induction-step conclusion: either the proof already
has an outcome, or it has a strictly smaller tracked candidate.
-/

abbrev DependencyRemovalLocalRepairResult
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase skCand : SkolemAssignment) : Prop :=
  DependencyRemovalDescentOutcome s vars on_ skBase ∨
    FlexibleRepairTrackedStrictStep s vars on_ skBase skCand

/-!
A `DependencyRemovalTrackedStrictFalseStep` is the local step specialized to a
failed, tracked repair candidate.
-/

abbrev DependencyRemovalTrackedStrictFalseStep
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand

/-!
The two-patch same-clause branch has one residual case: the two-patch
candidate is still not a model, but it is not smaller than the current
candidate by the plain witness count.  A residual handler is any argument that
continues that remaining case with the same local repair result.
-/

abbrev DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    (deleteWitnessFiberCountSet s.formula vars on_ skCand <
        deleteWitnessFiberCountSet s.formula vars on_ skNext ∨
      DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand) →
    ¬ deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand

/-!
Inside this residual, the footprint relation between the current candidate
\(f'\) and the two-patch candidate \(f''\) has two possible shapes.

The first shape is proper growth: every current witness fiber is still present
in \(f''\), and at least one additional current-to-two-patch witness fiber has
appeared.  This is not a decrease by the current count, but it is a concrete
case the proof can analyze.
-/

abbrev DependencyRemovalSameClauseConcreteProperGrowthResidualHandler
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skNext →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand

/-!
The second shape is equivalent footprint: the two candidates have the same
dependency-witness fibers, in both subset directions.  The residual facts in
`DependencyRemovalResidual` record the exact witnesses and missing fibers that
remain to be analyzed in that case.
-/

abbrev DependencyRemovalSameClauseConcreteEquivalentFootprintResidualHandler
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand →
    deleteWitnessFiberCountSet s.formula vars on_ skNext =
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand

/-!
Both footprint shapes contain the same local TeX data needed for the next
repair: a concrete residual false clause and a patch fiber already absent from
the current candidate.  A current-frontier handler is an argument that works
from exactly that shared data.
-/

abbrev DependencyRemovalSameClauseConcreteCurrentFrontierHandler
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DependencyRemovalCurrentResidualFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand

/-!
After the proper-growth residual has been unpacked, the remaining proof can
work from the explicit frontier facts rather than from the full residual
record.  A frontier handler is exactly such an argument.
-/

abbrev DependencyRemovalSameClauseConcreteProperGrowthFrontierHandler
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skNext →
    DependencyRemovalProperGrowthFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand

/-!
The equivalent-footprint branch gets the same treatment: all residual
bookkeeping is converted into the named frontier package before the
mathematical argument is applied.
-/

abbrev DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierHandler
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand skNext : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    s.clauses.matrixValue s.formula σ skCand = false →
    FlexibleRepairSameClauseTwoPolarityFailure
      s vars on_ skBase skCand σ →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    FlexibleRepairPoolTracked s vars on_ skBase skNext →
    deleteWitnessFiberCountSet s.formula vars on_ skNext <
      deleteWitnessFiberCountSet s.formula vars on_ skBase →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase →
    DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext →
    DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand →
    deleteWitnessFiberCountSet s.formula vars on_ skNext =
      deleteWitnessFiberCountSet s.formula vars on_ skCand →
    DependencyRemovalEquivalentFootprintFrontier
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalExactTwoPatchResidual
      s vars on_ skBase skCand skNext σ →
    DependencyRemovalLocalRepairResult s vars on_ skBase skCand

theorem dependencyRemoval_sameClauseConcreteProperGrowthResidualHandler_of_frontier
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hfrontier :
      DependencyRemovalSameClauseConcreteProperGrowthFrontierHandler
        s vars on_) :
    DependencyRemovalSameClauseConcreteProperGrowthResidualHandler
      s vars on_ := by
  intro skBase skCand skNext σ hall htracked hfalse hfailure
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hproperCandNext hexact
  exact hfrontier hall htracked hfalse hfailure hproperCand
    htrackedNext hltNextBase hproperNext hsubsetCandNext
    hproperCandNext
    (dependencyRemoval_exactTwoPatchResidual_properGrowthFrontier_data
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi htracked htrackedNext hproperCandNext hexact)
    hexact

theorem dependencyRemoval_sameClauseConcreteEquivalentFootprintResidualHandler_of_frontier
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hfrontier :
      DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierHandler
        s vars on_) :
    DependencyRemovalSameClauseConcreteEquivalentFootprintResidualHandler
      s vars on_ := by
  intro skBase skCand skNext σ hall htracked hfalse hfailure
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsubsetNextCand hcountEq hexact
  exact hfrontier hall htracked hfalse hfailure hproperCand
    htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsubsetNextCand hcountEq
    (dependencyRemoval_exactTwoPatchResidual_equivalentFrontier_data
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hexi hsubsetCandNext hsubsetNextCand hexact)
    hexact

/-!
The proper-growth frontier and equivalent-footprint frontier both reduce to
the current-frontier data above.  This is the Lean version of focusing the TeX
induction step on the one residual false clause, instead of keeping two
separate architectural branches alive.
-/

theorem dependencyRemoval_sameClauseConcreteProperGrowthFrontierHandler_of_current
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hcurrent :
      DependencyRemovalSameClauseConcreteCurrentFrontierHandler
        s vars on_) :
    DependencyRemovalSameClauseConcreteProperGrowthFrontierHandler
      s vars on_ := by
  intro skBase skCand skNext σ hall htracked hfalse hfailure
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    _hproperCandNext hfrontier hexact
  exact hcurrent hall htracked hfalse hfailure hproperCand
    htrackedNext hltNextBase hproperNext hsubsetCandNext
    hfrontier.2.2.2 hexact

theorem dependencyRemoval_sameClauseConcreteEquivalentFootprintFrontierHandler_of_current
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hcurrent :
      DependencyRemovalSameClauseConcreteCurrentFrontierHandler
        s vars on_) :
    DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierHandler
      s vars on_ := by
  intro skBase skCand skNext σ hall htracked hfalse hfailure
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    _hsubsetNextCand _hcountEq hfrontier hexact
  exact hcurrent hall htracked hfalse hfailure hproperCand
    htrackedNext hltNextBase hproperNext hsubsetCandNext
    (dependencyRemoval_equivalentFrontier_currentResidual
      (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
      (skCand := skCand) (skNext := skNext) (σ := σ)
      hfrontier)
    hexact

/-!
The TeX proof says the induction step must either get a strictly smaller
candidate or continue the repair analysis.  In this Lean branch, "not strictly
smaller by count" is split into the two concrete footprint cases above, and
each case still returns the same local repair result.
-/

theorem dependencyRemoval_sameClauseConcreteNondecreasingResidual_split
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skCand skNext : SkolemAssignment}
    (hsubsetCandNext :
      DeleteWitnessFiberSetSubset s.formula vars on_ skCand skNext)
    (hsplit :
      deleteWitnessFiberCountSet s.formula vars on_ skCand <
          deleteWitnessFiberCountSet s.formula vars on_ skNext ∨
        DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand)
    (_hnot_lt :
      ¬ deleteWitnessFiberCountSet s.formula vars on_ skNext <
        deleteWitnessFiberCountSet s.formula vars on_ skCand) :
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skNext ∨
      (DeleteWitnessFiberSetSubset s.formula vars on_ skNext skCand ∧
        deleteWitnessFiberCountSet s.formula vars on_ skNext =
          deleteWitnessFiberCountSet s.formula vars on_ skCand) := by
  rcases hsplit with hlt | hsubsetNextCand
  · exact Or.inl
      (deleteWitnessFiberSetProperSubset_of_subset_count_lt
        (f := s.formula) (vars := vars) (on_ := on_)
        hsubsetCandNext hlt)
  · exact Or.inr
      ⟨hsubsetNextCand,
        (deleteWitnessFiberCountSet_eq_of_subset_subset
          (f := s.formula) (vars := vars) (on_ := on_)
          hsubsetCandNext hsubsetNextCand).symm⟩

/-!
Therefore it is enough to prove two residual handlers: one for proper growth
and one for equivalent footprint.  This theorem is pure bookkeeping; it does
not discharge either mathematical residual case by itself.
-/

theorem dependencyRemoval_sameClauseConcreteNondecreasingResidualHandler_of_cases
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hgrowth :
      DependencyRemovalSameClauseConcreteProperGrowthResidualHandler
        s vars on_)
    (hequiv :
      DependencyRemovalSameClauseConcreteEquivalentFootprintResidualHandler
        s vars on_) :
    DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
      s vars on_ := by
  intro skBase skCand skNext σ hall htracked hfalse hfailure
    hproperCand htrackedNext hltNextBase hproperNext hsubsetCandNext
    hsplitCandNext hnot_lt hexact
  rcases dependencyRemoval_sameClauseConcreteNondecreasingResidual_split
      (s := s) (vars := vars) (on_ := on_)
      (skCand := skCand) (skNext := skNext)
      hsubsetCandNext hsplitCandNext hnot_lt with
    hproperCandNext | hequivFootprint
  · exact hgrowth hall htracked hfalse hfailure hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hproperCandNext hexact
  · rcases hequivFootprint with ⟨hsubsetNextCand, hcountEq⟩
    exact hequiv hall htracked hfalse hfailure hproperCand
      htrackedNext hltNextBase hproperNext hsubsetCandNext
      hsubsetNextCand hcountEq hexact

/-!
Consequently, the one-piece nondecreasing residual handler follows from the
two explicit frontier handlers.  This is still a reduction, not the final
mathematical closure of the residual branch.
-/

theorem dependencyRemoval_sameClauseConcreteNondecreasingResidualHandler_of_frontiers
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hgrowth :
      DependencyRemovalSameClauseConcreteProperGrowthFrontierHandler
        s vars on_)
    (hequiv :
      DependencyRemovalSameClauseConcreteEquivalentFootprintFrontierHandler
        s vars on_) :
    DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
      s vars on_ :=
  dependencyRemoval_sameClauseConcreteNondecreasingResidualHandler_of_cases
    (s := s) (vars := vars) (on_ := on_)
    (dependencyRemoval_sameClauseConcreteProperGrowthResidualHandler_of_frontier
      (s := s) (vars := vars) (on_ := on_) hexi hgrowth)
    (dependencyRemoval_sameClauseConcreteEquivalentFootprintResidualHandler_of_frontier
      (s := s) (vars := vars) (on_ := on_) hexi hequiv)

/-!
Thus a single current-frontier handler is enough for the whole nondecreasing
residual branch.
-/

theorem dependencyRemoval_sameClauseConcreteNondecreasingResidualHandler_of_current
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcurrent :
      DependencyRemovalSameClauseConcreteCurrentFrontierHandler
        s vars on_) :
    DependencyRemovalSameClauseConcreteNondecreasingResidualHandler
      s vars on_ :=
  dependencyRemoval_sameClauseConcreteNondecreasingResidualHandler_of_frontiers
    (s := s) (vars := vars) (on_ := on_) hexi
    (dependencyRemoval_sameClauseConcreteProperGrowthFrontierHandler_of_current
      (s := s) (vars := vars) (on_ := on_) hcurrent)
    (dependencyRemoval_sameClauseConcreteEquivalentFootprintFrontierHandler_of_current
      (s := s) (vars := vars) (on_ := on_) hcurrent)

/-!
If a tracked repair candidate still falsifies a clause, then its witness fibers
are not merely fewer by count: they form a proper subset of the original
witness fibers.  This is the set-theoretic form of the TeX statement that the
repair pool has removed at least one dependency witness and introduced none
outside the original pool.
-/

theorem dependencyRemoval_trackedFalseCandidate_hasProperSubset
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment} {σ : UnivAssignment}
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand)
    (hfalse : s.clauses.matrixValue s.formula σ skCand = false) :
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase :=
  dependencyRemoval_trackedFalseCandidate_properSubset
    (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
    (skCand := skCand) (σ := σ) htracked hallBase hfalse

/-!
A strict local step is enough for the count-based descent lemma.  If the next
tracked candidate is already a model, we stop.  If it is not a model, the
previous theorem supplies the proper-subset invariant required for the next
descent round.
-/

theorem dependencyRemoval_countFalseStep_of_trackedStrictFalseStep
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hstep : DependencyRemovalTrackedStrictFalseStep s vars on_) :
    DependencyRemovalCountFalseStep s vars on_ := by
  classical
  intro skBase skCand σ hallBase htracked hproper hfalse
  rcases hstep hallBase htracked hproper hfalse with houtcome | hstrict
  · exact Or.inl houtcome
  · rcases hstrict with ⟨skNext, htrackedNext, hltNext⟩
    by_cases hfailNext :
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false
    · rcases hfailNext with ⟨τ, hfalseNext⟩
      have hproperNext :
          DeleteWitnessFiberSetProperSubset
            s.formula vars on_ skNext skBase :=
        dependencyRemoval_trackedFalseCandidate_hasProperSubset
          (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
          (skCand := skNext) (σ := τ)
          hallBase htrackedNext hfalseNext
      exact Or.inr
        ⟨skNext, htrackedNext, hproperNext, hltNext, τ, hfalseNext⟩
    · exact Or.inl
        (Or.inl ⟨skNext,
          (by
            intro τ
            cases hval :
                s.clauses.matrixValue s.formula τ skNext with
            | false => exact False.elim (hfailNext ⟨τ, hval⟩)
            | true => rfl),
          htrackedNext.1.1⟩)

/-!
This is the finite-descent wrapper specialized to strict tracked repair steps.
It is the Lean form of repeatedly applying the TeX induction step until either
the current Skolem functions satisfy every clause or the forbidden pair of
pure paths has been exposed.
-/

theorem dependencyRemoval_trackedFalseRestart_of_trackedStrictFalseStep
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hstep : DependencyRemovalTrackedStrictFalseStep s vars on_) :
    DependencyRemovalTrackedFalseRestart s vars on_ :=
  dependencyRemoval_trackedFalseRestart_of_countFalseStep
    (s := s) (vars := vars) (on_ := on_)
    (dependencyRemoval_countFalseStep_of_trackedStrictFalseStep
      (s := s) (vars := vars) (on_ := on_) hstep)

/-!
A restart principle can also be applied directly to a single strict tracked
step.  This is useful when a local case analysis has already produced the next
candidate: Lean checks whether that candidate is a model, and otherwise
re-enters the restart loop.
-/

theorem dependencyRemoval_trackedStrictStep_apply_trackedFalseRestart
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment}
    (hrestart : DependencyRemovalTrackedFalseRestart s vars on_)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (hstrict :
      FlexibleRepairTrackedStrictStep s vars on_ skBase skCand) :
    DependencyRemovalDescentOutcome s vars on_ skBase := by
  classical
  rcases hstrict with ⟨skNext, htrackedNext, _hltNext⟩
  by_cases hfailNext :
      ∃ τ, s.clauses.matrixValue s.formula τ skNext = false
  · rcases hfailNext with ⟨τ, hfalseNext⟩
    exact hrestart hallBase htrackedNext
      (dependencyRemoval_trackedFalseCandidate_hasProperSubset
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skNext) (σ := τ)
        hallBase htrackedNext hfalseNext)
      hfalseNext
  · exact Or.inl
      ⟨skNext,
        (by
          intro τ
          cases hval : s.clauses.matrixValue s.formula τ skNext with
          | false => exact False.elim (hfailNext ⟨τ, hval⟩)
          | true => rfl),
        htrackedNext.1.1⟩

/-!
Finally, a restart principle turns any tracked repair candidate into a descent
outcome.  Either the candidate is already a model, or it is a failed candidate
with the proper-subset invariant needed to continue the finite descent.
-/

theorem dependencyRemoval_trackedCandidate_apply_trackedFalseRestart
    {s : CheckState} {vars : Array Var} {on_ : Var}
    {skBase skCand : SkolemAssignment}
    (hrestart : DependencyRemovalTrackedFalseRestart s vars on_)
    (hallBase : ∀ τ, s.clauses.matrixValue s.formula τ skBase = true)
    (htracked : FlexibleRepairPoolTracked s vars on_ skBase skCand) :
    DependencyRemovalDescentOutcome s vars on_ skBase := by
  classical
  by_cases hfail :
      ∃ σ, s.clauses.matrixValue s.formula σ skCand = false
  · rcases hfail with ⟨σ, hfalse⟩
    exact hrestart hallBase htracked
      (dependencyRemoval_trackedFalseCandidate_hasProperSubset
        (s := s) (vars := vars) (on_ := on_) (skBase := skBase)
        (skCand := skCand) (σ := σ)
        hallBase htracked hfalse)
      hfalse
  · exact Or.inl
      ⟨skCand,
        (by
          intro σ
          cases hval : s.clauses.matrixValue s.formula σ skCand with
          | false => exact False.elim (hfail ⟨σ, hval⟩)
          | true => rfl),
        htracked.1.1⟩

/-!
The last bridge from the local repair loop to dependency removal is another
finite descent.  At each nonzero witness count, pick one remaining witness.
The local repair proof may either produce a strictly smaller satisfying Skolem
set or expose the forbidden pair of pure paths.  If forbidden pairs are ruled
out, the descent must eventually reach witness count zero.
-/

theorem dependencyRemovalBridge_of_finite_outcome_descent
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hexi : ∀ of_ ∈ vars.toList, s.formula.isVarExistential of_ = true)
    (hnoPair :
      ∀ {badOf : Var} {pos : Bool},
        badOf ∈ vars.toList →
        DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) →
        DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)) →
        False)
    (hdescent :
      ∀ {of_ : Var} {sk : SkolemAssignment} {σ₀ : UnivAssignment},
        (∀ σ, s.clauses.matrixValue s.formula σ sk = true) →
        of_ ∈ vars.toList →
        DeleteDepWitness s.formula of_ on_ sk σ₀ →
        DependencyRemovalDescentOutcome s vars on_ sk) :
    DeleteIndependenceSetBridge s vars on_ := by
  classical
  intro htrue
  rcases htrue with ⟨sk, hall⟩
  let P : Nat → Prop := fun n =>
    ∀ sk,
      deleteWitnessFiberCountSet s.formula vars on_ sk = n →
      (∀ σ, s.clauses.matrixValue s.formula σ sk = true) →
      ∃ sk',
        (∀ σ, s.clauses.matrixValue s.formula σ sk' = true) ∧
        ExhibitsDeleteIndependenceSet s.formula vars on_ sk'
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn (motive := P) n (by
      intro n ih sk hcount hall
      by_cases hcount0 :
          deleteWitnessFiberCountSet s.formula vars on_ sk = 0
      · have hexhibit :
            ExhibitsDeleteIndependenceSet s.formula vars on_ sk := by
          exact (deleteWitnessFiberCountSet_zero_iff_exhibits
            s.formula vars on_ sk hexi).1 hcount0
        exact ⟨sk, hall, hexhibit⟩
      · have hwitExists :
            ∃ of_, of_ ∈ vars.toList ∧ ∃ σ,
              DeleteDepWitness s.formula of_ on_ sk σ := by
          exact (deleteWitnessFiberCountSet_ne_zero_iff_existsDeleteDepWitness
            s.formula vars on_ sk).1 hcount0
        rcases hwitExists with ⟨of_, hof, σ₀, hwit⟩
        rcases hdescent (of_ := of_) (sk := sk) (σ₀ := σ₀)
            hall hof hwit with
          hgood | hbad
        · rcases hgood with ⟨sk', hall', hcount_lt⟩
          have hlt_n :
              deleteWitnessFiberCountSet s.formula vars on_ sk' < n := by
            simpa [hcount] using hcount_lt
          exact ih (deleteWitnessFiberCountSet s.formula vars on_ sk')
            hlt_n sk' rfl hall'
        · rcases hbad with ⟨badOf, hbadMem, pos, hposPath, hnegPath⟩
          exact False.elim (hnoPair hbadMem hposPath hnegPath))
  exact hP (deleteWitnessFiberCountSet s.formula vars on_ sk) sk rfl hall
