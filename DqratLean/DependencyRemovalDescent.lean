import DqratLean.DependencyRemovalResidual

/-!
This file contains the small termination lemmas behind the final descent
paragraph of the dependency-removal proof.

The narrative file keeps the proof close to the TeX text.  The lemmas here are
supporting Lean infrastructure: they say that if every failed repair candidate
either finishes the proof or moves to a strictly smaller failed candidate, then
the process terminates by induction on a natural-valued measure.
-/

/-!
The TeX proof says:

\[
  \text{Since the set of dependency witnesses is finite, the induction step
  eventually terminates.}
\]

Lean phrases the possible end of one descent attempt as an `outcome`: either
we have found a satisfying Skolem set with fewer \(u\)-dependency witnesses, or
we have exhibited the forbidden pair of pure paths.
-/

abbrev DependencyRemovalDescentOutcome
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (skBase : SkolemAssignment) : Prop :=
  (∃ sk',
    (∀ σ, s.clauses.matrixValue s.formula σ sk' = true) ∧
    deleteWitnessFiberCountSet s.formula vars on_ sk' <
      deleteWitnessFiberCountSet s.formula vars on_ skBase) ∨
  (∃ badOf, badOf ∈ vars.toList ∧ ∃ pos : Bool,
    DeletePurePath s on_ (mkLit on_ true) (mkLit badOf pos) ∧
    DeletePurePath s on_ (mkLit on_ false) (mkLit badOf (!pos)))

/-!
A `TrackedFalseRestart` is the Lean form of re-running the repair procedure
from a failed candidate already known to have a proper subset of the original
witness fibers.

The hypotheses mean:
* `hall` says the original Skolem functions satisfy every clause.
* `htracked` says the current candidate is in the repair pool and carries the
  bookkeeping needed to compare it with the original Skolem functions.
* `hproper` says the current candidate has removed at least one witness fiber.
* `hfalse` says the current candidate still falsifies the matrix.
-/

abbrev DependencyRemovalTrackedFalseRestart
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    DependencyRemovalDescentOutcome s vars on_ skBase

/-!
For some parts of the Lean proof the decreasing measure is not immediately the
witness count itself.  A `RankedFalseStep` records the abstract form needed for
well-founded descent: every failed candidate either gives an outcome, or gives
another failed candidate with strictly smaller rank.
-/

abbrev DependencyRemovalRankedFalseStep
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : SkolemAssignment → Nat) : Prop :=
  ∀ {skBase skCand : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    DependencyRemovalDescentOutcome s vars on_ skBase ∨
      ∃ skNext,
        FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
        rank skNext < rank skCand ∧
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false

/-!
This is the formal induction behind "eventually terminates."  The proof is a
strong induction over the rank of the current failed candidate.  In the step
case, if the local proof returns a lower-ranked failed candidate, the induction
hypothesis is applied to that candidate.
-/

theorem dependencyRemoval_trackedFalseRestart_of_rankedFalseStep
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (rank : SkolemAssignment → Nat)
    (hstep : DependencyRemovalRankedFalseStep s vars on_ rank) :
    DependencyRemovalTrackedFalseRestart s vars on_ := by
  intro skBase skCand σ hall htracked hproper hfalse
  let P : Nat → Prop := fun n =>
    ∀ {skCur : SkolemAssignment} {τ : UnivAssignment},
      rank skCur = n →
      FlexibleRepairPoolTracked s vars on_ skBase skCur →
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCur skBase →
      s.clauses.matrixValue s.formula τ skCur = false →
      DependencyRemovalDescentOutcome s vars on_ skBase
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn (motive := P) n (by
      intro n ih skCur τ hrank htrackedCur hproperCur hfalseCur
      rcases hstep hall htrackedCur hproperCur hfalseCur with
        houtcome | hnext
      · exact houtcome
      · rcases hnext with
          ⟨skNext, htrackedNext, hproperNext, hrankNext, ρ,
            hfalseNext⟩
        have hlt_n : rank skNext < n := by
          simpa [hrank] using hrankNext
        exact ih (rank skNext) hlt_n (skCur := skNext) (τ := ρ)
          rfl htrackedNext hproperNext hfalseNext)
  exact hP (rank skCand) (skCur := skCand) (τ := σ) rfl htracked
    hproper hfalse

/-!
When the measure is exactly the number of remaining witness fibers, a failed
step only needs to produce another failed candidate with smaller witness count.
-/

abbrev DependencyRemovalCountFalseStep
    (s : CheckState) (vars : Array Var) (on_ : Var) : Prop :=
  ∀ {skBase skCand : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    DependencyRemovalDescentOutcome s vars on_ skBase ∨
      ∃ skNext,
        FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
        deleteWitnessFiberCountSet s.formula vars on_ skNext <
          deleteWitnessFiberCountSet s.formula vars on_ skCand ∧
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false

/-!
The witness count is itself a valid rank.  This is just a change of vocabulary:
the strictly smaller count becomes the strictly smaller rank required by the
generic induction lemma above.
-/

theorem dependencyRemoval_rankedFalseStep_of_countFalseStep
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hstep : DependencyRemovalCountFalseStep s vars on_) :
    DependencyRemovalRankedFalseStep s vars on_
      (fun sk => deleteWitnessFiberCountSet s.formula vars on_ sk) := by
  intro skBase skCand σ hall htracked hproper hfalse
  rcases hstep hall htracked hproper hfalse with houtcome | hnext
  · exact Or.inl houtcome
  · rcases hnext with
      ⟨skNext, htrackedNext, hproperNext, hcount_lt, τ, hfalseNext⟩
    exact Or.inr
      ⟨skNext, htrackedNext, hproperNext, hcount_lt, τ, hfalseNext⟩

/-!
Combining the previous two facts gives the direct count-based restart lemma:
if every failure can be replaced by a strictly smaller failure, then any
failed tracked candidate eventually yields an outcome.
-/

theorem dependencyRemoval_trackedFalseRestart_of_countFalseStep
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (hstep : DependencyRemovalCountFalseStep s vars on_) :
    DependencyRemovalTrackedFalseRestart s vars on_ :=
  dependencyRemoval_trackedFalseRestart_of_rankedFalseStep
    (s := s) (vars := vars) (on_ := on_)
    (fun sk => deleteWitnessFiberCountSet s.formula vars on_ sk)
    (dependencyRemoval_rankedFalseStep_of_countFalseStep
      (s := s) (vars := vars) (on_ := on_) hstep)
