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
The frontier proof sometimes needs one more piece of state than the candidate
itself.  In the TeX argument this is still the same finite descent: we are
tracking a search state, and the next failed state must have a smaller
measure.  Lean records this with a Boolean phase and a rank that may also
depend on the original satisfying Skolem set.

The starting phase is `false`.  The proof below does not assign mathematical
meaning to the phases; later lemmas use them to distinguish the ordinary failed
candidate from a frontier continuation where a same-clause failure has moved
to the two-patch candidate.
-/

abbrev DependencyRemovalPhasedRankedFalseStep
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : Bool → SkolemAssignment → SkolemAssignment → Nat) : Prop :=
  ∀ {phase : Bool} {skBase skCand : SkolemAssignment} {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    DependencyRemovalDescentOutcome s vars on_ skBase ∨
      ∃ phaseNext skNext,
        FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
        rank phaseNext skBase skNext < rank phase skBase skCand ∧
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
The same induction works for the phased search-state rank.  This is the finite
termination wrapper needed when the next state is not just a new candidate but
also a different kind of residual search state.
-/

theorem dependencyRemoval_trackedFalseRestart_of_phasedRankedFalseStep
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (rank : Bool → SkolemAssignment → SkolemAssignment → Nat)
    (hstep : DependencyRemovalPhasedRankedFalseStep s vars on_ rank) :
    DependencyRemovalTrackedFalseRestart s vars on_ := by
  intro skBase skCand σ hall htracked hproper hfalse
  let P : Nat → Prop := fun n =>
    ∀ {phase : Bool} {skCur : SkolemAssignment} {τ : UnivAssignment},
      rank phase skBase skCur = n →
      FlexibleRepairPoolTracked s vars on_ skBase skCur →
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCur skBase →
      s.clauses.matrixValue s.formula τ skCur = false →
      DependencyRemovalDescentOutcome s vars on_ skBase
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn (motive := P) n (by
      intro n ih phase skCur τ hrank htrackedCur hproperCur hfalseCur
      rcases hstep (phase := phase) hall htrackedCur hproperCur hfalseCur with
        houtcome | hnext
      · exact houtcome
      · rcases hnext with
          ⟨phaseNext, skNext, htrackedNext, hproperNext,
            hrankNext, ρ, hfalseNext⟩
        have hlt_n : rank phaseNext skBase skNext < n := by
          simpa [hrank] using hrankNext
        exact ih (rank phaseNext skBase skNext) hlt_n
          (phase := phaseNext) (skCur := skNext) (τ := ρ)
          rfl htrackedNext hproperNext hfalseNext)
  exact hP (rank false skBase skCand) (phase := false)
    (skCur := skCand) (τ := σ) rfl htracked hproper hfalse

/-!
The Boolean phase is enough for the first two-tier attempt, but the proof text
does not require phases to be Boolean.  A staged descent is the same finite
argument with an arbitrary type of search states.  Later proof layers can use a
small inductive phase type when the residual proof needs more than one
frontier state.
-/

abbrev DependencyRemovalStagedRankedFalseStep
    (Phase : Type)
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (rank : Phase → SkolemAssignment → SkolemAssignment → Nat) : Prop :=
  ∀ {phase : Phase} {skBase skCand : SkolemAssignment}
    {σ : UnivAssignment},
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    DependencyRemovalDescentOutcome s vars on_ skBase ∨
      ∃ phaseNext skNext,
        FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
        rank phaseNext skBase skNext < rank phase skBase skCand ∧
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false

theorem dependencyRemoval_trackedFalseRestart_of_stagedRankedFalseStep
    {Phase : Type} {s : CheckState} {vars : Array Var} {on_ : Var}
    (start : Phase)
    (rank : Phase → SkolemAssignment → SkolemAssignment → Nat)
    (hstep :
      DependencyRemovalStagedRankedFalseStep Phase s vars on_ rank) :
    DependencyRemovalTrackedFalseRestart s vars on_ := by
  intro skBase skCand σ hall htracked hproper hfalse
  let P : Nat → Prop := fun n =>
    ∀ {phase : Phase} {skCur : SkolemAssignment} {τ : UnivAssignment},
      rank phase skBase skCur = n →
      FlexibleRepairPoolTracked s vars on_ skBase skCur →
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCur skBase →
      s.clauses.matrixValue s.formula τ skCur = false →
      DependencyRemovalDescentOutcome s vars on_ skBase
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn (motive := P) n (by
      intro n ih phase skCur τ hrank htrackedCur hproperCur hfalseCur
      rcases hstep (phase := phase) hall htrackedCur hproperCur
          hfalseCur with
        houtcome | hnext
      · exact houtcome
      · rcases hnext with
          ⟨phaseNext, skNext, htrackedNext, hproperNext,
            hrankNext, ρ, hfalseNext⟩
        have hlt_n : rank phaseNext skBase skNext < n := by
          simpa [hrank] using hrankNext
        exact ih (rank phaseNext skBase skNext) hlt_n
          (phase := phaseNext) (skCur := skNext) (τ := ρ)
          rfl htrackedNext hproperNext hfalseNext)
  exact hP (rank start skBase skCand) (phase := start)
    (skCur := skCand) (τ := σ) rfl htracked hproper hfalse

/-!
The unguarded phased theorem above is intentionally small, but it is sometimes
too strong for the frontier proof: a phase is meaningful only for candidates
that carry the corresponding search-state provenance.  The guarded version
below is the same finite induction with one extra invariant.  The initial
failed candidate starts in phase `false`; every recursive step must return a
new valid phase/candidate pair.
-/

abbrev DependencyRemovalGuardedPhasedRankedFalseStep
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (valid : Bool → SkolemAssignment → SkolemAssignment → Prop)
    (rank : Bool → SkolemAssignment → SkolemAssignment → Nat) : Prop :=
  ∀ {phase : Bool} {skBase skCand : SkolemAssignment}
    {σ : UnivAssignment},
    valid phase skBase skCand →
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    DependencyRemovalDescentOutcome s vars on_ skBase ∨
      ∃ phaseNext skNext,
        valid phaseNext skBase skNext ∧
        FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
        rank phaseNext skBase skNext < rank phase skBase skCand ∧
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false

theorem dependencyRemoval_trackedFalseRestart_of_guardedPhasedRankedFalseStep
    {s : CheckState} {vars : Array Var} {on_ : Var}
    (valid : Bool → SkolemAssignment → SkolemAssignment → Prop)
    (rank : Bool → SkolemAssignment → SkolemAssignment → Nat)
    (hstart :
      ∀ {skBase skCand : SkolemAssignment},
        FlexibleRepairPoolTracked s vars on_ skBase skCand →
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
        valid false skBase skCand)
    (hstep :
      DependencyRemovalGuardedPhasedRankedFalseStep
        s vars on_ valid rank) :
    DependencyRemovalTrackedFalseRestart s vars on_ := by
  intro skBase skCand σ hall htracked hproper hfalse
  let P : Nat → Prop := fun n =>
    ∀ {phase : Bool} {skCur : SkolemAssignment} {τ : UnivAssignment},
      rank phase skBase skCur = n →
      valid phase skBase skCur →
      FlexibleRepairPoolTracked s vars on_ skBase skCur →
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCur skBase →
      s.clauses.matrixValue s.formula τ skCur = false →
      DependencyRemovalDescentOutcome s vars on_ skBase
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn (motive := P) n (by
      intro n ih phase skCur τ hrank hvalid htrackedCur hproperCur
        hfalseCur
      rcases hstep hvalid hall htrackedCur hproperCur hfalseCur with
        houtcome | hnext
      · exact houtcome
      · rcases hnext with
          ⟨phaseNext, skNext, hvalidNext, htrackedNext, hproperNext,
            hrankNext, ρ, hfalseNext⟩
        have hlt_n : rank phaseNext skBase skNext < n := by
          simpa [hrank] using hrankNext
        exact ih (rank phaseNext skBase skNext) hlt_n
          (phase := phaseNext) (skCur := skNext) (τ := ρ)
          rfl hvalidNext htrackedNext hproperNext hfalseNext)
  exact hP (rank false skBase skCand) (phase := false)
    (skCur := skCand) (τ := σ) rfl (hstart htracked hproper)
    htracked hproper hfalse

/-!
The Boolean guarded restart is enough for the two-tier witness-count rank, but
the residual proof may need more than two reachable search states.  This is the
same finite descent with an arbitrary phase type and an explicit start phase.
-/

abbrev DependencyRemovalGuardedStagedRankedFalseStep
    (Phase : Type)
    (s : CheckState) (vars : Array Var) (on_ : Var)
    (valid : Phase → SkolemAssignment → SkolemAssignment → Prop)
    (rank : Phase → SkolemAssignment → SkolemAssignment → Nat) : Prop :=
  ∀ {phase : Phase} {skBase skCand : SkolemAssignment}
    {σ : UnivAssignment},
    valid phase skBase skCand →
    (∀ τ, s.clauses.matrixValue s.formula τ skBase = true) →
    FlexibleRepairPoolTracked s vars on_ skBase skCand →
    DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
    s.clauses.matrixValue s.formula σ skCand = false →
    DependencyRemovalDescentOutcome s vars on_ skBase ∨
      ∃ phaseNext skNext,
        valid phaseNext skBase skNext ∧
        FlexibleRepairPoolTracked s vars on_ skBase skNext ∧
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skNext skBase ∧
        rank phaseNext skBase skNext < rank phase skBase skCand ∧
        ∃ τ, s.clauses.matrixValue s.formula τ skNext = false

theorem dependencyRemoval_trackedFalseRestart_of_guardedStagedRankedFalseStep
    {Phase : Type} {s : CheckState} {vars : Array Var} {on_ : Var}
    (start : Phase)
    (valid : Phase → SkolemAssignment → SkolemAssignment → Prop)
    (rank : Phase → SkolemAssignment → SkolemAssignment → Nat)
    (hstart :
      ∀ {skBase skCand : SkolemAssignment},
        FlexibleRepairPoolTracked s vars on_ skBase skCand →
        DeleteWitnessFiberSetProperSubset s.formula vars on_ skCand skBase →
        valid start skBase skCand)
    (hstep :
      DependencyRemovalGuardedStagedRankedFalseStep
        Phase s vars on_ valid rank) :
    DependencyRemovalTrackedFalseRestart s vars on_ := by
  intro skBase skCand σ hall htracked hproper hfalse
  let P : Nat → Prop := fun n =>
    ∀ {phase : Phase} {skCur : SkolemAssignment} {τ : UnivAssignment},
      rank phase skBase skCur = n →
      valid phase skBase skCur →
      FlexibleRepairPoolTracked s vars on_ skBase skCur →
      DeleteWitnessFiberSetProperSubset s.formula vars on_ skCur skBase →
      s.clauses.matrixValue s.formula τ skCur = false →
      DependencyRemovalDescentOutcome s vars on_ skBase
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn (motive := P) n (by
      intro n ih phase skCur τ hrank hvalid htrackedCur hproperCur
        hfalseCur
      rcases hstep hvalid hall htrackedCur hproperCur hfalseCur with
        houtcome | hnext
      · exact houtcome
      · rcases hnext with
          ⟨phaseNext, skNext, hvalidNext, htrackedNext, hproperNext,
            hrankNext, ρ, hfalseNext⟩
        have hlt_n : rank phaseNext skBase skNext < n := by
          simpa [hrank] using hrankNext
        exact ih (rank phaseNext skBase skNext) hlt_n
          (phase := phaseNext) (skCur := skNext) (τ := ρ)
          rfl hvalidNext htrackedNext hproperNext hfalseNext)
  exact hP (rank start skBase skCand) (phase := start)
    (skCur := skCand) (τ := σ) rfl (hstart htracked hproper)
    htracked hproper hfalse

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
