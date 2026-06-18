import DqratLean.WatchedRuntimeSoundness

/-!
# Watched Propagation Refinement

First state-projection and local propagation-refinement lemmas for the
experimental watched runtime.

Trust status: experimental watched-layer proof work, outside the certified
default path.
-/
namespace DqratLean.Watched

/-- Starting a fresh decision level does not affect cache soundness. -/
theorem runtimeSoundInvariant_newDecisionLevelState
    {st : CheckState} (hinv : RuntimeSoundInvariant st) :
    RuntimeSoundInvariant (newDecisionLevelState st) := by
  simpa [newDecisionLevelState, RuntimeSoundInvariant] using hinv

/-- Backtracking only changes assignments, trail, and queue, so caches stay sound. -/
theorem runtimeSoundInvariant_backtrackState
    {st : CheckState} (hinv : RuntimeSoundInvariant st) (level : Nat) :
    RuntimeSoundInvariant (backtrackState st level) := by
  unfold backtrackState
  simp [RuntimeSoundInvariant] at *
  exact hinv

/-- Enqueueing a literal does not change the cache layers or clause store. -/
theorem runtimeSoundInvariant_enqueueState
    {st : CheckState} (hinv : RuntimeSoundInvariant st) (l : Literal) :
    RuntimeSoundInvariant (enqueueState st l) := by
  unfold enqueueState
  by_cases hvar : l.var = 0 ∨ st.formula.maxVar < l.var
  · simp [hvar, RuntimeSoundInvariant] at *
    exact hinv
  · by_cases hbound : st.isAssigned.size ≤ l.var - 1
    · simp [hvar, hbound, RuntimeSoundInvariant] at *
      exact hinv
    · by_cases hassigned : st.isAssigned.getD (l.var - 1) false = true
      · simp [hvar, hbound, hassigned, RuntimeSoundInvariant] at *
        exact hinv
      · simp [hvar, hbound, hassigned, RuntimeSoundInvariant] at *
        exact hinv

/-- Clearing propagation state leaves the watched caches unchanged. -/
theorem runtimeSoundInvariant_resetPropagationStateState
    {st : CheckState} (hinv : RuntimeSoundInvariant st) :
    RuntimeSoundInvariant (resetPropagationStateState st) := by
  simpa [resetPropagationStateState, RuntimeSoundInvariant] using hinv

/-- The proof-facing decision-level transition refines the abstract checker state. -/
theorem newDecisionLevelState_refines_base
    {watched : CheckState} {base : _root_.CheckState}
    (href : RuntimeRefines watched base) :
    RuntimeRefines (newDecisionLevelState watched)
      { base with trail := base.trail.push #[] } := by
  rcases href with ⟨hbase, hinv⟩
  constructor
  · simpa [hbase] using
      (show (newDecisionLevelState watched).toBase =
        { watched.toBase with trail := watched.toBase.trail.push #[] } from rfl)
  · exact runtimeSoundInvariant_newDecisionLevelState hinv

/-- The proof-facing backtrack transition refines the abstract checker state. -/
theorem backtrackState_refines_base
    {watched : CheckState} {base : _root_.CheckState}
    (href : RuntimeRefines watched base) (level : Nat) :
    RuntimeRefines (backtrackState watched level)
      { base with
        trail := (backtrackState watched level).trail
        isAssigned := (backtrackState watched level).isAssigned
        propQueue := #[] } := by
  rcases href with ⟨hbase, hinv⟩
  constructor
  · simpa [hbase] using toBase_backtrackState level watched
  · exact runtimeSoundInvariant_backtrackState hinv level

/-- The proof-facing propagation reset refines the abstract checker state. -/
theorem resetPropagationStateState_refines_base
    {watched : CheckState} {base : _root_.CheckState}
    (href : RuntimeRefines watched base) :
    RuntimeRefines (resetPropagationStateState watched)
      { base with
        isAssigned := Array.replicate watched.formula.maxVar false
        value := Array.replicate watched.formula.maxVar false
        trail := #[#[]]
        propQueue := #[] } := by
  rcases href with ⟨hbase, hinv⟩
  constructor
  · simpa [hbase] using toBase_resetPropagationStateState watched
  · exact runtimeSoundInvariant_resetPropagationStateState hinv

/--
Applying one live binary-cache entry preserves cache soundness regardless of
whether it is a no-op, reports a conflict, or enqueues its implied literal.
-/
theorem runtimeSoundInvariant_applyBinaryImpEntryState
    {st : CheckState} (hinv : RuntimeSoundInvariant st)
    (entry : BinaryImpEntry) (conflict : Option CRef) :
    RuntimeSoundInvariant (applyBinaryImpEntryState st entry conflict).2 := by
  unfold applyBinaryImpEntryState
  by_cases hconf : conflict.isSome = true
  · simp [hconf, RuntimeSoundInvariant] at *
    exact hinv
  · by_cases hsat : satisfied st entry.implied = true
    · simp [hconf, hsat, RuntimeSoundInvariant] at *
      exact hinv
    · by_cases hneg : satisfied st entry.implied.negate = true
      · simp [hconf, hsat, hneg, RuntimeSoundInvariant] at *
        exact hinv
      · simpa [hconf, hsat, hneg] using runtimeSoundInvariant_enqueueState hinv entry.implied

/--
The enqueue branch of one live binary-cache entry refines to the abstract
queue update represented by `enqueueState`.
-/
theorem applyBinaryImpEntryState_enqueue_refines
    {watched : CheckState} {base : _root_.CheckState}
    (href : RuntimeRefines watched base)
    (entry : BinaryImpEntry)
    (hsat : satisfied watched entry.implied = false)
    (hneg : satisfied watched entry.implied.negate = false) :
    let res := applyBinaryImpEntryState watched entry none
    res.1 = none ∧
      RuntimeRefines res.2 (enqueueState watched entry.implied).toBase := by
  rcases href with ⟨_, hinv⟩
  dsimp [applyBinaryImpEntryState]
  simp [hsat, hneg]
  exact ⟨rfl, runtimeSoundInvariant_enqueueState hinv entry.implied⟩

end DqratLean.Watched
