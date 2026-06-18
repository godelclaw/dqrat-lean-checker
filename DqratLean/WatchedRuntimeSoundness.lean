import DqratLean.WatchedSoundness
import DqratLean.WatchedBinaryRefinement

/-!
# Watched Runtime Soundness

Runtime invariant bundles and local refinement lemmas for the watched caches.

Trust status: experimental watched-layer proof work, outside the certified
default path.
-/
namespace DqratLean.Watched

/--
Proof-facing invariant bundle for the current watched runtime.

This is intentionally a refinement layer: `CheckState.toBase` is the abstract
state used by the existing soundness theorem, while these cache invariants are
the extra obligations needed to justify the watched accelerators.
-/
def RuntimeInvariant (st : CheckState) : Prop :=
  LiveOccInvariant st ∧ BinaryImpInvariant st

/--
Minimal cache invariant needed for watched propagation soundness.

Completeness of `binaryImpBy` is useful for watched/base performance
refinement, but soundness of cached implications is the property needed to
justify using the binary fast path without trusting stale or spurious entries.
-/
def RuntimeSoundInvariant (st : CheckState) : Prop :=
  LiveOccInvariant st ∧ BinaryImpSound st

theorem runtimeInvariant_empty : RuntimeInvariant CheckState.empty := by
  exact ⟨liveOccInvariant_empty, binaryImpInvariant_empty⟩

theorem runtimeSoundInvariant_empty : RuntimeSoundInvariant CheckState.empty := by
  exact ⟨liveOccInvariant_empty, binaryImpSound_empty⟩

theorem runtimeSoundInvariant_of_runtimeInvariant
    {st : CheckState} (hinv : RuntimeInvariant st) :
    RuntimeSoundInvariant st := by
  exact ⟨hinv.1, hinv.2.1⟩

def RuntimeRefines (watched : CheckState) (base : _root_.CheckState) : Prop :=
  watched.toBase = base ∧ RuntimeSoundInvariant watched

def addClauseRuntimeCacheState (st : CheckState) (lits : Array Literal) : CheckState :=
  addClauseCacheState st lits

def deleteClauseRuntimeCacheState (st : CheckState) (cref : CRef) (c : Clause) :
    CheckState :=
  deleteClauseCacheState st cref c

theorem toBase_addClauseRuntimeCacheState
    (st : CheckState) (lits : Array Literal) :
    (addClauseRuntimeCacheState st lits).toBase =
      { st.toBase with clauses := (st.toBase.clauses.addClause lits).1 } := by
  simpa [addClauseRuntimeCacheState] using toBase_addClauseCacheState st lits

theorem runtimeSoundInvariant_addClauseRuntimeCacheState
    {st : CheckState} (hinv : RuntimeSoundInvariant st)
    (hpos : 0 < st.clauses.clauses.size) (lits : Array Literal) :
    RuntimeSoundInvariant (addClauseRuntimeCacheState st lits) := by
  change RuntimeSoundInvariant (addClauseCacheState st lits)
  rcases hinv with ⟨hlive, hbinSound⟩
  constructor
  · simpa [addClauseCacheState, RuntimeSoundInvariant] using
      liveOccInvariant_addClause hlive hpos lits
  · intro l entry hmem
    have hmem' :
        entry ∈ getBinaryImp
          (if lits.size = 2 then
            addBinaryClauseState st lits (lits.getD 0 (mkLit 0 false))
              (lits.getD 1 (mkLit 0 false))
          else
            addNonbinaryClauseState st lits) l := by
      by_cases hsize : lits.size = 2
      · simpa [addClauseCacheState, addBinaryClauseState, getBinaryImp, hsize]
          using hmem
      · simpa [addClauseCacheState, addNonbinaryClauseState, getBinaryImp, hsize]
          using hmem
    rcases binaryImpSound_addClause hbinSound hpos lits hmem' with
      ⟨c, hget, hmatch⟩
    refine ⟨c, ?_, hmatch⟩
    by_cases hsize : lits.size = 2
    · simpa [addClauseCacheState, addBinaryClauseState, hsize] using hget
    · simpa [addClauseCacheState, addNonbinaryClauseState, hsize] using hget

theorem toBase_deleteClauseRuntimeCacheState
    (st : CheckState) (cref : CRef) (c : Clause) :
    (deleteClauseRuntimeCacheState st cref c).toBase =
      { st.toBase with clauses := st.toBase.clauses.deleteClause cref } := by
  rfl

theorem runtimeSoundInvariant_deleteClauseRuntimeCacheState
    {st : CheckState} (hinv : RuntimeSoundInvariant st)
    {cref : CRef} {c : Clause}
    (hget : st.clauses.getClause cref = some c) :
    RuntimeSoundInvariant (deleteClauseRuntimeCacheState st cref c) := by
  rcases hinv with ⟨hlive, hbinSound⟩
  constructor
  · simpa [deleteClauseRuntimeCacheState, RuntimeSoundInvariant] using
      liveOccInvariant_deleteClause hlive hget
  · intro l entry hmem
    have hmem' : entry ∈ getBinaryImp { st with clauses := st.clauses.deleteClause cref } l := by
      simpa [deleteClauseRuntimeCacheState, getBinaryImp] using hmem
    rcases binaryImpSound_deleteClause hbinSound cref hmem' with ⟨c', hgetRaw, hmatch⟩
    exact ⟨c', by simpa [deleteClauseRuntimeCacheState] using hgetRaw, hmatch⟩

theorem addClauseRuntimeCacheState_refines_base_addClause
    {watched : CheckState} {base : _root_.CheckState}
    (href : RuntimeRefines watched base)
    (hpos : 0 < watched.clauses.clauses.size) (lits : Array Literal) :
    RuntimeRefines (addClauseRuntimeCacheState watched lits)
      { base with clauses := (base.clauses.addClause lits).1 } := by
  rcases href with ⟨hbase, hinv⟩
  constructor
  · rw [toBase_addClauseRuntimeCacheState, hbase]
  · exact runtimeSoundInvariant_addClauseRuntimeCacheState hinv hpos lits

theorem deleteClauseRuntimeCacheState_refines_base_deleteClause
    {watched : CheckState} {base : _root_.CheckState}
    (href : RuntimeRefines watched base)
    {cref : CRef} {c : Clause}
    (hget : watched.clauses.getClause cref = some c) :
    RuntimeRefines (deleteClauseRuntimeCacheState watched cref c)
      { base with clauses := base.clauses.deleteClause cref } := by
  rcases href with ⟨hbase, hinv⟩
  constructor
  · rw [toBase_deleteClauseRuntimeCacheState, hbase]
  · exact runtimeSoundInvariant_deleteClauseRuntimeCacheState hinv hget

theorem empty_refines_base :
    CheckState.empty.toBase = _root_.CheckState.empty ∧
      RuntimeInvariant CheckState.empty := by
  exact ⟨CheckState.toBase_empty, runtimeInvariant_empty⟩

theorem empty_runtime_refines_base :
    RuntimeRefines CheckState.empty _root_.CheckState.empty := by
  exact ⟨CheckState.toBase_empty, runtimeSoundInvariant_empty⟩

end DqratLean.Watched
