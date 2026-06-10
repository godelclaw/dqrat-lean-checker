# Soundness TODO

This file tracks the shortest still-honest path from the current branch state to
full soundness of the executable-aligned checker.

## Current state

- `lake build DqratLean.Soundness` passes.
- Parser/executable regressions are green.
- `parseDQDIMACS_correct` and `processProof_sound'` are proved.
- The no-negative-`e` scaffold is proved:
  - `checkActionNoNegE_sound`
  - `checkActionsNoNegE_sound`
  - `processProofNoNegE_sound'`
- `checkDQRATE_sound_spec` is now proved on the executable-aligned
  `FullCorrect` surface.
- This clone is `dqrat-lean-checker-watched` on
  `codex/watched-literals-port`.
- `checkAction_sound` is not the direct live frontier theorem in this clone.
- The remaining explicit theorem-body `sorry` in `DqratLean/Soundness.lean`
  is `computeDeps_activeDeletionPoolContinuation`.
- The matching split-file frontier in
  `DqratLean/DependencyRemovalComputeDeps.lean` is
  `computeDeps_activeDeletion_currentFrontier_externalHighPhaseRankBoundary`.
- A parallel clone, `dqrat-lean-checker-work` on
  `codex/wip-parser-soundness-seam`, is pursuing a shorter static
  reach-closure route with live theorem
  `forceDelDeps_formula_sound_of_noDeleteCrossPaths`. See
  `docs/negative_e_strategy_split.md`.

## Real blockers

The remaining work is no longer split across DQRATE and action-wrapper seams.
The live blocker is the negative-`e` rule family.

### 1. DQRATE closure is done, but the guardrails matter

`checkDQRATE_sound_spec` is closed. The repo should still preserve the facts
that made the direct route necessary:

- `CheckState.FullCorrect.liveOccurrencesComplete`
- the outer/blocker scan over actual occurrence lists

The old `Correct`-only surface was false. That is now backed by a concrete
executable witness in
`DqratLean/Counterexamples.lean`: `occurrenceHoleStore_not_liveOccurrencesComplete`
plus `occurrenceHoleAccepted_true` and `occurrenceHole_addedMatrix_false` show
that a live blocker clause missing from occurrence lists lets `checkDQRATE`
accept an unsound clause addition.

There is now a second auditable witness showing that the older finishing route
was too strong for the executable checker. The `dqrateBridge*` family in
`DqratLean/Counterexamples.lean` proves:

- `dqrateBridgeAccepted_true`
- `dqrateBridge_not_exec_condition`

So an accepted executable DQRATE step need not satisfy the legacy
`DQRATE_exec_Condition` / per-blocker-resolvent bridge. This means the remaining
work is not "finish the old bridge theorem"; that repair has already happened by
switching to the direct patched-model argument.

The blocker-trial state package remains the key local infrastructure:

- `OuterStateShadow`
- `runDQRATEBlockerTrial_restore_shadow_of_shadow_spec`
- `checkDQRATEBlockerFold_trial_shadow_spec`
- `checkDQRATEBlockerFold_none_gives_occ_semantic_shadow`
- `runDQRATEBlockerTrial_true_implies_outerClause_true_of_clause_false_agree_shadow`
- the pivot-phase private theorems now consume the shadow/queue-empty package directly

Compile-green direct-route support that now feeds the closed theorem:
- `clauseValue_patchPivotForClause_true_of_live_blocker_trial`
- `checkDQRATEBlockerFold_none_gives_patch_clause_true_shadow`
- `matrixValue_patchPivotForClause_true_of_successful_pivot_phase`
- `runDQRATEPivotPhase_true_soundness_direct`

### 2. Negative-`e` preservation

The positive-only existential modification path is already proved:

- `checkModifyExistentialAddOnly_sound`

The remaining full-checker gap is the deletion side:

- `checkModifyExistentialDelStep`
- `delDependencyReset`
- `notDependsOn`
- `forceDelDep`

This is the missing rule-family needed before the final `checkAction_sound`
wrapper can close for the full executable.

There is now a build-green semantic foothold for the deletion side. The repo
contains:

- `BadDeletePattern`
- `patchDeleteSkolemForFormula`
- `matrixValue_forceDelDep_patchDeleteForFormula_true_of_no_both_bad`
- `dqbfTrue_forceDelDep_of_no_both_bad`
- `DQBFTrue_forceDelDep_of_exhibiting_bridge`
- the one-universal / many-existentials scaffold from the paper:
  `forceDelDeps`, `liftForceDelDepsWitness`,
  `deleteIndependenceSetBridge_of_forceDelDepsTrue`,
  `DeleteIndependenceSetBridge.of_forceDelDepsTrue`
- `delDependencyReset_full_correct_lookup_spec_of_exhibiting_bridge`
- `checkModifyExistentialDelStep_full_sound_of_exhibiting_bridge`

So the semantic half is no longer "invent a witness for the weakened formula".
But one tempting bridge is now known to be false in the current repo.
`DqratLean/Counterexamples.lean` contains `deleteBridge...` witnesses showing:

- `notDependsOn 3 1` succeeds on a small formula,
- one concrete old witness satisfies the original matrix on both relevant
  Boolean choices for the unique universal, and
- for one particular old satisfying witness, forcing only the deleted variable
  `x` to either Boolean value makes some clause false on the unique reduced
  dependency pattern.

So the next semantic theorem cannot be:

1. successful `notDependsOn` implies a fixed old witness has no both-bad reduced
   pattern for `x`, or
2. successful deletion is handled by patching only the deleted existential while
   leaving all other Skolem functions unchanged.

The real remaining task is to find the right stronger transport principle:

1. either patch a larger dependency cone of Skolem functions, or
2. derive a better existential witness for the weakened formula from the old
   truth proof, not from an arbitrary old satisfying witness.

This means the wrapper side is now mostly in place. The deletion-step layer can
already be proved from an explicit `DeleteIndependenceBridge`, and the wrapper
reduction now goes one step further: `delDependencyReset` and the single-step
negative-`e` theorem can be derived directly from the paper-shaped assumption
that after successful `notDependsOn`, the formula with `u` removed from the
whole cached `indepOf[u - 1]` slice is true. The remaining content is therefore
no longer bridge packaging; it is the set-level deleted-formula truth theorem
itself.

## Shortest path from here

### Phase 0: Make the strategy choice explicit

Goal: stop running the negative-`e` frontier as two separate proof projects.

Working decision for this clone:

1. Treat `dqrat-lean-checker-work` as the recommended merge target.
2. Use this clone as a source of lemmas, diagnostics, and counterexample
   packaging unless the static route is shown false.
3. Do not deepen the dynamic continuation stack without first checking whether
   the cached `NoDeleteCrossPathsSet` facts already reduce the frontier to the
   static `forceDelDeps` theorem.

### Phase 1: Either collapse to the static route or justify the dynamic one

Goal: decide whether the dynamic continuation machinery is actually needed for
the final deletion theorem.

Steps:

1. Use `computeDeps_activeDeletionFacts_filter_contains` to expose the cached
   `NoDeleteCrossPathsSet` facts for `computeDepsActiveDeletionVars`.
2. If the static theorem
   `forceDelDeps_formula_sound_of_noDeleteCrossPaths` can be ported or proved
   here, rewrite `computeDeps_forceDelDeps_formula_sound` directly from those
   facts and bypass `computeDeps_activeDeletionSetBridge` /
   `computeDeps_activeDeletionPoolContinuation`.
3. If that reduction fails, record the exact missing implication rather than
   adding more continuation layers by default.
4. Only if the reduction genuinely fails, continue the dynamic proof through
   `computeDeps_activeDeletionPoolContinuation`.
5. Feed the resulting theorem into the existing build-green wrappers
   `delDependencyReset_full_correct_lookup_spec_of_forceDelDepsTrue` and
   `checkModifyExistentialDelStep_full_sound_of_forceDelDepsTrue`.
6. Show failed dep deletions return `.Failed ...` without breaking the
   action-boundary invariant.
7. Combine the add and delete sides into the full modify-existential action
   theorem.

### Phase 2: Promote the loop invariant if needed

Goal: keep the full checker on the stronger invariant that the DQRATE branch
actually consumes.

Expected route:

1. Prove a stronger single-action theorem for the full checker, likely on
   `FullCorrect` rather than bare `Correct`.
2. Prove the corresponding action-list theorem by induction.
3. Derive the existing end-to-end theorem from the parser's already-proved
   `parseDQDIMACS_full_correct`.

This is cleaner than trying to re-derive live-occurrence completeness ad hoc
inside the RAT branch.

## What to avoid

- Do not prove `checkDQRATE_sound_spec` against a precondition that is weaker
  than the semantic lift actually needs.
- Do not reopen parser work; the parser side is already closed enough.
- Do not broaden the target back into old abstract DQRATE/DQRATU statements.
- Do not spend time on watched literals or other performance refactors before
  the simple checker is fully verified.

## Immediate next action

1. Stop describing `checkAction_sound` as the live hole for this clone.
2. Keep `deleteBridge...` as a scope guard against the refuted fixed-witness,
   deleted-variable-only patch route.
3. Check whether the static `NoDeleteCrossPaths` route subsumes the current
   dynamic chain.
4. If it does, port that theorem and avoid deepening the continuation stack.
5. If it does not, write down the exact obstruction before proving more rank
   or restart lemmas.
