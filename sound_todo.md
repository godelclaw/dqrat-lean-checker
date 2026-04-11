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
- The only remaining explicit theorem-body `sorry` in
  `DqratLean/Soundness.lean` is `checkAction_sound`.

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

## Shortest path from here

### Phase 1: Close negative-`e`

Goal: prove full soundness of `checkModifyExistential`, not just the add-only fragment.

Steps:

1. Prove a result-dependent deletion-step spec for `checkModifyExistentialDelStep`.
2. Isolate the state/formula preservation theorem for successful `delDependencyReset`.
3. Show failed dep deletions return `.Failed ...` without breaking the action-boundary invariant.
4. Combine the add and delete sides into the full modify-existential action theorem.

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

1. Prove a result-dependent correctness/full-correctness spec for
   `delDependencyReset`.
2. Lift that into `checkModifyExistentialDelStep`.
3. Then close the remaining `ModifyExistential` case of `checkAction_sound`.
