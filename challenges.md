# Remaining Challenges

This note is for a fresh reviewer who wants to build the project, understand the
remaining proof gap, and help finish it honestly.

## What Is Left

As of the current green state, `DqratLean/Soundness.lean` has exactly one
theorem-body `sorry`:

1. `checkAction_sound`

That remaining branch is the known negative-`e` / dependency-deletion blocker.

## Build And Test

Use the pinned Lean toolchain:

```bash
elan toolchain install leanprover/lean4:4.29.0-rc6
lake build
lake build DqratLean.Soundness
./scripts/run_parser_regressions.sh
```

Quick executable examples:

```bash
lake exe dqrat-lean tests/test_04_propositional_drat.dqdimacs tests/test_04_propositional_drat.dqrat
lake exe dqrat-lean repros/stale_delete_state.dqdimacs repros/stale_delete_state.dqrat
```

## Resolved DQRATE Crux

The DQRATE proof was not blocked by syntax or by missing restore lemmas. It was
blocked by a semantic bridge, and that bridge is now closed directly.

The checker does this:

1. Run an outer negate/propagate trial on the candidate clause.
2. If not RUP, choose a pivot and scan blocker clauses from occurrence lists.
3. For each live blocker, run a nested blocker trial.
4. If every blocker trial succeeds, accept the clause as DQRATE.

The hard part was proving that step 4 yields the semantic consequence needed to
justify adding the clause.

### Why The Old Weaker Statement Failed

The old `Correct`-only DQRATE surface was false. The repo contains an auditable
counterexample:

- `DqratLean/Counterexamples.lean`
- `docs/dqrate_fullcorrect_audit.md`

The issue is live-occurrence completeness. If a live blocker clause is missing
from occurrence lists, the executable scan can miss a necessary blocker and
accept an unsound addition. So the real theorem must carry `FullCorrect`, not
bare `Correct`.

### Why The Older Finish Route Also Fails

There is now a second auditable witness in `DqratLean/Counterexamples.lean`:

- `dqrateBridgeAccepted_true`
- `dqrateBridge_not_exec_condition`

This shows something more subtle. Even with the right `FullCorrect`-style
surface, an accepted executable DQRATE step need not satisfy the old
`DQRATE_exec_Condition` / per-blocker-resolvent bridge.

So the remaining challenge is not to squeeze the executable checker through that
older semantic bottleneck. The challenge is to prove soundness by a route that
matches what the executable actually establishes.

### Why That Gap Was Subtle

We now preserve much more than before through the blocker fold:

- restored formula/clauses equality,
- restored assignment equality,
- restored assigned-value agreement,
- empty propagation queue.

This is packaged as `OuterStateShadow` and threaded through the blocker scan.

That means the old DQRATE gap was no longer about state restoration. It was also
no longer best viewed as:

- successful blocker-trial execution on a restored shadow state

into the old global per-blocker resolvent consequence.

Instead, the successful route is a direct patched-model argument for the added
clause itself.

## What Was Needed To Close It

The repo now already has the following useful infrastructure:

- `OuterStateShadow`
- `CheckState.ConsistentWith.of_outerStateShadow`
- `runDQRATEBlockerTrial_restore_shadow_of_shadow_spec`
- `checkDQRATEBlockerFold_trial_shadow_spec`
- `checkDQRATEBlockerFold_none_gives_occ_semantic_shadow`
- `runDQRATEBlockerTrial_true_implies_outerClause_true_of_clause_false_agree_shadow`

So the DQRATE proof did not need more restore/state machinery.

## What Closed The DQRATE Branch

```lean
theorem runDQRATEPivotPhase_true_soundness_direct
    ...
```

The expected proof split is:

1. Fix arbitrary `σ, sk` satisfying the matrix.
2. Build the patched Skolem function with `patchPivotSkolemForClause`.
3. Show the original matrix stays true under the patched Skolem model using the
   existing patch lemmas.
4. Case split on whether the reduced clause is already true under the original
   model.
5. In the easy branch, conclude the added clause directly.
6. In the hard branch, use the shadow blocker theorem to force truth of the
   relevant outer clause under the same model, then discharge the added-clause
   goal under the patched model.

This route is no longer just a sketch. The repo now has compile-green support
lemmas for it, and `checkDQRATE_sound_spec` is now proved from that route:

- `clauseValue_patchPivotForClause_true_of_live_blocker_trial`
- `checkDQRATEBlockerFold_none_gives_patch_clause_true_shadow`
- `matrixValue_patchPivotForClause_true_of_successful_pivot_phase`
- `runDQRATEPivotPhase_true_soundness_direct`

This was the semantic clarity that mattered:

- the blocker trial is only needed in the reduced-clause-false branch;
- the reduced-clause-true branch should stay direct and boring;
- the patch machinery should be the main semantic vehicle;
- the old `DQRATE_exec_Condition` lemmas should become optional legacy helpers,
  not the proof spine.

## What Is Left Hard Now

The remaining difficulty is no longer DQRATE. It is dependency deletion for
`ModifyExistential`.

What is missing is an executable-aligned theorem stack for:

- `notDependsOn`
- `delDependency`
- `delDependencyReset`
- `checkModifyExistentialDelStep`

The main semantic issue is that deletion changes the dependency relation in the
formula, not just the checker state. So the proof has to show both:

- failed deletions produce the right `.Failed ...` result without breaking the
  action boundary, and
- successful deletions return to a clean action-boundary state with a formula
  that still soundly relates models back to the old one.

There is now a cleaner semantic split for that remaining work. The repo already
has a build-green patched witness for the weakened formula:

- `BadDeletePattern`
- `patchDeleteSkolemForFormula`
- `matrixValue_forceDelDep_patchDeleteForFormula_true_of_no_both_bad`
- `dqbfTrue_forceDelDep_of_no_both_bad`
- `DQBFTrue_forceDelDep_of_exhibiting_bridge`
- the one-universal / many-existentials scaffold that matches the paper:
  `forceDelDeps`, `liftForceDelDepsWitness`,
  `deleteIndependenceSetBridge_of_forceDelDepsTrue`,
  `DeleteIndependenceSetBridge.of_forceDelDepsTrue`
- `delDependencyReset_full_correct_lookup_spec_of_exhibiting_bridge`
- `checkModifyExistentialDelStep_full_sound_of_exhibiting_bridge`

There is also now a concrete warning sign about one route that does *not* work.
`DqratLean/Counterexamples.lean` contains the `deleteBridge...` witness family:

- `notDependsOn` succeeds on a small live formula,
- one concrete old witness satisfies the original matrix on both relevant
  Boolean choices for the unique universal, but
- for one particular old satisfying witness, both Boolean choices for the
  deleted existential fail if only that existential is patched on the reduced
  dependency pattern.

So the unresolved content is no longer just "find some Skolem witness after
deletion", and it is not the fixed-witness bridge below either:

- successful `notDependsOn`
- plus a proof that one chosen old witness has no both-bad reduced pattern
- plus patching only the deleted existential

That route is now refuted in-repo.

The real unresolved content is:

- identify the right semantic transport after deletion;
- prove `computeDeps_forceDelDepsTrue`, i.e. that successful `computeDeps u`
  yields truth of the formula obtained by deleting `u` from every existential
  in the cached `indepOf[u - 1]` slice on the recomputed state;
- then instantiate the already-built
  `delDependencyReset_full_correct_lookup_spec_of_forceDelDepsTrue` and
  `checkModifyExistentialDelStep_full_sound_of_forceDelDepsTrue` wrappers,
  which already recover the single-variable bridge by membership;
- then wrap the full modify-existential action.

## What To Avoid

- Do not weaken the theorem surface back to `Correct`.
- Do not spend time on watched literals or performance refactors.
- Do not reopen parser work.
- Do not reopen the old DQRATE bridge route; that part is closed.
- Do not hide the negative-`e` gap under more generic reset lemmas; the hard
  part is the dependency semantics.

## Recommended Order

1. Use the `deleteBridge...` witness to state precisely why fixed-witness,
   deleted-variable-only patching is too strong.
2. Replace it with the right semantic object:
   either a recursive patch over the relevant dependency cone, or a proof that
   old truth yields a better witness for the weakened set-deleted formula than
   an arbitrary
   old Skolem assignment.
3. Prove that successful `notDependsOn` yields `DeleteIndependenceBridge`.
4. Feed that into the existing successful semantic theorem for `delDependencyReset`.
5. Reuse the existing result-sensitive wrapper for `checkModifyExistentialDelStep`.
6. Use that to close the remaining `ModifyExistential` branch of `checkAction_sound`.
7. Then let `checkActions_sound` and the end-to-end full checker wrapper stand on that.

That is the shortest still-honest path to full correctness of the current
checker.
