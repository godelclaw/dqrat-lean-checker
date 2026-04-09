# Soundness TODO

This file tracks the shortest solid path from the current state to full soundness.

## Current state

- `lake build` passes.
- Parser/executable milestone is green.
- Basic checker soundness is closed.
- `CheckState.empty_correct` is proved.

Remaining real `sorry` bodies in `DqratLean/Soundness.lean`:

1. `checkDQRATE_sound_spec`
2. `checkDQRATU_restore_spec`
3. `processProof_sound`
4. `checkAction_sound`
5. `checkActions_sound`
6. `parseDQDIMACS_correct`
7. `processProof_sound'`

## Important route correction

Not every remaining `sorry` should be proved as written.

The following theorem statements are still placeholders or obsolete proof targets:

- `checkDQRATE_sound_spec`
  This is now the right theorem boundary, but it is still unproved.
  The old abstract `DQRAT_e_Condition` remains only as background, not as the
  next proof target.

- `checkDQRATU_restore_spec`
  This is the right theorem for top-level soundness of the current executable.
  The old abstract `DQRATU_soundness` route was too broad because the program's
  non-trivial `u` branch re-adds an already-located clause.

- `processProof_sound`
  This is not the best top theorem anymore.
  `processProof_sound'` is the real parser-to-checker endpoint.

So the correct strategy is:

1. finish the parser and action-boundary foundation,
2. repair the full-rule theorem boundaries to match the executable,
3. prove the repaired rule theorems,
4. compose the final checker theorems.

## Step-by-step plan

### Phase 1: Parser-side foundation

Goal: prove `parseDQDIMACS_correct`.

This is now the best next milestone because it is a real theorem with a stable statement.

Steps:

1. Prefix-reader layer: done.
   Proved:
   - `readUniVarsM_prefix_spec`
   - `readExiVarsM_prefix_spec`
   - `readDepsM_prefix_spec`
   - `readPrefixDepLineM_prefix_spec`
   - `readPrefixM_prefix_spec`

2. Prove a result-dependent spec for `readMatrixM`.
   Required shape:
   - if it returns `false`, the final state is `Correct`
   - if it returns `true`, parsing found UP-unsat and `parseDQDIMACS` returns `none`
   New structure:
   - use `ReadMatrixPost`
   - do not require `Correct` on the conflict/`true` branch
   Route correction:
   - do not invent another prefix-to-`Correct` bridge;
     `PrefixState` already contains `Correct CheckState.empty.formula CheckState.empty.clauses`
   - use the new matrix substrate:
     - `PrefixState.toMatrixCorrect`
     - `CheckState.Correct.toSelf`
     - `CheckState.Correct.withSelfAddClause`
     - `AddClauseSelfPost`
     - `addClauseAfterCache_self_spec`
     - `addClause_self_spec`
     - `ClauseLitsWellFormed.sortLits`
   - the parser now uses `ClauseStore.sortLits`, so the executable/proof boundary is aligned
   - the next real design choice is the smallest recursive theorem over `readMatrixM`;
     the earlier direct theorem attempt degraded into monad-reduction noise and was
     intentionally backed out

3. Prove `parseDQDIMACS_correct`.
   Route:
   - `validateDQDIMACSStructure` gives well-formed line discipline
   - `readPrefixM` keeps the parser in `PrefixState`
   - `readMatrixM` preserves `Correct` on the non-unsat branch

### Phase 2: Full action-boundary specs

Goal: remove full-checker state mutation ambiguity before proving rule semantics.

Steps:

1. Positive modify-existential path:
   - prove a clean spec for `checkModifyExistentialAddStep`
   - then prove the positive-only loop fragment of `checkModifyExistential`

2. Negative modify-existential path:
   - executable alignment is now better: successful deletions go through `delDependencyReset`
   - executable seam is now explicit in `checkModifyExistentialDelStep`
   - isolate the deletion side condition around `checkModifyExistentialDelStep` / `notDependsOn` / `delDependencyReset`
   - prove a result-dependent spec for the negative branch

3. Combine the two into a full `checkModifyExistential_correct_spec`.

4. Keep using the existing proved action-boundary specs:
   - `checkAddUniversal_correct_spec`
   - `checkDeleteClause_correct_spec`

### Phase 3: Repair full rule semantics

Goal: replace placeholder theorem statements with executable-aligned ones.

This is the most important design step left.

#### 3A. DQRATE

Do not go back to the old abstract `DQRATE_soundness` target.

Needed work:

1. Prove `checkDQRATE_sound_spec`.
2. Reuse the already-proved RUP/basic trial infrastructure where possible.
3. Keep the theorem executable-aligned:
   - restore `Correct`
   - preserve literal well-formedness
   - on success, justify `addClause lits`

Expected helper seam:

- a full blocker-trial theorem around the `negateAndPropagate ... ; backtrackBefore 2` pattern
- executable refactor already landed:
  - `runDQRATEBlockerTrial` now exists in `Checker.lean`

#### 3B. DQRATU

Do not revive the old broad `DQRATU_soundness` target before the executable is closed.

Needed work:

1. Prove `checkDQRATU_restore_spec`, matching the actual `checkDQRATU` path:
   - RUP without pivot
   - connected blocker scan via `checkPathC`
   - blocker trial via `negateAndPropagate`
   - restore action-boundary `Correct`

2. Use the earlier UR permutation/lookup cleanup already in the branch.
3. In `checkUniversalReduction_sound`, treat the non-trivial `u` branch as
   restoration + duplicate-add of an already-located clause.
4. Executable alignment already landed:
   - full `checkUniversalReduction` now reuses `translateExistingLits`

Expected helper seam:

- `checkDQRATU_restore_spec`, not bare `URCondition`

### Phase 4: Full checker composition

Once Phases 1-3 are done:

1. Prove `checkAction_sound`
   by case split on `DQRatAction` using:
   - proved action-boundary specs
   - `checkDQRATE_sound_spec`
   - `checkDQRATU_restore_spec`
   - existing RUP / delete / addClause lemmas

2. Prove `checkActions_sound`
   by induction on the action list.

3. Prove `processProof_sound'`
   using:
   - `parseDQDIMACS_correct`
   - `checkActions_sound`

## What to avoid

These are likely time sinks:

- reviving the old abstract `DQRATE_soundness` theorem before the executable-aligned spec
- proving a broad semantic `DQRATU_soundness` theorem before the restoration theorem
- proving `processProof_sound` before `processProof_sound'`
- proving large generic theorems when a smaller executable seam is available
- forcing more proof through a boundary once it degrades into monad-reduction noise
- blindly removing the parser readers' `{p // start ≤ p}` return witness before replacing
  the termination argument for `readPrefixM`

## Immediate next action

Prove the prefix-reader side of `parseDQDIMACS_correct` through the parser-specific
invariant `PrefixState`, not directly through `Correct`.

Already landed:

- `PrefixState`
- `PrefixState.withSetDepset`
- `PrefixState.withIndepCaches`
- `PrefixState.withAddVarForall`
- `PrefixState.withAddVarExists`
- `setDepset_prefix_spec`
- `makeIndepUnknown_prefix_spec`
- `makeIndepUnknown_prefix_loop_spec`
- `ensureWithinMaxVar_prefix_spec`
- `addVarForall_prefix_spec`
- `addVarExists_prefix_spec`

Next:

1. done: `readUniVarsM` preserves `PrefixState`
2. done: `readExiVarsM` preserves `PrefixState`
3. done: `readDepsM` preserves `PrefixState`
4. done: factor the `d`-branch of `readPrefixM` into a proof-aligned helper theorem
5. done: `readPrefixM` preserves `PrefixState`
6. done: prove the right `readMatrixM` result-dependent theorem (`ReadMatrixPost`)
7. next: prove the inner parser kernel theorem for `parseDQDIMACSInner`
8. then derive small wrappers for `parseDQDIMACSTokensAfterHeader` /
   `parseDQDIMACSTokens`
9. then finish `parseDQDIMACS_correct`
10. then move the full-checker theorems onto the parser-complete boundary

Tactical note:

- use the generated `readUniVarsM.eq_def` / `readExiVarsM.eq_def` / `readPrefixM.eq_def`
  equations as the proof surface
- keep the reader proofs result-dependent (`⇓?`) so parse errors stay vacuous
- do not re-open parser API refactors until the recursive reader proofs are in
- the direct `readPrefixM` recursion was the wrong proof boundary until the `d`-branch helper
  was extracted; that helper is now in place
- `readMatrixM_sound_spec` is now the matrix-side parser kernel
- `parseDQDIMACS` has now been split into the executable helpers
  `parseDQDIMACSInner`, `parseDQDIMACSTokensAfterHeader`, and `parseDQDIMACSTokens`
- a direct outer-shell proof attempt for `parseDQDIMACS_correct` was backed out;
  the next parser proof surface should be `parseDQDIMACSInner`
  so the next parser proof should target the post-header helper or inner `CheckM`
  run, not the full outer `Except` shell directly
- the next boundary to choose carefully is the final parser theorem order, not more matrix substrate
- keep `parseDQDIMACS_correct` after `readMatrixM_sound_spec`; proving it earlier forces a bad forward-reference shape
- once parser work resumes, the better next executable-aligned semantic seam is the `checkDQRATU` RUP phase, now isolated by `checkDQRATU_rup_phase_restore_spec`
- for the remaining `checkDQRATU` branch, prove the named nested helper
  `runDQRATUBlockerTrial` instead of the old inline `negateAndPropagate ...; backtrackBefore 2` block
- the blocker fold is now factored into the executable cases:
  missing clause, deleted clause, disconnected clause, and connected blocker
  reducing to `runDQRATUBlockerTrial`; only the last one is still semantically hard
- the missing/deleted/disconnected blocker cases are now lifted to outer-trial
  preservation specs; next for `checkDQRATU` is a nested restore theorem for
  `runDQRATUBlockerTrial`
- nested blocker-trial substrate now exists: `NestedTrialState`,
  `newDecisionLevel_nested_trial_spec`, and preservation of outer assignments
  into the nested state; next is `backtrackBefore 2` restoring the outer trial
- attempted route (failed): proving `propagateOne_nested_trial_spec` with `mvcgen`
  currently gets pulled into semantic `enqueue_consistent_spec` obligations
  (`ConsistentWith` witness goals) instead of the structural nested invariant
- Lean 4.29 in this file rejects removing `[spec]` via `attribute [-spec] enqueue_consistent_spec`,
  so that workaround is unavailable here
- practical next route: prove the connected nested blocker boundary without relying
  on `mvcgen` spec selection for `propagateOne`, then resume
  `runDQRATUBlockerTrial` restoration and `checkDQRATU_restore_spec`
