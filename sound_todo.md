# Soundness TODO

This file tracks the shortest solid path from the current state to full soundness.

## Current state

- `lake build` passes.
- Parser/executable milestone is green.
- Basic checker soundness is closed.
- `CheckState.empty_correct` is proved.

Remaining real `sorry` bodies in `DqratLean/Soundness.lean`:

1. `DQRATE_soundness`
2. `DQRATU_soundness`
3. `processProof_sound`
4. `checkAction_sound`
5. `checkActions_sound`
6. `parseDQDIMACS_correct`
7. `processProof_sound'`

## Important route correction

Not every remaining `sorry` should be proved as written.

The following theorem statements are still placeholders or obsolete proof targets:

- `DQRATE_soundness`
  Current `DQRAT_e_Condition` only states that the pivot is existential.
  That is not the real executable condition.

- `DQRATU_soundness`
  Current hypothesis only uses `URCondition`.
  The executable `checkDQRATU` does more than that.

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

1. Prove local specs for prefix readers starting from `CheckState.empty_correct`.
   Targets:
   - `readUniVarsM`
   - `readExiVarsM`
   - `readDepsM`
   - `readPrefixM`

2. Prove a result-dependent spec for `readMatrixM`.
   Required shape:
   - if it returns `false`, the final state is `Correct`
   - if it returns `true`, parsing found UP-unsat and `parseDQDIMACS` returns `none`

3. Prove `parseDQDIMACS_correct`.
   Route:
   - `validateDQDIMACSStructure` gives well-formed line discipline
   - `readPrefixM` builds a `Correct` state from `CheckState.empty`
   - `readMatrixM` preserves `Correct` on the non-unsat branch

### Phase 2: Full action-boundary specs

Goal: remove full-checker state mutation ambiguity before proving rule semantics.

Steps:

1. Positive modify-existential path:
   - prove a clean spec for `checkModifyExistentialAddStep`
   - then prove the positive-only loop fragment of `checkModifyExistential`

2. Negative modify-existential path:
   - isolate the deletion side condition around `notDependsOn` / `delDependency`
   - prove a result-dependent spec for the negative branch

3. Combine the two into a full `checkModifyExistential_correct_spec`.

4. Keep using the existing proved action-boundary specs:
   - `checkAddUniversal_correct_spec`
   - `checkDeleteClause_correct_spec`

### Phase 3: Repair full rule semantics

Goal: replace placeholder theorem statements with executable-aligned ones.

This is the most important design step left.

#### 3A. DQRATE

Do not prove current `DQRATE_soundness` as-is.

Needed work:

1. Extract the real executable condition from `checkDQRATE`.
2. State the semantic theorem in terms of that executable-aligned condition.
3. Reuse the already-proved RUP/basic trial infrastructure where possible.

Expected helper seam:

- a full blocker-trial theorem around the `negateAndPropagate ... ; backtrackBefore 2` pattern

#### 3B. DQRATU

Do not prove current `DQRATU_soundness` as-is.

Needed work:

1. State a theorem matching the actual `checkDQRATU` path:
   - RUP without pivot
   - connected blocker scan via `checkPathC`
   - blocker trial via `negateAndPropagate`

2. Use the earlier UR permutation/lookup cleanup already in the branch.

Expected helper seam:

- a blocker-check theorem aligned with `checkDQRATU`, not bare `URCondition`

### Phase 4: Full checker composition

Once Phases 1-3 are done:

1. Prove `checkAction_sound`
   by case split on `DQRatAction` using:
   - proved action-boundary specs
   - repaired `DQRATE` / `DQRATU` soundness theorems
   - existing RUP / delete / addClause lemmas

2. Prove `checkActions_sound`
   by induction on the action list.

3. Prove `processProof_sound'`
   using:
   - `parseDQDIMACS_correct`
   - `checkActions_sound`

## What to avoid

These are likely time sinks:

- proving `DQRATE_soundness` against the current fake `DQRAT_e_Condition`
- proving `DQRATU_soundness` against the current simplified `URCondition`
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

1. prove `readUniVarsM` preserves `PrefixState`
2. prove `readExiVarsM` preserves `PrefixState`
3. prove `readDepsM` preserves `PrefixState`
4. prove `readPrefixM` preserves `PrefixState`
5. then lift `PrefixState` back to the `Correct` boundary needed by `parseDQDIMACS_correct`

Tactical note:

- use the generated `readUniVarsM.eq_def` / `readExiVarsM.eq_def` / `readPrefixM.eq_def`
  equations as the proof surface
- keep the reader proofs result-dependent (`⇓?`) so parse errors stay vacuous
- do not re-open parser API refactors until the recursive reader proofs are in
