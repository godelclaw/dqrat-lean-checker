# GPT Pro Handoff

This package is meant to be handed to GPT Pro as a buildable source snapshot of
the current DQRAT Lean checker work.

## Snapshot

- Repo: `dqrat-lean-checker-work`
- Branch: `codex/wip-parser-soundness-seam`
- Base commit: `0a74c94a8887667d6eba33caf2d4de1dd57f6f4b`
- Current source state in this zip: base commit plus the current uncommitted,
  build-green additions to `DqratLean/Soundness.lean`

At packaging time, the only dirty source file was:

- `DqratLean/Soundness.lean`

## Verify

Use the pinned toolchain:

```bash
elan toolchain install leanprover/lean4:4.29.0-rc6
lake build
lake build DqratLean.Soundness
./scripts/build_and_test.sh
```

The current working-tree state passes:

- `lake build DqratLean.Soundness`
- `./scripts/build_and_test.sh`

## Best Files To Read First

1. `README.md`
2. `sound_todo.md`
3. `challenges.md`
4. `docs/dqrate_fullcorrect_audit.md`
5. `DqratLean/Counterexamples.lean`
6. `DqratLean/Soundness.lean`

## Exact Frontier

The main DQRATE soundness seam is closed.

The only remaining theorem-body `sorry` is in:

- `DqratLean/Soundness.lean:16483` `checkAction_sound`
- specifically the `ModifyExistential` branch at `DqratLean/Soundness.lean:16490`

So the remaining work is the full negative-`e` / dependency-deletion path.

## Current Working-Tree Additions

The current uncommitted patch adds a proof-only no-negative wrapper layer:

- `DqratLean/Soundness.lean:9899`
  `checkModifyExistentialNoNegCore`
- `DqratLean/Soundness.lean:9907`
  `checkModifyExistential_body_eq_noNegCore`
- `DqratLean/Soundness.lean:9938`
  `checkModifyExistentialNoNegCore_full_sound`
- `DqratLean/Soundness.lean:9975`
  `checkModifyExistentialNoNegCore_full_step_spec`
- `DqratLean/Soundness.lean:9994`
  `checkModifyExistentialNoNegProof`
- `DqratLean/Soundness.lean:10010`
  `checkModifyExistentialNoNegProof_full_sound`

These are intentionally modest:

- they factor the no-negative executable shape into a cleaner proof-only core;
- they reuse the existing init theorem and add-step theorem;
- they stop short of claiming the executable `checkModifyExistential` itself is
  proved in the no-negative case.

## Useful Existing Negative-`e` Infrastructure

The semantic and wrapper groundwork already in the repo includes:

- `DqratLean/Soundness.lean:1034`
  `DeleteIndependenceSetBridge`
- `DqratLean/Soundness.lean:1261`
  `forceDelDeps`
- `DqratLean/Soundness.lean:1484`
  `DeleteIndependenceSetBridge.of_forceDelDepsTrue`
- `DqratLean/Soundness.lean:1492`
  `DeleteIndependenceBridge.of_forceDelDepsTrue`
- `DqratLean/Soundness.lean:3617`
  `DeleteIndependenceBridge.of_notDependsOn_true_forceDelDepsTrue`
- `DqratLean/Soundness.lean:5914`
  `delDependencyReset_full_correct_lookup_spec_of_forceDelDepsTrue`
- `DqratLean/Soundness.lean:10094`
  `checkModifyExistentialDelStep_full_sound_of_forceDelDepsTrue`

So the deletion-side wrapper stack is not the main missing piece anymore. The
missing content is the semantic theorem that a successful `notDependsOn`
justifies the relevant `forceDelDeps` truth claim.

## Challenges We Ran Into

### 1. DQRATE had two different false finish routes

The repo contains auditable witnesses for both:

- the old weak `Correct`-only DQRATE surface was false because live occurrence
  completeness matters;
- the older `DQRATE_exec_Condition` / per-blocker-resolvent bridge was also too
  strong for the executable checker.

These are already resolved in the current proof spine, but they are useful
guardrails for avoiding regressions.

### 2. The naive deletion bridge is too strong

The repo has `deleteBridge...` counterexamples showing that this route fails:

1. take one arbitrary old satisfying witness;
2. patch only the deleted existential;
3. try to prove that successful `notDependsOn` implies the patched witness works.

That is not the right semantic object.

### 3. Large loop-wrapper proofs quickly turned into plumbing

A few attempts at proving the executable no-negative path directly became
fragile because they were fighting Lean's desugaring of:

- `for` loops,
- `do`-notation,
- `EStateM.bind`,
- result-shape normalization.

The current proof-only wrapper layer exists precisely to avoid spending more
time inside that plumbing than the semantic content justifies.

### 4. The direct executable no-negative theorem is still open

The obvious next theorem

- executable `checkModifyExistential` soundness under `∀ cv ∈ depChanges, ¬ cv < 0`

looks very close, but the direct proof attempts kept getting stuck on monadic
shape normalization rather than on the real semantic issue.

That theorem is likely still doable, but it should be approached in a way that
leans on the new proof-only wrapper theorems rather than replaying the raw
desugared loop.

## Where We Want To Go

There are two clear next goals.

### Near-term proof engineering goal

Use the new no-negative wrapper theorems to derive the executable no-negative
soundness theorem for `checkModifyExistential`, then split `checkAction_sound`
into:

- a proved no-negative branch;
- the remaining honest negative-deletion branch.

This is the shortest way to reduce the final `sorry` to its real semantic core.

### Real semantic end-goal

Prove the paper-shaped negative-`e` theorem:

- `computeDeps_forceDelDepsTrue`: after successful `computeDeps u`, the
  recomputed state `s₁` satisfies
  `DQBFTrue (forceDelDeps s₁.formula (s₁.indepOf.getD (u - 1) #[]) u) s₁.clauses`

Once that is available, the repo already has wrappers that should lift it
through:

- `delDependencyReset`
- `checkModifyExistentialDelStep`
- the remaining `ModifyExistential` case of `checkAction_sound`

## Most Useful GPT Pro Help

The best narrow ask is not "audit the whole project". It is one of these:

1. Give a clean executable-aligned proof strategy for deriving the no-negative
   executable theorem from:
   - `checkModifyExistentialNoNegProof_full_sound`
   - `checkModifyExistential_body_eq_noNegCore`
   - `checkModifyExistentialInit_full_correct_spec`
2. Or, more ambitiously, help formalize `computeDeps_forceDelDepsTrue`, the
   semantic theorem behind the remaining negative-`e` deletion path.

If choosing only one, the second is more important for full completion, but the
first is a good short-term checkpoint and may simplify later auditing.

## What Not To Suggest

- Do not reopen parser work.
- Do not weaken the DQRATE surface back to `Correct`.
- Do not route DQRATE back through the old `DQRATE_exec_Condition`.
- Do not suggest watched literals or performance refactors.
- Do not rely on the refuted fixed-witness, deleted-variable-only patch route
  for negative-`e`.
