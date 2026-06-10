# Negative-E Strategy Split

This note records the current branch split for the negative-`e` /
dependency-deletion soundness frontier.

## Active clones

- `dqrat-lean-checker-work`
  - branch: `codex/wip-parser-soundness-seam`
  - live theorem-body `sorry`:
    `forceDelDeps_formula_sound_of_noDeleteCrossPaths`
- `dqrat-lean-checker-watched`
  - branch: `codex/watched-literals-port`
  - live theorem-body `sorry`:
    `computeDeps_activeDeletionPoolContinuation`
  - matching split-file frontier:
    `computeDeps_activeDeletion_currentFrontier_externalHighPhaseRankBoundary`

## Strategy difference

- `-work` is pursuing a static reach-closure route:
  prove that pointwise `NoDeleteCrossPaths` over the cached active set is
  enough to preserve `DQBFTrue` under `forceDelDeps`.
- `-watched` is pursuing a dynamic continuation route:
  rebuild the same deletion result through tracked pool continuations,
  restart boundaries, and rank-step diagnostics.

## Audit result

- In `-watched`, `NoDeleteCrossPathsSet` is definitionally just
  `∀ of_ ∈ vars.toList, NoDeleteCrossPaths ...`.
- In `-watched`, `computeDeps_activeDeletionFacts_filter_contains` already
  produces that set-level fact for the cached active-deletion variables.
- Therefore, if the static theorem
  `forceDelDeps_formula_sound_of_noDeleteCrossPaths` is available on the
  watched branch, then its current
  `computeDeps_forceDelDeps_formula_sound` theorem can likely be rewritten
  directly from the cached `NoDeleteCrossPathsSet` facts, bypassing
  `computeDeps_activeDeletionSetBridge` and
  `computeDeps_activeDeletionPoolContinuation`.

This does not prove the static theorem. It does show that the dynamic branch
is not obviously required for the final `forceDelDeps` truth result.

## Counterexample scope

The `deleteBridge...` family refutes the narrow route:

1. keep one fixed old satisfying witness,
2. patch only the deleted existential, and
3. expect that to justify successful deletion.

It does not refute these broader possibilities:

1. dependency-cone patching,
2. witness recomputation from `DQBFTrue`,
3. a direct static semantic argument from `NoDeleteCrossPaths`.

## Working decision

Use `dqrat-lean-checker-work` as the merge target unless the static
reach-closure theorem is shown false. Treat the watched branch as a source of
lemmas, diagnostics, and counterexample packaging rather than as an
independent proof frontier.

## ARCHIVED (2026-06-10)

This clone is archived. The strategy split was resolved in favor of
`dqrat-lean-checker-work`: the frontier there is now the bridge-form
full-exhibition theorem `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet`
(`DqratLean/DeletionExhibition.lean`), and the descent/pool-continuation
machinery (both this clone's dynamic route and -work's fiber-counting
variant) is abandoned — the restart obligations over abstract candidates
are as hard as the full theorem. Mine this clone for lemmas, diagnostics,
and counterexample packaging only; do not continue frontier work here.
