# Soundness TODO

This file tracks the shortest still-honest path from the current branch state
to full soundness of the executable-aligned checker.

## Current state (2026-06-10)

- `scripts/build_and_test.sh` is green: full build, `DqratLean.Soundness`,
  parser regressions, executable smoke test.
- Exactly TWO theorem-body `sorry`s remain in the whole library, both in
  `DqratLean/DeletionExhibition.lean`: `reformLeft_matrix_true` and
  `reformRight_matrix_true` — the two polarity instances of Lemma 2 of
  Beyersdorff-Blinkhorn-Chew-Schmidt-Suda (JAR 2019), whose proof is
  transcribed line-by-line in comments at the sorry sites.
  The construction (two-stage reformed model, paper Defs. 12-13), its
  evaluation rules, and the Lemma 4 analogue (exhibition,
  `reformSkolem_exhibits_mem`) are PROVED; the frontier theorem
  `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet` assembles from
  these. Papers archived in `docs/papers/`.
- Everything else is proved: parser correctness, DEL/addClause/UR, RUP,
  DQRATE (`checkDQRATE_sound_spec` on the `FullCorrect` surface), add-only
  existential modification, and the full wrapper chain
  `checkAction_sound` / `processProof_sound'` — all green modulo the one
  frontier theorem above.

## The frontier theorem

`deleteIndependenceSetBridge_of_noDeleteCrossPathsSet`:
given `FullCorrect` side conditions and `NoDeleteCrossPathsSet st vars on_`
(no variable of `vars` is connected to both polarities of the universal `on_`
by `on_`-pure resolution paths, as certified by the executable `getReachable`
BFS), produce `DeleteIndependenceSetBridge st vars on_`: any model can be
repaired into a model whose Skolem functions for every `of_ ∈ vars` are
simultaneously independent of `on_`.

This is **full exhibition of the reflexive resolution-path dependency
scheme**, a published theorem:

- R. Wimmer, K. Wimmer, C. Scholl, B. Becker, "Dependency Schemes for DQBF"
  (SAT 2016).
- O. Beyersdorff, J. Blinkhorn, "Reinterpreting Dependency Schemes:
  Soundness Meets Incompleteness in DQBF" (J. Automated Reasoning 2019) —
  Theorem 8 (`Drrs` is fully exhibited), proved via "reformed paths": the
  repaired Skolem function copies its value from the `u`-flipped assignment
  along resolution-path cones.

So the remaining work is theorem *transcription*, not theorem discovery.

## Plan: the JAR 2019 reformed-model construction (in DeletionExhibition.lean)

STATUS 2026-06-10 (evening): steps below superseded by the faithful paper
transcription. DONE: reformLeft/reformRight/reformSkolem (paper Defs. 12-13),
all evaluation rules, Lemma 4 analogue (`reformSkolem_exhibits_mem`), and
the assembly of the bridge theorem. REMAINING: the two Lemma 2 analogues
(`reformLeft_matrix_true` / `reformRight_matrix_true`); their paper proof is
transcribed in the module — the Lean work is the per-literal clause analysis
using `matrixValue_false_implies_exists_false_clause`, the
`litValue_false_true_flip_*` lemmas, and a `DeletePurePath` extension step.

### Original sketch (historical)

1. `reduce_to_pathComplete` — trade `FullCorrect` for the two
   `DeletePurePathComplete st on_ (mkLit on_ pos)` facts via
   `deletePurePathComplete_mkLit`; cross-pair freedom is then
   `noDeleteCrossPathsSet_not_deletePurePath_pair`.
2. Defs `coneSide` (classify an existential by which `getReachable` array
   hits it) and `mergeSkolem` (pin the `on_`-coordinate of the argument
   vector to the cone-canonical constant for in-cone `on_`-dependent
   existentials; identity otherwise). Built on `fullDepArgs` /
   `deleteDepArgs`.
3. `mergeSkolem_exhibits` — flip-invariance of `varValue` for `of_ ∈ vars`
   via `varValue_eq_of_fullDepArgs_eq` + pinning; discharges the exhibition
   conjunct through `exhibitsDeleteIndependence_iff_flipUniv`.
4. `mergeSkolem_offCone_eq` — off-cone literals keep their old values
   (`litValue_flipUniv_eq_of_off_cone` etc.).
5. `falseClause_changed_lit_in_cone` — a clause false under the merge but
   true under the model contains either the negated cone literal (the BFS
   skip case) or a changed literal that is a `DeletePurePath` step premise
   (`litValue_false_true_flip_universal_eq_on` /
   `litValue_false_true_flip_existential_contains`).
6. `falseClause_extends_path` — package 5 as a `DeletePurePath.step`
   extension along the clause (`deletePurePath_step_from_opposite_target_tail`,
   `noStartNeg_of_false_other_literals` slot in here).
7. `merge_matrix_true` — by contradiction: a false clause yields
   cross-polarity pure paths to some `of_ ∈ vars`, killed by
   `noDeleteCrossPathsSet_not_deletePurePath_pair`
   (via `matrixValue_false_implies_exists_false_clause`).
8. Assemble `DeleteIndependenceSetBridge`. The downstream chain
   (`DQBFTrue_forceDelDeps_of_setBridge` →
   `forceDelDeps_formula_sound_of_noDeleteCrossPaths` →
   `computeDeps_forceDelDeps_formula_sound` → `checkAction_sound` →
   `processProof_sound'`) is already green.

Iterate with `lake build DqratLean.DeletionExhibition` (sub-second replay;
the leaf only rebuilds itself against compiled support modules).

## History: the abandoned descent route

A fiber-counting witness-descent proof was attempted (preserved in the WIP
checkpoint commit `64c375e`, removed in `f6c72b7`). It dead-ended in a
restart obligation (`DeleteWitnessProgressCurrentStrictRestart`) quantified
over abstract progress candidates related to the base model only by
fiber-count decrease + fiber-subset. That relation admits adversarial
instances (candidate scrambled off the deletion frontier, fiber count 0,
falsified elsewhere) for which the obligation degenerates to the full
theorem with no usable hypotheses. Do not resurrect that route; if a
descent is ever reattempted, the candidate relation must carry the patch
chain construction itself.

The parallel dynamic-continuation route in `dqrat-lean-checker-watched`
(`codex/watched-literals-port`) is subsumed: see
`docs/negative_e_strategy_split.md`. That clone is archived as a source of
lemmas and counterexample packaging only.

## What to avoid

- Do not reopen parser work; the parser side is closed.
- Do not broaden the target back into abstract DQRATE/DQRATU statements.
- Do not spend time on watched literals or performance refactors before the
  simple checker is fully verified.
- The `deleteBridge...` counterexamples in `DqratLean/Counterexamples.lean`
  still rule out the naive route (fixed old witness, patch only the deleted
  existential). The merged-witness construction is not subject to them: it
  re-routes *all* in-cone existentials through one pinned half-space.
