# Dependency Removal Revision Notes

Date: 2026-04-17

## Archived reference material

- `docs/references/proof_rules_2026-04-17.tex`
- `docs/references/proof_rules_2026-04-17.pdf`
- `DqratLean/dependency_removal_tex.txt`

These are the revised paper-side proof files that corrected the invariant package
for the dependency-removal lemma.

## What changed in the proof story

The revised paper proof now tracks a repair pool of Skolem functions with three
relevant constraints:

- changed values stay on the chosen `u`-polarity slice,
- any remaining `u`-dependency witness was already present before the repair,
- each changed existential still satisfies the required no-pure-path side
  condition.

That invariant shape is directly relevant to the remaining semantic blocker in
`DqratLean/Soundness.lean`.

## What it does not affect

The watched-runtime proofs are still a separate local refinement layer:

- `DqratLean/WatchedSoundness.lean`
- `DqratLean/WatchedBinarySoundness.lean`
- `DqratLean/WatchedBinaryRefinement.lean`

Those invariants are about cache correctness, not Skolem repair semantics, so
the paper correction does not change their statements.

## Lean consequence

The right theorem boundary for the remaining semantic frontier is the cached-set
statement

- `computeDeps_forceDelDeps_formula_sound`

not the sharper single-variable statement

- `computeDeps_forceDelDep_formula_sound_of_member_contains`.

The intended route is:

1. prove truth preservation for `forceDelDeps` on the whole cached
   `indepOf[on_ - 1]` set produced by `computeDeps`,
2. derive the single-variable bridge with
   `DeleteIndependenceBridge.of_forceDelDepsTrue`,
3. finish the one-variable formula theorem using
   `DQBFTrue_forceDelDep_of_exhibiting_bridge`.

## Use policy for the paper files

Treat the revised TeX/PDF as semantic guidance, not as a line-by-line Lean port.
The invariant direction is the important part for this mirror.
