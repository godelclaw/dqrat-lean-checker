# Deletion Exhibition: paper-to-Lean proof map

Target: `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet`
(`DqratLean/DeletionExhibition.lean`) — full exhibition of the reflexive
resolution-path dependency scheme (Wimmer et al. SAT 2016; Beyersdorff &
Blinkhorn JAR 2019, Thm 8 via "reformed paths").

## The construction (pin to a half-space)

Given a model `sk` (`∀ σ, matrixValue σ sk = true`), repair it by *pinning*:
for each `v ∈ vars`, re-route `sk v` through the assignment with the
`on_`-coordinate forced to a per-variable constant `cpol v`:

- `pinUniv on_ c σ`  := `σ[on_ := c]`
- `pinDepArgs f v on_ c args` := the dep-vector `args` with every coordinate
  belonging to `on_` overwritten by `c` (zipWith over `depset v`; duplicate-safe)
- `pinSkolem f vars on_ cpol sk` := `fun v args => if v ∈ vars then
  sk v (pinDepArgs f v on_ (cpol v) args) else sk v args`

Exhibition (conjunct ii) is then *mechanical*: pinned variables read only the
pinned half-space, so `varValue` is flip-invariant
(`exhibitsDeleteIndependence_iff_flipUniv`). This holds for ANY `cpol`.

## Truth (conjunct i): the case table

Fix σ with `b := σ on_`, write `σ_c := pinUniv on_ c σ` (so `σ_b = σ`,
`σ_{!b} = flipUniv on_ σ`). Suppose clause `C` is false under `(σ, sk')`.
Then every literal of `C` is false there, which translates per class:

| literal class                   | false under sk' at σ means … |
|--------------------------------|------------------------------|
| universal ≠ on_                | false at σ_true AND σ_false  |
| `mkLit on_ b`                  | impossible (it would be true) |
| `mkLit on_ (!b)`               | false at σ, but TRUE at σ_{!b} |
| existential, on_ ∉ depset      | false at σ_true AND σ_false (flip-insensitive) |
| `v ∈ vars` (pinned at `cpol v`)| `sk` gives false at σ_{cpol v} |
| `v ∉ vars`, on_ ∈ depset       | `sk` gives false at σ_b = σ  |

The model gives `C` true under `(σ_true, sk)` and `(σ_false, sk)`. Each
half-space must therefore contain a true literal among the classes NOT yet
known false there:

- at `σ_true`: a pinned `v₁` with `cpol v₁ = false` that is flip-sensitive
  (true at σ_true, false at σ_false), or — if b = false — an unpinned
  on_-dependent flip-sensitive variable, or `mkLit on_ true` if b = false…
- at `σ_false`: symmetric (`cpol = true` pinned, `¬on_` if b = true, unpinned
  if b = true).

The contradiction must come from `NoDeleteCrossPathsSet`: the surviving
combinations force `on_`-pure resolution paths from BOTH polarities of `on_`
to some `of_ ∈ vars` at opposite literal polarities
(`noDeleteCrossPathsSet_not_deletePurePath_pair`).

Worked sub-case (eliminates `¬on_ ∈ C` + pinned-false `v₁`, with
`cpol v := true iff the negative reach cone touches v`): `C ∋ mkLit on_ false`
and `C` does not contain `mkLit on_ true`, so `C` is a `DeletePurePath.first`
clause for the NEGATIVE cone, making every on_-dependent existential of `C`
negCone-reachable — in particular `v₁`, contradicting `cpol v₁ = false`.

## What remains open (the real content)

The pure existential-vs-existential sub-case: `C` with no `on_`-literal,
containing a pinned-false flip-sensitive `v₁` (true on the true side) and a
true-on-the-false-side partner `v₂` (pinned-true or unpinned). Closing it
needs the value-oriented path-extension machinery
(`DeletionPaths.lean`: `noDeleteCrossPathsSet_orients_seed`,
`deletePurePath_step_from_opposite_target_tail`,
`oriented_dependent_tail_forces_next_old_lit_nonpath`,
`noStartNeg_of_false_other_literals`), whose lemma shapes require an
"all other literals false" packaging — i.e. an induction over the multiset of
true literals per half-space, or per-path reform as in the JAR paper
(two stages: left reform on ¬u-paths, then right reform on u-paths).

Before finalizing: pull the JAR 2019 construction (§ reformed paths,
Definition 12 and the proof of Theorem 8 — open access, PMC6710225) and align
the pin/cone choice with their left/right two-stage reform. The repo's
`deleteBridge…` counterexamples (`Counterexamples.lean`) are the sanity
check: the construction must NOT reduce to "patch only the deleted
existential under a fixed witness".

## Lean wiring

- conjunct ii: proved generically over `cpol` (`pinSkolem_exhibits`).
- conjunct i: single remaining `sorry` (`pinSkolem_matrix_true`).
- assembly: `⟨pinSkolem …, pinSkolem_matrix_true, pinSkolem_exhibits …⟩`;
  downstream (`DQBFTrue_forceDelDeps_of_setBridge` → … → `checkAction_sound`
  → `processProof_sound'`) is green.
- iterate with `lake build DqratLean.DeletionExhibition` (sub-second).
