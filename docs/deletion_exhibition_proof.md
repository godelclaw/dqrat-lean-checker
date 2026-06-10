# Deletion Exhibition: paper-to-Lean proof map

Primary source (archived in `docs/papers/`): Beyersdorff, Blinkhorn, Chew,
Schmidt, Suda, "Reinterpreting Dependency Schemes: Soundness Meets
Incompleteness in DQBF", JAR 63 (2019) 597-623, § 6 (reformed paths).
The alignment table lives in the header of `DqratLean/DeletionExhibition.lean`.

## Status

- Defs. 12-13 (reformed path / left-right reform / reformed model):
  IMPLEMENTED as `reformLeft`, `reformRight`, `reformSkolem`, with the
  refusal condition stated as a `DeletePurePath` Prop and decided
  classically — so only the (proved) completeness direction of the
  `getReachable` BFS spec is needed, never its soundness direction.
- Evaluation rules (the computational content of Def. 12): PROVED
  (`varValue_reform{Left,Right}_{of_not_contains, of_on_true/false,
  refused, reformed}`).
- Lemma 4 (exhibition): PROVED (`reformSkolem_exhibits_mem` via
  `reformSkolem_flip_eq_of_on_false`), following the paper's case analysis:
  agreement case, reform-fired case, and the both-refused case killed by
  `noDeleteCrossPathsSet_not_deletePurePath_pair_of_fullCorrect`.
- Lemma 3 (reform is a model/assignment tree): automatic in Skolem form.
- Lemma 5 (reforms preserve earlier exhibitions): NOT NEEDED — the checker
  deletes one universal per step and re-runs the theorem on the updated
  formula.
- Lemma 2 (reformed paths satisfy every clause): PROVED
  (`reformLeft_matrix_true` / `reformRight_matrix_true`), following the
  paper's argument exactly: disagreement-literal extraction
  (`reformLeft_disagree_inv`), exclusion of `on_`-literals (value side +
  one-clause path), per-literal transfer to the flipped assignment with the
  path-extension step for dependent existentials, and contradiction with
  the model. The whole development is now sorry-free.

## Lemma 2: the remaining Lean work (left stage; right is the mirror)

Fix σ with `σ on_ = false` and suppose the reformed matrix is false at σ.

1. `matrixValue_false_implies_exists_false_clause` extracts a false clause C.
2. From `hall σ` (C true under sk) extract a literal `lx ∈ C` true under
   `(σ, sk)`, false under `(σ, reformLeft)`. Its variable x must be
   existential, `on_`-dependent, and *reformed* (all other classes keep
   their values — the evaluation rules); unfolding gives
   `lx = mkLit x (!v)` with `v := varValue (flip σ) sk x` and the refusal
   failure `(1): ¬ DeletePurePath … (mkLit on_ true) lx`.
3. `mkLit on_ false ∉ C` (it would be true at σ); `mkLit on_ true ∈ C`
   would give a one-clause `DeletePurePath.first` to `lx`, contradicting (1).
4. Every literal of C is then shown false under `(flipUniv on_ σ, sk)`:
   universals and non-dependent existentials are flip-invariant; `lx`
   itself has value `v` there (false); for a dependent `ly` (y ≠ x), if it
   were true there, the y-reform at σ would have fired (its refusal path
   would extend through C to `lx` via a `DeletePurePath.step` with
   connector `¬ly` — contradiction with (1)), making `ly` true under the
   reform at σ — contradicting C false.
5. `matrixValue_false_of_false_clause` contradicts `hall (flipUniv on_ σ)`. ∎

Useful existing pieces: `litValue_false_true_flip_universal_eq_on`,
`litValue_false_true_flip_existential_contains` (DeletionSemantics);
`deletePurePath_step_from_opposite_target_tail`,
`noStartNeg_of_false_other_literals`,
`litValue_start_neg_true_of_start_eq_not_sigma` (DeletionPaths);
clause-level true/false literal extraction in DeletionSemantics
(`clauseValue_*` lemmas).

## Historical note

An earlier unconditional per-variable pinning construction (`pinSkolem`)
proved the exhibition conjunct trivially but had a likely-unprovable truth
conjunct: the paper's Lemma 2 proof *requires* the refusal condition.
Superseded by the faithful conditional reform; see git history.
