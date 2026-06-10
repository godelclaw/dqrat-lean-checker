# Soundness status: COMPLETE

As of 2026-06-10, the executable-aligned soundness proof is **finished**.

- `grep -rn sorry DqratLean/` → no theorem-body `sorry` anywhere.
- Axiom audit (`#print axioms`): `processProof_sound'`, `checkAction_sound`,
  and `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet` depend only on
  `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`.
- `scripts/build_and_test.sh` green: full build, `DqratLean.Soundness`,
  parser regressions, executable smoke test.

## What was proved (top-level)

`processProof_sound'`: if the executable checker verifies a DQRAT proof for
a parsed DQDIMACS formula, the formula's truth is preserved through every
proof action — parser correctness, DEL/addClause/UR, RUP, DQRATE (on the
`FullCorrect` occurrence-complete surface), and the dependency-deletion
(negative-`e`) rule family.

The final piece was full exhibition of the reflexive resolution-path
dependency scheme (`DqratLean/DeletionExhibition.lean`), transcribed from
Beyersdorff, Blinkhorn, Chew, Schmidt, Suda, JAR 2019 (archived in
`docs/papers/`): the two-stage reformed-model construction (Defs. 12-13),
its evaluation rules, Lemma 2 (`reformLeft_matrix_true`,
`reformRight_matrix_true`), and Lemma 4 (`reformSkolem_exhibits_mem`).
Lemma 3 is automatic in Skolem form; Lemma 5 is unnecessary (one universal
per checker step). See `docs/deletion_exhibition_proof.md` for the
paper-to-Lean map.

## History

- The fiber-counting witness-descent attempt is preserved at checkpoint
  `64c375e` and was removed in `f6c72b7`: its restart obligation over
  abstract progress candidates admits adversarial instances and was as hard
  as the full theorem. The faithful paper construction replaced it.
- An intermediate unconditional pinning construction (`pinSkolem`) was also
  superseded: the paper's Lemma 2 proof requires the conditional refusal.
- The parallel dynamic-continuation clone (`dqrat-lean-checker-watched`)
  is archived; see `docs/negative_e_strategy_split.md`.

## Possible follow-ups (not blockers)

- Lint pass over the ~1.7k `simp`-style warnings.
- Upstream the module split and proof to the canonical repository.
- Performance work (watched literals) can now resume against a fully
  verified simple checker.
