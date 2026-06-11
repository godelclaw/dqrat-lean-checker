# Coverage matrix: DQRAT+D^∀pure format → Lean implementation → theorem

Date: 2026-06-11. C++ reference: `dqrat-check` at upstream `d60d50e`
(latest main; the format's SAT 2026 submission implementation).
Lean: this repo at HEAD. Evidence columns refer to
`scripts/crosscheck_cpp.sh` (parity) and `scripts/run_parser_regressions.sh`.

## Proof-line rules (C++ `DQRATRule` enum, dqrat_check.hh)

| C++ rule | proof syntax | Lean parser action (Parser.lean) | Lean checker (Checker.lean) | covered by theorem | parity evidence |
|---|---|---|---|---|---|
| DEL | `d <lits> 0` | `DeleteClause` | `checkDeleteClause` (LOCATE via `findSortedClause`, delete + propagation reset) | `checkAction_sound` (DEL case) | test_07, test_08, del1k–del50k |
| UADD | `a <vars> 0` | `AddUniversal` | `checkAddUniversal` | `checkAction_sound` | exercised in test_05/06 corpora |
| RUP | `<lits> 0` | `RatClause` | `checkRatClause` → RUP trial (`negateAndPropagate`) | `checkAction_sound` (RatClause case) | test_02, test_04, all benches |
| DQRATE | `<lits> 0` (RUP fails) | `RatClause` | `checkDQRATE` (blocker scan over occurrence lists, outer-clause trials) | `checkDQRATE_sound_spec` on the `FullCorrect` occurrence-complete surface, via `checkAction_sound` | test_01 (reject), test_05 |
| UR | `u <lits> 0` (pivot reducible) | `UniversalReduction` | `checkUniversalReductionLocated` (reducible branch); tautological pivot is **not** reducible (Mixed-EUR) | `checkAction_sound` (UR case) | test_05/06, test_09 |
| DQRATU | `u <lits> 0` (pivot not reducible) | `UniversalReduction` | `checkDQRATU` (RUP-without-pivot, then RAT over `getOcc ¬pivot` with `checkPathC` D^∀pure connectivity **and the candidate-clause self-exemption** `crefOfLits`) | `checkAction_sound` (UR case) | test_09 (UNKNOWN, matches d60d50e) |
| DPURE | `e <exi> <deps> 0` (negatives = removal) | `ModifyExistential` | `checkModifyExistential` (additions + `computeDeps`/`notDependsOn`-gated removals) | `checkAction_sound`; removals justified by `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet` (full exhibition of the reflexive resolution-path scheme, JAR 2019 — see `DeletionExhibition.lean` and `docs/papers/`) | exercised by the dependency-removal corpus; semantic theorem machine-checked |
| LOCATE (failure tag) | — | — | `findSortedClause` misses → FAILED | n/a (rejection needs no soundness) | repro corpus |

All five `DQRatAction` constructors are dispatched by `checkAction`
(Checker.lean) and the dispatch is covered, sorry-free, by
`checkAction_sound` → `processProof_sound'`. Rejections (`Failed`,
`Unknown`) carry no semantic claim and need none.

## Formula (DQDIMACS prefix) syntax

| line | Lean | covered by |
|---|---|---|
| `p cnf <maxVar> <n>` header | `parseDQDIMACSTokens` (maxVar enforced via `ensureWithinMaxVar`) | `parseDQDIMACS_correct` / `_full_correct` |
| `a <vars> 0` | `readPrefixM` | parser theorems above |
| `e <var> <deps> 0` | `readPrefixM` | parser theorems above |
| `d <exi> <deps> 0` dependency line | `readPrefixM` | parser theorems above |
| matrix clauses (tautologies **kept**, matching upstream Mixed-EUR item 3) | `readMatrixM` | `readMatrixM_full_run` / `_sound_run`; parse-time UP refutation covered by `parseDQDIMACS_none_sound` |

## Known behavioral deltas vs C++ d60d50e

1. `repro:proof_missing_zero`: C++ hangs (unbounded read loop); Lean
   reports a parse error. Upstream robustness bug; report planned.
2. Deletion compaction: C++ d60d50e loses clauses / dumps core at
   5k/20k deletions (see `docs/benchmarks.md`); the godelclaw bench fork
   fix (950c007) and the Lean checker agree on VERIFIED. Upstream report
   planned.
3. No rule-semantics divergence is known: 9/9 upstream tests match,
   including the Mixed-EUR additions.

## Papers covered

- **Format & checker**: `dqrat-check` README (DQRAT+D^∀pure, SAT 2026
  submission). Every proof-line command and prefix syntax it defines is
  implemented and in the table above.
- **D^∀pure dependency deletion**: Wimmer, Wimmer, Scholl, Becker,
  "Dependency Schemes for DQBF" (SAT 2016) and Beyersdorff, Blinkhorn,
  Chew, Schmidt, Suda (JAR 2019) — the full-exhibition theorem is
  transcribed and machine-checked in `DqratLean/DeletionExhibition.lean`
  with a Definition/Lemma alignment table; papers archived in
  `docs/papers/`.

## Upstream relationship

- C++ `dqrat-check`: local clone fast-forwarded to upstream `d60d50e`
  (2026-06-11); bench fork carries the compaction fix.
- Lean canonical upstream (git.olsak.net/mirek/dqrat-lean-checker,
  `main` = `2e290e6`): exactly our merge-base — this branch is 48 commits
  ahead, 0 behind. Upstreaming is the next conversation with the
  maintainers.
