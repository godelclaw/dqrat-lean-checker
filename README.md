# dqrat-lean-checker

Lean formalization and executable checker for DQRAT proofs over DQBF.

This GitHub repository is a working mirror of Mirek Olsak's original project:
- Upstream: `https://git.olsak.net/mirek/dqrat-lean-checker`

The original project and baseline code are by Mirek Olsak. This mirror carries ongoing executable-alignment, parser, and soundness-proof work.

## Current State

What is already done on this branch:
- The Lean project builds.
- The executable checker builds and runs.
- Parser fixes and parser regressions are in place.
- `parseDQDIMACS_correct` is proved.
- Low-level soundness infrastructure is largely proved, including propagation, `addClause`, and UR.
- The full non-watched checker path used by `Main.lean` is theorem-backed:
  - `parseDQDIMACS_none_sound`
  - `checkAction_sound`
  - `processProof_sound'`

Nothing is unfinished: the soundness development is **sorry-free**.
The audited top-level theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The DQRATE seam was substantive, not just inconvenient:
`DqratLean/Counterexamples.lean` contains an occurrence-hole witness showing that
if live blocker clauses are missing from occurrence lists, `checkDQRATE` can
accept an unsound addition. The branch now carries the stronger
live-occurrence invariant where the RAT proof actually needs it, and
`checkDQRATE_sound_spec` is proved on that executable-aligned route.

The dependency-deletion rule is justified by full exhibition of the
reflexive resolution-path dependency scheme, formalized in
`DqratLean/DeletionExhibition.lean` by transcribing Beyersdorff, Blinkhorn,
Chew, Schmidt, Suda (JAR 2019, archived in `docs/papers/`); see
`docs/deletion_exhibition_proof.md` for the paper-to-Lean map.

Counterexample diagnostics using `native_decide` are kept outside the root
import path. `DqratLean.Basic` does not import `DqratLean.Counterexamples`, and
`scripts/build_and_test.sh` builds that module separately as a diagnostics step.

## Watched-Literals Status

This repo carries the watched-literals runtime modules (`WatchedState`,
`WatchedChecker`, `WatchedParser`, plus cache-invariant and refinement
lemmas up to `RuntimeRefines` in `WatchedRuntimeSoundness`) as an
experimental layer, and builds them in CI (`scripts/build_and_test.sh`)
together with an experimental executable `dqrat-lean-watched`
(`WatchedMain.lean`).

Status, honestly stated:
- The watched runtime agrees with the certified checker on all 9 shared
  test instances and on the generated benchmarks.
- It is **not** on the certified path: there is no end-to-end watched
  `processProof` refinement theorem yet (the per-operation cache-invariant
  lemmas exist and are sorry-free; the propagation-loop refinement is the
  open part). The theorem-backed CLI remains `dqrat-lean` (`Main.lean`).
- The watched add/delete actions now route their proof-relevant store/cache
  edits through shared proof-facing transitions from `WatchedState.lean`
  (store addition, live-occurrence indexing, binary-cache updates, clause
  deletion), reducing the remaining code/proof mismatch to runtime-only
  watchlist updates.
- Phase 1 refinement work now also includes explicit proof-facing state
  transitions for decision-level start, backtrack, enqueue, and propagation
  reset, plus a first binary-step lemma
  (`WatchedPropagationRefinement.applyBinaryImpEntryState_enqueue_refines`)
  showing that one live binary cache entry's enqueue branch refines to the
  corresponding abstract queue update.
- Current measured performance does not yet beat the simple checker on
  deletion-heavy workloads (cache maintenance dominates); see
  `docs/benchmarks.md`. Optimization and the end-to-end refinement
  theorem are the designated next work items.
- The repo enforces watched/base functionality parity on the shared tests
  and repros via `scripts/crosscheck_watched.sh`; use
  `scripts/bench_watched.sh [ratio]` to track watched/base performance
  ratios on representative generated instances without changing the
  certified default path.

## Repository Layout

Top-level files:
- `Main.lean`: CLI entrypoint for `dqrat-lean`
- `DqratLean.lean`: library root
- `MonadTutor.lean`: notes/manual for the `mvcgen` proof style used in parts of the development
- `sound_todo.md`: proof status (complete) and history
- `CLAUDE.md`: local workflow notes from prior work on this mirror

Core Lean modules:
- `DqratLean/Types.lean`: basic types such as `Var`, `Literal`, `CRef`
- `DqratLean/Formula.lean`: DQBF prefix / dependency-set representation
- `DqratLean/ClauseStore.lean`: clause database and clause operations
- `DqratLean/CheckState.lean`: checker state and executable state-transforming operations
- `DqratLean/Checker.lean`: executable checker implementation
- `DqratLean/Parser.lean`: DQDIMACS / proof parsing
- `DqratLean/Semantics.lean`: DQBF semantics via Skolem functions
- `DqratLean/SoundnessCore.lean`: checker-state invariant definitions (`Sound`/`Correct`/`FullCorrect`)
- `DqratLean/DeletionSemantics.lean`: dependency-deletion semantic layer (forceDelDeps, independence bridges, flipUniv)
- `DqratLean/DeletionPaths.lean`: resolution paths, `getReachable` BFS spec/completeness, `NoDeleteCrossPaths`
- `DqratLean/DeletionExhibition.lean`: completed dependency-deletion exhibition theorem
- `DqratLean/Soundness.lean`: main proof development
- `DqratLean/Counterexamples.lean`: counterexample / bug-exploration material
- `DqratLean/Basic.lean`: re-export module

Support directories:
- `docs/`: short factual notes for reviewers, including upstream-facing bugfix notes
- `tests/`: main example formulas/proofs used for executable checking
- `repros/`: parser and checker repro cases, including stale-state bug repro material
- `scripts/run_parser_regressions.sh`: parser regression runner

## Build

Build the whole project:

```bash
lake build
```

Build the main proof file directly:

```bash
lake build DqratLean.Soundness
```

Run the executable checker:

```bash
lake exe dqrat-lean <formula.dqdimacs> <proof.dqrat>
```

## Tests And Repros

Run parser regressions:

```bash
./scripts/run_parser_regressions.sh
```

Run the main build/test bundle used for handoff packaging:

```bash
./scripts/build_and_test.sh
```

Main checker examples live in `tests/`.

Focused repros live in `repros/`, including:
- parser edge cases
- header / max-var / missing-terminator cases
- stale-state checker repros and report material

Reviewer-facing notes live in `docs/`, including:
- `docs/dqrate_fullcorrect_audit.md`
- `docs/upstream_bugfix_notes.md`

## Proof Map

If you want the shortest orientation path:

1. `DqratLean/Checker.lean`
   This is the executable program being verified.
2. `DqratLean/Semantics.lean`
   This defines `DQBFTrue` / `DQBFFalse`.
3. `DqratLean/Soundness.lean`
   This contains the proof development.

Useful milestones inside `DqratLean/Soundness.lean`:
- `parseDQDIMACS_correct`
- `parseDQDIMACS_none_sound`
- `addClause_sound_spec`
- `checkAction_sound`
- `processProof_sound'`

Current full-checker frontier: none — `checkAction_sound` and
`processProof_sound'` are fully proved.

## Notes For Reviewers

- This GitHub mirror is not the canonical upstream repository.
- The file `DqratLean/Soundness.lean` is large because most of the proof work still lives in one place.
- The authoritative proof-status check is a proof-hole grep plus a fresh `lake build`.
- The current CLI is the non-watched checker. The watched-literals modules are present as experimental runtime work, not the certified default path in this repo.
