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
- The basic checker path is fully proved:
  - `checkActionBasic_sound`
  - `checkActionsBasic_sound`
  - `processProofBasic_sound`

What is not finished yet:
- Full single-action wrapper soundness for the complete checker:
  - `checkAction_sound`

The real proof blocker underneath that remaining theorem is:
- the negative-`e` / dependency-deletion proof path

The DQRATE seam was substantive, not just inconvenient:
`DqratLean/Counterexamples.lean` contains an occurrence-hole witness showing that
if live blocker clauses are missing from occurrence lists, `checkDQRATE` can
accept an unsound addition. The branch now carries the stronger
live-occurrence invariant where the RAT proof actually needs it, and
`checkDQRATE_sound_spec` is proved on that executable-aligned route.

As of the current green branch state, the only remaining explicit theorem-body
`sorry` in `DqratLean/Soundness.lean` is `checkAction_sound`, specifically its
negative-`e` `ModifyExistential` branch.

The current negative-`e` frontier is subtler than "prove `notDependsOn`
eliminates both-bad patterns for one fixed old witness." The repo now contains
`deleteBridge...` counterexamples showing that `notDependsOn` can succeed while
a concrete old witness, even on the two relevant universal cases, still
requires coordinated changes beyond the deleted existential itself. So the
remaining proof needs a richer semantic transport argument, not just a
one-variable patch.

## Repository Layout

Top-level files:
- `Main.lean`: CLI entrypoint for `dqrat-lean`
- `DqratLean.lean`: library root
- `MonadTutor.lean`: notes/manual for the `mvcgen` proof style used in parts of the development
- `sound_todo.md`: current proof roadmap / notes
- `CLAUDE.md`: local workflow notes from prior work on this mirror

Core Lean modules:
- `DqratLean/Types.lean`: basic types such as `Var`, `Literal`, `CRef`
- `DqratLean/Formula.lean`: DQBF prefix / dependency-set representation
- `DqratLean/ClauseStore.lean`: clause database and clause operations
- `DqratLean/CheckState.lean`: checker state and executable state-transforming operations
- `DqratLean/Checker.lean`: executable checker implementation
- `DqratLean/Parser.lean`: DQDIMACS / proof parsing
- `DqratLean/Semantics.lean`: DQBF semantics via Skolem functions
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
- `addClause_sound_spec`
- `checkActionBasic_sound`
- `checkActionsBasic_sound`
- `processProofBasic_sound`

Current full-checker frontier:
- `checkAction_sound`

## Notes For Reviewers

- This GitHub mirror is not the canonical upstream repository.
- The file `DqratLean/Soundness.lean` is large because most of the proof work still lives in one place.
- Some comments in `Soundness.lean` mentioning older `sorry` status are stale; the authoritative check is the actual theorem bodies and a fresh `lake build DqratLean.Soundness`.
