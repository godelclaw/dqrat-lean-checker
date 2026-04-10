# Upstream Bugfix Notes

This note records Lean-side checker issues found during executable-alignment work on this mirror.
It is intentionally factual and narrow in scope.

## Scope

- This mirror is not the canonical upstream repository.
- The items below concern the Lean executable checker in this repository.
- The repros below do **not** by themselves show a proof of top-level DQRAT unsoundness in the sense of accepting a satisfiable instance as `VERIFIED`.
- What they do show is that older checker states / omitted checks could produce weaker behavior (`UNKNOWN` instead of `FAILED`) on focused cases.

## Recorded Repros

See:

- `repros/stale_delete_state.dqdimacs`
- `repros/stale_delete_state.dqrat`
- `repros/stale_delete_neg_state.dqdimacs`
- `repros/stale_delete_neg_state.dqrat`
- `repros/stale_state_bug_report.md`
- `DqratLean/Counterexamples.lean`

Observed behavior recorded in `repros/stale_state_bug_report.md`:

- fixed Lean checker: `s FAILED`
- older Lean checker: `s UNKNOWN`
- current C++ checker used as baseline during this work: `s UNKNOWN`

## Lean-side Fixes

### 1. Deleted blocker clauses must be skipped during RAT/DQRATU scans

Lean code locations:

- `DqratLean/Checker.lean`
- `DqratLean/CheckState.lean`

The executable now explicitly ignores `clause.deleted` entries when scanning blocker occurrences.
This keeps tombstoned clauses from being treated as live blockers.

### 2. Dependency cache trust was too optimistic

Lean code location:

- `DqratLean/CheckState.lean`

`notDependsOn` now recomputes dependency information before consulting the cached relation.
This removes an unnecessary proof burden around stale cache state and aligns the executable more closely with the intended semantics.

## Related Commits On This Mirror

- `ae14a52` Add stale delete-state bug repros
- `06b83d1` Add formal stale-state counterexample
- `e93cd71` Checkpoint basic soundness progress and reset weakening-step state
- `081af8f` Clarify README status and file map
- `5b8f235` Restore buildable parser and checker alignment state

## Recommended Upstream Communication Style

The most responsible wording is:

1. State the exact repro files.
2. State the exact observed outputs before/after.
3. Describe each issue as a missing check / stale-state handling bug unless there is a real `VERIFIED`-on-satisfiable counterexample.
4. Keep theorem-boundary discussions separate from executable bug reports.

That keeps the report precise, polite, and easy to audit.
