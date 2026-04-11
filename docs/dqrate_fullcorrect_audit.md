# DQRATE FullCorrect Audit

Date: 2026-04-11

## Claim

The public full-checker soundness frontier must carry live-occurrence completeness.
Bare `CheckState.Correct` is too weak for the executable existential-RAT branch.

## Auditable witness

See [DqratLean/Counterexamples.lean](../DqratLean/Counterexamples.lean).

The witness is the `occurrenceHole*` family:

- `occurrenceHoleFormula`
- `occurrenceHoleStore`
- `occurrenceHoleState`
- `occurrenceHoleStore_not_liveOccurrencesComplete`
- `occurrenceHoleAccepted_true`
- `occurrenceHole_matrix_true`
- `occurrenceHole_addedClause_false`
- `occurrenceHole_addedMatrix_false`

What it does:

1. The live matrix contains one active blocker clause `¬x`.
2. The occurrence list for `¬x` is intentionally empty.
3. `checkDQRATE #[x] occurrenceHoleState` returns success.
4. Under the witness assignment `x := false`, the old matrix is true.
5. After adding `x`, the matrix is false.

So if a theorem only assumes the action-boundary fields of `Correct`, without
also requiring occurrence completeness, the executable RAT success result is not
sound in general.

## Consequence for the proof frontier

The following full-checker path must be stated on a stronger invariant:

- DQRATE clause-check theorem
- RAT-clause theorem
- single-action theorem
- action-list theorem
- parser-to-proof top theorem

The intended invariant is `CheckState.FullCorrect` or an equivalent package that
includes `ClauseStore.LiveOccurrencesComplete`.

## Second witness: accepted execution need not satisfy the legacy bridge

The repo now also contains a separate `dqrateBridge*` witness in
[DqratLean/Counterexamples.lean](../DqratLean/Counterexamples.lean):

- `dqrateBridgeAccepted_true`
- `dqrateBridgeMatrixTrue`
- `dqrateBridgeResolvent_eq`
- `dqrateBridgeResolventFalse`
- `dqrateBridge_not_exec_condition`

What it shows:

1. The executable `checkDQRATE` path accepts a concrete clause addition.
2. The original matrix is true under a concrete witness assignment.
3. One blocker resolvent from the legacy `DQRATE_exec_Condition` route is false
   under that same witness.
4. Therefore accepted execution does not imply the old
   `DQRATE_exec_Condition`.

This does not mean the checker is unsound. It means the older proof route was
too strong and should no longer be treated as the target bridge for finishing
the DQRATE theorem.

## Consequence for the remaining proof strategy

The honest route was:

1. keep `FullCorrect` on the public theorem surface,
2. use the existing shadow-restoration infrastructure only as a local tool,
3. finish the successful pivot branch by a direct patched-Skolem /
   patched-clause argument,
4. avoid forcing accepted execution through the legacy per-blocker resolvent
   consequence path.

That route is now the one used by the closed `checkDQRATE_sound_spec`.

## Build check

The witness compiles with:

```bash
lake build DqratLean.Counterexamples
```
