# Stale Delete-State Repros

These two proofs exercise the stale propagation-state bug after clause deletion.

## Repro 1: positive unit deleted, then re-added

Files:
- `repros/stale_delete_state.dqdimacs`
- `repros/stale_delete_state.dqrat`

Formula after deletion: `(-1 v 2)`.

The later proof step `1 0` is invalid, since `1 = false, 2 = false` satisfies the remaining formula.

Observed behavior:
- fixed Lean checker: `s FAILED`
- old Lean checker: `s UNKNOWN`
- C checker: `s UNKNOWN`

## Repro 2: negative unit deleted, then re-added

Files:
- `repros/stale_delete_neg_state.dqdimacs`
- `repros/stale_delete_neg_state.dqrat`

Formula after deletion: `(1 v 2)`.

The later proof step `-1 0` is invalid, since `1 = true, 2 = false` satisfies the remaining formula.

Observed behavior:
- fixed Lean checker: `s FAILED`
- old Lean checker: `s UNKNOWN`
- C checker: `s UNKNOWN`

In both cases, `UNKNOWN` is already wrong: the bad lemma should be rejected at the step where it is checked.
