# Stale Delete-State Repros

These two proofs exhibit a stale-state sensitivity after clause deletion.
They do not by themselves prove a top-level DQRAT unsoundness bug.

## Repro 1: positive unit deleted, then re-added

Files:
- `repros/stale_delete_state.dqdimacs`
- `repros/stale_delete_state.dqrat`

Formula after deletion: `(-1 v 2)`.

Plain semantic witness:
`1 = false, 2 = false` satisfies the remaining formula while falsifying the
re-added unit clause `1`.

Observed behavior:
- fixed Lean checker: `s FAILED`
- old Lean checker: `s UNKNOWN`
- C checker: `s UNKNOWN`

## Repro 2: negative unit deleted, then re-added

Files:
- `repros/stale_delete_neg_state.dqdimacs`
- `repros/stale_delete_neg_state.dqrat`

Formula after deletion: `(1 v 2)`.

Plain semantic witness:
`1 = true, 2 = false` satisfies the remaining formula while falsifying the
re-added unit clause `-1`.

Observed behavior:
- fixed Lean checker: `s FAILED`
- old Lean checker: `s UNKNOWN`
- C checker: `s UNKNOWN`

What is established:
- the post-delete formula does not propositionally force the re-added unit
  clause
- the fixed Lean checker returns `FAILED`
- the old Lean checker and the C checker return `UNKNOWN`

What is not yet established:
- a formal proof that the re-added clause fails the full DQRAT/DQRATU criterion
- a formal top-level unsoundness theorem of the form `VERIFIED` on a satisfiable
  input
