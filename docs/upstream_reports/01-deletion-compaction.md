# Upstream `dqrat-check` `d60d50e`: deletion compaction can reject a valid proof and later crash

## Symptom

On a family of valid deletion-heavy proofs, upstream `d60d50e` first rejects a
valid `DEL` step with `lemma does not exist (DEL)` and then, at a larger size,
crashes during constraint-database compaction. This is the same divergence
summarized in [docs/benchmarks.md](../benchmarks.md).

The failure pattern is stable on the generated family from
`scripts/bench_cpp.sh`:

- `del5k` (`depth = 2`, `deletes = 5000`): spurious `FAILED`
- `del20k` (`depth = 2`, `deletes = 20000`): core dump
- `del1k` passes only because the garbage-collection trigger is strict
  `> 1000`, so exactly `1000` deletions do not compact

## Minimal repro

The generator below is the same one embedded in `scripts/bench_cpp.sh`, reduced
to just the two failing instances:

```bash
python3 - <<'PY'
def clause(*lits):
    return " ".join(map(str, lits)) + " 0\n"

def gen(path, depth, deletes):
    left = list(range(2, depth + 2))
    right = list(range(depth + 2, 2 * depth + 2))
    dup = (1, right[0])
    cl = [clause(-1, left[0])]
    cl += [clause(-left[i], left[i + 1]) for i in range(depth - 1)]
    cl.append(clause(-left[-1], -1))
    cl += [clause(*dup) for _ in range(deletes + 1)]
    cl += [clause(-right[i], right[i + 1]) for i in range(depth - 1)]
    cl.append(clause(-right[-1], 1))
    max_var = right[-1]
    formula = (
        f"p cnf {max_var} {len(cl)}\n"
        + "e "
        + " ".join(map(str, range(1, max_var + 1)))
        + " 0\n"
        + "".join(cl)
    )
    proof = "".join(f"d {dup[0]} {dup[1]} 0\n" for _ in range(deletes)) + clause(-1)
    open(f"{path}.dqdimacs", "w").write(formula)
    open(f"{path}.dqrat", "w").write(proof)

gen("/tmp/del5k", 2, 5000)
gen("/tmp/del20k", 2, 20000)
PY

/path/to/dqrat-check /tmp/del5k.dqdimacs /tmp/del5k.dqrat
/path/to/dqrat-check /tmp/del20k.dqdimacs /tmp/del20k.dqrat
```

Observed on `d60d50e`:

- `/tmp/del5k.*`: valid proof rejected with `lemma does not exist (DEL)`
- `/tmp/del20k.*`: crash during or after compaction

## Root cause

The bug is in the relocation path for constraint-database compaction.

Each clause is referenced from multiple vectors:

- the occurrence list of every literal in the clause
- the global constraint list
- the propagator-side watch structures

The current relocation logic copies a clause on first encounter and leaves a
forwarding header in the old arena cell. Later encounters are supposed to check
whether the clause was already relocated before inspecting the old cell.

Instead, `relocVector` reads `isMarked()` from the old arena cell while
relocating multiply referenced `CRef`s. After the first relocation, that old
cell no longer holds clause flags; it holds a forwarding header. The read is
therefore interpreted as clause metadata when it is no longer clause metadata.

That misread produces both observed symptoms:

- one direction drops a live clause from an occurrence list, so a later
  `retrieveSortedConstraint` scan cannot find the lemma and a valid `DEL` step
  is rejected
- the other direction copies a deleted clause into a new arena that was sized
  without it, so the target arena is overrun and the process crashes

So the `del5k` rejection and the `del20k` crash are two manifestations of the
same relocation bug.

## Fix pointer

The robust fix is to stop patching old references in place during compaction.

The replacement `relocAll` strategy in commit `950c007` rebuilds the
`constraint_list` and all occurrence lists from the live clauses, then resets
the propagator state and re-installs the watches. That is slower per compaction
than trying to patch every reference, but it removes the stale-forwarding-cell
hazard entirely.

## Notes

This report is about executable behavior only. The generated proofs are valid,
and the same instances are accepted by the fixed compaction rewrite and by the
verified Lean checker described in [docs/benchmarks.md](../benchmarks.md).
