# Benchmarks and behavioral parity vs the C++ reference checker

Date: 2026-06-11. Machine: HP EliteBook x360 1030 G4 (i7, 16 GB).
Binaries: `dqrat-check` upstream `d60d50e` (github.com/peitl/dqrat-check,
latest main); `dqrat-check` bench fork `950c007`
(github.com/godelclaw/dqrat-check, branch codex/benchmark-fixes — adds a
deletion-compaction fix); Lean `dqrat-lean` at this repo's HEAD.
Reproduce with `scripts/crosscheck_cpp.sh` and `scripts/bench_cpp.sh`.

## Verdict parity (tests + repros)

All 9 upstream test instances match exactly (including the new
`test_07_del_unit` FAILED, `test_08_del_nonunit` UNKNOWN,
`test_09_tautology_UR` UNKNOWN added with the Mixed-EUR merge).
All repro instances match except one, where the difference favors the
verified checker:

| instance | C++ d60d50e | Lean | note |
|---|---|---|---|
| repro:proof_missing_zero | **HANG** (infinite read loop) | FAILED (parse error) | upstream robustness bug |

## Deletion-heavy benchmark (generated; valid VERIFIED proofs)

Generator: duplicate-clause deletion chains ending in a RUP conflict
(adapted from the bench fork's `generate_duplicate_delete_threshold.py`);
`depth × deletes` as listed. Median of 3 runs.

| instance | clauses | C++ d60d50e | C++ bench-fix | Lean (verified) |
|---|---|---|---|---|
| del1k (2×1000) | 1,006 | 0.00s VERIFIED | 0.00s VERIFIED | 0.00s VERIFIED |
| del5k (2×5000) | 5,006 | **FAILED (bug)** | 0.00s VERIFIED | 0.00s VERIFIED |
| del20k (2×20000) | 20,006 | **core dump** | 0.02s VERIFIED | 3.0s VERIFIED |
| del50k (2×50000) | 50,006 | — | 0.08s VERIFIED | 21.4s VERIFIED |
| chain5k (5000×10) | 10,012 | 0.00s VERIFIED | 0.00s VERIFIED | 0.00s VERIFIED |

Findings:

1. **Upstream d60d50e has a deletion-compaction defect**: at ~5k deletions
   its constraint-DB garbage collection loses clauses ("lemma does not
   exist (DEL)" on a valid proof → spurious FAILED); at 20k deletions it
   crashes (core dump). The bench fork's `relocAll` rewrite (950c007)
   fixes both. The Lean checker — whose VERIFIED verdicts are
   machine-checked — agrees with the fixed behavior at every size.
   Both this and the parse hang above should be reported upstream.
2. **Performance**: the verified checker is the simple (non-watched)
   implementation: ~3s at 20k clauses and ~21s at 50k vs ~0.1s for C++.
   Growth is roughly quadratic in deletions (linear clause lookups and a
   full propagation reset per deletion). Entirely usable for the current
   corpus; a verified watched-literals port is the designated performance
   work (an unverified port exists on branch `codex/watched-literals-port`).
3. Deep unit-propagation chains (chain5k) are no problem for either
   checker.

## Honest scope

Soundness (`s VERIFIED` ⇒ formula false) is machine-checked for the Lean
checker only. Parity testing is evidence about *completeness* and format
conformance, not soundness. The single conformance-relevant divergence
found during this audit (parse-time dropping of tautological clauses,
upstream Mixed-EUR item 3) was fixed in this repo with proofs re-checked;
see `git log` and `docs/coverage_matrix.md`.
