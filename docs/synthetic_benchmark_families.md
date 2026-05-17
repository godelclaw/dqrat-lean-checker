# Synthetic Benchmark Families

Date: 2026-04-17

This repo now includes a deterministic local generator for synthetic
`*.dqdimacs + *.dqrat` benchmark pairs:

- `scripts/generate_synthetic_benchmarks.py`

The point is not to replace real competition corpora. The point is to have a
large local proof corpus that we can generate immediately, validate against both
checkers, and use for runtime regression testing while the final semantic proof
is still being finished.

## Families

### `up_chain`

- propositional only
- formula is already unit-unsatisfiable during read-in
- proof file is empty
- good for parser and propagation throughput

### `rup_twochain`

- propositional only
- formula is unsatisfiable but not trivially by initial unit propagation
- proof is a single RUP unit clause
- good for exercising clause-addition proof checking

### `delete_rup`

- same unsat core as `rup_twochain`
- proof begins with many valid clause deletions, then ends with the same RUP unit
- good for stressing proof-stream parsing, clause lookup, and deletion handling
- profile sizes are capped to a cross-checked safe range so both the Lean checker
  and the current C++ reference accept the generated cases

## Output Location

The script is intended to generate data outside the repo, for example:

```bash
python3 scripts/generate_synthetic_benchmarks.py \
  --out /home/zarclaw/benchmarks/generated-dqrat-synthetic \
  --profile full
```

The generated directory contains:

- `README.md`
- `manifest.tsv`
- family subdirectories with benchmark pairs

To benchmark a generated corpus against two Lean binaries:

```bash
ITERS=25 ./scripts/benchmark_corpus.sh
```

or point it at a different corpus root with `BENCH_ROOT=/path/to/corpus`.

## Why This Helps

- We do not need external solver tooling to get started.
- The generated cases are deterministic and easy to reproduce.
- They give us a scalable local corpus for benchmarking the Lean checker against
  the C++ checker before we have a broader native DQBF proof-pair pipeline.
