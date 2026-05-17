# Watched Runtime Benchmarks

## Local benchmark run

- Date: `2026-04-17T12:34:04+02:00`
- Host CPU: `Intel(R) Core(TM) i5-8365U CPU @ 1.60GHz`
- Host arch: `x86_64`
- Baseline binary: `/home/zarclaw/repos/dqrat-lean-checker-work/.lake/build/bin/dqrat-lean`
- Candidate binary: `/home/zarclaw/repos/dqrat-lean-checker-watched/.lake/build/bin/dqrat-lean`
- Harness: `scripts/benchmark_runtime.sh`
- Iterations per case: `100`

Command:

```bash
ITERS=100 ./scripts/benchmark_runtime.sh
```

Results:

| Case | Verdict | Baseline ms/run | Candidate ms/run | Speedup |
| --- | --- | ---: | ---: | ---: |
| test_01_ldq-unsound | `s FAILED` | 3.397 | 2.882 | 1.18x |
| test_02_propositionally_unsat | `s VERIFIED` | 2.581 | 3.054 | 0.85x |
| test_03_UP_unsat | `s VERIFIED` | 2.748 | 2.852 | 0.96x |
| test_04_propositional_drat | `s UNKNOWN` | 2.792 | 2.595 | 1.08x |
| test_05_ex2_BCJ14_Thm7 | `s VERIFIED` | 2.950 | 3.220 | 0.92x |
| test_06_fork | `s VERIFIED` | 3.187 | 3.470 | 0.92x |
| stale_delete_state | `s FAILED` | 2.549 | 2.422 | 1.05x |
| stale_delete_neg_state | `s FAILED` | 2.502 | 2.839 | 0.88x |
| **Average** |  | **2.838** | **2.917** | **0.97x** |

## Interpretation

The watched runtime plus binary-clause specialization and live-occurrence cache
is functionally stable on the current local corpus, but this corpus is too
small to support strong performance claims. The average in this run is slightly
slower, while some stale-delete-sensitive cases improve and others regress.
That is exactly the pattern where a larger proof corpus is required before
deciding which cache maintenance ideas are actually helping.

The current binary-implication cleanup path is therefore kept as a
verification-friendly maintenance optimization. The same currently applies to
the live-occurrence cache: it is a clean runtime/proof split, but not yet a
demonstrated overall speed win on this machine.
