# Benchmark Corpus Sources

This branch currently has only a small local proof corpus:

- `tests/`
- `repros/`

These are sufficient for regression checking, but not for convincing performance
evaluation.

## External formula sources

### QBFEVAL / QBFLIB

Official QBF Solver Evaluation portal:

- https://www.qbflib.org/qbfeval20.php

Relevant points:

- the portal lists downloadable evaluation datasets;
- QBFEVAL'20 explicitly includes a `DQBF Solvers` track.

### iDQ

Official iDQ project page:

- https://fmv.jku.at/idq/

Relevant points:

- the page explicitly publishes `DQBF benchmarks`;
- it also publishes `Evaluation scripts and log files`.

### Pedant SAT 2022

Tool paper:

- Franz-Xaver Reichl, Friedrich Slivovsky.
  *Pedant: A Certifying DQBF Solver*.
  SAT 2022.
  https://drops.dagstuhl.de/opus/volltexte/2022/16694/pdf/LIPIcs-SAT-2022-20.pdf

Relevant point:

- Table 2 reports the QBFEVAL'20 DQBF-track families
  `Balabanov`, `Bloem`, `Kullmann`, `Scholl`, and `Tentrup`
  for a total of `354` instances.

## Important limitation

These sources provide a larger **formula** corpus, not a ready-made **checker**
corpus. For checker benchmarking we need matching pairs of:

- `*.dqdimacs`
- `*.dqrat`

So a serious benchmark suite will require one of:

- a proof-producing DQBF solver pipeline; or
- an external artifact that already publishes formula/proof pairs.

At the time of writing, the local workspace does not contain such a larger
proof-pair corpus.
