# Upstreaming Summary

This branch is the publication/artifact line for the non-watched Lean checker.
As of 2026-06-11 it is 53 commits ahead of the canonical upstream merge-base
`2e290e6`.

The delta is easiest to review by theme rather than by commit order.

## 1. Proof completion

- The full non-watched checker soundness path is now theorem-closed:
  `parseDQDIMACS_correct`, `parseDQDIMACS_none_sound`,
  `checkAction_sound`, `checkActions_sound`, and `processProof_sound'`.
- The dependency-deletion proof frontier is closed through
  `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet`, with the semantic
  development split into `SoundnessCore`, `DeletionSemantics`,
  `DeletionPaths`, and `DeletionExhibition`.
- The parser-side `s VERIFIED` branch is now covered by theorem rather than by
  executable argument alone.
- The certified path keeps the same axiom boundary for the audited top-level
  theorems: `[propext, Classical.choice, Quot.sound]`.

## 2. Conformance and executable alignment

- The parser was aligned with the intended format behavior by keeping
  tautological matrix clauses instead of dropping them.
- Parser robustness was tightened around comments, unterminated lines,
  declared-max-var violations, and prefix/matrix ordering, with dedicated repro
  cases kept under `repros/`.
- Diagnostic counterexamples were moved off the certified import path so the
  default library and CLI expose only the theorem-backed checker.
- Trust boundaries are now explicit in the module headers and README:
  the default non-watched path is certified, diagnostics are separate, and the
  watched layer is explicitly experimental.

## 3. Test, benchmark, and artifact tooling

- `scripts/run_parser_regressions.sh` captures the parser and proof-format
  regression suite.
- `scripts/crosscheck_cpp.sh` compares Lean verdicts against the upstream C++
  checker across tests and repros.
- `scripts/bench_cpp.sh` generates deletion-heavy and propagation-chain cases
  for behavioral and performance comparison.
- `docs/benchmarks.md` records the parity results and the two upstream runtime
  bugs found during this branch.
- `docs/coverage_matrix.md` maps format rules to implementation points and
  proving theorems.
- `scripts/verify_everything.sh`, `scripts/AxiomAudit.lean`, and the Dockerfile
  provide a one-command artifact-verification path.

## 4. Experimental watched layer

- The watched-literals runtime is integrated as a buildable, parity-tested
  experimental track with its own CLI and local refinement lemmas.
- It is not the certified default path and is not described here as a proved
  replacement for the non-watched checker.
- Its current value is proof and engineering scaffolding, not artifact-critical
  performance.

## Review suggestion

If this work is being upstreamed in pieces, the natural split is:

1. parser/conformance fixes and regression cases
2. proof-completion modules and theorem closure
3. artifact/test tooling
4. optional watched-layer scaffolding as a clearly separate experimental track
