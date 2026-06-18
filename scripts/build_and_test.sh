#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

echo "[1/9] lake build"
lake build

echo "[2/9] lake build DqratLean.Soundness"
lake build DqratLean.Soundness
echo "[3/9] lake build DqratLean.Counterexamples (diagnostics, outside certified path)"
lake build DqratLean.Counterexamples
echo "[4/9] lake build watched-literals layer (experimental, outside certified path)"
lake build DqratLean.WatchedRuntimeSoundness DqratLean.WatchedPropagationRefinement DqratLean.WatchedParser dqrat-lean-watched
echo "[5/9] lake build watched proof modules (experimental runtime proofs)"
lake build DqratLean.WatchedRuntimeSoundness DqratLean.WatchedPropagationRefinement
echo "[6/9] lake build DqratLean.WatchedParser (experimental runtime checker/parser)"
lake build DqratLean.WatchedParser

echo "[7/9] parser regressions"
./scripts/run_parser_regressions.sh

echo "[8/9] watched/base parity on tests + repros (experimental runtime)"
./scripts/crosscheck_watched.sh

echo "[9/9] executable smoke test"
lake exe dqrat-lean \
  tests/test_04_propositional_drat.dqdimacs \
  tests/test_04_propositional_drat.dqrat

echo "build_and_test.sh: OK"
