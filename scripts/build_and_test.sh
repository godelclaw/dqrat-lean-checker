#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

echo "[1/7] lake build"
lake build

echo "[2/7] lake build DqratLean.Soundness"
lake build DqratLean.Soundness
echo "[3/7] lake build DqratLean.Counterexamples (diagnostics, outside certified path)"
lake build DqratLean.Counterexamples
echo "[2c] lake build watched-literals layer (experimental, outside certified path)"
lake build DqratLean.WatchedRuntimeSoundness DqratLean.WatchedParser dqrat-lean-watched
echo "[4/7] lake build DqratLean.WatchedRuntimeSoundness (experimental runtime proofs)"
lake build DqratLean.WatchedRuntimeSoundness
echo "[5/7] lake build DqratLean.WatchedParser (experimental runtime checker/parser)"
lake build DqratLean.WatchedParser

echo "[6/7] parser regressions"
./scripts/run_parser_regressions.sh

echo "[7/7] executable smoke test"
lake exe dqrat-lean \
  tests/test_04_propositional_drat.dqdimacs \
  tests/test_04_propositional_drat.dqrat

echo "build_and_test.sh: OK"
