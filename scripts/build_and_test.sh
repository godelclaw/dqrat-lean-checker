#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

echo "[1/5] lake build"
lake build

echo "[2/5] lake build DqratLean.Soundness"
lake build DqratLean.Soundness
echo "[2b/5] lake build DqratLean.Counterexamples (diagnostics, outside certified path)"
lake build DqratLean.Counterexamples

echo "[3/5] parser regressions"
./scripts/run_parser_regressions.sh

echo "[4/5] executable smoke test"
lake exe dqrat-lean \
  tests/test_04_propositional_drat.dqdimacs \
  tests/test_04_propositional_drat.dqrat

echo "build_and_test.sh: OK"
