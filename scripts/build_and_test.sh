#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

echo "[1/8] lake build"
lake build

echo "[2/8] lake build DqratLean.Soundness"
lake build DqratLean.Soundness

echo "[3/8] lake build DqratLean.WatchedSoundness"
lake build DqratLean.WatchedSoundness

echo "[4/8] lake build DqratLean.WatchedBinarySoundness"
lake build DqratLean.WatchedBinarySoundness

echo "[5/8] lake build DqratLean.WatchedBinaryRefinement"
lake build DqratLean.WatchedBinaryRefinement

echo "[6/8] lake build DqratLean.WatchedRuntimeSoundness"
lake build DqratLean.WatchedRuntimeSoundness

echo "[7/8] parser regressions"
./scripts/run_parser_regressions.sh

echo "[8/8] executable smoke test"
lake exe dqrat-lean \
  tests/test_04_propositional_drat.dqdimacs \
  tests/test_04_propositional_drat.dqrat

echo "build_and_test.sh: OK"
