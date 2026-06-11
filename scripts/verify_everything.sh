#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

fail() {
  local step="$1"
  echo "verify_everything.sh: FAIL ($step)"
  exit 1
}

if ! command -v lake >/dev/null 2>&1; then
  fail "lake not found in PATH"
fi

echo "[1/6] lake build + lake build DqratLean.Soundness"
lake build || fail "[1/6] lake build + lake build DqratLean.Soundness"
lake build DqratLean.Soundness || fail "[1/6] lake build + lake build DqratLean.Soundness"

echo "[2/6] sorry/axiom grep"
grep_output="$(rg -n 'sorry|axiom' DqratLean Main.lean WatchedMain.lean || true)"
if [[ -n "$grep_output" ]]; then
  echo "$grep_output"
  fail "[2/6] sorry/axiom grep"
fi

echo "[3/6] axiom audit"
expected_axioms="$(cat <<'EOF'
'parseDQDIMACS_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'parseDQDIMACS_none_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'checkAction_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'processProof_sound'' depends on axioms: [propext, Classical.choice, Quot.sound]
'deleteIndependenceSetBridge_of_noDeleteCrossPathsSet' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
)"
actual_axioms="$(lake env lean scripts/AxiomAudit.lean)" || fail "[3/6] axiom audit"
if [[ "$actual_axioms" != "$expected_axioms" ]]; then
  echo "$actual_axioms"
  fail "[3/6] axiom audit"
fi

echo "[4/6] parser regressions"
./scripts/run_parser_regressions.sh || fail "[4/6] parser regressions"

echo "[5/6] C++ crosscheck"
if [[ $# -ge 1 ]]; then
  ./scripts/crosscheck_cpp.sh "$1" || fail "[5/6] C++ crosscheck"
else
  echo "SKIPPED: no C++ binary path provided"
fi

echo "[6/6] summary"
echo "verify_everything.sh: OK"
