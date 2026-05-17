#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build dqrat-lean >/dev/null
bin="./.lake/build/bin/dqrat-lean"

run_case() {
  local label="$1"
  local formula="$2"
  local proof="$3"
  local expected="$4"
  local output
  output="$("$bin" "$formula" "$proof" 2>&1 || true)"
  if [[ "$output" != *"$expected"* ]]; then
    echo "FAIL: $label"
    echo "expected substring: $expected"
    echo "actual output:"
    echo "$output"
    exit 1
  fi
  echo "PASS: $label"
}

run_case "test_01_ldq-unsound" tests/test_01_ldq-unsound.dqdimacs tests/test_01_ldq-unsound.dqrat "s FAILED"
run_case "test_02_propositionally_unsat" tests/test_02_propositionally_unsat.dqdimacs tests/test_02_propositionally_unsat.dqrat "s VERIFIED"
run_case "test_03_UP_unsat" tests/test_03_UP_unsat.dqdimacs tests/test_03_UP_unsat.dqrat "s VERIFIED"
run_case "test_04_propositional_drat" tests/test_04_propositional_drat.dqdimacs tests/test_04_propositional_drat.dqrat "s UNKNOWN"
run_case "test_05_ex2_BCJ14_Thm7" tests/test_05_ex2_BCJ14_Thm7.dqdimacs tests/test_05_ex2_BCJ14_Thm7.dqrat "s VERIFIED"
run_case "test_06_fork" tests/test_06_fork.dqdimacs tests/test_06_fork.dqrat "s VERIFIED"

run_case "repro_header_comment_contains_p_cnf" repros/header_comment_contains_p_cnf.dqdimacs repros/header_comment_contains_p_cnf.dqrat "s UNKNOWN"
run_case "repro_maxvar_violation" repros/maxvar_violation.dqdimacs repros/maxvar_violation.dqrat "c parse error: Variable 2 exceeds maximum declared variable"
run_case "repro_proof_comment_ignored" repros/proof_comment_ignored.dqdimacs repros/proof_comment_ignored.dqrat "s UNKNOWN"
run_case "repro_proof_missing_zero" repros/proof_missing_zero.dqdimacs repros/proof_missing_zero.dqrat "c proof parse error: Line 1: expected 0 terminator in clause line"
run_case "repro_formula_missing_zero" repros/formula_missing_zero.dqdimacs repros/formula_missing_zero.dqrat "c parse error: Line 2: expected 0 terminator in 'a' line"
run_case "repro_prefix_after_matrix_started" repros/prefix_after_matrix_started.dqdimacs repros/prefix_after_matrix_started.dqrat "c parse error: Line 3: prefix line after matrix started"
run_case "repro_prefix_dep_var_zero" repros/prefix_dep_var_zero.dqdimacs repros/prefix_dep_var_zero.dqrat "c parse error: Expected positive exi var in 'd' line"

echo "All parser regressions passed."
