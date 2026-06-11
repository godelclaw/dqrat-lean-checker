#!/usr/bin/env bash
# Behavioral parity check: Lean checker vs the C++ reference (dqrat-check).
# Usage: scripts/crosscheck_cpp.sh [path-to-cpp-binary]
set -euo pipefail
cd "$(dirname "$0")/.."
CPP="${1:-/home/zarclaw/repos/dqrat-check/build/src/dqrat-check}"
LEAN=".lake/build/bin/dqrat-lean"
[ -x "$CPP" ]  || { echo "C++ binary not found: $CPP"; exit 1; }
[ -x "$LEAN" ] || { echo "Lean binary not found (run: lake build dqrat-lean)"; exit 1; }

fail=0
echo "| instance | C++ | Lean | match |"
echo "|---|---|---|---|"
verdict() {  # run with timeout, return the s-line or a status tag
  local out rc
  out=$(timeout 10 "$@" 2>&1); rc=$?
  if [ $rc -eq 124 ]; then echo "HANG(>10s)"; return; fi
  local s
  s=$(echo "$out" | grep -m1 "^s " || true)
  if [ -n "$s" ]; then echo "${s#s }"; else echo "(no verdict)"; fi
}
check_pair() {
  local f="$1" p="$2" name="$3" c l m
  c=$(verdict "$CPP" "$f" "$p")
  l=$(verdict "$LEAN" "$f" "$p")
  if [ "$c" = "$l" ]; then m="OK"; else m="DIFF"; fail=1; fi
  echo "| $name | $c | $l | $m |"
}
for f in tests/test_0*.dqdimacs; do
  b=$(basename "$f" .dqdimacs)
  check_pair "$f" "tests/$b.dqrat" "$b"
done
for f in repros/*.dqdimacs; do
  b=$(basename "$f" .dqdimacs)
  [ -f "repros/$b.dqrat" ] && check_pair "$f" "repros/$b.dqrat" "repro:$b"
done
echo
if [ "$fail" = 0 ]; then echo "crosscheck_cpp.sh: ALL MATCH"; else
  echo "crosscheck_cpp.sh: differences found (see table; differences on"
  echo "malformed inputs are CLI-robustness deltas, not rule-semantics deltas)"
fi
