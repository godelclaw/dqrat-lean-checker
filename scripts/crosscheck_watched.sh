#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build dqrat-lean dqrat-lean-watched >/dev/null

BASE="./.lake/build/bin/dqrat-lean"
WATCHED="./.lake/build/bin/dqrat-lean-watched"

[ -x "$BASE" ] || { echo "Base binary not found: $BASE"; exit 1; }
[ -x "$WATCHED" ] || { echo "Watched binary not found: $WATCHED"; exit 1; }

normalize_output() {
  local out rc
  set +e
  out=$(timeout 20 "$@" 2>&1)
  rc=$?
  set -e
  if [ "$rc" -eq 124 ]; then
    echo "HANG(>20s)"
    return
  fi
  local parse_err proof_parse sline
  parse_err=$(printf '%s\n' "$out" | grep -m1 "^c parse error:" || true)
  if [ -n "$parse_err" ]; then
    echo "$parse_err"
    return
  fi
  proof_parse=$(printf '%s\n' "$out" | grep -m1 "^c proof parse error:" || true)
  if [ -n "$proof_parse" ]; then
    echo "$proof_parse"
    return
  fi
  sline=$(printf '%s\n' "$out" | grep -m1 "^s " || true)
  if [ -n "$sline" ]; then
    echo "$sline"
  else
    echo "(no verdict)"
  fi
}

fail=0
echo "| instance | base | watched | match |"
echo "|---|---|---|---|"

check_pair() {
  local formula="$1"
  local proof="$2"
  local name="$3"
  local base watched match
  base=$(normalize_output "$BASE" "$formula" "$proof")
  watched=$(normalize_output "$WATCHED" "$formula" "$proof")
  if [ "$base" = "$watched" ]; then
    match="OK"
  else
    match="DIFF"
    fail=1
  fi
  echo "| $name | $base | $watched | $match |"
}

for formula in tests/test_0*.dqdimacs; do
  name=$(basename "$formula" .dqdimacs)
  check_pair "$formula" "tests/$name.dqrat" "$name"
done

for formula in repros/*.dqdimacs; do
  name=$(basename "$formula" .dqdimacs)
  if [ -f "repros/$name.dqrat" ]; then
    check_pair "$formula" "repros/$name.dqrat" "repro:$name"
  fi
done

echo
if [ "$fail" -eq 0 ]; then
  echo "crosscheck_watched.sh: ALL MATCH"
else
  echo "crosscheck_watched.sh: differences found"
  exit 1
fi
