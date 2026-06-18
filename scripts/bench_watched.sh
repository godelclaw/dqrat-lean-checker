#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build dqrat-lean dqrat-lean-watched >/dev/null

BASE="./.lake/build/bin/dqrat-lean"
WATCHED="./.lake/build/bin/dqrat-lean-watched"
GEN=/tmp/dqrat_watched_bench_gen.py
OUT=/tmp/dqrat_watched_bench
mkdir -p "$OUT"

ratio_limit="${1:-}"

cat > "$GEN" <<'PY'
import sys

def clause(*lits):
    return " ".join(map(str, lits)) + " 0\n"

def gen(depth, deletes):
    left = list(range(2, depth + 2))
    right = list(range(depth + 2, 2 * depth + 2))
    dup = (1, right[0])
    cl = [clause(-1, left[0])]
    cl += [clause(-left[i], left[i + 1]) for i in range(depth - 1)]
    cl.append(clause(-left[-1], -1))
    cl += [clause(*dup) for _ in range(deletes + 1)]
    cl += [clause(-right[i], right[i + 1]) for i in range(depth - 1)]
    cl.append(clause(-right[-1], 1))
    max_var = right[-1]
    formula = (
        f"p cnf {max_var} {len(cl)}\n"
        + "e "
        + " ".join(map(str, range(1, max_var + 1)))
        + " 0\n"
        + "".join(cl)
    )
    proof = "".join(f"d {dup[0]} {dup[1]} 0\n" for _ in range(deletes)) + clause(-1)
    return formula, proof

name, depth, deletes = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
formula, proof = gen(depth, deletes)
open(f"{name}.dqdimacs", "w").write(formula)
open(f"{name}.dqrat", "w").write(proof)
PY

median3() {
  local t1 t2 t3 out verdict
  for i in 1 2 3; do
    local start end elapsed
    start=$(date +%s.%N)
    out=$(timeout 600 "$@" 2>&1) || true
    end=$(date +%s.%N)
    elapsed=$(awk -v end="$end" -v start="$start" 'BEGIN { printf "%.2f", end - start }')
    eval "t$i='$elapsed'"
  done
  verdict=$(printf '%s\n' "$out" | grep -m1 "^s " || echo "s (none)")
  local median
  median=$(printf "%s\n%s\n%s\n" "$t1" "$t2" "$t3" | sort -n | sed -n '2p')
  echo "$median ${verdict#s }"
}

limit_failed=0
echo "| instance | base | watched | ratio | verdicts match |"
echo "|---|---|---|---|---|"
for spec in "del5k 2 5000" "del20k 2 20000" "chain5k 5000 10"; do
  set -- $spec
  name="$OUT/$1"
  depth="$2"
  deletes="$3"
  python3 "$GEN" "$name" "$depth" "$deletes"
  read -r base_time base_verdict <<<"$(median3 "$BASE" "$name.dqdimacs" "$name.dqrat")"
  read -r watched_time watched_verdict <<<"$(median3 "$WATCHED" "$name.dqdimacs" "$name.dqrat")"
  ratio=$(awk -v base="$base_time" -v watched="$watched_time" 'BEGIN {
    if (base == 0) { print "inf" } else { printf "%.2f", watched / base }
  }')
  if [ "$base_verdict" = "$watched_verdict" ]; then
    match="OK"
  else
    match="DIFF"
  fi
  echo "| $1 | $base_time ($base_verdict) | $watched_time ($watched_verdict) | $ratio | $match |"
  if [ -n "$ratio_limit" ] && [ "$ratio" != "inf" ]; then
    if ! awk -v ratio="$ratio" -v limit="$ratio_limit" 'BEGIN { exit !(ratio <= limit) }'; then
      limit_failed=1
    fi
  fi
done

if [ -n "$ratio_limit" ] && [ "$limit_failed" -ne 0 ]; then
  echo
  echo "bench_watched.sh: watched/base ratio exceeded limit $ratio_limit"
  exit 1
fi

echo
echo "bench_watched.sh: OK"
