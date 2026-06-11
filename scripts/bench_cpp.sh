#!/usr/bin/env bash
# Wall-clock benchmark: Lean checker vs C++ reference on generated instances.
# Usage: scripts/bench_cpp.sh [path-to-cpp-binary]
set -euo pipefail
cd "$(dirname "$0")/.."
CPP="${1:-/home/zarclaw/repos/dqrat-check/build/src/dqrat-check}"
LEAN=".lake/build/bin/dqrat-lean"
GEN=/tmp/dqrat_bench_gen.py
OUT=/tmp/dqrat_bench
mkdir -p "$OUT"

cat > "$GEN" << 'PY'
import sys
def clause(*lits): return " ".join(map(str, lits)) + " 0\n"
def gen(depth, deletes):
    left = list(range(2, depth + 2)); right = list(range(depth + 2, 2*depth + 2))
    dup = (1, right[0])
    cl = [clause(-1, left[0])]
    cl += [clause(-left[i], left[i+1]) for i in range(depth-1)]
    cl.append(clause(-left[-1], -1))
    cl += [clause(*dup) for _ in range(deletes + 1)]
    cl += [clause(-right[i], right[i+1]) for i in range(depth-1)]
    cl.append(clause(-right[-1], 1))
    mv = right[-1]
    f = f"p cnf {mv} {len(cl)}\n" + "e " + " ".join(map(str, range(1, mv+1))) + " 0\n" + "".join(cl)
    p = "".join(f"d {dup[0]} {dup[1]} 0\n" for _ in range(deletes)) + clause(-1)
    return f, p
name, depth, deletes = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
f, p = gen(depth, deletes)
open(f"{name}.dqdimacs", "w").write(f)
open(f"{name}.dqrat", "w").write(p)
PY

median3() {  # run command 3x, print median seconds and the verdict
  local t1 t2 t3 v out
  for i in 1 2 3; do
    local start end
    start=$(date +%s.%N)
    out=$(timeout 600 "$@" 2>&1) || true
    end=$(date +%s.%N)
    eval "t$i=$(echo "$end $start" | awk '{printf "%.2f", $1-$2}')"
  done
  v=$(echo "$out" | grep -m1 "^s " || echo "s (none)")
  local med
  med=$(printf "%s\n%s\n%s\n" "$t1" "$t2" "$t3" | sort -n | sed -n 2p)
  echo "$med ${v#s }"
}

echo "| instance (depth × deletes) | clauses | C++ s | Lean s | verdicts match |"
echo "|---|---|---|---|---|"
for spec in "del1k 2 1000" "del5k 2 5000" "del20k 2 20000" "chain5k 5000 10"; do
  set -- $spec
  name=$OUT/$1; depth=$2; deletes=$3
  python3 "$GEN" "$name" "$depth" "$deletes"
  nclauses=$(head -1 "$name.dqdimacs" | awk '{print $4}')
  read ctime cverdict <<< "$(median3 "$CPP" "$name.dqdimacs" "$name.dqrat")"
  read ltime lverdict <<< "$(median3 "$LEAN" "$name.dqdimacs" "$name.dqrat")"
  match=$([ "$cverdict" = "$lverdict" ] && echo OK || echo DIFF)
  echo "| $1 (${depth}×${deletes}) | $nclauses | $ctime ($cverdict) | $ltime ($lverdict) | $match |"
done
