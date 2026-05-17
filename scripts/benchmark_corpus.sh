#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

BASELINE_BIN="${BASELINE_BIN:-/home/zarclaw/repos/dqrat-lean-checker-work/.lake/build/bin/dqrat-lean}"
CANDIDATE_BIN="${CANDIDATE_BIN:-$repo_root/.lake/build/bin/dqrat-lean}"
BENCH_ROOT="${BENCH_ROOT:-/home/zarclaw/benchmarks/generated-dqrat-synthetic}"
ITERS="${ITERS:-25}"

run_case() {
  local bin="$1"
  local formula="$2"
  local proof="$3"
  local iters="$4"
  local start_ns end_ns total_ns

  start_ns="$(date +%s%N)"
  for ((i = 0; i < iters; i++)); do
    "$bin" "$formula" "$proof" >/dev/null
  done
  end_ns="$(date +%s%N)"
  total_ns="$((end_ns - start_ns))"
  awk -v ns="$total_ns" -v it="$iters" 'BEGIN { printf "%.3f", ns / it / 1000000 }'
}

verdict_of() {
  local bin="$1"
  local formula="$2"
  local proof="$3"
  "$bin" "$formula" "$proof" 2>&1 | grep '^s ' | tail -n 1
}

if [[ ! -x "$BASELINE_BIN" ]]; then
  echo "missing baseline binary: $BASELINE_BIN" >&2
  exit 1
fi

if [[ ! -x "$CANDIDATE_BIN" ]]; then
  echo "missing candidate binary: $CANDIDATE_BIN" >&2
  exit 1
fi

if [[ ! -d "$BENCH_ROOT" ]]; then
  echo "missing benchmark root: $BENCH_ROOT" >&2
  exit 1
fi

mapfile -t formulas < <(find "$BENCH_ROOT" -name '*.dqdimacs' | sort)
if [[ "${#formulas[@]}" -eq 0 ]]; then
  echo "no benchmark formulas found under $BENCH_ROOT" >&2
  exit 1
fi

printf '| Case | Verdict | Baseline ms/run | Candidate ms/run | Speedup |\n'
printf '| --- | --- | ---: | ---: | ---: |\n'

sum_base=0
sum_cand=0
count=0

for formula in "${formulas[@]}"; do
  proof="${formula%.dqdimacs}.dqrat"
  if [[ ! -f "$proof" ]]; then
    echo "missing proof file for $formula" >&2
    exit 1
  fi

  rel="${formula#$BENCH_ROOT/}"
  verdict_base="$(verdict_of "$BASELINE_BIN" "$formula" "$proof")"
  verdict_cand="$(verdict_of "$CANDIDATE_BIN" "$formula" "$proof")"
  if [[ "$verdict_base" != "$verdict_cand" ]]; then
    echo "verdict mismatch on $rel" >&2
    echo "  baseline:  $verdict_base" >&2
    echo "  candidate: $verdict_cand" >&2
    exit 1
  fi

  base_ms="$(run_case "$BASELINE_BIN" "$formula" "$proof" "$ITERS")"
  cand_ms="$(run_case "$CANDIDATE_BIN" "$formula" "$proof" "$ITERS")"
  speedup="$(awk -v b="$base_ms" -v c="$cand_ms" 'BEGIN { if (c == 0) printf "inf"; else printf "%.2fx", b / c }')"

  printf '| %s | `%s` | %s | %s | %s |\n' \
    "$rel" "$verdict_cand" "$base_ms" "$cand_ms" "$speedup"

  sum_base="$(awk -v a="$sum_base" -v b="$base_ms" 'BEGIN { printf "%.6f", a + b }')"
  sum_cand="$(awk -v a="$sum_cand" -v b="$cand_ms" 'BEGIN { printf "%.6f", a + b }')"
  count="$((count + 1))"
done

avg_base="$(awk -v sum="$sum_base" -v n="$count" 'BEGIN { printf "%.3f", sum / n }')"
avg_cand="$(awk -v sum="$sum_cand" -v n="$count" 'BEGIN { printf "%.3f", sum / n }')"
avg_speedup="$(awk -v b="$avg_base" -v c="$avg_cand" 'BEGIN { if (c == 0) printf "inf"; else printf "%.2fx", b / c }')"

printf '| **Average** |  | **%s** | **%s** | **%s** |\n' \
  "$avg_base" "$avg_cand" "$avg_speedup"
