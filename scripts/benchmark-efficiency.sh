#!/usr/bin/env bash
# Explicit fresh execution benchmark; it is intentionally outside core builds.
set -euo pipefail
repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
runs=3
mode=all
while (($#)); do
  case "$1" in
    -h|--help)
      cat <<'HELP'
Usage: scripts/benchmark-efficiency.sh [--runs N] [--phases-only]
Run fresh, single-thread interpreted checker/lasso ablations (default: 3).
Requires existing example builds; run scripts/verify-examples.sh first.
Writes timestamped output, median/range timings and process peak RSS under
.lake/logs. Baseline lasso searches can take minutes. Execution errors fail.
--phases-only skips slow reference/ablation runs, retaining optimized phases,
work counts, witness validation and full formula-facing timers.
HELP
      exit 0 ;;
    --runs)
      [[ $# -ge 2 && $2 =~ ^[1-9][0-9]*$ ]] || { echo 'Expected --runs N with positive N' >&2; exit 2; }
      runs=$2; shift 2 ;;
    --phases-only) mode=phases; shift ;;
    *) echo 'Unknown option; use --help' >&2; exit 2 ;;
  esac
done
cd "$repo_dir"
mkdir -p .lake/logs
log_path="$(mktemp ".lake/logs/efficiency-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX.log")"
export LEAN_NUM_THREADS=1
printf 'Benchmark log: %s\n' "$repo_dir/$log_path"
# pipefail preserves Lean or time failures; a failed execution never becomes a verdict.
/usr/bin/time -v lake env lean --run Benchmarks/Efficiency.lean "$runs" "$mode" 2>&1 | tee "$log_path"
python3 - "$log_path" <<'PY' | tee -a "$log_path"
import collections, statistics, sys
samples = collections.defaultdict(list)
for line in open(sys.argv[1]):
    if line.startswith('TIMING '):
        _, label, value, unit = line.split()
        samples[label].append(int(value))
print('\nSUMMARY (ms; fresh interpreted executions)')
for label, values in sorted(samples.items()):
    print(f'{label}: n={len(values)}, median={statistics.median(values):g}, range={min(values)}..{max(values)}')
PY
