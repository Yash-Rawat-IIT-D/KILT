#!/usr/bin/env bash
# Fresh processes; compilation is outside all reported execution timings.
set -euo pipefail
repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
runs=3
mode=both
while (($#)); do
  case "$1" in
    -h|--help)
      printf '%s\n' 'Usage: scripts/benchmark-indexed.sh [--runs N] [--mode both|native|interpreted]' \
        'Compare cached and reachable-indexed Boolean/lasso search in fresh processes.' \
        'Native compilation precedes measurement. Logs, latency summaries and process RSS' \
        'are written to .lake/logs. Failures propagate as nonzero exit status.'
      exit 0 ;;
    --runs)
      [[ $# -ge 2 && $2 =~ ^[1-9][0-9]*$ ]] || { printf 'Expected positive --runs N\n' >&2; exit 2; }
      runs=$2; shift 2 ;;
    --mode)
      [[ $# -ge 2 ]] || { printf 'Missing --mode value\n' >&2; exit 2; }
      case "$2" in both|native|interpreted) mode=$2 ;; *) printf 'Invalid mode\n' >&2; exit 2 ;; esac
      shift 2 ;;
    *) printf 'Unknown option; use --help\n' >&2; exit 2 ;;
  esac
done
cd "$repo_dir"
export LEAN_NUM_THREADS=1
mkdir -p .lake/logs
log_path="$(mktemp ".lake/logs/indexed-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX.log")"
printf 'Indexed benchmark log: %s/%s\n' "$repo_dir" "$log_path"
if [[ $mode != interpreted ]]; then
  lake build benchmark-indexed > "${log_path%.log}-build.log" 2>&1 || {
    printf 'Native build failed; see %s\n' "${log_path%.log}-build.log" >&2; exit 1;
  }
else
  lake build Benchmarks.IndexedStorage > "${log_path%.log}-build.log" 2>&1 || {
    printf 'Benchmark build failed; see %s\n' "${log_path%.log}-build.log" >&2; exit 1;
  }
fi
for execution_mode in native interpreted; do
  [[ $mode == both || $mode == "$execution_mode" ]] || continue
  if [[ $execution_mode == native ]]; then
    command_args=(.lake/build/bin/benchmark-indexed 1)
  else
    command_args=(lake env lean --run Benchmarks/IndexedStorage.lean 1)
  fi
  for ((sample=1; sample<=runs; sample++)); do
    printf 'MODE %s REPETITION %s/%s\n' "$execution_mode" "$sample" "$runs" | tee -a "$log_path"
    /usr/bin/time -v "${command_args[@]}" 2>&1 | tee -a "$log_path"
  done
done
python3 - "$log_path" <<'PY' | tee -a "$log_path"
import collections, statistics, sys
samples = collections.defaultdict(list)
memory = collections.defaultdict(list)
mode = None
for line in open(sys.argv[1]):
    if line.startswith('MODE '):
        mode = line.split()[1]
    elif line.startswith('TIMING '):
        _, label, value, unit = line.split()
        assert unit == 'ns'
        samples[mode, label].append(int(value) / 1_000_000)
    elif 'Maximum resident set size (kbytes):' in line:
        memory[mode].append(int(line.rsplit(':', 1)[1]))
print('\nSUMMARY latency in ms; preparation phases are not an additive decomposition')
for (mode, label), values in sorted(samples.items()):
    print(f'{mode} {label}: n={len(values)}, median={statistics.median(values):.3f}, range={min(values):.3f}..{max(values):.3f}')
for mode, values in sorted(memory.items()):
    print(f'{mode} whole-process peak RSS KiB: max={max(values)}, samples={values}')
PY
