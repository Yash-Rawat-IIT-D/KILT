#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'HELP'
Usage: ./scripts/verify-examples.sh [OPTIONS]

Compile and verify every Examples module, including its proofs, build-failing
execution checks and axiom audits. Required KILT dependencies are built too.
Runs directly without the GUI and uses build.sh's timestamped plain-text logs,
coloured output, exit status and single-thread default.

Options:
  -v, --verbose   Include commands executed by Lake.
  -r, --rebuild   Clean project outputs, then verify examples; keep dependency caches.
  -h, --help      Show this help.

Examples:
  ./scripts/verify-examples.sh
  ./scripts/verify-examples.sh --verbose
  ./scripts/verify-examples.sh --rebuild --verbose

Lake reuses up-to-date modules. --rebuild reruns project checks and demos.
Logs: .lake/logs/build-*.log; latest: .lake/logs/latest.log.
HELP
}

flags=()
for argument in "$@"; do
  case "$argument" in
    -h|--help) usage; exit 0 ;;
    -v|--verbose|-r|--rebuild) flags+=("$argument") ;;
    *) printf 'Unknown option: %s\nUse --help for usage.\n' "$argument" >&2; exit 2 ;;
  esac
done

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
GUI_LAUNCH=false exec "$script_dir/build.sh" "${flags[@]}" Examples
