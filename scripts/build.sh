#!/usr/bin/env bash
set -euo pipefail

# Open the menu by default; --gui also opens it when this toggle is false.
GUI_LAUNCH="${GUI_LAUNCH:-true}"

usage() {
  cat <<'EOF'
Usage: ./scripts/build.sh [OPTIONS] [TARGET ...]

Build KILT and its checked examples, displaying and saving terminal output.
Can be run from any directory. Optional targets are passed to lake build.

Options:
      --gui         Open the keyboard-operated terminal menu (needs whiptail).
  -v, --verbose     Include the commands Lake executes.
  -c, --clean       Remove KILT build outputs; keep logs; exit.
      --clean-logs  Remove generated build logs; exit.
  -C, --clean-all   Remove KILT build outputs and script logs; exit.
  -r, --rebuild     Clean KILT outputs, then build and log.
  -h, --help        Show this help menu.

Cleanup keeps downloaded dependencies and their compiled caches.
Choose one cleanup mode. Targets are accepted for builds and rebuilds.
--gui accepts initial targets and --verbose, but no cleanup mode flags.

Examples:
  ./scripts/build.sh
  GUI_LAUNCH=false ./scripts/build.sh
  ./scripts/build.sh --gui
  ./scripts/build.sh --verbose
  ./scripts/build.sh --rebuild Examples
  ./scripts/build.sh --clean-logs

Logs: .lake/logs/build-*.log; latest: .lake/logs/latest.log.
LEAN_NUM_THREADS defaults to 1; set it explicitly to use more threads.
GUI_LAUNCH=true (default) opens the menu when no target or cleanup mode is given.
GUI_LAUNCH=false runs the CLI by default; --gui still opens the menu.
EOF
}

argument_error() {
  printf '%s\nUse --help for usage.\n' "$1" >&2
  exit 2
}

select_mode() {
  [[ "$mode" == build ]] || argument_error 'Choose only one cleanup mode.'
  mode=$1
}

mode=build
verbose=false
gui=false
targets=()
for argument in "$@"; do
  case "$argument" in
    -h|--help) usage; exit 0 ;;
    --gui) gui=true ;;
    -v|--verbose) verbose=true ;;
    -c|--clean) select_mode clean ;;
    -C|--clean-all) select_mode clean-all ;;
    --clean-logs) select_mode clean-logs ;;
    -r|--rebuild) select_mode rebuild ;;
    -*) argument_error "Unknown option: $argument" ;;
    *) targets+=("$argument") ;;
  esac
done
case "$GUI_LAUNCH" in
  true|false) ;;
  *) argument_error 'GUI_LAUNCH must be true or false.' ;;
esac
if [[ "$GUI_LAUNCH" == true && "$mode" == build ]] && ((${#targets[@]} == 0)); then
  gui=true
fi
if [[ "$gui" == true && "$mode" != build ]]; then
  argument_error 'Choose cleanup actions inside --gui, or omit --gui.'
fi
if [[ "$mode" != build && "$mode" != rebuild ]] && ((${#targets[@]})); then
  argument_error 'Targets are only supported when building or rebuilding.'
fi

repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$repo_dir"
log_dir="$repo_dir/.lake/logs"

if [[ "$gui" == true ]]; then
  source "$repo_dir/scripts/build-menu.sh"
  build_menu "$repo_dir/scripts/build.sh" "$verbose" "${targets[@]}"
  exit $?
fi

lake_command=(lake)
if [[ "$verbose" == true ]]; then lake_command+=(--verbose); fi

clean_build() {
  "${lake_command[@]}" clean kilt || return $?
  printf 'Cleaned KILT build outputs; dependency builds are kept.\n'
}

clean_logs() {
  if [[ -d "$log_dir" ]]; then
    find "$log_dir" -maxdepth 1 -type f -name 'build-*.log' -delete
    if [[ -L "$log_dir/latest.log" ]]; then
      rm -f -- "$log_dir/latest.log"
    fi
  fi
  printf 'Removed script build logs from %s.\n' "$log_dir"
}

if [[ "$mode" == clean-logs ]]; then
  clean_logs
  exit 0
fi

if ! command -v lake >/dev/null 2>&1; then
  printf 'Lake is missing from PATH. Install elan and use the pinned toolchain.\n' >&2
  exit 127
fi

if [[ "$mode" == clean || "$mode" == clean-all ]]; then
  clean_build
  if [[ "$mode" == clean-all ]]; then clean_logs; fi
  exit 0
fi

build_command=("${lake_command[@]}" build "${targets[@]}")
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
mkdir -p -- "$log_dir"
log_file=$(mktemp "$log_dir/build-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX.log")
ln -sfn -- "${log_file##*/}" "$log_dir/latest.log"

started_at=$SECONDS
run_build() {
  printf 'Started: %s\n' "$(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  printf 'Repository: %s\n' "$repo_dir"
  printf 'Toolchain: %s\n' "$(<lean-toolchain)"
  printf 'LEAN_NUM_THREADS: %s\n' "$LEAN_NUM_THREADS"
  printf 'Log: %s\n' "$log_file"
  printf 'Command:'
  printf ' %q' "${build_command[@]}"
  printf '\n\n'
  if [[ "$mode" == rebuild ]]; then
    clean_build || return $?
  fi
  "${build_command[@]}"
}

set +e
run_build 2>&1 | tee "$log_file"
pipeline_status=("${PIPESTATUS[@]}")
set -e

build_status=${pipeline_status[0]}
log_status=${pipeline_status[1]}
{
  printf '\nFinished: %s\n' "$(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  printf 'Elapsed: %s seconds\n' "$((SECONDS - started_at))"
  printf 'Build exit status: %s\n' "$build_status"
  printf 'Log: %s\n' "$log_file"
} | tee -a "$log_file"

if ((log_status != 0)); then
  printf 'Failed to capture the complete build log.\n' >&2
  if ((build_status == 0)); then exit "$log_status"; fi
fi
exit "$build_status"
