#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: ./scripts/docs.sh [OPTIONS] [KILT|Examples ...]

Build and preview KILT API documentation with doc-gen4. Run --setup once after
cloning or whenever the Lean/doc-gen4 revision changes. With no mode flag, both
the KILT and Examples documentation targets are built.

Modes (choose one):
      --setup       Download/pin doc-gen4 and refresh the local KILT dependency.
  -b, --build       Build selected documentation targets (default).
  -r, --rebuild     Clean generated documentation, then build selected targets.
  -c, --clean       Remove generated documentation output; keep dependencies/logs.
      --clean-logs  Remove documentation build/setup logs only.
  -C, --clean-all   Remove generated documentation output and documentation logs.
  -s, --serve       Serve existing HTML on a local HTTP server; Ctrl-C stops it.
      --status      Show setup, output and latest-log status.

Options:
  -v, --verbose     Include commands executed by Lake.
      --source KIND Source links: github, file or vscode (default: github).
      --host HOST   Server bind address (default: 127.0.0.1).
      --port PORT   Server port (default: 8000).
  -h, --help        Show this help.

Examples:
  ./scripts/docs.sh --setup
  ./scripts/docs.sh
  ./scripts/docs.sh KILT
  ./scripts/docs.sh --rebuild KILT Examples
  ./scripts/docs.sh --source vscode KILT
  ./scripts/docs.sh --serve --port 8080
  ./scripts/docs.sh --clean-all

Generated HTML: docbuild/.lake/build/doc/index.html
Logs: .lake/logs/docs-*.log; latest: .lake/logs/latest-docs.log
LEAN_NUM_THREADS defaults to 1. Setup and the first build can take time and
disk space because doc-gen4 also generates documentation for Lean, Init, Lake
and Std. Downloaded dependencies and compiled dependency caches are preserved
by clean operations.
EOF
}

argument_error() {
  printf '%s\nUse --help for usage.\n' "$1" >&2
  exit 2
}

select_mode() {
  [[ "$mode_selected" == false ]] || argument_error 'Choose only one mode.'
  mode=$1
  mode_selected=true
}

mode=build
mode_selected=false
verbose=false
source_kind="${DOCGEN_SRC:-github}"
serve_host="${DOCS_HOST:-127.0.0.1}"
serve_port="${DOCS_PORT:-8000}"
targets=()

while (($#)); do
  case "$1" in
    --setup) select_mode setup ;;
    -b|--build) select_mode build ;;
    -r|--rebuild) select_mode rebuild ;;
    -c|--clean) select_mode clean ;;
    --clean-logs) select_mode clean-logs ;;
    -C|--clean-all) select_mode clean-all ;;
    -s|--serve) select_mode serve ;;
    --status) select_mode status ;;
    -v|--verbose) verbose=true ;;
    --source)
      shift
      (($#)) || argument_error '--source needs github, file or vscode.'
      source_kind=$1
      ;;
    --host)
      shift
      (($#)) || argument_error '--host needs an address.'
      serve_host=$1
      ;;
    --port)
      shift
      (($#)) || argument_error '--port needs a number.'
      serve_port=$1
      ;;
    -h|--help) usage; exit 0 ;;
    -*) argument_error "Unknown option: $1" ;;
    *) targets+=("$1") ;;
  esac
  shift
done

case "$source_kind" in
  github|file|vscode) ;;
  *) argument_error '--source must be github, file or vscode.' ;;
esac
[[ "$serve_port" =~ ^[0-9]+$ ]] || argument_error '--port must be an integer.'
((serve_port >= 1 && serve_port <= 65535)) || argument_error '--port must be between 1 and 65535.'

if [[ "$mode" != build && "$mode" != rebuild ]] && ((${#targets[@]})); then
  argument_error 'Targets are supported only by build and rebuild.'
fi

if ((${#targets[@]} == 0)); then
  targets=(KILT Examples)
fi
doc_targets=()
for target in "${targets[@]}"; do
  case "$target" in
    KILT|Examples) doc_targets+=("$target:docs") ;;
    *) argument_error "Unknown documentation target: $target (use KILT or Examples)." ;;
  esac
done

repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
docbuild_dir="$repo_dir/docbuild"
output_dir="$docbuild_dir/.lake/build/doc"
index_file="$output_dir/index.html"
log_dir="$repo_dir/.lake/logs"
manifest_file="$docbuild_dir/lake-manifest.json"
source "$repo_dir/scripts/build-output.sh"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

if ! command -v lake >/dev/null 2>&1; then
  printf 'Lake is missing from PATH. Install elan and use the pinned toolchain.\n' >&2
  exit 127
fi
if [[ ! -f "$docbuild_dir/lakefile.toml" || ! -f "$docbuild_dir/lean-toolchain" ]]; then
  printf 'Documentation configuration is missing from %s.\n' "$docbuild_dir" >&2
  exit 1
fi
if ! cmp -s "$repo_dir/lean-toolchain" "$docbuild_dir/lean-toolchain"; then
  printf 'The project and documentation toolchains differ. Update docbuild before continuing.\n' >&2
  exit 1
fi
docgen_rev=$(awk -F '"' '/^rev = "/ { print $2; exit }' "$docbuild_dir/lakefile.toml")
[[ -n "$docgen_rev" ]] || {
  printf 'Could not read the doc-gen4 revision from %s.\n' "$docbuild_dir/lakefile.toml" >&2
  exit 1
}

lake_command=(lake --no-ansi)
if [[ "$verbose" == true ]]; then lake_command+=(--verbose); fi

clean_logs() {
  if [[ -d "$log_dir" ]]; then
    find "$log_dir" -maxdepth 1 -type f -name 'docs-*.log' -delete
    if [[ -L "$log_dir/latest-docs.log" ]]; then
      rm -f -- "$log_dir/latest-docs.log"
    fi
  fi
  printf 'Removed documentation logs from %s.\n' "$log_dir"
}

clean_docs() {
  cd -- "$docbuild_dir"
  "${lake_command[@]}" clean
  printf 'Cleaned generated documentation; downloaded dependencies are kept.\n'
}

show_status() {
  printf 'Documentation project: %s\n' "$docbuild_dir"
  printf 'Toolchain: %s\n' "$(<"$docbuild_dir/lean-toolchain")"
  printf 'doc-gen4 revision: %s\n' "$docgen_rev"
  if [[ -f "$manifest_file" ]]; then
    printf 'Setup: ready (%s)\n' "$manifest_file"
  else
    printf 'Setup: required (run ./scripts/docs.sh --setup)\n'
  fi
  if [[ -f "$index_file" ]]; then
    printf 'HTML: ready (%s)\n' "$index_file"
    printf 'Preview: ./scripts/docs.sh --serve\n'
  else
    printf 'HTML: not built\n'
  fi
  if [[ -e "$log_dir/latest-docs.log" ]]; then
    printf 'Latest log: %s\n' "$log_dir/latest-docs.log"
  else
    printf 'Latest log: none\n'
  fi
}

if [[ "$mode" == status ]]; then
  show_status
  exit 0
fi
if [[ "$mode" == clean-logs ]]; then
  clean_logs | display_build_output
  exit 0
fi
if [[ "$mode" == clean || "$mode" == clean-all ]]; then
  clean_docs | display_build_output
  if [[ "$mode" == clean-all ]]; then clean_logs | display_build_output; fi
  exit 0
fi
if [[ "$mode" == serve ]]; then
  [[ -f "$index_file" ]] || {
    printf 'No generated documentation found. Run ./scripts/docs.sh first.\n' >&2
    exit 1
  }
  command -v python3 >/dev/null 2>&1 || {
    printf 'Python 3 is required to serve the generated site.\n' >&2
    exit 127
  }
  printf 'Serving KILT documentation at http://%s:%s/\n' "$serve_host" "$serve_port"
  printf 'Press Ctrl-C to stop.\n'
  exec python3 -m http.server "$serve_port" --bind "$serve_host" --directory "$output_dir"
fi

mkdir -p -- "$log_dir"
log_file=$(mktemp "$log_dir/docs-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX.log")
ln -sfn -- "${log_file##*/}" "$log_dir/latest-docs.log"
started_at=$SECONDS

run_docs() {
  printf 'Started: %s\n' "$(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  printf 'Repository: %s\n' "$repo_dir"
  printf 'Documentation project: %s\n' "$docbuild_dir"
  printf 'Toolchain: %s\n' "$(<"$docbuild_dir/lean-toolchain")"
  printf 'LEAN_NUM_THREADS: %s\n' "$LEAN_NUM_THREADS"
  printf 'Source links: %s\n' "$source_kind"
  printf 'Log: %s\n\n' "$log_file"
  cd -- "$docbuild_dir"

  if [[ "$mode" == setup ]]; then
    printf 'Updating doc-gen4 and the local KILT dependency...\n'
    MATHLIB_NO_CACHE_ON_UPDATE=1 "${lake_command[@]}" update doc-gen4
    MATHLIB_NO_CACHE_ON_UPDATE=1 "${lake_command[@]}" update kilt
    printf 'Documentation dependencies are ready.\n'
    return
  fi

  [[ -f "$manifest_file" ]] || {
    printf 'Documentation dependencies are not set up. Run ./scripts/docs.sh --setup first.\n' >&2
    return 1
  }
  if [[ "$mode" == rebuild ]]; then
    clean_docs || return $?
    cd -- "$docbuild_dir"
  fi
  printf 'Command:'
  printf ' %q' "${lake_command[@]}" build "${doc_targets[@]}"
  printf '\n\n'
  DOCGEN_SRC="$source_kind" "${lake_command[@]}" build "${doc_targets[@]}"
}

set +e
run_docs 2>&1 | tee "$log_file" | display_build_output
pipeline_status=("${PIPESTATUS[@]}")
set -e

docs_status=${pipeline_status[0]}
log_status=${pipeline_status[1]}
display_status=${pipeline_status[2]}
total_seconds=$((SECONDS - started_at))
set +e
{
  printf '\nFinished: %s\n' "$(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  printf 'Total time: %sm %ss (%s seconds)\n' \
    "$((total_seconds / 60))" "$((total_seconds % 60))" "$total_seconds"
  printf 'Documentation exit status: %s\n' "$docs_status"
  printf 'Log: %s\n' "$log_file"
  if ((docs_status == 0)) && [[ "$mode" != setup ]]; then
    printf 'HTML: %s\n' "$index_file"
    printf 'Preview: ./scripts/docs.sh --serve\n'
  fi
} | tee -a "$log_file" | display_build_output
summary_status=("${PIPESTATUS[@]}")
set -e

if ((log_status != 0 || summary_status[1] != 0)); then
  print_build_line 'Failed to capture the complete documentation log.' >&2
  if ((docs_status == 0)); then exit 1; fi
fi
if ((docs_status == 0 && (display_status != 0 || summary_status[2] != 0))); then
  exit 1
fi
exit "$docs_status"
