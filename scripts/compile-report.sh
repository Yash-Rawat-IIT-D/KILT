#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: ./scripts/compile-report.sh [OPTIONS]

Build report/src/main.tex into report/build/main.pdf with pdfLaTeX by default.
Uses latexmk when available, otherwise runs the selected engine twice.
Can be run from any directory; no Lean build or shell escape is required.
Set REPORT_ENGINE=pdflatex|xelatex|lualatex to choose an engine explicitly.

Options:
  -v, --verbose     Print compiler commands as well as compiler output.
  -c, --clean       Remove TeX intermediates; keep the PDF and script logs.
  -C, --clean-all   Remove TeX intermediates and the generated main.pdf.
      --clean-logs  Remove report script logs only; keep outputs and sources.
  -r, --rebuild     Remove generated PDF/intermediates, then build.
  -h, --help        Show this help.

Sources and figures are always kept. Script logs: .lake/logs/report-*.log;
latest: .lake/logs/latest-report.log. All generated TeX files stay in report/build/.
The same options are available through ./scripts/build.sh --report.
EOF
}

mode=build
verbose=false
for argument in "$@"; do
  case "$argument" in
    -h|--help) usage; exit 0 ;;
    -v|--verbose) verbose=true ;;
    -c|--clean|-C|--clean-all|--clean-logs|-r|--rebuild)
      if [[ "$mode" != build ]]; then
        printf 'Choose only one report cleanup/rebuild mode.\n' >&2
        exit 2
      fi
      case "$argument" in
        -c|--clean) mode=clean ;;
        -C|--clean-all) mode=clean-all ;;
        --clean-logs) mode=clean-logs ;;
        -r|--rebuild) mode=rebuild ;;
      esac
      ;;
    *) printf 'Unknown report option: %s\n' "$argument" >&2; exit 2 ;;
  esac
done

repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
source_dir="$repo_dir/report/src"
build_dir="$repo_dir/report/build"
log_dir="$repo_dir/.lake/logs"
source "$repo_dir/scripts/build-output.sh"

clean_report() {
  local extension
  for extension in aux bbl bcf blg fdb_latexmk fls log out run.xml synctex.gz \
    toc lof lot nav snm vrb xdv; do
    rm -f -- "$build_dir/main.$extension"
  done
  if [[ "$mode" == clean-all || "$mode" == rebuild ]]; then
    rm -f -- "$build_dir/main.pdf"
  fi
  printf 'Cleaned report build files.\n'
}

if [[ "$mode" == clean-logs ]]; then
  if [[ -d "$log_dir" ]]; then
    find "$log_dir" -maxdepth 1 -type f -name 'report-*.log' -delete
    if [[ -L "$log_dir/latest-report.log" ]]; then
      rm -f -- "$log_dir/latest-report.log"
    fi
  fi
  printf 'Removed report script logs.\n'
  exit 0
fi
if [[ "$mode" == clean || "$mode" == clean-all ]]; then
  clean_report | display_build_output
  exit 0
fi
if [[ ! -f "$source_dir/main.tex" ]]; then
  printf 'Missing report source: %s\n' "$source_dir/main.tex" >&2
  exit 1
fi

engine="${REPORT_ENGINE:-}"
if [[ -n "$engine" ]]; then
  case "$engine" in
    pdflatex|xelatex|lualatex) ;;
    *) printf 'REPORT_ENGINE must be pdflatex, xelatex or lualatex.\n' >&2; exit 2 ;;
  esac
  if ! command -v "$engine" >/dev/null 2>&1; then
    printf 'Requested LaTeX engine is unavailable: %s\n' "$engine" >&2
    exit 127
  fi
else
  for candidate in pdflatex xelatex lualatex; do
    if command -v "$candidate" >/dev/null 2>&1; then
      engine=$candidate
      break
    fi
  done
fi
if [[ -z "$engine" ]]; then
  printf 'No LaTeX compiler found. Install pdfLaTeX, XeLaTeX or LuaLaTeX.\n' >&2
  exit 127
fi

mkdir -p -- "$build_dir" "$log_dir"
log_file=$(mktemp "$log_dir/report-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX.log")
ln -sfn -- "${log_file##*/}" "$log_dir/latest-report.log"
cd -- "$source_dir"
started_at=$SECONDS

run_compiler() {
  if [[ "$verbose" == true ]]; then
    printf 'Command:'
    printf ' %q' "$@"
    printf '\n'
  fi
  "$@"
}

run_report() {
  printf 'Started: %s\n' "$(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  printf 'Report source: %s/main.tex\nEngine: %s\nLog: %s\n' \
    "$source_dir" "$engine" "$log_file"
  if [[ "$mode" == rebuild ]]; then clean_report || return $?; fi
  if command -v latexmk >/dev/null 2>&1; then
    local engine_flag="-$engine"
    if [[ "$engine" == pdflatex ]]; then engine_flag=-pdf; fi
    run_compiler latexmk "$engine_flag" -interaction=nonstopmode -halt-on-error \
      -file-line-error "-outdir=$build_dir" main.tex || return $?
  else
    local pass
    for pass in 1 2; do
      run_compiler "$engine" -interaction=nonstopmode -halt-on-error \
        -file-line-error "-output-directory=$build_dir" main.tex || return $?
    done
  fi
  [[ -s "$build_dir/main.pdf" ]] || return 1
  printf 'Built %s/main.pdf\n' "$build_dir"
}

set +e
run_report 2>&1 | tee "$log_file" | display_build_output
pipeline_status=("${PIPESTATUS[@]}")
set -e
report_status=${pipeline_status[0]}
elapsed=$((SECONDS - started_at))
printf '\nTotal time: %sm %ss\nReport exit status: %s\nLog: %s\n' \
  "$((elapsed / 60))" "$((elapsed % 60))" "$report_status" "$log_file" |
  tee -a "$log_file" | display_build_output
if ((pipeline_status[1] != 0 || pipeline_status[2] != 0)); then
  printf 'Failed to capture or display the complete report build log.\n' >&2
  if ((report_status == 0)); then exit 1; fi
fi
exit "$report_status"
