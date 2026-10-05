#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/compile-proposal.sh [OPTION]

Compile Proposal/src/KILT_Proposal.tex into Proposal/build/KILT_Proposal.pdf.
Uses latexmk, pdflatex, lualatex, xelatex, or tectonic, whichever is available.
Can be run from any directory.

Options:
  -c, --clean        Remove build intermediates without compiling; keep PDFs.
  -C, --clean-all    Also remove the generated KILT_Proposal.pdf.
      --clean-after Compile, then remove build intermediates.
  -h, --help        Show this help.

The submitted KILT_Proposal-1.pdf and source files are always kept.
EOF
}

mode=build
if (($# > 1)); then
  usage >&2
  exit 2
fi
case "${1:-}" in
  '') ;;
  -c|--clean) mode=clean ;;
  -C|--clean-all) mode=clean-all ;;
  --clean-after) mode=clean-after ;;
  -h|--help) usage; exit 0 ;;
  *) printf 'Unknown option: %s\n' "$1" >&2; usage >&2; exit 2 ;;
esac

repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
source_dir="$repo_dir/Proposal/src"
build_dir="$repo_dir/Proposal/build"
name=KILT_Proposal

clean() {
  local extension
  for extension in aux bbl bcf blg fdb_latexmk fls log out run.xml synctex.gz \
    toc lof lot nav snm vrb xdv; do
    rm -f -- "$build_dir/$name.$extension"
  done
  if [[ "$mode" == clean-all ]]; then
    rm -f -- "$build_dir/$name.pdf"
  fi
}

if [[ "$mode" == clean || "$mode" == clean-all ]]; then
  clean
  printf 'Cleaned proposal build files.\n'
  exit 0
fi

if [[ ! -f "$source_dir/$name.tex" ]]; then
  printf 'Missing proposal source: %s\n' "$source_dir/$name.tex" >&2
  exit 1
fi
if [[ ! -f "$source_dir/lean-logo-official.png" ]]; then
  printf 'Missing proposal figure: %s\n' "$source_dir/lean-logo-official.png" >&2
  exit 1
fi

engine=
for candidate in latexmk pdflatex lualatex xelatex tectonic; do
  if command -v "$candidate" >/dev/null 2>&1; then
    engine=$candidate
    break
  fi
done
if [[ -z "$engine" ]]; then
  printf 'No LaTeX compiler found. Install TeX Live (or Tectonic).\n' >&2
  exit 1
fi

mkdir -p -- "$build_dir"
cd -- "$source_dir"
printf 'Compiling proposal with %s...\n' "$engine"
case "$engine" in
  latexmk)
    latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
      -outdir="$build_dir" "$name.tex"
    ;;
  tectonic)
    tectonic --outdir "$build_dir" "$name.tex"
    ;;
  *)
    # Two passes resolve cross-references, page numbers, and PDF bookmarks.
    for pass in 1 2; do
      "$engine" -interaction=nonstopmode -halt-on-error -file-line-error \
        -output-directory="$build_dir" "$name.tex"
    done
    ;;
esac

if [[ "$mode" == clean-after ]]; then
  clean
fi
printf 'Built %s/%s.pdf\n' "$build_dir" "$name"
