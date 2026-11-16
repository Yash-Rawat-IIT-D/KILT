# Working report

The source entry point is `src/main.tex`; output is `build/main.pdf`.
Run from the repository root (the scripts also work from another directory):

```sh
./scripts/build.sh --report
./scripts/build.sh --report --rebuild
./scripts/build.sh --report --clean       # intermediates only; keep PDF
./scripts/build.sh --report --clean-all   # intermediates and generated PDF
./scripts/build.sh --report --clean-logs  # report script logs only
```

The terminal menu has a Report entry. `scripts/compile-report.sh` also accepts
these options directly and supports `--verbose`. pdfLaTeX is preferred by default;
XeLaTeX and LuaLaTeX are alternatives. Set `REPORT_ENGINE` to select one explicitly.
latexmk is used when available; otherwise the script runs the engine once,
BibTeX when requested, and then two final engine passes. Compiler
failures return a nonzero status. The preamble supports pdfLaTeX without fontspec;
the Unicode engines use fontspec and DejaVu Sans Mono when selected.
Logs go to `.lake/logs/report-*.log`, with `latest-report.log` pointing to the
latest attempt. Sources are kept by every cleanup action; generated outputs
under `build/` are ignored by Git. Report actions do not build or clean Lean.
