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
latexmk is used when available; otherwise the engine runs twice. Compiler
failures return a nonzero status. The preamble supports pdfLaTeX without fontspec;
the Unicode engines use fontspec and DejaVu Sans Mono when selected.
Logs go to `.lake/logs/report-*.log`, with `latest-report.log` pointing to the
latest attempt. Sources are kept by every cleanup action; generated outputs
under `build/` are ignored by Git. Report actions do not build or clean Lean.

Each file in `src/sections/` starts as an unapproved placeholder. Daily review
and report-intake notes live only under `.ai/human/notes/`, beginning with
`.ai/human/notes/2026-11-10.md`. They are not included verbatim in the PDF.
Dump details there first; later editing passes organise, verify and cut selected
material into these section files. Avoid treating daily notes as approved claims.
Keep sources next to drafted claims using `% PROV[user]`, `% PROV[code]` and
`% PROV[build]` comments.

Use the local `.ai/submission/REPORT.md` guidance when polishing: draft and review
one section at a time, preserve human explanations, and leave visible
`\needsinput{...}` markers for gaps. Write the abstract and conclusion after
the body is approved. The current title/author/course come from the proposal;
the date is the planned submission deadline. Institution, supervisor, template,
page limit and citation style remain to be confirmed. `src/refs.bib` is reserved
for confirmed references; no bibliography backend or syntax-highlighting/shell
escape dependency is needed for the initial scaffold.
