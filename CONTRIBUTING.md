# Development

This is an individual COL876 project. Keep changes small and organized around
definitions, algorithms, proofs, and worked examples.

- Use the toolchain in `lean-toolchain` and run `lake build` before committing.
- Put reusable definitions and theorems in the `KILT` namespace, in focused
  modules under `KILT/`. Export public modules through `KILT.lean`.
- Put examples and regression cases under `Examples/` and import them from
  `Examples.lean` so the default build checks them.
- Document theorem assumptions, the supported fragment, and algorithm trust
  boundaries. Mark unfinished proofs clearly; a theorem using `sorry` is not a
  completed correctness result.
- When adding CSLib or other dependencies, choose compatible revisions, run
  `lake update`, and commit both the Lake configuration and `lake-manifest.json`.
  Coordinate dependency changes with the toolchain pin.
- Keep generated build files and LaTeX intermediates out of Git. Keep proposal
  sources, figures, and the submitted PDF under `Proposal/`.
- Commit the toolchain pin, dependency lockfile, and shared editor extension
  recommendations. Keep local editor settings and environment files untracked;
  an `.env.example` may be committed if it contains only sample values.

The original proposal references `lean-logo-official.png`, which is not yet in
`Proposal/`. Restore that figure before rebuilding the proposal PDF.
