# KILT — Kripke in Lean Toolkit

KILT is my semester project for **COL876: Special Topics in Formal Methods**.
My goal is to build a verified LTL model-checking toolkit in Lean 4, connecting
trace semantics, Büchi automata, finite Kripke structures, and kernel-checked
correctness proofs.

**Yash Rawat · 2023CS50334**

For example, `G(request → F grant)` expresses that every request is eventually
followed by a grant.

## Project scope

I will develop a reusable, CSLib-oriented path from a **bounded LTL fragment**
to a verified model-checking result:

1. Define the formula interface, trace semantics, and Kripke execution model.
2. Translate the selected fragment to Büchi or generalized Büchi automata.
3. Construct the system/property product and an executable accepting-run
   emptiness check.
4. Prove the correspondence between the checker and the declared semantics.
5. Demonstrate representative safety and liveness properties and document the
   design, trust boundary, and limitations.

I will first audit CSLib, LeanLTL, LeanearTemporalLogic, and Veil to select the
supported fragment and decide which existing interfaces to reuse. I plan to
build on CSLib's automata foundations and use LeanLTL as a semantic comparison
point, proving compatibility with its trace semantics where feasible.

I will prioritize the semantic correspondence and verified checker. If time
permits, I will add a lightweight Lean frontend for writing properties and
running checks, then explore proof-producing automation and CTL*.

## Getting started

Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager,
and optionally the Lean 4 VS Code extension. From this repository:

```sh
lake build
```

The toolchain is pinned in `lean-toolchain` to **Lean 4.35.0-rc4**, matching
the CSLib revision in `lakefile.toml`. Dependency revisions are locked in
`lake-manifest.json`.
The default build checks both the `KILT` library
and the `Examples` library. To build just the core:

```sh
lake build KILT
```

To build while saving the terminal output:

```sh
./scripts/build.sh                # Open the terminal menu by default
GUI_LAUNCH=false ./scripts/build.sh  # Build the library and examples directly
./scripts/build.sh --gui          # Open the menu even if GUI_LAUNCH=false
./scripts/build.sh --verbose      # Open the menu with verbose output enabled
./scripts/build.sh Examples       # Build just the examples and their dependencies
./scripts/build.sh --rebuild      # Clean KILT outputs, then build again
./scripts/build.sh --clean        # Remove KILT outputs; keep logs
./scripts/build.sh --clean-logs   # Remove script build logs
./scripts/build.sh --clean-all    # Remove KILT outputs and script logs
./scripts/build.sh --help         # Show options and examples
```

Each run saves a timestamped log under `.lake/logs/`, with the latest available
at `.lake/logs/latest.log`. The script returns the build's exit status and
defaults to one Lean thread; use `LEAN_NUM_THREADS=2 ./scripts/build.sh` to change it.
Build logs remain excluded from Git with the other `.lake` outputs.
Cleanup preserves downloaded dependencies and their compiled caches. Cleanup
options run without building; `--rebuild` cleans first and then builds.

The optional menu uses `whiptail` (on Ubuntu, install with
`sudo apt install whiptail`). Use arrow keys, Tab and Enter to select targets,
build, rebuild, clean, toggle verbose output, or view the latest log. Esc
cancels a dialog. `GUI_LAUNCH` defaults to `true`, so running without a target
or cleanup mode opens the menu. With `GUI_LAUNCH=false`, the script builds
directly unless `--gui` is supplied. Explicit targets and cleanup modes run
directly, and command-line builds do not require `whiptail`.

Open this folder in VS Code to use the pinned toolchain. See
[CONTRIBUTING.md](CONTRIBUTING.md) for the development workflow.

## Building the proposal

The script uses an available LaTeX compiler and writes the PDF to
`Proposal/build/KILT_Proposal.pdf`:

```sh
./scripts/compile-proposal.sh
./scripts/compile-proposal.sh --clean       # Remove intermediates, keep PDFs
./scripts/compile-proposal.sh --clean-all   # Also remove the generated PDF
./scripts/compile-proposal.sh --clean-after # Build and remove intermediates
```

## Repository layout

```text
KILT.lean               Public library entry point
KILT/                   Library definitions and proofs
Examples.lean           Example entry point
Examples/               Worked examples and regression cases
Proposal/src/           Proposal LaTeX source and figures
Proposal/build/         Submitted PDF and local build outputs
scripts/                Build and maintenance scripts
lakefile.toml           Lake package and build targets
lean-toolchain          Pinned Lean version
lake-manifest.json      Lake dependency lockfile
.github/workflows/      Automated build on pushes and pull requests
```

## Planned milestones

My plan for the semester is:

| Period (2026) | Primary focus |
| --- | --- |
| 24–30 September | Literature/API audit, setup, scoped design |
| 1–14 October | LTL semantics, Kripke executions, Büchi interface and translation |
| 15–31 October | Product construction, emptiness, central correctness theorem |
| 1–15 November | Verified examples, evaluation, write-up; frontend if time permits |

See my [project proposal](Proposal/build/KILT_Proposal-1.pdf) for the full scope
and schedule, or the [LaTeX source](Proposal/src/KILT_Proposal.tex).

## References

- [LeanLTL](https://github.com/UCSCFormalMethods/LeanLTL) and its
  [ITP 2025 paper](https://doi.org/10.4230/LIPIcs.ITP.2025.37).
- [CSLib](https://github.com/leanprover/cslib).
- [Automata Theory in Lean](https://github.com/ctchou/AutomataTheory).
- [LeanearTemporalLogic](https://github.com/mrigankpawagi/LeanearTemporalLogic).
- [Veil](https://github.com/verse-lab/veil).
