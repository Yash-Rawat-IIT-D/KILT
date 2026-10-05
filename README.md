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

The toolchain is pinned in `lean-toolchain` to **Lean 4.32.1**.
The default build checks both the `KILT` library
and the `Examples` library. To build just the core:

```sh
lake build KILT
```

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
