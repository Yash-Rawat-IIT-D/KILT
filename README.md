# KILT — Kripke in Lean Toolkit

A semester project for **COL876: Special Topics in Formal Methods**, by
**Yash Rawat (2023CS50334)**. KILT aims to build a verified LTL model-checking
toolkit in Lean 4, connecting trace semantics, Büchi automata, finite Kripke
structures, and kernel-checked correctness proofs.

For example, `G(request → F grant)` expresses that every request is eventually
followed by a grant.

## Project scope

The intended contribution is a reusable, CSLib-oriented path from a **bounded
LTL fragment** to a verified model-checking result:

1. Define the formula interface, trace semantics, and Kripke execution model.
2. Translate the selected fragment to Büchi or generalized Büchi automata.
3. Construct the system/property product and an executable accepting-run
   emptiness check.
4. Prove the correspondence between the checker and the declared semantics.
5. Demonstrate representative safety and liveness properties and document the
   design, trust boundary, and limitations.

The supported fragment and exact reuse boundary will be chosen after an API
audit. LeanLTL is prior work and a semantic comparison point; a compatibility
theorem is a goal where feasible. CSLib supplies the intended automata
foundations. LeanearTemporalLogic and Veil are also part of the initial audit.
A Lean frontend is a stretch goal; proof-producing automation and CTL* are
optional extensions after the verified core.

**Current status:** repository scaffold only. The checker and correctness
proofs are not implemented yet. The initial package uses Lean's standard
library; external dependencies will be added and pinned after the audit.

## Getting started

Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager,
and optionally the Lean 4 VS Code extension. From this repository:

```sh
lake build
```

The toolchain is pinned in `lean-toolchain` to **Lean 4.32.1**, matching the
current local course setup. The default build checks both the `KILT` library
and the `Examples` library. To build just the core:

```sh
lake build KILT
```

Open this folder in VS Code to use the pinned toolchain. See
[CONTRIBUTING.md](CONTRIBUTING.md) for the development workflow.

## Repository layout

```text
KILT.lean               Public library entry point
KILT/                   Library definitions and proofs
Examples.lean           Example entry point
Examples/               Worked examples and regression cases
Proposal/               Original project proposal (LaTeX and PDF)
lakefile.toml           Lake package and build targets
lean-toolchain          Pinned Lean version
lake-manifest.json      Lake dependency lockfile
.github/workflows/      Automated build on pushes and pull requests
```

As the design settles, library modules can cover LTL semantics, Kripke
structures, automata translation, product/emptiness algorithms, and correctness.

## Planned milestones

The [proposal](Proposal/KILT_Proposal-1.pdf) sets out this semester's plan:

| Period (2026) | Primary focus |
| --- | --- |
| 24–30 September | Literature/API audit, setup, scoped design |
| 1–14 October | LTL semantics, Kripke executions, Büchi interface and translation |
| 15–31 October | Product construction, emptiness, central correctness theorem |
| 1–15 November | Verified examples, evaluation, write-up; frontend if time permits |

Semantic correspondence and the verified checker take priority over extensions.
The full scope and schedule are in the [LaTeX proposal](Proposal/KILT_Proposal.tex).

## References from the proposal

- [LeanLTL](https://github.com/UCSCFormalMethods/LeanLTL) and its
  [ITP 2025 paper](https://doi.org/10.4230/LIPIcs.ITP.2025.37).
- [CSLib](https://github.com/leanprover/cslib).
- [Automata Theory in Lean](https://github.com/ctchou/AutomataTheory).
- [LeanearTemporalLogic](https://github.com/mrigankpawagi/LeanearTemporalLogic).
- [Veil](https://github.com/verse-lab/veil).
