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
Plain `lake build` checks both the `KILT` and `Examples` libraries. Our build
script defaults to the core library so routine builds skip the demos. To build
just the core with Lake:

```sh
lake build KILT
```

To build while saving the terminal output:

```sh
./scripts/build.sh                # Open the terminal menu by default
GUI_LAUNCH=false ./scripts/build.sh  # Build the KILT library only
./scripts/build.sh --gui          # Open the menu even if GUI_LAUNCH=false
./scripts/build.sh --verbose      # Open the menu with verbose output enabled
./scripts/build.sh --with-examples  # Build KILT and verify all examples
./scripts/verify-examples.sh      # Verify examples, proofs, execution tests and audits
./scripts/verify-examples.sh --verbose  # Same checks with verbose logged commands
./scripts/build.sh --rebuild      # Clean KILT outputs, then build again
./scripts/build.sh --clean        # Remove KILT outputs; keep logs
./scripts/build.sh --clean-logs   # Remove script build logs
./scripts/build.sh --clean-all    # Remove KILT outputs and script logs
./scripts/build.sh --help         # Show options and examples
```

`verify-examples.sh` always runs directly, even when `GUI_LAUNCH=true`. It
uses the same logging and exit-status handling as `build.sh`. Lake reuses
up-to-date modules; use `./scripts/verify-examples.sh --rebuild --verbose` to
clean project outputs and rerun the examples and audits. Dependency caches
are retained. The full regression build remains available through plain
`lake build` or `./scripts/build.sh --with-examples`.

Each run saves a timestamped log under `.lake/logs/`, with the latest available
at `.lake/logs/latest.log`. The script returns the build's exit status and
defaults to one Lean thread; use `LEAN_NUM_THREADS=2 ./scripts/build.sh` to change it.
Build logs remain excluded from Git with the other `.lake` outputs.
Terminal output highlights successful steps in green, timestamps and durations
in yellow, and failures in red. The total duration is shown in minutes and
seconds. Saved logs stay plain text; set `NO_COLOR=1` to disable terminal colors.
Cleanup preserves downloaded dependencies and their compiled caches. Cleanup
options run without building; `--rebuild` cleans first and then builds.

The optional menu uses `whiptail` (on Ubuntu, install with
`sudo apt install whiptail`). The launch page has four entries: **Build**,
**Build with examples**, **Clean**, and **Help**. Each build submenu offers
normal/verbose builds, rebuilds, logs and documentation. Use arrow keys, Tab
and Enter; Esc goes back or exits. `GUI_LAUNCH` defaults to `true`, so running without a target
or cleanup mode opens the menu. With `GUI_LAUNCH=false`, the script builds
directly unless `--gui` is supplied. Explicit targets and cleanup modes run
directly, and command-line builds do not require `whiptail`.

Documentation remains available inside the build submenus. The equivalent commands are:

```sh
./scripts/docs.sh --setup          # Fetch the pinned doc-gen4 dependency once
./scripts/docs.sh                  # Build KILT and Examples API documentation
./scripts/docs.sh KILT             # Build library documentation only
./scripts/docs.sh --rebuild        # Clean generated documentation, then rebuild
./scripts/docs.sh --serve          # Preview the generated site locally
./scripts/docs.sh --status         # Show setup, output, and latest-log status
./scripts/docs.sh --clean          # Remove generated docs; keep dependencies/logs
./scripts/docs.sh --help           # Show all documentation options
```

The generated site is under `docbuild/.lake/build/doc/`, and documentation logs
are stored alongside build logs under `.lake/logs/`. The first build also
generates pages for imported Lean and Mathlib modules, so later incremental
builds are much faster. Generated HTML and compiled documentation outputs are
excluded from Git.

Open this folder in VS Code to use the pinned toolchain. See
[CONTRIBUTING.md](CONTRIBUTING.md) for the development workflow.

## Generalized Büchi conversion

`FiniteGeneralizedBuchi` supports several recurring acceptance obligations and
an executable, language-preserving `toFiniteBuchi` conversion. Empty families,
partial transitions and unrestricted symbol types are supported. See
`Examples/GeneralizedBuchi.lean` for counter traces and traffic-colour recurrence
through the existing accepted-path backend. The formula compiler below reuses
this conversion.

## Verified Büchi backend

The library includes finite Büchi automata with symbol-driven successors,
verified accepting-cycle search, and a finite Kripke/property-automaton product.
`FiniteKripke.checkAgainst` checks a supplied violation automaton; its correctness
theorem connects the Boolean verdict to universal LTL satisfaction, given a
seriality proof and the automaton's language specification.

Handwritten automata cover eventuality and response violations. General LTL
formula-input checking is available through `FiniteKripke.check`. See
[design notes](docs/design.md) for contracts, assumptions, and limitations. Check the examples with:

```sh
lake build Examples.Buchi Examples.BuchiTrust
```

The default build also runs these examples and rejects unexpected axioms in
their principal correctness results.

For a complete worked example, read
[TrafficLight.lean](Examples/TrafficLight.lean) from top to bottom: colour
valuations, finite controllers, infinite paths and words, safety and next-step
proofs, reachability/routes, then verified eventuality and response checks.
The red → green → yellow controller passes; a variant that can stay red
forever preserves colour safety but fails progress. An explicit all-red path
explains the failure. These examples run in the default build.

The formula compiler foundation now includes negation normal form and a
verified finite subformula closure. Normalization preserves truth at every
word position, including negated formulas. Read
[Normalization.lean](Examples/Normalization.lean) for the response-formula
walkthrough, until/release duality, and transfer of traffic-light proofs.
The tableau now includes until acceptance sets and full language correctness.
[Compile.lean](KILT/LTL/Compile.lean) exposes `Formula.toBuchi`: an executable
finite automaton whose `.toCSLib` adapter accepts exactly the satisfying words,
proved by `Formula.toBuchi_accepts`. Only decidable atom equality is required.
Read [Tableau.lean](Examples/Tableau.lean) for local rules, then
[Translation.lean](Examples/Translation.lean) for acceptance, compilation, and
comparisons with the handwritten monitors. This explicit construction enumerates
exponentially many candidate states; examples intentionally stay small.
`FiniteKripke.check` compiles violations and uses the verified product search.
Its `check_correct` theorem connects a true verdict to universal satisfaction;
`check_eq_false_iff` connects false to existence of an initial violating path.
For example:

```lean
import KILT
import Examples.TrafficLight

open Examples.TrafficLight

#eval controller.check eventuallyGreen controller_serial -- true

example (h : controller.check eventuallyGreen controller_serial = true) :
    controller.toKripke.Satisfies eventuallyGreen :=
  (controller.check_correct eventuallyGreen controller_serial).mp h
```

The seriality argument is an explicit precondition. `#eval` executes the check;
a proof of its Boolean verdict is needed to derive a theorem as above.
[Checker.lean](Examples/Checker.lean) combines small kernel-computed proofs with
build-failing execution tests for larger request/grant and traffic properties.
Compiled outputs are not treated as proofs. Search caches successors within each
invocation and stops at fixed points, target discovery and the first accepting
cycle. The explicit tableau construction still has exponential size.
False verdicts establish counterexample existence. The separate
`counterexample?` API below extracts a lasso describing a violating path.

## Two-thread lock example

[TwoThreadLock.lean](Examples/TwoThreadLock.lean) models two interleaved threads
sharing a lock bit. A split check/claim permits both threads into the critical
section; atomic test-and-acquire preserves mutual exclusion on every initial
path. Without scheduler fairness, a requesting thread can still starve. The
example includes explicit infinite schedules, LTL proofs, finite reachability
counts, and the existing verified response monitor. Future extensions can add
turn-taking or a Peterson protocol.

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
docbuild/               Pinned doc-gen4 project for local API documentation
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

## Counterexamples

`M.counterexample? φ hserial order` returns `none` when every initial infinite
path satisfies `φ`, or a product-state lasso when a violating path exists.
The model order makes witness selection deterministic; the compiler order is
generated internally. For example:

```lean
import KILT
import Examples.TrafficLight
open KILT Examples.TrafficLight

-- The traffic example already provides phaseOrder : Graph.Enumeration Phase.
#eval (stuckController.counterexample? eventuallyGreen
  stuckController_serial phaseOrder).map fun l =>
    let system := l.map Prod.fst
    (system.prefix, system.loop)
```

Read the result as a prefix followed by the loop repeated forever. The loop is
nonempty and omits its duplicate closing state. `counterexample?_sound` proves
that the returned trace itself is initial and violates the formula;
`counterexample?_eq_none_iff` relates absence to universal satisfaction.
`#eval` displays computed data; it does not itself create a theorem.
See [the worked examples](Examples/Counterexample.lean) for request/grant,
traffic and monitor-based two-thread lock witnesses.

## Shared prepared checking

Supply the model's order and seriality proof once. Preparing a property bundles
its compiled violation automaton and enumeration with one reachable product,
accepting mask and dense witness order. Both queries consume that prepared value:

```lean
import KILT
import Examples.Buchi

open KILT Examples

#eval do
  let runner := Buchi.waitingSystem.checker Buchi.waitingSerial
    (Graph.Enumeration.ofList [.waiting, .granting] (by intro s; cases s <;> simp))
  let problem := runner.prepare RequestGrant.response
  let verdict := problem.check
  let witness := problem.counterexample?
  IO.println (verdict, witness.map fun l => (l.prefix.length, l.loop.length))
-- (false, some (0, 1)): waiting forever violates the response property.
```

`problem.check_correct` connects its Boolean verdict to universal satisfaction.
`problem.counterexample?_sound` proves that its returned trace itself violates
the property; `problem.counterexamplePath` converts that result to a Kripke path.
`systemCounterexample?` provides a system-state lasso view. For an already
returned product lasso, `lasso.map Prod.fst` projects it without another search.

To reuse compilation across models, compile `(Formula.neg property).compile`
once and pass the bundle to each runner's `prepareCompiled`. Its fields are
`automaton`, `order`, and the proved `accepts_iff`. A concrete model can also
derive its `Fintype` instance from its complete `stateOrder.fintype`; this helper
is explicit and introduces no generic instance-search cycle.

Preparation is shared within one evaluation/program. Query results are not
memoized, and separate `#eval` commands do not share a runtime cache. Boolean
queries retain their visited-array search; witness queries use parent storage
and perform no Boolean precheck. Existing `M.check`, `M.checkWithOrder`, and
`M.counterexample?` signatures remain available as one-shot wrappers. See
[prepared checking examples](Examples/PreparedChecking.lean).

## Finite graph backend

The graph layer prepares seed-reachable adjacency arrays, uses Boolean visited
frontiers for return queries, and reconstructs witnesses from parent IDs and
depths. `FiniteGraph` is the bounded-ID representation. The ordinary `check`
API uses this backend. To supply an explicit model-state order:

```lean
#eval M.checkWithOrder property serialProof modelOrder
```

`checkWithOrder_eq_check` proves identical verdicts for every complete order.
`counterexample?` retains its existing arguments and deterministic witness
selection. Mathematical recurrences under `KILT/Graph/Specification` state the
reachability and route-selection contracts; cached association-list and stored
full-route implementations have been removed. See
[graph regressions](Examples/GraphStorage.lean) and [design notes](docs/design.md).

## Measuring search performance

```bash
./scripts/verify-examples.sh --verbose
./scripts/benchmark-graph.sh                 # Three fresh runs per mode
./scripts/benchmark-graph.sh --mode native    # Native executable only
```

The optional harness measures canonical preparation, search, reconstruction and
formula checking, validating verdict agreement, selected routes and finite lasso
certificates. Compilation precedes measurement; logs include latency medians,
ranges and whole-process RSS. Phase timings are independent measurements, not
an additive breakdown. Benchmarks remain separate from ordinary builds.
Historical cached/indexed comparisons describe earlier revisions; their timings
must not be presented as fresh results for later refactors.

For graph-level route queries, `g.parentForest order seeds` returns complete
parent information and `forest.route? target` reconstructs a route. A stopped
query uses `g.parentsTo order seeds target` and `result.route?`; it has a distinct
result type. Raw refinement engines live under `FiniteGraph.Internal`.
`Graph.Enumeration` is independent of route specifications. See
[the design notes](docs/design.md#production-searches-and-proof-interfaces).
