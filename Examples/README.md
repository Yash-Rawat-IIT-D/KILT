# Examples and checks

Start with [the frontend demo](Demos/Frontend.lean) for the shortest session,
or [the walkthrough](Demos/Walkthrough.lean) for setup, direct semantic proofs,
computed verdicts and the returned lasso's own infinite trace.

| Directory | Purpose | Suggested reading |
| --- | --- | --- |
| `Demos/` | Small end-to-end user sessions | `Frontend`, then `Walkthrough` |
| `Models/` | Worked transition systems, assumptions and properties | `RequestGrant`, `TrafficLight`, `TwoThreadLock` |
| `Theory/` | Syntax, infinite-word semantics and compiler constructions | `Syntax`, `Words`, `SemanticLaws`, `Normalization`, `GeneralizedBuchi`, `Tableau`, `Translation` |
| `Regression/` | Boundary cases, execution tests, refinement checks and axiom audits | `FrontendRegression`, `Checker`, `Counterexample`, then graph/storage cases |

These groups describe the main purpose of each file. Model and theory examples
also contain checked propositions; regressions reuse their fixtures. A focused
group build therefore checks its dependencies too. `Regression/BuchiTrust.lean`
audits named theorem dependencies against the standard-axiom allowlist.

## Building and running

Run from the repository root:

```bash
# All examples, regression executions and axiom audits.
LEAN_NUM_THREADS=1 ./scripts/verify-examples.sh --verbose

# Focus on one group (substitute Models, Theory or Regression as needed).
GUI_LAUNCH=false LEAN_NUM_THREADS=1 ./scripts/build.sh Examples.Demos

# One module and its dependencies.
GUI_LAUNCH=false LEAN_NUM_THREADS=1 ./scripts/build.sh Examples.Demos.Frontend

# Rerun its displays after building the library.
LEAN_NUM_THREADS=1 lake env lean Examples/Demos/Frontend.lean

# Full library plus all four example groups.
GUI_LAUNCH=false LEAN_NUM_THREADS=1 ./scripts/build.sh --with-examples --verbose
```

`Examples.lean` imports every group. Core-only `scripts/build.sh` builds do not
run this suite. Lake can replay cached display output without rerunning its
execution; use `verify-examples.sh --rebuild` when a fresh execution of all
project modules is required. `#eval` displays are execution evidence; theorem
declarations are kernel-checked proofs.

## Imports and declaration names

Files are grouped by purpose, while their existing declaration namespaces are
preserved. For example:

```lean
import Examples.Models.TrafficLight

open Examples.TrafficLight
```

The import identifies the file; `Examples.TrafficLight.controller` still names
the same model. Existing flat module imports must use their new category; there
are no forwarding files duplicating the old layout.

For new work, put user sessions in `Demos/`, system case studies in `Models/`,
conceptual worked examples in `Theory/`, and automated boundary/refinement
checks in `Regression/`. Add the module to that group's umbrella so the full
suite includes it. Keep reusable library definitions under `KILT/`.
