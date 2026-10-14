# FiniteKripke, verified reachability, and witness routes

## Summary and locked decisions

Build an executable finite-model layer over the existing Kripke semantics, then stop for your code-reading break.

The selected design is:

- An enumerable finite state type with decidable equality.
- Initial states and successors represented by `Finset`.
- A generic reachability engine reusable by future automata products.
- Repeated set expansion, bounded by the number of states.
- Executable witness routes, with validity and completeness proofs.
- An explicit, complete, duplicate-free state list to choose between witnesses.
- Both global and reachable-deadlock diagnostics.
- Agent-run targeted checks and a final logged build.

Keep atom types unrestricted, initial sets nonempty, transitions potentially partial, and fairness absent. The first checker’s global seriality requirement remains unchanged. Büchi construction, accepting-cycle search, and shortest-route guarantees are later work.

## Interfaces and execution

**Finite models.** Add `FiniteKripke State AP`, using `[Fintype State]` and `[DecidableEq State]`, with:

```lean
initials         : Finset State
initials_nonempty : initials.Nonempty
successors       : State → Finset State
label            : State → LTL.Valuation AP
```

Provide `toKripke` with initial membership and successor membership as its predicates. Prove the corresponding initial, transition, and label equations. Existing path, satisfaction, and CSLib bridge APIs then apply through this adapter.

**Generic reachability.** Accept arbitrary seed and successor sets, independently of labels or Kripke models. Define mathematical reachability using `Relation.ReflTransGen`, including zero-step reachability from each seed.

Compute:

```text
R₀     = seeds
Rₖ₊₁   = Rₖ ∪ ⋃ s ∈ Rₖ, successors s
result = R at round Fintype.card State
```

Prove monotonicity, stability by the cardinality bound, and:

```text
t ∈ result ↔ t is mathematically reachable from a seed
```

Use the cardinality argument rather than requiring shortest-path results. The generic engine permits empty seeds; FiniteKripke retains its nonempty-initial invariant.

**Witness routes.** Define a separate enumeration record containing a state list, a no-duplicates proof, and a completeness proof. Require it only for route computation.

Use a route table `State → Option (List State)`:

- Round zero assigns `[s]` to each seed.
- Each subsequent round retains existing routes.
- For an undiscovered target, scan the enumeration for the first predecessor with a route in the previous round and an edge to the target.
- Append the target to that predecessor’s route.
- Run the same cardinality-bounded number of rounds.

Prove that the table’s discovered states agree with set expansion at every round. Expose route lookup with these guarantees:

- A returned route is nonempty, starts at a seed, ends at the requested state, and follows valid transitions.
- Lookup returns a route exactly when the target is reachable.
- Changing enumeration order preserves reachable membership, although the selected witness may differ.

Executable definitions must use supplied enumeration and equality operations; no classical selection or `noncomputable` definitions in the execution path. Classical reasoning remains permitted in correctness proofs.

## Diagnostics and semantic preservation

Expose the finite set of all deadlocks, the finite set of reachable deadlocks, and Boolean checks for their absence.

Prove:

- Global deadlock absence is equivalent to `toKripke.Serial`.
- Reachable-deadlock absence means every reachable state has a successor.
- Every state on an initial infinite path belongs to the computed reachable set.

Deadlock checks report facts without changing transitions. No implicit self-loops or automatic rejection belongs in the model representation.

Add finite versions of the existing cycle, waiting-loop, and deadlocked models. Prove their adapters equal the existing relational models, allowing the current response-property and counterexample theorems to transfer without duplicating their temporal proofs.

Finite reachability includes a deadlocked initial state via a zero-step route. Document why this differs from the absence of infinite initial paths and the resulting vacuous LTL satisfaction.

## Verification and learning handoff

Use small executable examples and kernel-checked propositions covering:

- Empty seeds in the generic engine.
- Multiple initial states.
- A chain, branching and merging routes, cycles, and self-loops.
- An unreachable component.
- Reachable and unreachable deadlocks.
- A one-state deadlock: reachable with route `[s]`, but no infinite path.
- Two enumeration orders selecting different valid routes while producing the same reachable set.
- An unrestricted atom type such as `Nat`.
- Preservation of the existing request/grant semantics.

Use `#eval` for readable demonstrations and `decide` for concrete assertions where suitable. Verify the general correctness theorems and inspect their axiom reports; require no admitted proofs or `sorryAx`.

Run targeted checks with one Lean thread, followed by:

```bash
GUI_LAUNCH=false LEAN_NUM_THREADS=1 ./scripts/build.sh --verbose
```

The handoff should explain one expansion trace and one witness-route proof in plain language. Include a suggested reading sequence: finite data → semantic adapter → expansion invariant → witness invariant → diagnostics. Mark your mathematical review separately from build verification, and stop before starting the next algorithm.

## Records and implementation boundaries

When implementation mode begins:

- Append every selected choice, rejected alternative, rationale, and consequence to `.ai/DESIGN_DECISIONS.md`.
- Replace `.ai/CURRENT.md` with this milestone’s plan and live status, retaining a concise record of the completed Kripke milestone and its build evidence.
- Update TODO and PROGRESS to place finite models and reachability before Büchi translation; record exact theorem names, build evidence, outstanding work, and the reading checkpoint.
- Update public design notes with executable contracts and limitations.

Organize finite models under the Kripke layer and the reusable reachability engine under a separate graph layer. Preserve dependency pins and unrelated edits. Make no commit or push.

The earlier 40-minute implementation window has ended; it is not carried forward as this milestone’s deadline. No files have been changed during this planning turn.
