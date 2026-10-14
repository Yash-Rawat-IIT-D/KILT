# KILT design notes

## Scope through 18 October

KILT first defines a small LTL syntax over named atomic propositions and its
infinite-word semantics.  A Kripke path produces a word of Boolean valuations;
a Kripke model satisfies a formula when every initial path satisfies that word
formula at position zero.  This establishes the semantic interface needed by a
later automata translation and finite-state checker.

The implemented constructor basis is falsehood, atomic propositions, negation,
disjunction, next, and strong until. Truth, conjunction, implication,
eventually, globally, and release are derived. The first model semantics
does not include fairness. Deadlocks are allowed and seriality is an explicit
predicate rather than an implicit convention.

## Implemented LTL interface

`KILT.LTL.Formula AP` stores named atoms of type `AP`. Syntax and semantics
require neither a finite atom type nor decidable atom equality. Formulas have
decidable equality when atoms do, and `Formula.size` counts constructor nodes
after expanding derived operators.

Enable the formula shorthand with `open scoped KILT.LTL`:

| Notation | Formula |
| --- | --- |
| `□ p` | `Formula.globally p` |
| `◇ p` | `Formula.eventually p` |
| `𝒩 p` | `Formula.next p` |
| `p 𝒰 q` | `Formula.until p q` |
| `¬ₗ p` | `Formula.neg p` |
| `p ∧ₗ q` | `Formula.conj p q` |
| `p ∨ₗ q` | `Formula.disj p q` |
| `p ⟹ q` | `Formula.imp p q` |

Unary operators have precedence 75, until 60, conjunction 35, disjunction 30,
and implication 25. All binary operators associate to the right. Thus
`𝒩 p 𝒰 ◇ q` means `(𝒩 p) 𝒰 (◇ q)`. For the response property, write
`□ (request ⟹ ◇ grant)`. The shorthands expand to the same formula definitions,
so the existing semantics and laws apply directly. Ordinary Lean `→`, `∧`,
`∨`, and `¬` continue to express propositions in proofs.

`Valuation AP` is `AP → Bool`. `Word AP` is
`Cslib.ωSequence (Valuation AP)`, so CSLib's sequence operations are available
without an adapter. `Sat word i φ` interprets the formula at position `i`,
and `WordSat word φ` abbreviates satisfaction at zero.

| Constructor | Meaning at position `i` |
| --- | --- |
| `falsehood` | False |
| `atom a` | `word i a = true` |
| `neg φ` | `φ` does not hold at `i` |
| `disj φ ψ` | `φ` or `ψ` holds at `i` |
| `next φ` | `φ` holds at `i + 1` |
| `until φ ψ` | Some `j ≥ i` satisfies `ψ`, and every `k` with `i ≤ k < j` satisfies `φ` |

Until and eventually permit a witness at the current position. Release is
defined by the dual `¬(¬φ U ¬ψ)`, so the right operand may hold forever without
the left operand ever holding. Satisfaction is a structurally recursive
mathematical proposition. Executable translation and model checking remain
later work; no decision procedure for arbitrary infinite words is assumed.

`Examples.Syntax` checks formula equality, connective expansion, and size.
`Examples.Words` checks constant and alternating words, immediate and later
until witnesses, required left prefixes, and unsatisfied eventualities.
`Examples.Integration` checks CSLib's sequence, run, and indexed-product APIs.
`Examples.SemanticLaws` exercises the reusable laws, suffix offsets, until
unfolding, release boundaries, and satisfying/violating request/grant words.
These modules are imported by `Examples.lean` for checking with `lake build`.

## Semantic-law interface

`KILT.LTL.Basic` supplies simplification lemmas for atoms, falsehood, negation,
disjunction, next, truth, conjunction, implication, eventually, and globally.
The named lemmas `sat_until_now` and `sat_eventually_now` express satisfaction
with a witness at the current position.

`sat_until_unfold` says that `left U right` holds at `i` precisely when `right`
holds now, or `left` holds now and the until formula holds at `i + 1`. It is not
a simplification rule because unfolding repeatedly would generate more next
obligations. This law does not make indefinitely postponing `right` valid.

`sat_release` characterizes `left R right`: at every `j ≥ i`, if `left` was
false throughout `[i, j)`, then `right` holds at `j`. In particular, `right`
must hold at the first position where `left` holds; afterward it may be false.
If `left` never holds, `right` must hold forever.

`sat_drop word n i formula` relates satisfaction on `word.drop n` at `i` to
satisfaction on `word` at `n + i`. Its proof handles arbitrary temporal
formulas, including until, by translating witnesses and prefix intervals.
`wordSat_drop` specializes this correspondence to position zero on the suffix.

## Module boundaries

`KILT.LTL` is independent of the state type of a Kripke structure.
`KILT.Kripke` consumes the LTL interface to map paths to valuation words and
state model satisfaction. The `KILT.Automata.Kripke` module consumes both
interfaces and exposes the CSLib encoding as methods in `KILT.Kripke`. This
direction prevents an automata encoding from changing the underlying temporal
semantics.

## Kripke execution semantics

`KILT.Kripke State AP` is a generic relational model. It contains an initial
predicate, a proof that at least one initial state exists, a step relation, and
a Boolean valuation for each state. The definition has no finiteness or
decidability requirements. Those belong to the later executable checker.

Transitions may be partial. `Kripke.Serial M` separately means that every state
has a successor. Under seriality, `Path.fromState` uses classical choice to
construct an infinite path from any state, and `Path.exists_initial` combines
that construction with the model's nonempty initial set. This is a semantic
existence result rather than an executable successor-selection algorithm.

`Kripke.Path M` contains a CSLib infinite state sequence and a proof that each
state steps to the next. `Path.IsInitial` is separate from this record. Thus
`Path.drop n` always remains a valid path, while `Path.drop_isInitial` states
that the suffix is initial exactly when its state at the cut belongs to the
model's initial set.

`Path.word` maps the model label over the state sequence. Its position zero is
the label of the path's first state. `Path.word_drop` proves that observation
commutes with dropping a prefix, and `Path.wordSat_drop` connects that fact to
the existing indexed LTL suffix theorem.

`M.Satisfies formula` quantifies over every infinite initial path. No fairness
filter is applied. If a partial model has no infinite initial path, the
universal proposition is vacuously true even though the model has a nonempty
initial set. `Examples.RequestGrant.deadlock_satisfies_vacuously` records this
boundary explicitly. Meaningful examples establish seriality separately.

## CSLib run encoding

`M.toNA` represents a Kripke model as a CSLib nondeterministic automaton whose
states are model states and whose symbols are valuations. It preserves the
initial predicate and defines a transition by

```text
Tr s valuation t  iff  M.step s t and valuation = M.label s.
```

The source-state label convention makes automaton symbol zero equal to the
initial state's observation. `toNA_run_iff` characterizes an arbitrary run by
an initial first state, valid adjacent steps, and equality of its word with the
state sequence mapped through the model label. `path_run_iff` specializes this
to a valid path's own observation word. `satisfies_iff_all_runs` proves that
Kripke satisfaction is equivalent to satisfaction of every word carried by a
run of this encoding. These theorems do not assume seriality; they characterize
the runs that actually exist.

`Examples.RequestGrant` contains a serial two-state cycle. Waiting states label
`request`, granting states label `grant`, and every request is followed by a
grant at the next position. Its negative variant adds a waiting self-loop. The
constant waiting path violates `□ (request ⟹ ◇ grant)`, because KILT makes no
fairness assumption that would force the enabled granting transition to occur.

These results are a semantic bridge. They do not yet translate LTL formulas to
Büchi automata or search a finite graph for counterexamples.

## Finite models and executable reachability

`KILT.FiniteKripke State AP` is the executable model layer. It requires
`Fintype State` and `DecidableEq State`, stores initial states and successors
as `Finset`s, and keeps the atom type unrestricted. `FiniteKripke.toKripke`
forgets this storage representation and produces the existing relational
semantics. Its initial, step, and label equations are definitional contracts,
so paths, satisfaction, and the CSLib bridge apply without a second semantics.

`KILT.Graph` contains graph algorithms independently of state labels. Starting
from any finite seed set, `layers` repeatedly takes the union of the discovered
states and all their successors. `reachableSet` executes
`Fintype.card State` rounds. `mem_layers_iff` characterizes every intermediate
round using a bounded finite route, while `mem_reachableSet_iff` proves that
the final set is exactly reflexive-transitive reachability from a seed.
Zero-step reachability is intentional: every seed is reachable from itself.

Witness lookup uses a `RouteTable State`, a function assigning at most one
route to each state. Round zero assigns `[s]` to each seed. At the next round,
an existing route is retained; an undiscovered target scans a caller-supplied
`Graph.Enumeration` for the first predecessor discovered in the preceding
round and appends the target. The enumeration is explicit, complete, and
duplicate-free. `routeTables_isSome_iff_mem_layers` proves the table and set
expansion discover the same states at every round. `route?_sound` proves a
returned list is nonempty, begins at a seed, ends at the requested state, and
follows successor edges. `route?_isSome_iff` proves lookup succeeds exactly on
reachable targets. Enumeration order may select a different valid witness;
it cannot change reachable membership. No shortest-route guarantee is made.

`FiniteKripke.deadlocks` reports all states with no successors, and
`reachableDeadlocks` restricts the report to computed reachable states.
`isSerial_eq_true_iff` connects the global Boolean diagnostic to relational
`Kripke.Serial`. `hasNoReachableDeadlocks_eq_true_iff` characterizes the
reachable-only diagnostic. Neither operation changes the transition system.
`path_state_mem_reachableSet` additionally proves that every position of an
initial infinite path appears in the computed reachable set.

`Examples.FiniteKripke` covers empty and multiple seed sets, branching and
merging routes, a self-loop, an unreachable component, reachable and
unreachable deadlocks, and two traversal orders that return different routes
to the same target. Its labels use `Nat` atoms to demonstrate that atoms need
not be finite. Finite request/grant adapters are proved equal to the existing
relational models, so their temporal proofs transfer unchanged.

A one-state deadlock illustrates two distinct claims. It is finitely reachable
and has the zero-step route `[()]`, but it has no infinite path. Consequently,
universal infinite-path LTL satisfaction remains vacuous for that model.
Reachability does not repair this semantic boundary; the seriality diagnostics
make it visible to a future checker.

## Sources and attribution

KILT pins [CSLib at `a3da622f14ac47924a4ffb293fdb0dad6fcdfae1`](https://github.com/leanprover/cslib/tree/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1)
and imports its infinite-sequence infrastructure. The dependency lockfile
preserves CSLib's Mathlib revision `1f414401f69059aa7eead47b53ee40bd38455eeb`
and its transitive dependency revisions. Both use Lean `v4.35.0-rc4`.
The Kripke bridge imports CSLib's
[nondeterministic automaton and run definitions](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Basic.lean)
and its
[infinite execution relation](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean)
directly rather than copying them.

KILT's LTL definitions and examples are independently written standard LTL.
The separation of syntax and trace semantics is informed by
[LeanLTL's LTL module](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Logics/LTL.lean)
and [temporal definitions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Defs.lean).
No LeanLTL source was copied, and semantic equivalence with that library has
not yet been proved. See the [source audit](audit.md) for upstream API details
and reuse considerations.
