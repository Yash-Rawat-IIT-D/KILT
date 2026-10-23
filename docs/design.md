# KILT design notes

## Semantic foundation and the 22 October backend

KILT first defines a small LTL syntax over named atomic propositions and its
infinite-word semantics.  A Kripke path produces a word of Boolean valuations;
a Kripke model satisfies a formula when every initial path satisfies that word
formula at position zero.  This establishes the semantic interface needed by a
automata translation and finite-state checking. The finite Büchi backend now
checks supplied violation automata; general formula translation remains later
work.

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
mathematical proposition. General executable translation remains later work;
the finite backend below checks supplied automata, without assuming a decision
procedure for arbitrary infinite words.

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

These bridge results do not themselves translate LTL formulas. The finite
backend below adds acceptance search while reusing these conventions.

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
make it visible to the property-checking interface.

## Finite Büchi backend

`Automata.FiniteBuchi Q Symbol` stores finite initial and accepting state sets
and `successors : Q → Symbol → Finset Q`. Only states require `Fintype` and
decidable equality. Symbols and atom identifiers stay unrestricted; the product
evaluates actual model valuations instead of enumerating all possible ones.
Empty state types, empty initials, empty acceptance, and missing transitions
are allowed. `toBuchi` preserves this data as CSLib predicates.

`Graph.HasAcceptingRun` requires an infinite initial sequence with valid edges
and accepting visits arbitrarily late. `HasAcceptingCycle` requires a reachable
accepting state `q` with a positive-length return path. The executable
`hasAcceptingCycle` filters reachable accepting states by membership of `q` in
`reachableSet (successors q) successors`. Starting the second search from
successors is essential: zero-step reachability alone would incorrectly accept
a deadlock. Both `hasAcceptingCycle_eq_true_iff` and
`hasAcceptingCycle_iff_hasAcceptingRun` are proved.

The infinite-run proof uses finite-state recurrence in one direction and
CSLib execution concatenation in the other. These are semantic existence
proofs; the executable search uses finite sets and the existing bounded
reachability algorithm. It repeats reachability for candidate accepting states;
it is not an SCC implementation, and it returns no executable lasso.

## Product and property-checking contract

`FiniteKripke.productInitials`, `productSuccessors`, and `productAccepting`
describe graph data on system/automaton pairs. A transition from `(s, q)` takes
a system successor of `s` and an automaton successor of `q` on `M.label s`.
Thus the automaton consumes the initial valuation on the first edge. Only the
automaton component determines acceptance. Product starts may be empty, so the
product does not reuse the nonempty-initial Kripke record.

`product_run_iff` characterizes compatible runs. `hasAcceptedPath_eq_true_iff`
proves that the Boolean accepted-path search succeeds exactly when some initial
system path's word is accepted by the supplied automaton. Neither theorem
requires seriality. An accepting product deadlock has no infinite execution.

`M.checkAgainst A hserial` returns the negation of accepted-path existence and
requires a proof of global `M.toKripke.Serial`. Its principal theorem,
`checkAgainst_correct`, additionally requires a language specification:

```text
for every word, A accepts word iff the word violates formula
```

Under that specification, a true result is equivalent to
`M.toKripke.Satisfies formula`. No fairness is added, no deadlocks are repaired,
and no arbitrary formula is automatically compiled. The generic backend still
supports partial graphs; seriality is the public checker precondition.

## Handwritten languages and regression checks

`Automata.Monitors` supplies three proved constructions: `eventually q`,
`notEventually q`, and `notResponse p q`. The two-state `guessAndStay` helper
nondeterministically selects a triggering position, then maintains an obligation
forever. Its accepting commitment begins at the next state. Response violation
therefore checks `p ∧ ¬q` at the trigger and `¬q` at all later positions. A grant
at the request position already answers that request.

`Examples.Buchi` checks the existing alternating and waiting-loop systems and
derives semantic theorems from their computed verdicts. Further cases cover an
initial-only grant, no requests, simultaneous request/grant, delayed grants,
permanent waiting, and a violation after a prefix. Their atom type can be `Nat`.
`Examples.BuchiGraph` checks empty graphs, accepting deadlocks, self-loops,
transient acceptance, unreachable cycles, and nondeterministic acceptance.

New concrete assertions use kernel checking, while earlier `native_decide`
examples remain unchanged. `Examples.BuchiTrust` runs a build-failing transitive
axiom audit on principal new results and selected existing contracts. It allows
only `propext`, `Classical.choice`, and `Quot.sound`, and rejects missing
declarations, unfinished-proof dependencies, and additional axioms. All three
new example modules are included in the default build and existing CI.

## Normalization and finite subformulas

`LTL.NNF` makes truth/falsehood, literal polarity, conjunction/disjunction,
next, strong until and release explicit. It has no arbitrary negation node.
`NNF.toFormula` embeds it into the existing public formula basis; `NNF.Sat`
is an abbreviation for the existing indexed semantics of that embedding.
`NNF.negate_negate` and `NNF.sat_negate` verify the complement operation.
In particular, until and release exchange under negation; this preserves the
strong-until witness requirement and release's inclusive endpoint.

`Formula.normalize` is structural, with no minimization or CNF/DNF expansion.
`sat_normalize`, `wordSat_normalize`, and `sat_normalize_neg` cover all words
and indices. Neither the normalizer nor these proofs requires atom equality.
Named equations describe normalization of derived public operators. Normalized
syntax is interpreted through the original semantics, not a second trace model.

`NNF.subformulas` includes the root and all descendants in a duplicate-free
Finset. Only this collection layer needs `[DecidableEq AP]`; AP need not be
finite. `mem_subformulas_iff` characterizes membership using immediate children;
`subformulas_subset_of_mem` proves transitive closure. `child_size_lt`,
`size_le_of_mem`, and `card_subformulas_le_size` bound recursion and collection
size in terms of the actual NNF node count. `NNF.Subformula f` supplies an
executable finite carrier, without enumerating words or valuations.

For example, `□(p ⟹ ◇q)` normalizes to `false R (¬p ∨ (true U q))`, with
seven distinct subformulas. `Examples.Normalization.model_normalization`
lifts word equivalence to universal Kripke satisfaction, without needing
seriality; positive traffic-light safety/ordering and a negative response
result transfer through that equivalence. Other examples exercise duality,
time-zero, until postponement, release forever and its endpoint, Nat atoms,
deduplication and finite-carrier computation. Principal results are audited.
Generalized acceptance is implemented below; tableau construction and formula-input
checking remain subsequent work. Finite syntax collection is not an automaton compiler.

## Traffic-light walkthrough

`Examples.TrafficLight` separates colour propositions (`red`, `green`, `yellow`)
from controller phases (`stop`, `go`, `caution`). Labels give one-hot Boolean
valuations. The normal controller cycles red → green → yellow → red, starting
red; the faulty controller additionally permits a red self-loop. Both are
serial and have no reachable deadlocks. Steps represent logical ticks, with
no real-time duration or fairness assumption.

`cyclePath` exhibits state-to-word mapping, initial observations, next, strong
until, release's inclusive right-operand boundary, and suffix evaluation.
`controller_safe` and `stuckController_safe` prove exactly one colour is lit
on every path. `controller_ordered` proves the next-colour transition law.
These are direct semantic proofs. Finite reachability and a route to caution
are computed separately.

`controller_eventually_green` and `controller_red_responds` use the verified
backend and the existing violation-language theorems for eventuality/response.
Their faulty-model counterparts are refuted; `stuckPath` explicitly witnesses
the infinite all-red behaviour. This path is supplied by the example rather
than extracted by the Boolean checker. General formula compilation, timed
controllers, multi-road safety and executable lasso extraction remain future
extensions. New principal example proofs are included in the axiom audit.

## Generalized Büchi acceptance and conversion

`FiniteGeneralizedBuchi` stores finite initial/successor sets and an ordered
`List (Finset Q)` of acceptance obligations. An accepting run is an infinite
CSLib initial run visiting every listed set arbitrarily late. Symbols remain
unrestricted; state types and initial sets may be empty. An empty family accepts
every existing infinite initial run, whereas a family containing an empty set
accepts no word. Partial transitions and deadlocks retain their original meaning.

`toFiniteBuchi` uses `Q × Fin (max 1 accepting.length)`, initially counter zero.
The counter waits for its current set, then advances cyclically using the
**source** state. The same transition consumes the current input valuation.
For a nonempty family, acceptance requires counter zero **and membership in
set zero**. Merely waiting at counter zero must not count as accepting.
For an empty family, the sole counter value stays zero and every state accepts.
No transitions are inserted. The carrier has `card Q * max 1 length` states;
this is a direct construction with no SCC or minimization performance claim.

`RoundRobin.complete` proves recurrent obligations force completed rounds:
from any counter, either the relevant set is hit or the counter would wait
forever, contradicting that set's recurrence. Advancing reduces the remaining
distance to wraparound. `RoundRobin.sound` proves recurring completions force
each intermediate obligation: if its counter stopped moving, no later completion
could occur. `counter_acceptance` specializes these arguments to finite sets.
`lift_run`, `project_run`, and `run_eq_lift` relate the deterministic annotation
to CSLib runs. `toFiniteBuchi_accepts` proves exact word-language preservation.
`accepts_family_ext` covers reordering and duplication without altering language.
These correctness proofs allow classical reasoning; execution uses finite data
and decidable operations, without classical selection or new trust assumptions.

For example, on the three-state cycle `0,1,2,0,...` with sets `[{0},{1},{2}]`,
the source counters are `0,1,2,0,...`: every round discharges all obligations.
A state outside set zero with counter zero, looping forever, is rejected.
`Examples.GeneralizedBuchi` checks these boundaries, empty families and deadlocks,
repeated/overlapping obligations, symbol-dependent edges and transient acceptance.
A traffic monitor requires green and yellow repeatedly. The progressing controller
has an accepted path; a red-only controller has none. The nondeterministic
waiting controller still has an accepted progressing path: this is existential
acceptance, not a claim that all executions progress.

`hasAcceptedPath_generalized_iff` derives this meaning from existing product
search and language preservation. No seriality assumption is added to the generic
conversion/search. The public universal property checker retains its seriality
requirement. Tableau translation will use one generalized acceptance set per
until obligation, then feed this converter to the verified ordinary backend.

The history-counter idea is also illustrated by CSLib's
[Büchi intersection construction](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/BuchiInter.lean)
by Ching-Tsun Chou (Apache 2.0). KILT uses CSLib's run definitions directly and
implements its own executable arbitrary-family counter and recurrence proofs;
CSLib's noncomputable binary intersection is not called by this conversion.

## Tableau local foundation

`KILT.LTL.Tableau` uses `Assignment f = Finset (NNF.Subformula f)` and a
`State f` subtype carrying a `StaticConsistent` proof. It enumerates subsets
and filters constant/connective consistency, requiring only decidable atom
equality. `Holds` is false outside the existing closure; no complementary
formulas or valuations are enumerated. State enumeration is executable and
`card_state_le` bounds its size by `2 ^ f.subformulas.card`.

Static consistency applies only to formulas in the closure: true is included,
false excluded, conjunction membership iff both operands are included, and
disjunction membership iff either operand is included. It does not guarantee
temporal realizability. Literal conflicts remain possible in static states,
but no valuation permits a transition from a state containing both polarities.

`Step s t valuation` checks each closure formula. Literal membership agrees
exactly with the source valuation. Next membership agrees with operand membership
in the successor. Until uses `right-now OR (left-now AND until-next)`; release
uses `right-now AND (left-now OR release-next)`. Release therefore includes its
right operand at the endpoint. The unfolding theorems are explicit, not recursive
simp rules. `initials` filters states containing the root; `successors` filters
states satisfying Step. `toNA` adapts them to CSLib without acceptance conditions.
The first transition consumes word position zero, preserving source observations.

`Represents` explicitly assumes that membership equals indexed semantic truth
for every subformula. `step_of_represents` proves consecutive such states obey
the local transition rules, using subformula closure and the unfolding laws.
It does not infer semantic falsity from absence in an arbitrary local run.

`Examples.Tableau` reports (closure, raw assignments, consistent states):
true `(1,2,1)`, repeated conjunction `(2,4,2)`, two-atom conjunction/disjunction
`(3,8,4)`, and until/release `(3,8,8)`. Computed checks cover literals,
next-source indexing, immediate and continued until, and release endpoints.
For `p U q`, a state containing `p` and `p U q` but not `q` can loop locally
under the valuation making only `p` true. `postponed_run` constructs this initial
infinite NA run; `postponed_word_fails` proves the word violates strong until.
Until acceptance conditions are therefore essential and remain the next layer.
No generalized translator with placeholder acceptance or formula checker is
exposed by this batch. Principal contracts are part of the default axiom audit.

## Two-thread lock walkthrough

`Examples.TwoThreadLock` gives two program counters and a shared Boolean lock.
Each transition schedules exactly one thread. All reads/writes use a single
shared value; no weak-memory or timing behavior is represented. Both threads
start Idle with the lock free. Idle requests when scheduled; Critical releases
when scheduled; a failed acquisition spins. There is no scheduling fairness.

Broken acquisition separates the free-lock test (Trying → Checked) from the
unconditional claim (Checked → Critical). The explicit schedule 0,0,1,1,0,1
lets both threads check before either claims, reaching simultaneous Critical
at word position six. `broken_not_mutualExclusion` refutes the universal safety
formula on an actual infinite initial path extending this finite prefix.
Atomic acquisition combines the test/write in Trying → Critical. Its carrier
retains Checked for comparison, but `AtomicInvariant` proves it unreachable,
proves critical threads hold the lock, and excludes simultaneous Critical.
`atomic_step_invariant` and `atomic_path_invariant` lift the invariant to
`atomic_mutualExclusion` on every infinite initial path.

`starvationFreedom t` is `□(requesting t ⟹ ◇ inCritical t)`, where requesting
includes Trying and Checked. `unfairSchedule` lets thread zero request once,
then schedules only thread one, repeatedly requesting/acquiring/releasing.
`unfair_not_response` proves thread zero's response property fails;
`atomic_response_check` establishes the false backend verdict using existing
checker correctness. Separate `#eval` executes the Boolean product search;
no native-computation axiom is added. Both models are globally serial by
construction, so these results do not rely on deadlock vacuity. The shared
carrier has 32 states; compiled reachability reports 22 broken and 8 atomic
reachable states. No arbitrary-formula compiler is claimed.

This example independently implements small lock protocols, rather than
Peterson's algorithm. Its safety/liveness questions follow the standard
[mutual-exclusion verification setting](https://lamport.azurewebsites.net/tla/peterson.html?back-link=high-level-view.html).
Program counters, scheduling and observation labels are separate extension
points for turn-taking protocols and future explicit fairness assumptions.

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
