# KILT design notes

## Semantic foundation and the 22 October backend

KILT first defines a small LTL syntax over named atomic propositions and its
infinite-word semantics.  A Kripke path produces a word of Boolean valuations;
a Kripke model satisfies a formula when every initial path satisfies that word
formula at position zero.  This establishes the semantic interface needed by an
automata translation and finite-state checking. The finite Büchi backend now
checks supplied violation automata. Formula compilation now has a proved
CSLib word-language equivalence. The public formula-input checker now composes
that theorem with the finite backend.

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
mathematical proposition. Executable compilation produces an automaton with
that word language; it does not decide satisfaction of arbitrary infinite words.
The finite system backend below checks supplied violation automata.

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
states and all their successors. This `reachableSetSpec` recurrence executes
`Fintype.card State` rounds as a proof specification; public `reachableSet`
computes the carrier through reachable graph preparation. `mem_layers_iff` characterizes every intermediate
round using a bounded finite route, while `mem_reachableSet_iff` proves that
the final set is exactly reflexive-transitive reachability from a seed.
Zero-step reachability is intentional: every seed is reachable from itself.

The witness specification uses a `RouteTable State`, a function assigning at most one
route to each state; executable lookup instead uses parent IDs/depths. Round zero assigns `[s]` to each seed. At the next round,
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
`hasAcceptingCycle` searches reachable accepting states for a return to `q`
from `successors q`, stopping at its first successful candidate. Starting the second search from
successors is essential: zero-step reachability alone would incorrectly accept
a deadlock. Both `hasAcceptingCycle_eq_true_iff` and
`hasAcceptingCycle_iff_hasAcceptingRun` are proved.

The infinite-run proof uses finite-state recurrence in one direction and
CSLib execution concatenation in the other. These are semantic existence
proofs; the executable search uses finite sets and the existing bounded
reachability algorithm. It repeats reachability for candidate accepting states;
it is not an SCC implementation. This Boolean search returns no witness; the
separate lasso extractor below reuses its accepting-cycle criterion.

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
Generalized acceptance and tableau language correctness are implemented below.
The compiler composes normalization, tableau construction, and conversion;
the formula-input checker composes its violation language with product search.

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
than extracted by the Boolean checker. The subsequent formula-checker and lasso
examples add compilation and automatic witnesses. Timed controllers and multi-road
safety remain extensions. Principal example proofs are included in the axiom audit.

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
requirement. Tableau translation uses one generalized acceptance set per
until obligation, then feeds this converter to the verified ordinary backend.

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
Until acceptance conditions are therefore essential. The acceptance layer below
rejects that loop and proves the complete word language. Principal contracts
are part of the default axiom audit.

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
reachable states. This example uses the handwritten response monitor; the
general compiler is documented below.

This example independently implements small lock protocols, rather than
Peterson's algorithm. Its safety/liveness questions follow the standard
[mutual-exclusion verification setting](https://lamport.azurewebsites.net/tla/peterson.html?back-link=high-level-view.html).
Program counters, scheduling and observation labels are separate extension
points for turn-taking protocols and future explicit fairness assumptions.

## Tableau acceptance and verified formula compilation

`Tableau.untilObligations` traverses the syntax root-first and left-to-right,
retaining the first occurrence of each distinct until formula. Atom ordering is
unnecessary. `mem_untilObligations` characterizes the list exactly;
`untilObligations_nodup` and `length_untilObligations_le` prove that its length
is at most the closure size. Distinct obligations remain separate even when
their resulting accepting sets are equal.

For each `a U b`, `acceptanceSet` contains states where the until is absent or
`b` holds. `toGeneralizedBuchi` reuses the existing starts and local transitions;
`toGeneralizedBuchi_toNA` proves agreement with the local CSLib adapter. An
empty obligation family still requires an infinite initial run. Release adds no
recurrence condition: its local rule preserves the required right operand until
the left operand holds, including that endpoint, or forever.

For a worked example, let a state contain `p` and `p U q` while omitting `q`.
Its self-loop under only-p valuations satisfies the local equations. It never
visits the until accepting set, so `postponed_run_rejected` rejects that run.
`until_witness` proves the general argument: if the right operand never appears,
the local rule keeps the until present, contradicting a later accepting visit.
Choosing the first right-operand occurrence also establishes the left prefix.
An immediate right operand requires no left prefix.

`acceptingRun_sound` proves each present subformula true at every run position,
by structural induction with until witnesses and finite release propagation.
It does not prove that absent formulas are false. The regression
`partial_release_accepting` records a true release formula as absent on a valid
accepting run; `partial_release_not_represents` explicitly rules out treating
all accepting states as exact truth assignments.

Conversely, proof-only `semanticState` filters the closure by actual semantic
truth. This function is noncomputable because truth of an arbitrary infinite
word is not executable input. `semanticState_represents` and
`semanticRun_accepting` use it to construct an accepting run from root truth.
Consecutive states obey `step_of_represents`. For every until and every bound,
either it is already absent, or its finite semantic witness supplies an
accepting position. None of these classical witnesses are called by compilation.

`Tableau.accepts_iff_sat` states generalized acceptance iff `NNF.Sat word 0 f`.
`Tableau.toFiniteBuchi_accepts` composes this with the existing verified
round-robin conversion. Finally `Formula.toBuchi` normalizes and converts:

```lean
Formula.toBuchi_accepts (φ : Formula AP) (word : Word AP) :
  ωAcceptor.Accepts φ.toBuchi.toCSLib word ↔ WordSat word φ
```

The first `toBuchi` returns KILT's executable `FiniteBuchi`; the second is its
CSLib adapter. CSLib supplies run and Büchi acceptance semantics. KILT supplies
the finite representation, generalized conversion, graph search and compiler;
this milestone does not replace the existing product or accepting-cycle proofs.
No seriality or Kripke model is assumed for these word-language results.

Only `DecidableEq AP` is required, with no finite-atom or valuation enumeration.
For `n` normalized subformulas and `m` distinct until obligations,
`card_automatonState_le` bounds the converted carrier by `2^n * max 1 m`;
`m ≤ n`. Enumeration is exponential even before product search. Small checked
examples report (closure, obligations, converted states): true `(1,0,1)`,
eventually q `(3,1,4)`, next p `(2,0,4)`, release p q `(3,0,8)`. The eventuality
automaton has two initial and three accepting carrier states; accepting states
can still lack an outgoing transition for a particular valuation. These counts
are measurements of small examples, not performance guarantees.

`Examples.Translation` covers all constructors, derived operators, multiple and
repeated obligations, source-position-zero input, and word-language equivalence
with the handwritten eventuality/response monitors. Finite assertions use
`decide`, infinite-word assertions use semantic proofs, and `#eval` displays
construction counts. Principal theorems are checked by the default axiom audit.

The construction follows the standard tableau acceptance idea described by
[Gerth, Peled, Vardi and Wolper](https://www.cs.rice.edu/~vardi/papers/pstv95rj.pdf)
([alternate PDF](https://spinroot.com/spin/Doc/ltl.pdf)). KILT enumerates explicit
consistent subsets; it does not implement that paper's optimized on-the-fly
construction or claim its performance.

## Formula-input checker and end-to-end correctness

`Formula.violationAutomaton φ` compiles `¬φ`, with carrier
`Formula.AutomatonState (Formula.neg φ)`. `violationAutomaton_accepts` proves
its CSLib language is exactly `¬ WordSat word φ`. `FiniteKripke.check M φ hserial`
passes this automaton to the existing `checkAgainst`; product construction,
reachability and positive-length accepting-cycle search are unchanged.

The public contracts are:

```lean
M.check φ hserial = true ↔ M.toKripke.Satisfies φ
M.check φ hserial = false ↔
  ∃ p : M.toKripke.Path, p.IsInitial ∧ ¬ WordSat p.word φ
```

`check_correct` proves the first by composing the violation-language theorem
with `checkAgainst_correct`. `check_eq_false_iff` proves the second through the
existing accepted-path correspondence. `check_eq_checkAgainst` establishes
equality with any supplied automaton having the same proved violation language.
This permits rigorous comparison with handwritten monitors of different state
types. All state/atom/automaton universes remain independent in these APIs.

Models require an enumerable finite state type and decidable equality; executable
translation also needs decidable atom equality. Atoms need not be finite, and
valuations are never enumerated. Global seriality is an explicit public
precondition retained from the backend API. It is a selected modeling boundary,
not an extra prerequisite of the generic product/acceptance correspondence.
The deadlock regression proves no seriality proof exists and checks the
lower-level search without inserting transitions or exposing a checker bypass.
There is no fairness assumption. The result is Boolean, and the false-verdict
theorem provides semantic existence. The separate counterexample? operation
below adds an executable path description while preserving this Boolean API.

For a response walkthrough, `□(p ⟹ ◇q)` is violated by
`true U (p ∧ (false R ¬q))`: at some position there is a request with no grant
then or later. The outer until acceptance prevents postponing that position
forever. The release equation requires grant to remain false starting at the
chosen position; a simultaneous request/grant is therefore not a violation.
Product edges read the source valuation, including word position zero.
On the alternating request/grant system, no infinite product run can maintain
the violation, so no reachable accepting cycle exists. `check` returns true,
and `check_correct` quantifies that result over every initial infinite path.
The waiting-loop variant has a permanently waiting violating execution, hence
an accepting cycle and a false verdict. `waiting_response_counterexample`
demonstrates the existence theorem using a verdict transported from the monitor.
It is not an independent kernel computation of the general compiler.

### Validation evidence and trust

`Examples.Checker` proves the small verdicts `truth_verdict`,
`falsehood_verdict`, `atom_verdict`, `initial_atom_verdict`, and
`multiple_initials_verdict` by kernel computation. `singleton_satisfies_atom`
and `falsehood_counterexample` derive semantic contracts through the public
theorems. `deadlock_no_accepted_path` is also kernel computed. Nat atoms and
multiple initial states exercise the intended interfaces.

The 18 compiled expected-result checks cover four request/grant progress cases,
four traffic progress cases, safety on both traffic models, and eight boundary
cases (initial-only eventuality, both next outcomes, until now/later, release
endpoints, and universal multiple starts). All eight eventuality/response cases
also compare against actual handwritten-monitor executions. Unexpected verdicts
or disagreements throw IO errors and fail the default build. Separate negative
probes confirmed both error paths fail Lean with exit status 1.

These executions are tests of compiled code, not proof terms. The general
correctness theorems and principal example proofs remain kernel checked and
covered by the standard-axiom audit. No native-computation axioms are added.
A cached Lake build may replay the previously successful execution output; the
reported per-case times below are from the fresh targeted checker build.

| Model/property | Verdict | Negated closure | Automaton carrier | Product carrier | Measured check |
| --- | --- | --- | --- | --- | --- |
| Request/grant cycle, eventual grant | true | 3 | 4 | 8 | 10 ms |
| Waiting variant, eventual grant | false | 3 | 4 | 8 | 12 ms |
| Request/grant cycle, response | true | 7 | 16 | 32 | 5,525 ms |
| Waiting variant, response | false | 7 | 16 | 32 | 8,109 ms |
| Traffic cycle, eventual green | true | 3 | 4 | 12 | 13 ms |
| Stuck traffic, eventual green | false | 3 | 4 | 12 | 20 ms |
| Traffic cycle, red response | true | 7 | 16 | 48 | 10,750 ms |
| Stuck traffic, red response | false | 7 | 16 | 48 | 14,318 ms |
| Traffic cycle, no red/green overlap | true | 5 | 8 | 24 | 354 ms |
| Stuck traffic, no red/green overlap | true | 5 | 8 | 24 | 359 ms |

Times measure the compiled check call using a monotonic clock, excluding the
subsequent count reporting and monitor comparison. They are single observed
runs on this machine, not reproducible performance guarantees or reachable-state
counts. The expensive response results show that even small explicit products
need further evaluation; no efficiency claim is made from correctness alone.
Timeouts/resources are not mapped to false, and the checker exposes no runtime
budget parameter. Large lock checking remains outside this milestone.

This supplies the proposal's central checker/trace-semantics correspondence.
Mathematical review, broader evaluation and the report remain pending. Formal
compatibility with external LeanLTL and the outstanding audit/community work
remain separate commitments. Fairness, SCC optimization and optional frontend automation remain later
extensions. Executable lasso extraction is described below.

## Executable lasso counterexamples

`Graph.Lasso State` stores a finite prefix, a loop and a proof that the loop
is nonempty. Its sequence observes each prefix state once, then repeats the
loop forever. A singleton loop is a real self-loop; it is never inserted to
repair a deadlock. Mapping the lasso commutes with its infinite sequence.

Validity is checked mathematically by two finite chains: the prefix followed
by the loop entry starts initially, and the loop followed by its entry closes
under the edge relation. `Lasso.Valid.initial`, `Valid.step` and
`frequently_entry` connect these finite contracts to infinite execution and
recurrence. These are ordinary Lean proofs; CSLib's sequence and acceptance
interfaces retain their existing meanings.

`Graph.acceptingLasso?` stores routes from the seeds and scans reachable
accepting states in the supplied explicit enumeration. For candidate q it
searches for a route from successors(q) back to q. This enforces a positive
return length, rejecting an accepting deadlock or a transient accepting visit.
For routes stem (initial to q) and back (successor of q to q), it returns
`prefix = stem.dropLast` and `loop = q :: back.dropLast`.
`acceptingLasso?_sound` proves validity and acceptance at the loop entry;
`acceptingLasso?_isSome_iff` equates success to the existing Boolean search.
Enumeration changes may select different witnesses but preserve success.
No shortest-route, simple-cycle or shortest-counterexample guarantee is made.

Successor rows are stored only for seed-reachable states, in bounded-ID arrays.
Parent forests retain one predecessor and depth per discovered vertex; complete
routes are reconstructed only for requested witnesses. Mathematical route-table
recurrences remain under `Graph/Specification` and fix the enumeration-based
choice. No association-list cache or stored full-route backend remains. The
array/parent refinement proves equality with those specifications, rather than
requiring the retired executable implementation.

`FiniteKripke.acceptedLasso?` applies extraction to the existing product and
accepts explicit model and automaton orders. It permits partial models and
empty automaton initial sets. `productLassoPath` projects the returned sequence
to a Kripke path, while `productLassoPath_accepts` reuses product-run
correspondence to prove CSLib acceptance on its actual observation word.
Position zero and every product edge still consume the source state's label.

`M.counterexample? φ hserial modelOrder` compiles the violation automaton and
returns an optional product lasso. Compiler enumeration follows root-first,
left-to-right first-occurrence subformulas, exclude-before-include subsets,
static-consistency filtering and ascending acceptance counters. Product order
is model-first. This requires decidable atom equality but neither atom
ordering, finite atoms nor valuation enumeration. Compilation and extraction
use no classical selection. The formula carrier still has exponential size.

The main contracts are `counterexample?_sound` (the returned trace itself
violates φ), `counterexample?_isSome_iff` (success iff check returns false),
and `counterexample?_eq_none_iff` (none iff universal satisfaction). The Boolean
checker is unchanged, and extraction does not first run it. Global seriality
remains required at this public formula boundary. An execution failure is an
error, never a successful none result. No fairness assumption is added.

For the waiting model and □(request ⟹ ◇grant), compilation searches for an
unanswered request and a grant-free continuation. A returned system view may
include waiting in its prefix and again in a singleton loop. Repeating that
loop yields waiting forever: the request occurs and no grant follows. The
product trace retains the accepting monitor/compiler state that certifies the
violation. Acceptance must be proved on the product; a repeated system state
alone would not certify an LTL violation.

Examples.Counterexample executes formula-input extraction for request/grant
and traffic, and verified small monitors for lock safety and starvation. The
lock safety monitor guesses a collision and permits any later symbols; its
language is proved to be the negation of mutual exclusion. The atomic lock
can have no safety witness while still having a starvation witness under
unconstrained scheduling. The witnesses do not claim fair scheduling.

Small graph outputs and formula boundaries are proved by kernel computation.
Larger build-failing execution checks validate initiality, every finite edge
including loop closure, and acceptance at the entry, then print system states
and selected valuations. These checks are tests, not generated proofs; the
general soundness theorems remain kernel-checked independently.

### Reference extraction costs before early stopping

Before the search refinement, fresh execution in Examples.Counterexample on
this machine measured:

| Case | Witness | Product carrier | Prefix / loop length | Extraction |
| --- | --- | --- | --- | --- |
| Request cycle, eventual grant | no | 8 | — | 28 ms |
| Waiting, eventual grant | yes | 8 | 0 / 1 | 16 ms |
| Request cycle, response | no | 32 | — | 14,222 ms |
| Waiting, response | yes | 32 | 0 / 1 | 10,430 ms |
| Traffic cycle, eventual green | no | 12 | — | 95 ms |
| Stuck red, eventual green | yes | 12 | 0 / 1 | 56 ms |
| Traffic cycle, red response | no | 48 | — | 64,662 ms |
| Stuck red, red response | yes | 48 | 0 / 1 | 39,811 ms |
| Broken lock, mutual exclusion | yes | 64 | 8 / 4 | 8,738 ms |
| Atomic lock, mutual exclusion | no | 64 | — | 5,473 ms |
| Atomic lock, thread-zero starvation | yes | 64 | 4 / 3 | 11,416 ms |

Times cover extraction including formula enumeration where applicable, before
finite validation and printing. The three lock cases use handwritten monitors.
These are single observations, not reachable-state counts or performance
guarantees. Even a 48-state carrier is expensive with this reference algorithm;
materialization alone does not justify a claim of practical scalability. These
figures describe the retired original algorithm;
the current array/parent implementation has different costs. Cached Lake builds replay these measurements
rather than performing a fresh benchmark.

## Canonical graph backend and proof specifications

`Graph.Basic` defines `FiniteGraph`: bounded vertex IDs and sparse adjacency
arrays. `Prepare` discovers only seed-reachable sources. `Correspondence`
proves that decoding is injective and preserves seeds, edges, finite paths and
positive return paths. `Traversal` uses Boolean visited arrays and frontiers;
`Parents`, `ParentSearch` and `Frontier` implement route storage and stopping.
`RouteTransport` proves exact enumeration-selected route preservation under
reindexing. `LassoExtraction` and `LassoSearch` preserve the exact prefix/loop.

The specification modules contain bounded set expansion, deterministic
route-selection recurrences, and lasso selection. They serve as mathematical
contracts, not alternative production backends. `reachableSet_eq_spec`,
`route?_eq_spec` and `acceptingLasso?_eq_spec` establish exact result equality.
The retired caching/early-exit implementations, materialized route tables and
their dependencies are removed. Historical versions remain in Git history.

`check` retains its arguments and theorem. Without an explicit order, its
finite carrier is a multiset quotient of lists. `Enumeration.runInvariant`
eliminates that quotient only for an operation proved independent of list
order. It does not choose an ordering, require atom/state ordering, or use
classical selection during execution. `runInvariant_eq` proves the resulting
computation equals its specification. `checkWithOrder` bypasses that quotient
interface with the caller's order and is proved equal to `check`. Witness APIs
continue to require explicit enumeration because selected witnesses may depend
on order. Duplicate order entries are removed executably by `ofList`.

`hasAcceptingCycle_eq_true_iff_run` connects the canonical Boolean algorithm
to infinite acceptance, and `check_correct` composes with CSLib and formula
language correctness. The equality chain is a kernel-checked proof for all
finite graphs, not an inference from the finite regression examples. It proves
the stated contracts, subject to their model/semantics assumptions and standard
Lean trusted kernel; human review of those contracts remains separate.

Positive returns start from successors, rejecting accepting deadlocks. Empty
seeds or acceptance bypass preparation. Full searches stop at stability;
target parent searches finish the discovery level to settle enumeration ties.
The public route API reconstructs parent chains; no shortest-witness or SCC
complexity claim is made.

### Historical caching and early-exit measurements

The following data belongs to the earlier cached implementation and is retained
for comparison. Its benchmark implementation was retired with the canonical
backend refactor; it is not evidence about subsequent source revisions.



Three completed single-thread interpreted invocations per case gave these
medians in milliseconds. Graph inputs already include enumeration, initial
and accepting sets; cache construction is included in cache-using variants.
Validation and printing are outside the timers.

| Case | Boolean reference | Cache only | Early exits only | Combined Boolean | Lasso reference | Combined lasso |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Waiting / response | 7,712 | 509 | 264 | 239 | 10,468 | 518 |
| Traffic cycle / response | 10,390 | 677 | 504 | 363 | 62,950 | 1,758 |

The corresponding full public API medians were 262 / 385 ms for `check`, and
576 / 1,819 ms for `counterexample?` (waiting / traffic respectively). These
are measured invocations, not scalability or latency guarantees. The 12-state
cheap chain illustrates overhead: cache-only Boolean took 1 ms versus a
reference below 1 ms; combined Boolean stayed below 1 ms. Zero displayed
milliseconds means below timer resolution, not zero work. Its lasso fell from
2 ms to 1 ms. No broad claim about arbitrary cheap or dense graphs follows.

The separately instrumented ordered traversal reduced waiting's total expansion
rounds from 416 to 7 and successor requests from 1,276 to 38; traffic reduced
528 to 13 rounds and 1,710 to 74 requests. Caching evaluates raw successor rows
32 / 48 times respectively, converting subsequent requests into lookups. Initial
route rounds fell from 32 to 2 and 48 to 3. The waiting self-loop return needed
zero expansions. These counts describe the instrumented explicit order; public
unordered candidate traversal can use another order.

The completed benchmark process peaked at 2,487,616 KiB RSS (about 2.37 GiB),
including Lean imports, elaboration and runtime. This exceeds the original
roughly 1 GiB target; the user subsequently allowed exceeding that soft target.
It does not isolate cache allocation or establish native-executable memory use.
The combined JSON report in `.lake/logs/efficiency-summary-20261024T225014Z.json`
records ranges and exact source logs. Two complete repetitions were retained
from the interrupted run, and one complete fresh run replaced its unfinished
third repetition. The replacement harness completed with exit status zero,
including median/range summaries and finite witness validation.

## Reachable storage and parent invariants

`prepareReachable order seeds successors` discovers a successor-closed graph
from the seeds. Each discovered source supplies one cached row; an unprocessed
pending state is distinct from a processed deadlock with an empty row. Queue
invariants prove no duplicate sources, termination within the original finite
cardinality, and exact agreement with mathematical reachability. Completed
rows are converted to sparse arrays of bounded dense vertex IDs. The decoder
is injective and preserves initial membership, edges, finite paths and positive
return paths. A prepared graph stores its source enumeration and each vertex's
rank, separately from discovery IDs. Dense IDs are not witness tie-breakers.

Preparation currently uses a verified list work queue and finite membership
checks, then an integer-keyed `Std.ExtTreeMap` for adjacency conversion. It does
not yet use that dictionary as the discovery visited set. Rank lookup scans the
complete enumeration. These setup costs are explicit; reachable-only storage
does not imply linear-time preparation or eliminate compiler enumeration.
There is no atom ordering, Hashable-state requirement or valuation enumeration.

Boolean return searches store a visited array and the newly discovered frontier.
The invariant says that all edges behind the frontier have already been covered.
An accepting candidate in a prepared graph is already initial-reachable, so its
positive return query starts directly from its successor IDs. Empty acceptance
or seeds short-circuit preparation at the public graph wrappers.

Witness searches store an unseen/root marker or a parent ID and discovery depth.
The synchronous pointer engine is a proof reference; the executable frontier
engine ignores earlier-level predecessors. A theorem proves those predecessors
cannot reach an undiscovered target, so filtering them preserves the first
predecessor in the original enumeration. Target queries finish the discovery
level before returning, resolving ties. Queries stop on target discovery or no
new parent entries. Parent depth decreases strictly, and bounded reconstruction
uses an accumulator. Complete route lists appear only in proof specifications
and successful witness reconstruction, not in expansion entries.

The current frontier implementations still scan the vertex domain to produce
the next array and test sparse-row membership. They are not adjacency-linear
queue algorithms and are not SCC algorithms. Allocation and setup overhead need
measurement. The prepared graph stores adjacency, decoder and initial IDs. It does not retain
the construction's source order or a duplicate rank array. The caller supplies
an order when constructing a dense query order; `PreparedSearch` caches that
query order once alongside the acceptance mask. Seeds outside the stored
carrier require new preparation.

`routeSpec?_transport` proves exact route preservation under reachable reindexing.
`PreparedReachable.acceptingLasso?_eq_spec` and
`Graph.acceptingLasso?_eq_spec` prove exact optional-lasso preservation,
including the selected prefix, loop and time indices. They depend on the
mathematical lasso selection specification, not the removed cached backend.
Existing actual-returned-trace soundness and no-counterexample equivalences
continue through these equalities.

`hasAcceptedPathWithOrder` agrees with `hasAcceptedPath`. The formula-facing
`checkWithOrder formula hserial modelOrder` agrees with `check`, including
universal satisfaction and false-verdict theorems. Seriality remains explicit;
generic graph preparation and acceptance allow deadlocks. CSLib acceptance,
source-label timing and no-fairness semantics are unchanged.

Some concrete branching rank-sort expressions do not normalize in `decide`.
Their displays and expected-result assertions run as build-failing execution
tests; they are not promoted to proof. Small pointer/visited-array verdicts are
kernel computed. Previous small formula-witness results are transported through
the exact specification equality and kernel-computed specification results. The
general representation and algorithm theorems remain kernel checked using only
the allowed standard axioms. A reduction limitation is distinct from a false
verdict or a missing proof, and user mathematical review is still pending.

`Benchmarks/GraphStorage.lean` and `scripts/benchmark-graph.sh` measure the
canonical graph layer outside routine builds. Historical indexed/cached
comparisons established improvements on small fixtures before this naming and
dependency refactor. No benchmarks were run for the refactor itself; previous
measurements do not establish performance of the new quotient-based default
checker. Complete compiler enumeration, linear rank lookup, preparation costs
and lack of isolated backend RSS measurements remain limitations.

## Unified compilation and prepared checking

`Formula.Compiled φ` holds the finite automaton on `AutomatonState φ`, its
complete deterministic enumeration and the word-language theorem. `φ.compile`
shares the normalized root between construction and enumeration.
`compile_automaton` and `compile_order` preserve the previous compiler outputs;
`compile_accepts` retains CSLib acceptance equivalence for all words. No atom
ordering, finite atom type or valuation enumeration is added.

A `FiniteKripke.Checker M` holds the chosen model order and global-seriality
proof. Its `prepare φ` compiles the negated property once; `prepareCompiled`
reuses a supplied compiled negation, also across models. `PreparedCheck M φ`
contains that context, bundle and a prepared product. `M.prepareCheck` is a
convenience constructor with explicit order and seriality. Existing formula
checker and counterexample signatures remain wrappers over this path. The
order-free `check` uses `Enumeration.runInvariant` on model orders; witness
selection continues to use the supplied model order and compiler order.

`Graph.PreparedSearch` caches reachable adjacency, the dense enumeration and
acceptance mask. The ready case includes equations fixing order and mask to
the original specification. Its empty case carries a proof that seeds or
acceptance are empty; it skips graph preparation, rather than treating a
missing graph or execution failure as a negative result. Return queries read
cached adjacency. Extraction uses the cached order and parent forests, then
maps the result back through the same decoder.

`PreparedSearch.hasAcceptingCycle_eq` and `acceptingLasso?_eq` prove exact
agreement with the existing graph entry points, including the selected prefix
and loop. The product constructor `M.prepareProduct` is reusable for supplied
monitors and permits partial models and empty automata without seriality.
Actual-trace product projection lives in `Automata.ProductLasso`; its original
public theorem names and statements remain available.

For prepared formula problems, `check_correct` and `check_eq_false_iff` give
universal satisfaction and violating-path existence. `counterexample?_sound`
proves violation by the returned witness's own `counterexamplePath`;
`counterexamplePath_states` fixes its exact projected sequence.
`counterexample?_isSome_iff` equates witness presence with a false verdict,
and `counterexample?_eq_none_iff` equates absence with satisfaction. `check_eq`
proves verdict independence across well-specified preparations. The legacy
`counterexample?_eq_acceptedLasso` preserves its exact enumeration-selected
output, and all previous source-label/position-zero contracts remain.

For example, prepare the waiting-response product once. Boolean checking finds
an accepting positive return using visited arrays. Witness extraction from the
same prepared value builds parent information and yields prefix `[]` and the
waiting self-loop. It does not first call the Boolean method. The language
proof turns this particular infinite repetition into a response violation.

Shared preparation does not imply cached query results or cross-call persistent
storage. Repeated queries rerun search; separate evaluations rebuild pure
values. A changed formula changes its product. Boolean and witness engines
remain separate to avoid allocating parent data for a Boolean query. Global
versus reachable deadlocks, partial generic semantics, and no-fairness policy
are unchanged. No benchmark or performance claim is added by this interface refinement.

`Examples.PreparedChecking` covers exact legacy witnesses, empty shortcuts,
accepting deadlocks, compiled reuse across models, multiple initial states,
position zero/next, Nat atoms, enumeration-derived finiteness, and request/grant
and traffic results. Kernel-checked propositions and build-failing execution
assertions remain distinct; principal contracts join the standard-axiom audit.

## Production searches and proof interfaces

`Graph.Enumeration` is defined in `Graph/Enumeration/Basic.lean`; its executable
operations import this independent foundation rather than the route recurrence.
The route specification depends on enumeration, not the reverse.

Use `g.parentForest order seeds` for complete parent information and
`forest.route? target` to reconstruct a route. Use `g.parentsTo order seeds target`
for a target-only result, followed by `result.route?`, or the convenience
`g.parentRoute? order seeds target`. These interfaces fix initialization, fuel
and initial level. Their distinct result types do not present stopped searches
as complete forests. `ParentForest.route?_eq_spec` and
`TargetParents.route?_eq_spec` equate results with the same enumeration-selected
`routeSpec?`; the `reached_eq` lemmas connect constant-time discovery tests to
route existence. Lasso extraction uses these production interfaces and retains
its exact optional-witness refinement theorem.

Full-round, stopped-round and frontier implementations remain necessary steps
in that proof, under `FiniteGraph.Internal` in `Graph/Internal/`. Their raw
fuel/level/state operations are an implementation and refinement interface;
application code should use the production operations above.

`Formula.compile` assembles the executable finite automaton, order and language
proof. `Formula.toBuchi` remains the finite-only compilation API. In contrast,
`FiniteBuchi.toCSLib` forgets finite storage and supplies CSLib's semantic Büchi
interface. Write `φ.toBuchi.toCSLib`, or `φ.compile.automaton.toCSLib`, when stating
word acceptance. The old finite adapter spelling `FiniteBuchi.toBuchi` and its
three membership lemmas remain definitionally compatible aliases. Algorithms,
acceptance semantics, dependency pins and witness tie-breaking are unchanged.

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
