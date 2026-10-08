# Library audit

Audit date: 9 October 2026.
These notes are based on the local reference clones and the source revisions
listed below. I inspected definitions and proof bodies; I did not build either
upstream library or test a combined dependency configuration during this audit.

## CSLib

### Revision and dependency choice

The reference checkout is `leanprover/cslib` at commit
`a3da622f14ac47924a4ffb293fdb0dad6fcdfae1`.
Its package version is `0.1.0`, but the commit is the useful identifier for this
audit. The checkout declares Lean `v4.35.0-rc4` and Mathlib `v4.35.0-rc4`;
the manifest locks Mathlib to `1f414401f69059aa7eead47b53ee40bd38455eeb`.
See the [toolchain](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/lean-toolchain), [Lake configuration](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/lakefile.toml), and [manifest](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/lake-manifest.json#L4-L13).

KILT currently uses Lean `v4.32.1`, and its Lake configuration has no CSLib
dependency. Therefore, this is the CSLib revision I am auditing, rather than an
already adopted dependency. My preferred integration route is to align KILT
with the audited CSLib toolchain, verify a small import, and pin this commit.
If the course requires `v4.32.1`, I will instead find a compatible CSLib revision
and repeat the API checks against it. Compatibility remains a build question.

### Relevant modules

The main APIs for KILT are concentrated in these files:

| Module under `Cslib` | Relevant objects |
| --- | --- |
| `Foundations.Data.OmegaSequence.Defs` | `ωSequence`, `map`, `drop`, `take` |
| `Foundations.Semantics.LTS.OmegaExecution` | Infinite executions and finite-prefix lemmas |
| `Computability.Automata.NA.Basic` | `NA`, `NA.Run`, `NA.Buchi` |
| `Computability.Automata.Acceptors.OmegaAcceptor` | `ωAcceptor.Accepts`, `ωAcceptor.language` |
| `Computability.Automata.NA.Prod` | `NA.iProd`, `NA.iProd_run_iff` |
| `Computability.Automata.NA.BuchiInter` | Büchi intersection and its language theorem |
| `Computability.Automata.NA.Pair` | Finite-state Büchi language decomposition |

### Words, transition systems, and runs

`Cslib.ωSequence α` wraps a function `ℕ → α`; `xs n` reads position `n`.
It provides `map` for state labelling, `drop` for temporal suffixes, and `take`
for finite prefixes. This is a suitable representation of KILT's infinite
valuation words. [Source: infinite sequences](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Data/OmegaSequence/Defs.lean#L33-L84).

`Cslib.LTS State Label` stores `Tr : State → Label → State → Prop`. [Source](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Semantics/LTS/Basic.lean#L59-L66).
`LTS.OmegaExecution ss xs` means that `Tr (ss i) (xs i) (ss (i + 1))`
holds at every natural-number index. The label at position zero is consumed by
the transition from state zero to state one. [Source: infinite executions](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean#L22-L40).

`Cslib.Automata.NA State Symbol` extends that LTS with `start : Set State`.
`NA.Run na xs ss` adds the requirement `ss 0 ∈ na.start` to an infinite
execution. Neither `NA` nor its run definition requires a finite state space
or a decision procedure for transitions. [Source: nondeterministic automata](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Basic.lean#L38-L81).

This separation is useful: the semantic model can stay relational, while the
executable layer supplies finite representations and decidability explicitly.
The prefix lemmas `OmegaExecution.extract_execution` and `extract_mTr` should
also help connect an infinite accepting run with finite reachability arguments.

### The Büchi interface

`Cslib.Automata.NA.Buchi State Symbol` extends `NA` with
`accept : Set State`. It therefore has three ingredients: initial states,
labelled transitions, and accepting states. [Source: `NA.Buchi`](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Basic.lean#L38-L81).

Its `ωAcceptor` instance accepts an infinite word when there exists a run whose
states visit `accept` infinitely often. The source expresses the latter as
`∃ᶠ k in atTop, ss k ∈ a.accept`. This means visits occur arbitrarily far along
the run; one accepting visit, or merely reaching an accepting state, is insufficient.

`ωAcceptor.language A` packages the accepted words as a `Cslib.ωLanguage`.
`ωAcceptor.mem_language` identifies membership with `Accepts A xs`.
I will state translation correctness using this language interface, so the
formula semantics and automata semantics can meet at a word-level theorem.
[Source: acceptor interface](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/Acceptors/OmegaAcceptor.lean#L17-L34).

The interface describes existential acceptance by a nondeterministic automaton.
KILT's system-level satisfaction will quantify over all executions from initial
system states. The checker will therefore search for an accepting execution of
the product with an automaton for the negated property.

### Products and acceptance conditions

`NA.iProd` constructs the synchronous product of an indexed family of automata.
Its state is a dependent tuple, and every component consumes the same symbol.
`NA.iProd_run_iff` proves that a product run is exactly a compatible family of
component runs. This is the main reusable product lemma. [Source: products](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Prod.lean#L22-L38).

For two Büchi automata, requiring both components to be accepting at the same
position would be wrong: each may accept infinitely often at different times.
`NA.Buchi.interNA` adds a Boolean history component which alternates between
waiting for the two acceptance conditions. `interAccept` defines acceptance,
and `inter_language_eq` proves the resulting language is the intersection.
[Source: Büchi intersection](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/BuchiInter.lean#L34-L101).

`histTrans` and `interNA` are marked `noncomputable` at this revision because
their definitions use classical decisions about set membership. I can reuse
their semantic results, but an executable intersection needs decidable finite
data and a correspondence proof. The auxiliary `addHist`, `hist_run_proj`, and
`hist_run_exists` show how to transport runs through history augmentation.
[Source: history construction](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Hist.lean#L27-L55).

For a Kripke structure paired with one property automaton, only the automaton
component needs a Büchi acceptance condition. If the system is encoded as a
Büchi automaton with every state accepting, the extra alternation is unnecessary.
I will use the simpler product where its correctness proof permits it.

### Other results worth reusing

`NA.Buchi.reindex` changes the state representation along an equivalence.
`reindex_language_eq` proves that this preserves the accepted language. This
could connect a mathematical state type with a numbered finite representation,
provided I construct an actual equivalence. [Source: state reindexing](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/BuchiEquiv.lean#L24-L68).

`NA.Buchi.language_eq_fin_iSup_hmul_omegaPow` decomposes a finite-state Büchi
language into finite prefixes reaching accepting states, followed by infinitely
many nonempty return segments. It assumes `[Finite State]` and
`[Inhabited Symbol]`. This is relevant background for the accepting-cycle proof,
although it is not itself an executable emptiness algorithm. [Source](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Pair.lean#L103-L110).

`ωLanguage.IsRegular` means recognition by a finite-state nondeterministic
Büchi automaton. The regular-language file proves closure under union,
intersection, and complement. Its complement theorem gives a semantic
existence result, not a ready-made finite complement procedure for KILT.
The file also contains `proof_wanted IsRegular.iff_da_muller`; I will not count
that requested result as a completed proof or use it in the checker argument.
[Source: omega-regular languages](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Languages/OmegaRegularLanguage.lean).

### Kripke encoding and executable checking

My proposed system interface has a finite state type, initial states, a step
relation `R`, and a valuation `L`. I will encode a step from `s` to `s'` with
symbol `L s`, so a path `s₀, s₁, ...` produces `L s₀, L s₁, ...`.
This convention matches CSLib's run indexing and keeps the initial valuation
visible to the property automaton. It needs an explicit trace-correspondence lemma.

Deadlocks need a deliberate policy. My initial preference is to require every
system state to have a successor. CSLib's `LTS.Total` is stronger for a labelled
system: it requires a successor for every state and every label. Its
`totalize` construction adds a sink reachable from any state, so I cannot use
it as a substitute for a proof about Kripke deadlock self-loops. [Source](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Semantics/LTS/Total.lean#L27-L75).

For execution, I will use an enumerable state type, decidable initial and
accepting membership, and decidable transitions or a verified successor list.
A finite atom type with Boolean valuations gives a finite, inhabited alphabet.
The intended emptiness test searches for a reachable accepting state with a
nonempty return path. The positive-length condition excludes a false witness
consisting only of zero-step reachability. This criterion still needs a proof
connecting it to CSLib's infinite-run acceptance.

I did not find a supplied LTL translator, a standalone generalized-Büchi record,
or an executable Büchi emptiness checker in the automata, language, logic, and
algorithm directories reviewed at this revision. These are scoped search
findings, not a claim about all Lean libraries. If translation needs several
acceptance sets, I will define that interface and prove its conversion to
ordinary Büchi acceptance, using the history construction as a reference.

### Integration plan

1. Resolve the toolchain choice and compile imports of `NA.Basic` and `NA.Prod`.
2. Define the finite Kripke interface and prove the valuation-word encoding.
3. Build a tiny Büchi example and check the initial-symbol convention by hand.
4. Make the selected formula fragment produce a finite CSLib Büchi automaton.
5. Prove product-run correspondence and the finite accepting-cycle criterion.
6. Implement the search and prove that its result agrees with that criterion.

The central planned statement is that the checker returns true exactly when
every initial system execution satisfies the property. Its proof should factor
through translation correctness, product correctness, and emptiness correctness.
The version alignment and executable representation are the first decisions to
settle; neither follows just from having the reference checkout available.

## LeanLTL

### Revision and role in KILT

The reference checkout is `UCSCFormalMethods/LeanLTL` at commit
`d5473f06ab9d0ea652a51b2e78b11089731c4b6c`, with package version `0.1.0`.
Its toolchain is Lean `v4.17.0-rc1`; its manifest pins Mathlib to
`6f90ebd99f9b2de8cbaa9784d6767412e91d804b`. The Lake requirement itself does
not fix a revision, so the checked-in manifest matters for reproduction.
See the [toolchain](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/lean-toolchain), [Lake configuration](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/lakefile.toml), and [manifest](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/lake-manifest.json#L4-L13).

This differs from both KILT's `v4.32.1` and the audited CSLib toolchain.
I will initially use LeanLTL as the semantic reference described in the proposal.
Directly importing both upstream snapshots into one Lake project will require
a common Lean/Mathlib version and source-level compatibility work.

The ITP 2025 paper describes a framework for temporal reasoning over finite
and infinite traces, with Lean expressions embedded in specifications and
automation for proofs. That is the right context for the library's role here:
it provides semantics and reasoning tools that KILT can compare against.
[Source: Vin, Miller, and Fremont, ITP 2025](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.37).

### What I inspected

The source divides into traces, functions on traces, sets of traces, logical
embeddings, notation, and tactics. The [README](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/README.md) identifies those areas;
the concrete files relevant to this audit are:

| File under `LeanLTL` | Relevance to KILT |
| --- | --- |
| `Trace/Defs.lean` and `Trace/Basic.lean` | Trace representation and suffix operations |
| `TraceSet/Defs.lean` | Satisfaction and temporal operators |
| `TraceSet/Basic.lean` | Semantic laws, normalization, temporal unfolding |
| `Logics/LTL.lean` | Inductive LTL syntax and its semantic embedding theorem |
| `TraceFun/Defs.lean` | Optional-valued observations on traces |
| `TraceSet/Notation.lean` | `LLTL[...]` elaboration and value bindings |
| `Util/SimpAttrs.lean` and `Tactic/PushLTL.lean` | Proof automation |

I also inspected the traffic-light and induction examples to distinguish
temporal theorem proving from the finite-state checking workflow KILT needs.

### Trace representation

`LeanLTL.Trace σ` represents a nonempty finite or infinite sequence of states.
It stores `toFun? : ℕ → Option σ`, a length in `ℕ∞`, a nonemptiness proof,
and a proof relating defined positions to the length. `Trace.Infinite` means
that this length is `⊤`. [Source: trace definitions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Trace/Defs.lean#L11-L76).

`Trace.toFun` reads a position with an in-bounds proof. `Trace.shift` drops a
prefix and also needs an in-bounds proof; `Trace.map` changes the state values.
For an infinite trace, every natural-number index is in bounds.
The lemmas `infinite_lt_length`, `infinite_shift_iff`, `toFun_shift`, and
`shift_shift` are useful for comparing KILT suffixes with LeanLTL suffixes.
[Source: trace lemmas](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Trace/Basic.lean).

KILT can use CSLib's `ωSequence` for its core word semantics and build an
adapter to LeanLTL: set `toFun? n = some (xs n)` and `length = ⊤`, then prove
the record obligations. The important bridge lemma is that adapting a dropped
word agrees with shifting its adapted trace. I expect this lemma to carry much
of the bookkeeping in the `X` and `U` compatibility cases.

I will keep finite-trace behavior outside the first Büchi checker. Reusing
LeanLTL's trace type in a comparison module does not require giving KILT a
second, finite-trace model-checking mode.

### Trace sets and satisfaction

`LeanLTL.TraceSet σ` wraps `sat : Trace σ → Prop`.
The notation `t ⊨ f` applies this predicate. `TraceSet.of p` lifts a state
predicate by evaluating it at position zero. [Source: trace-set definitions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Defs.lean).

This is an extensional semantic object: it describes which traces satisfy a
property. It can also express arbitrary Lean predicates and quantification.
Consequently, a general `TraceSet` is wider than the finite propositional
formula language I can feed to an automata construction.

The library distinguishes validity over all traces (`⊨`), finite traces
(`⊨ᶠ`), and infinite traces (`⊨ⁱ`). KILT's model-specific satisfaction needs
another restriction: quantify only over executions generated by the given
Kripke structure. Infinite-trace validity alone does not impose that restriction.

`TraceSet.Basic` provides extensional equality and Boolean/lattice instances,
which support ordinary logical rewriting of semantic properties.
I will use these laws in the compatibility layer where imports are feasible,
while keeping the finite syntax and its evaluation explicit in the checker.
[Source: trace-set algebra](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean#L18-L168).

### Temporal operators and boundary behavior

LeanLTL defines strong and weak shifts separately. A strong shift requires the
target position to exist; a weak shift quantifies over a proof of its existence.
At the end of a finite trace, strong next is false and weak next is true.
On an infinite trace, the bound exists at every position, so they agree.
[Source: shift definitions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Defs.lean).

`TraceSet.until` requires a witness position for the right operand and the left
operand at every earlier position. `release` is defined by duality with until;
`finally` is true-until, and `globally` is the dual of finally.
The semantic expansion lemmas include `sat_until_iff`, `sat_finally_iff`, and
`sat_globally_iff`. [Sources: definitions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Defs.lean) and [semantic lemmas](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean#L18-L168).

For KILT, the intended meaning of `p U q` includes `q` holding immediately.
The eventuality witness may be position zero, and the obligation on earlier
positions is then empty. Likewise, `F p` includes the current position.
These conventions will be explicit in the semantics and example expectations.

I will compare KILT's single infinite-word `X` with LeanLTL's strong next,
following its standard LTL embedding. The compatibility theorem must carry
the infinite-trace assumption, rather than silently applying finite-trace laws.

### The existing inductive LTL syntax

There is already an inductive syntax in `LeanLTL.Logics.LTL`.
`LTL.Formula σ` has constructors `var`, `not`, `or`, `next`, and `until`.
Its atoms have type `LTL.Var σ = σ → Prop`. Additional connectives, including
conjunction, implication, eventually, and globally, are defined from this basis.
[Source: LTL syntax and connectives](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Logics/LTL.lean).

This is useful prior work, but predicates as atoms are awkward for KILT's
executable formula processing. Arbitrary functions into `Prop` do not provide
the syntactic equality or decision procedures needed to enumerate subformulas
and evaluate transition guards. A formula is finite syntax even with these
atoms; the problem is deciding and representing its atomic observations.

My proposed formula layer instead uses a finite atom identifier type `AP`.
A valuation supplies the truth value of each atom. I can interpret atom `a`
as the LeanLTL predicate `fun valuation => valuation a = true`, then translate
the Boolean and temporal constructors recursively.

This is a representation choice for automata construction, not a claim that
LeanLTL lacks syntax. I will keep derived connectives small and preserve their
meaning through explicit translation lemmas.

### The semantic embedding already proved

`LTL.Trace σ` pairs a LeanLTL trace with a proof that it is infinite.
The file defines recursive satisfaction `LTL.sat` and an interpretation
`LTL.toLeanLTL : LTL.Formula σ → TraceSet σ`.
The theorem `LTL.equisat` connects the two:

```text
LTL.sat t f ↔ t.trace ⊨ LTL.toLeanLTL f
```

This gives KILT two possible comparison targets. I can translate KILT formulas
to `LTL.Formula` and compose with `equisat`, or interpret them directly as
trace sets and prove the bridge by induction. I prefer the first route if the
chosen syntax maps cleanly to its constructors. [Source: embedding theorem](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Logics/LTL.lean).

That theorem establishes agreement within LeanLTL. KILT still needs to prove
its own word-to-trace and formula-translation compatibility statements.

### Proof tools worth reusing

`push_ltl` is a small tactic macro expanding to
`simp +contextual only [push_ltl]`. The associated simp set rewrites temporal
satisfaction into ordinary propositions and quantifiers, allowing normal Lean
tactics to handle the resulting proof goals. [Source: tactic](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Tactic/PushLTL.lean).

The registered simp sets also include `push_not_ltl` and `neg_norm_ltl`.
They organize semantic negation pushing and normalization; the latter is
documented to eliminate finally/globally in favor of the core operators.
[Source: simp attributes](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Util/SimpAttrs.lean).

For compatibility proofs, this is a useful way to expose the meaning of a
temporal constructor before applying an induction hypothesis. It does not
enumerate a Kripke graph or decide Büchi emptiness, so KILT's search algorithm
will remain a separate development.

### Normalization and temporal unfolding

The semantic lemmas `not_until`, `not_release`, `not_finally`, and `not_globally`
are useful specifications for negating a property. Strong and weak shifts swap
under negation; that distinction disappears only after restricting to infinite
traces. [Source: negation laws](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean#L258-L280).

KILT will need an executable normalization function on its own syntax, with
a theorem that normalization preserves satisfaction. Rewriting a `TraceSet`
does not itself return the finite syntax tree needed by a translation algorithm.
If until is supported, negation handling must account for its release dual.

The lemmas `until_eq_or_and`, `release_eq_and_or`, `finally_eq_or_finally`, and
`globally_eq_and_globally` give one-step unfoldings. They should guide local
transition obligations in a tableau-style construction. [Source: unfolding](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean#L803-L862).
For until/eventually, local unfolding alone allows obligations to be deferred
forever. The automaton's acceptance condition must also force their discharge.

### Frontend reuse and restrictions

`LLTL[...]` produces a `TraceSet`; `LLTLV[...]` produces a `TraceFun`.
The notation supports Lean terms and strong/weak value bindings, beyond a
plain propositional formula grammar. Its implementation includes elaboration
helpers and transformations for embedded next operators. [Source: notation](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Notation.lean#L9-L207).

`TraceFun σ α` evaluates a trace to `Option α`. Its operations support state
observations, value transformations, and shifts which may be undefined on
finite traces. This is useful for rich specifications and arithmetic proofs.
[Source: trace functions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceFun/Defs.lean#L11-L85).

For the first KILT frontend, I will accept a restricted grammar producing
KILT's finite syntax directly. Supporting arbitrary `LLTL[...]` expressions
would require a separate account of which embedded Lean predicates and
quantifiers can be compiled. I will borrow notation conventions where helpful,
without presenting arbitrary trace-set expressions as executable LTL input.

### Reuse decisions

| Component | Plan for KILT |
| --- | --- |
| Trace and suffix operations | Use through an adapter in the compatibility layer |
| `LTL.sat`, `toLeanLTL`, `equisat` | Use as the standard infinite-trace comparison target |
| Semantic operator laws | Reuse where importable; otherwise prove the corresponding KILT lemmas |
| `push_ltl` and related simp sets | Use for semantic proofs after version alignment |
| `LLTL[...]` and `TraceFun` | Study for frontend design; keep the initial input grammar finite |
| Predicate-valued atoms | Replace in KILT syntax with finite atom identifiers and a valuation |
| Normalization | Implement on KILT syntax and prove semantic preservation |
| Automata translation and emptiness | Implement against CSLib and connect to the semantics |

Any adapted source should retain its attribution. Direct theorem reuse means
importing the checked theorem on a compatible toolchain; a similar proof idea
alone does not establish that the theorem is available in KILT.

### Examples and proof coverage

The traffic-light example proves safety and recurring-green properties from
temporal assumptions. Its state includes natural-number queue sizes, so copying
the whole example would not give KILT a finite-state input. I will use a bounded
or Boolean abstraction and state that abstraction explicitly. [Source](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTLExamples/TrafficLights.lean).

The induction example combines temporal assumptions with a property quantified
over natural numbers. It is a useful example of semantic proof automation,
while also showing why the full specification language exceeds the planned
finite propositional frontend. [Source](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTLExamples/Induction.lean).

The reviewed trace, trace-set, and standard LTL files contain no active `sorry`
found by the source search; `TraceSet.Basic` has a commented-out candidate lemma.
The separate `Logics/LTLfMT.lean` does contain unfinished cases, and its import
is commented out in the root module. I will keep it outside KILT's comparison
path. This source inspection does not replace a build or an axiom-dependency
check of imported theorems. [Sources: root module](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL.lean#L3-L5) and [unfinished cases](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Logics/LTLfMT.lean#L191-L212).

### Next steps for the compatibility layer

1. Fix the finite atom type and the operators in KILT's supported fragment.
2. Define a valuation-word semantics using CSLib's infinite sequences.
3. Define the infinite-trace adapter and prove its suffix correspondence.
4. Translate KILT formulas to `LeanLTL.LTL.Formula` and prove satisfaction agrees.
5. Compose with `LTL.equisat` to obtain agreement with trace-set semantics.
6. Connect the same KILT semantics to the CSLib automaton-language theorem.

Before importing LeanLTL, I will test porting the necessary modules to the
selected CSLib/Mathlib toolchain. If that requires substantial changes, I will
record the port separately and keep the core checker independent of it.

## Source references

The code links below use the exact audited commits. Line anchors refer to those
snapshots; the findings above were checked against the local source files.

### CSLib sources

- **C1.** [CSLib toolchain](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/lean-toolchain)
- **C2.** [CSLib package configuration](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/lakefile.toml)
- **C3.** [CSLib dependency lock](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/lake-manifest.json#L4-L13)
- **C4.** [Infinite words: OmegaSequence/Defs](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Data/OmegaSequence/Defs.lean#L33-L84)
- **C5.** [Infinite LTS executions](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean#L22-L40)
- **C6.** [NA, runs, and Büchi acceptance](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Basic.lean#L38-L81)
- **C7.** [OmegaAcceptor interface](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/Acceptors/OmegaAcceptor.lean#L17-L34)
- **C8.** [Synchronous product and run correspondence](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Prod.lean#L22-L38)
- **C9.** [Büchi intersection](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/BuchiInter.lean#L34-L101)
- **C10.** [Finite-state Büchi language decomposition](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Pair.lean#L103-L110)
- **C11.** [History augmentation](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/Hist.lean#L27-L55)
- **C12.** [State reindexing](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Automata/NA/BuchiEquiv.lean#L24-L68)
- **C13.** [Omega-regular languages and closure results](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Computability/Languages/OmegaRegularLanguage.lean)
- **C14.** [Total LTS and sink construction](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Semantics/LTS/Total.lean#L27-L75)
- **C15.** [LTS structure](https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Semantics/LTS/Basic.lean#L59-L66)

### LeanLTL sources

- **L1.** [LeanLTL toolchain](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/lean-toolchain)
- **L2.** [Vin, Miller, and Fremont: LeanLTL, ITP 2025](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.37)
- **L3.** [LeanLTL README](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/README.md)
- **L4.** [Trace definitions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Trace/Defs.lean#L11-L76)
- **L5.** [Trace and suffix lemmas](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Trace/Basic.lean)
- **L6.** [Trace-set semantics and operators](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Defs.lean)
- **L7.** [Trace-set algebra and satisfaction lemmas](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean#L18-L168)
- **L8.** [Standard LTL syntax, semantics, and equisat](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Logics/LTL.lean)
- **L9.** [push_ltl tactic](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Tactic/PushLTL.lean)
- **L10.** [Temporal simp attributes](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Util/SimpAttrs.lean)
- **L11.** [Negation laws](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean#L258-L280)
- **L12.** [Temporal unfolding laws](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean#L803-L862)
- **L13.** [LLTL notation and elaboration](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Notation.lean#L9-L207)
- **L14.** [Trace functions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceFun/Defs.lean#L11-L85)
- **L15.** [Traffic-light example](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTLExamples/TrafficLights.lean)
- **L16.** [Induction examples](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTLExamples/Induction.lean)
- **L17.** [LeanLTL root imports](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL.lean#L3-L5)
- **L18.** [LeanLTL package configuration](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/lakefile.toml)
- **L19.** [LeanLTL dependency lock](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/lake-manifest.json#L4-L13)
- **L20.** [Unfinished finite-trace modulo-theories embedding](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Logics/LTLfMT.lean#L191-L212)
