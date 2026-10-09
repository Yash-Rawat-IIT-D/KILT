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
does not include fairness.  Deadlocks and seriality will be explicit design
choices in the Kripke interface rather than implicit conventions.

## Implemented LTL interface

`KILT.LTL.Formula AP` stores named atoms of type `AP`. Syntax and semantics
require neither a finite atom type nor decidable atom equality. Formulas have
decidable equality when atoms do, and `Formula.size` counts constructor nodes
after expanding derived operators.

`Valuation AP` is `AP → Bool`. `Word AP` is
`Cslib.ωSequence (Valuation AP)`, so CSLib's sequence operations are available
without an adapter. `Sat word i φ` interprets the formula at position `i`,
and `WordSat word φ` abbreviates satisfaction at zero.

| Constructor | Meaning at position `i` |
| --- | --- |
| `falsum` | False |
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
All three are imported by `Examples.lean` and checked by `lake build`.

## Module boundaries

`KILT.LTL` is independent of the state type of a Kripke structure.
`KILT.Kripke` consumes the LTL interface to map paths to valuation words and
state model satisfaction.  `KILT.Automata` will consume both interfaces to
prove the correspondence with CSLib runs.  This direction prevents an automata
encoding from changing the underlying temporal semantics.

## Sources and attribution

KILT pins [CSLib at `a3da622f14ac47924a4ffb293fdb0dad6fcdfae1`](https://github.com/leanprover/cslib/tree/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1)
and imports its infinite-sequence infrastructure. The dependency lockfile
preserves CSLib's Mathlib revision `1f414401f69059aa7eead47b53ee40bd38455eeb`
and its transitive dependency revisions. Both use Lean `v4.35.0-rc4`.

KILT's LTL definitions and examples are independently written standard LTL.
The separation of syntax and trace semantics is informed by
[LeanLTL's LTL module](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Logics/LTL.lean)
and [temporal definitions](https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Defs.lean).
No LeanLTL source was copied, and semantic equivalence with that library has
not yet been proved. See the [source audit](audit.md) for upstream API details
and reuse considerations.
