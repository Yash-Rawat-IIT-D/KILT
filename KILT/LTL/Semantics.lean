import KILT.LTL.Syntax
import Cslib.Foundations.Data.OmegaSequence.Defs

/-!
# Infinite-word semantics for LTL

`Valuation AP` assigns a Boolean value to each named atom. A `Word AP` is a
CSLib infinite sequence of valuations. `Sat word i φ` interprets a formula
at position `i`; `WordSat word φ` starts at position zero.

The constructor clauses are:

* Falsehood is never satisfied.
* An atom holds iff its valuation at `i` is `true`.
* Negation means the operand does not hold at `i`.
* Disjunction means at least one operand holds at `i`.
* Next evaluates the operand at `i + 1`.
* Strong until has a witness `j ≥ i` where the right operand holds, with the
  left operand holding at every `k` such that `i ≤ k < j`.

The until witness can be `i`, in which case the left interval is empty.
Satisfaction recurses structurally on formulas and is a mathematical
proposition. There is no decision procedure here for searching an infinite
word, and no formula-to-automaton compiler is supplied by this module.

## Sources

The semantics is independently written, with LeanLTL as a design reference:
https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Defs.lean

The infinite-sequence representation is imported from CSLib:
https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Data/OmegaSequence/Defs.lean
-/

namespace KILT.LTL

universe u

/-- A Boolean assignment to atomic proposition identifiers. -/
abbrev Valuation (AP : Type u) := AP → Bool

/-- An infinite word of valuations, using CSLib's sequence representation. -/
abbrev Word (AP : Type u) := Cslib.ωSequence (Valuation AP)

variable {AP : Type u}

/-- Indexed satisfaction for infinite-word LTL. -/
def Sat (word : Word AP) : Nat → Formula AP → Prop
  | _, .falsehood => False
  | i, .atom a => word i a = true
  | i, .neg φ => ¬ Sat word i φ
  | i, .disj φ ψ => Sat word i φ ∨ Sat word i ψ
  | i, .next φ => Sat word (i + 1) φ
  | i, .until φ ψ => ∃ j, i ≤ j ∧ Sat word j ψ ∧ ∀ k, i ≤ k → k < j → Sat word k φ

/-- A word satisfies a formula when it holds at position zero. -/
def WordSat (word : Word AP) (φ : Formula AP) : Prop := Sat word 0 φ

end KILT.LTL
