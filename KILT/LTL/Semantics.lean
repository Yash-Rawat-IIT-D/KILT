import KILT.LTL.Syntax
import Cslib.Foundations.Data.OmegaSequence.Defs

/-!
# Infinite-word semantics for LTL

This module gives `Formula` its declarative meaning over infinite traces of
atomic-proposition valuations. It defines mathematical satisfaction only; the
executable formula-to-automaton pipeline is provided by later modules.

Strong until follows the standard non-strict convention: its right operand may
hold at the current position, leaving no earlier position at which the left
operand must hold.

## Sources

The semantics is independently written, with LeanLTL as a design reference:
https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Defs.lean

The infinite-sequence representation is imported from CSLib:
https://github.com/leanprover/cslib/blob/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations/Data/OmegaSequence/Defs.lean
-/

namespace KILT.LTL

universe u

/--
A truth assignment for one position of a word. Every atomic proposition
identifier is mapped to the Boolean value observed at that position.
-/
abbrev Valuation (AP : Type u) := AP → Bool

/--
An infinite trace of valuations, represented by a CSLib omega sequence. Index
`i` contains the valuation observed at position `i` of the trace.
-/
abbrev Word (AP : Type u) := Cslib.ωSequence (Valuation AP)

variable {AP : Type u}

/--
`Sat word i φ` states that `φ` holds at position `i` of `word`. Its structural
clauses give the formula constructors their meanings:

* Falsehood is never satisfied.
* An atom holds exactly when its value at position `i` is `true`.
* Negation holds when its operand does not hold at `i`.
* Disjunction holds when at least one operand holds at `i`.
* Next evaluates its operand at position `i + 1`.
* Strong until has some witness `j ≥ i` where its right operand holds, while
  its left operand holds at every position `k` with `i ≤ k < j`.

This is a proposition, not a Boolean decision procedure over infinite words.
-/
def Sat (word : Word AP) : Nat → Formula AP → Prop
  | _, .falsehood => False
  | i, .atom a => word i a = true
  | i, .neg φ => ¬ Sat word i φ
  | i, .disj φ ψ => Sat word i φ ∨ Sat word i ψ
  | i, .next φ => Sat word (i + 1) φ
  | i, .until φ ψ => ∃ j, i ≤ j ∧ Sat word j ψ ∧ ∀ k, i ≤ k → k < j → Sat word k φ

/-- Top-level word satisfaction: the formula holds at the initial (zero) position. -/
def WordSat (word : Word AP) (φ : Formula AP) : Prop := Sat word 0 φ

end KILT.LTL
