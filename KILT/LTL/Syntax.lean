import KILT.Basic

/-!
# LTL syntax

`Formula AP` is syntax over atomic proposition identifiers. It is independent
of Kripke states and does not require `AP` to be finite or have decidable
equality. Formula equality is decidable when atom equality is decidable.

The constructor basis is falsehood, atoms, negation, disjunction, next and
strong until. Other connectives expand into this basis; `Formula.size` counts
nodes after that expansion. Syntax and semantics cover these operators, but
an executable formula-to-automaton translation is still future work.

## Design reference

These are independently written standard LTL definitions. LeanLTL informed
the separation of syntax and trace semantics; its predicate-valued atom type
is replaced here by named atoms supplied with a valuation:
https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/Logics/LTL.lean
-/

namespace KILT.LTL

universe u

/-- Future-time LTL formulas over named atomic propositions. -/
inductive Formula (AP : Type u) where
  /-- Falsehood. -/
  | falsum
  /-- An atomic proposition identifier. -/
  | atom (name : AP)
  /-- Boolean negation. -/
  | neg (operand : Formula AP)
  /-- Boolean disjunction. -/
  | disj (left right : Formula AP)
  /-- The operand at the next position. -/
  | next (operand : Formula AP)
  /-- Strong until: the right operand must eventually hold. -/
  | until (left right : Formula AP)
  deriving DecidableEq, Repr

namespace Formula

variable {AP : Type u}

/-- Truth, derived from falsehood and negation. -/
def truth : Formula AP := neg falsum

/-- Conjunction, derived by De Morgan's law. -/
def conj (φ ψ : Formula AP) : Formula AP := neg (disj (neg φ) (neg ψ))

/-- Material implication. -/
def imp (φ ψ : Formula AP) : Formula AP := disj (neg φ) ψ

/-- Eventually, including the current position. -/
def eventually (φ : Formula AP) : Formula AP := .until truth φ

/-- Globally, including the current position. -/
def globally (φ : Formula AP) : Formula AP := neg (eventually (neg φ))

/-- Release, the dual of strong until: `φ R ψ = ¬(¬φ U ¬ψ)`. -/
def release (φ ψ : Formula AP) : Formula AP := neg (.until (neg φ) (neg ψ))

/-- Number of constructor nodes; each leaf has size one. -/
def size : Formula AP → Nat
  | falsum => 1
  | atom _ => 1
  | neg φ => 1 + size φ
  | disj φ ψ => 1 + size φ + size ψ
  | next φ => 1 + size φ
  | .until φ ψ => 1 + size φ + size ψ

end Formula

end KILT.LTL
