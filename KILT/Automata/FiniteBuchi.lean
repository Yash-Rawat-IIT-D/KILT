import Cslib.Computability.Automata.NA.Basic
import Mathlib.Data.Finset.Prod

/-!
# Finite symbol-driven Büchi automata

Only states are enumerated. Symbols may be arbitrary, including valuations
over infinitely many atom identifiers. Empty initial sets, empty acceptance,
and missing transitions denote legitimate languages.
-/
namespace KILT.Automata
universe u v

structure FiniteBuchi (Q : Type u) (Symbol : Type v)
    [Fintype Q] [DecidableEq Q] where
  initials : Finset Q
  successors : Q → Symbol → Finset Q
  accepting : Finset Q

namespace FiniteBuchi
variable {Q : Type u} {Symbol : Type v} [Fintype Q] [DecidableEq Q]

/-- Forget finite storage, preserving CSLib's infinite-word acceptance. -/
def toBuchi (A : FiniteBuchi Q Symbol) : Cslib.Automata.NA.Buchi Q Symbol where
  start q := q ∈ A.initials
  Tr q symbol r := r ∈ A.successors q symbol
  accept q := q ∈ A.accepting

@[simp] theorem toBuchi_start (A : FiniteBuchi Q Symbol) (q : Q) :
    q ∈ A.toBuchi.start ↔ q ∈ A.initials := Iff.rfl
@[simp] theorem toBuchi_transition (A : FiniteBuchi Q Symbol) (q r : Q) (symbol : Symbol) :
    A.toBuchi.Tr q symbol r ↔ r ∈ A.successors q symbol := Iff.rfl
@[simp] theorem toBuchi_accept (A : FiniteBuchi Q Symbol) (q : Q) :
    q ∈ A.toBuchi.accept ↔ q ∈ A.accepting := Iff.rfl

end FiniteBuchi
end KILT.Automata
