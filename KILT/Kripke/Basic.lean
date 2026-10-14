import KILT.LTL.Semantics

/-!
# Kripke structures

This module will define initial states, the transition relation, Boolean state
labels, and the seriality predicate.  Seriality is recorded explicitly rather
than assumed for every Kripke structure.
-/

namespace KILT

universe u v

/-- A relational Kripke structure with Boolean labels and a nonempty set of
initial states. Transitions may be partial. -/
structure Kripke (State : Type u) (AP : Type v) where
  initial : State → Prop
  initial_nonempty : ∃ s, initial s
  step : State → State → Prop
  label : State → LTL.Valuation AP

namespace Kripke

variable {State : Type u} {AP : Type v}

/-- Every state has at least one successor. This is an explicit property, not
part of the definition of a Kripke structure. -/
def Serial (M : Kripke State AP) : Prop := ∀ s, ∃ t, M.step s t

end KILT.Kripke
