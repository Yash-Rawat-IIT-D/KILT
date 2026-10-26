import KILT.Graph.LassoExtraction
import KILT.Graph.Buchi

/-! Canonical accepting-lasso extraction with reachable arrays and parent chains. -/
namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

def acceptingLasso? (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) : Option (Lasso State) :=
  if seeds = ∅ ∨ accepting = ∅ then none else
    (prepareReachable order seeds successors).acceptingLasso? order accepting

theorem acceptingLasso?_eq_spec (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    acceptingLasso? order seeds successors accepting = lassoSpec? order seeds successors accepting := by
  by_cases h : seeds = ∅ ∨ accepting = ∅
  · simp [acceptingLasso?, h, lassoSpec?_empty _ _ _ _ h]
  · simp only [acceptingLasso?, h, ↓reduceIte]
    exact PreparedReachable.acceptingLasso?_eq_spec _ _ _

theorem acceptingLasso?_sound (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) {l : Lasso State}
    (h : acceptingLasso? order seeds successors accepting = some l) :
    l.Valid seeds successors ∧ l.entry ∈ accepting := by
  rw [acceptingLasso?_eq_spec] at h
  exact lassoSpec?_sound _ _ _ _ h

theorem acceptingLasso?_isSome_iff (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    (acceptingLasso? order seeds successors accepting).isSome = true ↔
      hasAcceptingCycle seeds successors accepting = true := by
  rw [acceptingLasso?_eq_spec, lassoSpec?_isSome_iff, hasAcceptingCycle_eq_true_iff]

theorem acceptingLasso?_iff_run (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    (acceptingLasso? order seeds successors accepting).isSome = true ↔ HasAcceptingRun seeds successors accepting :=
  (acceptingLasso?_isSome_iff _ _ _ _).trans (hasAcceptingCycle_eq_true_iff_run _ _ _)

theorem acceptingLasso?_order_independent (first second : Enumeration State)
    (seeds : Finset State) (successors : State → Finset State) (accepting : Finset State) :
    (acceptingLasso? first seeds successors accepting).isSome =
      (acceptingLasso? second seeds successors accepting).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [acceptingLasso?_isSome_iff, acceptingLasso?_isSome_iff]

end KILT.Graph
