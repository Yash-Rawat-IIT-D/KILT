import KILT.Graph.IndexedLasso

/-!
# Reachable indexed lasso extraction

The original algorithms remain available as acceptingLassoCached? and
acceptingLassoReference?. The default prepares only seed-reachable rows and
stores predecessor IDs and depths, preserving the exact reference witness.
-/
namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

def acceptingLasso? (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) : Option (Lasso State) :=
  if seeds = ∅ ∨ accepting = ∅ then none else
    (prepareReachable order seeds successors).acceptingLasso? order accepting

theorem acceptingLasso?_eq_reference (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    acceptingLasso? order seeds successors accepting =
      acceptingLassoReference? order seeds successors accepting := by
  by_cases h : seeds = ∅ ∨ accepting = ∅
  · have hz : acceptingLassoCached? order seeds successors accepting = none := by
      simp [acceptingLassoCached?, h]
    rw [acceptingLassoCached?_eq_reference] at hz
    simp [acceptingLasso?, h, hz]
  · simp only [acceptingLasso?, h, ↓reduceIte]
    exact PreparedReachable.acceptingLasso?_eq_reference _ _ _

theorem acceptingLasso?_eq_cached (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    acceptingLasso? order seeds successors accepting =
      acceptingLassoCached? order seeds successors accepting := by
  rw [acceptingLasso?_eq_reference, acceptingLassoCached?_eq_reference]

theorem acceptingLasso?_sound (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) {l : Lasso State}
    (h : acceptingLasso? order seeds successors accepting = some l) :
    l.Valid seeds successors ∧ l.entry ∈ accepting := by
  rw [acceptingLasso?_eq_cached] at h
  exact acceptingLassoCached?_sound _ _ _ _ h

theorem acceptingLasso?_isSome_iff (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    (acceptingLasso? order seeds successors accepting).isSome = true ↔
      hasAcceptingCycle seeds successors accepting = true := by
  rw [acceptingLasso?_eq_cached]
  exact acceptingLassoCached?_isSome_iff _ _ _ _

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
