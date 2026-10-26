import KILT.Graph.Correspondence
import KILT.Graph.Traversal

/-!
# Acceptance on a prepared reachable graph

All prepared vertices are reachable from the original seeds. Only a positive
return query is needed for each accepting candidate; those queries use visited
arrays and discovery frontiers, without constructing parent routes.
-/
namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Search a prepared graph, without evaluating the original successor function. -/
def PreparedReachable.hasAcceptingCycle {seeds : Finset State}
    {next : State → Finset State} (p : PreparedReachable seeds next) (accepting : Finset State) : Bool :=
  decide (∃ q ∈ p.accepting accepting,
    p.graph.canReturn? q = true)

theorem PreparedReachable.hasAcceptingCycle_eq_spec {seeds : Finset State}
    {next : State → Finset State} (p : PreparedReachable seeds next) (accepting : Finset State) :
    p.hasAcceptingCycle accepting = Graph.hasAcceptingCycleSpec seeds next accepting := by
  apply Bool.eq_iff_iff.mpr
  rw [hasAcceptingCycle, decide_eq_true_eq, Graph.hasAcceptingCycleSpec_eq_true_iff]
  constructor
  · rintro ⟨q, hq, hr⟩
    rw [FiniteGraph.canReturn?_eq_reachable, FiniteGraph.reachable?_eq_spec, decide_eq_true_eq, mem_reachableSetSpec_iff] at hr
    exact (p.acceptingCycle_iff accepting).mp ⟨q, hq,
      (p.reachable_iff q).mpr (p.decode_reachable q), Relation.TransGen.head'_iff.mpr hr⟩
  · intro hc
    obtain ⟨q, hq, _, hr⟩ := (p.acceptingCycle_iff accepting).mpr hc
    refine ⟨q, hq, ?_⟩
    rw [FiniteGraph.canReturn?_eq_reachable, FiniteGraph.reachable?_eq_spec, decide_eq_true_eq, mem_reachableSetSpec_iff]
    exact Relation.TransGen.head'_iff.mp hr

/-- Ordered reachable preparation followed by acceptance over dense IDs. -/
def hasAcceptingCycleWithOrder (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (accepting : Finset State) : Bool :=
  if seeds = ∅ ∨ accepting = ∅ then false else
    (prepareReachable order seeds next).hasAcceptingCycle accepting

theorem hasAcceptingCycleWithOrder_eq_spec (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (accepting : Finset State) :
    hasAcceptingCycleWithOrder order seeds next accepting = hasAcceptingCycleSpec seeds next accepting := by
  by_cases h : seeds = ∅ ∨ accepting = ∅
  · rw [hasAcceptingCycleWithOrder, if_pos h]
    apply Eq.symm
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨q, hq, hr, _⟩ := (hasAcceptingCycleSpec_eq_true_iff _ _ _).mp hh
    rcases h with hs | ha
    · simpa [hs, Reachable] using hr
    · simpa [ha] using hq
  · simp only [hasAcceptingCycleWithOrder, h, ↓reduceIte]
    exact PreparedReachable.hasAcceptingCycle_eq_spec _ _

/-- Canonical Boolean backend: reachable preparation followed by array search. -/
def hasAcceptingCycle (seeds : Finset State) (next : State → Finset State)
    (accepting : Finset State) : Bool :=
  Enumeration.runInvariant false (fun order => hasAcceptingCycleWithOrder order seeds next accepting)
    (fun a b => (hasAcceptingCycleWithOrder_eq_spec a seeds next accepting).trans
      (hasAcceptingCycleWithOrder_eq_spec b seeds next accepting).symm)

theorem hasAcceptingCycle_eq_spec (seeds : Finset State) (next : State → Finset State)
    (accepting : Finset State) :
    hasAcceptingCycle seeds next accepting = hasAcceptingCycleSpec seeds next accepting :=
  Enumeration.runInvariant_eq _ _ _ _ (fun order => hasAcceptingCycleWithOrder_eq_spec order seeds next accepting)

theorem hasAcceptingCycleWithOrder_eq (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (accepting : Finset State) :
    hasAcceptingCycleWithOrder order seeds next accepting = hasAcceptingCycle seeds next accepting := by
  rw [hasAcceptingCycleWithOrder_eq_spec, hasAcceptingCycle_eq_spec]

theorem hasAcceptingCycle_eq_true_iff (seeds : Finset State) (next : State → Finset State)
    (accepting : Finset State) :
    hasAcceptingCycle seeds next accepting = true ↔ HasAcceptingCycle seeds next accepting := by
  rw [hasAcceptingCycle_eq_spec, hasAcceptingCycleSpec_eq_true_iff]

theorem hasAcceptingCycle_eq_true_iff_run (seeds : Finset State) (next : State → Finset State)
    (accepting : Finset State) :
    hasAcceptingCycle seeds next accepting = true ↔ HasAcceptingRun seeds next accepting :=
  (hasAcceptingCycle_eq_true_iff _ _ _).trans (hasAcceptingCycle_iff_hasAcceptingRun _ _ _)

end KILT.Graph
