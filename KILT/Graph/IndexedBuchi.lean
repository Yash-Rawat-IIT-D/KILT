import KILT.Graph.IndexedCorrect
import KILT.Graph.IndexedReachability

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
    p.graph.reachable? (p.graph.successors q) q = true)

theorem PreparedReachable.hasAcceptingCycle_eq {seeds : Finset State}
    {next : State → Finset State} (p : PreparedReachable seeds next) (accepting : Finset State) :
    p.hasAcceptingCycle accepting = Graph.hasAcceptingCycle seeds next accepting := by
  apply Bool.eq_iff_iff.mpr
  rw [hasAcceptingCycle, decide_eq_true_eq, Graph.hasAcceptingCycle_eq_true_iff]
  constructor
  · rintro ⟨q, hq, hr⟩
    rw [IndexedGraph.reachable?_eq, Graph.reachable?_eq_true_iff] at hr
    exact (p.acceptingCycle_iff accepting).mp ⟨q, hq,
      (p.reachable_iff q).mpr (p.decode_reachable q), Relation.TransGen.head'_iff.mpr hr⟩
  · intro hc
    obtain ⟨q, hq, _, hr⟩ := (p.acceptingCycle_iff accepting).mpr hc
    refine ⟨q, hq, ?_⟩
    rw [IndexedGraph.reachable?_eq, Graph.reachable?_eq_true_iff]
    exact Relation.TransGen.head'_iff.mp hr

/-- Ordered reachable preparation followed by acceptance over dense IDs. -/
def hasAcceptingCycleIndexed (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (accepting : Finset State) : Bool :=
  if seeds = ∅ ∨ accepting = ∅ then false else
    (prepareReachable order seeds next).hasAcceptingCycle accepting

theorem hasAcceptingCycleIndexed_eq (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (accepting : Finset State) :
    hasAcceptingCycleIndexed order seeds next accepting = hasAcceptingCycle seeds next accepting := by
  by_cases h : seeds = ∅ ∨ accepting = ∅
  · rw [hasAcceptingCycleIndexed, if_pos h]
    apply Eq.symm
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨q, hq, hr, _⟩ := (hasAcceptingCycle_eq_true_iff _ _ _).mp hh
    rcases h with hs | ha
    · simpa [hs, Reachable] using hr
    · simpa [ha] using hq
  · simp only [hasAcceptingCycleIndexed, h, ↓reduceIte]
    exact PreparedReachable.hasAcceptingCycle_eq _ _

end KILT.Graph
