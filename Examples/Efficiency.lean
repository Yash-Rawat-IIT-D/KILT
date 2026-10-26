import KILT.Graph.Internal.ParentSearch
import Examples.LassoGraph
import KILT.Graph.Routes
import KILT.Graph.Reachability

/-! Kernel-computed regressions for prepared graph and parent-pointer search.
General refinement theorems quantify over every finite graph and route table. -/
namespace Examples.Efficiency
open KILT.Graph
open Examples.LassoGraph

def line (s : Fin 6) : Finset (Fin 6) :=
  if h : s.val < 4 then {⟨s.val + 1, by omega⟩} else ∅

theorem target_is_seed : reachable? ({0} : Finset (Fin 6)) line 0 = true := by rw [reachable?, reachableSet_eq_spec]; decide +kernel

theorem first_round : reachable? ({0} : Finset (Fin 6)) line 1 = true := by rw [reachable?, reachableSet_eq_spec]; decide +kernel

theorem long_chain : reachable? ({0} : Finset (Fin 6)) line 4 = true := by rw [reachable?, reachableSet_eq_spec]; decide +kernel

theorem unreachable_target : reachable? ({0} : Finset (Fin 6)) line 5 = false := by rw [reachable?, reachableSet_eq_spec]; decide +kernel

theorem stable_closure :
    reachableSet ({0} : Finset (Fin 6)) (fun s => {s}) = {0} := by rw [reachableSet_eq_spec]; decide +kernel

theorem full_chain : reachableSet ({0} : Finset (Fin 6)) line = {0, 1, 2, 3, 4} := by rw [reachableSet_eq_spec]; decide +kernel

abbrev graph : FiniteGraph := ⟨6, #[#[1], #[2], #[3], #[4], #[], #[]], rfl⟩

theorem zero_fuel : (FiniteGraph.Visits.initial graph {0}).search 1 0 = false := by decide +kernel

theorem seed_route : route? (Enumeration.fin 6) {0, 5} line 5 = some [5] := by rw [route?_eq_spec]; decide +kernel

theorem first_route : route? (Enumeration.fin 6) {0} line 1 = some [0, 1] := by rw [route?_eq_spec]; decide +kernel

theorem last_route :
    route? (Enumeration.fin 6) {0} line 4 = some [0, 1, 2, 3, 4] := by rw [route?_eq_spec]; decide +kernel

theorem no_route : route? (Enumeration.fin 6) {0} line 5 = none := by rw [route?_eq_spec]; decide +kernel

theorem no_growth : FiniteGraph.Internal.Parents.grows
    (FiniteGraph.Internal.Parents.initial graph {4})
    ((FiniteGraph.Internal.Parents.initial graph {4}).round (Enumeration.fin 6)) = false := by decide +kernel

theorem growth : FiniteGraph.Internal.Parents.grows
    (FiniteGraph.Internal.Parents.initial graph {0})
    ((FiniteGraph.Internal.Parents.initial graph {0}).round (Enumeration.fin 6)) = true := by decide +kernel

theorem cached_deadlock : graph.successors 4 = ∅ := by decide +kernel

theorem cached_edge : graph.successors 0 = {1} := by decide +kernel

theorem empty_carrier :
    hasAcceptingCycle (∅ : Finset (Fin 0)) (fun _ => ∅) ∅ = false := by rw [hasAcceptingCycle_eq_spec]; decide +kernel

theorem accepting_deadlock : hasAcceptingCycle ({4} : Finset (Fin 6)) line {4} = false := by rw [hasAcceptingCycle_eq_spec]; decide +kernel

theorem positive_return :
    hasAcceptingCycle ({0} : Finset (Fin 6)) (fun s => {s}) {0} = true := by rw [hasAcceptingCycle_eq_spec]; decide +kernel

theorem same_lasso_forward :
    shape (acceptingLasso? (Enumeration.fin 3) {0} branchEdges {1, 2}) =
      shape (lassoSpec? (Enumeration.fin 3) {0} branchEdges {1, 2}) := by
  rw [acceptingLasso?_eq_spec]

theorem same_lasso_reverse :
    shape (acceptingLasso? reverseOrder {0} branchEdges {1, 2}) =
      shape (lassoSpec? reverseOrder {0} branchEdges {1, 2}) := by
  rw [acceptingLasso?_eq_spec]

#eval (reachableSet ({0} : Finset (Fin 6)) line).card
#eval route? (Enumeration.fin 6) {0} line 4
end Examples.Efficiency
