import Examples.LassoGraph

/-! Kernel-computed regressions for cached, early-stopping graph search.
General refinement theorems quantify over every finite graph and route table. -/
namespace Examples.Efficiency
open KILT.Graph
open Examples.LassoGraph

def line (s : Fin 6) : Finset (Fin 6) :=
  if h : s.val < 4 then {⟨s.val + 1, by omega⟩} else ∅

theorem target_is_seed : reachable? ({0} : Finset (Fin 6)) line 0 = true := by decide

theorem first_round : reachable? ({0} : Finset (Fin 6)) line 1 = true := by decide

theorem long_chain : reachable? ({0} : Finset (Fin 6)) line 4 = true := by decide

theorem unreachable_target : reachable? ({0} : Finset (Fin 6)) line 5 = false := by decide

theorem stable_closure :
    reachableSetFast ({0} : Finset (Fin 6)) (fun s => {s}) = {0} := by decide

theorem full_chain : reachableSetFast ({0} : Finset (Fin 6)) line = {0, 1, 2, 3, 4} := by decide

theorem zero_fuel : targetSearch line 1 0 {0} = false := by decide

theorem seed_route : routeFast? (Enumeration.fin 6) {0, 5} line 5 = some [5] := by decide

theorem first_route : routeFast? (Enumeration.fin 6) {0} line 1 = some [0, 1] := by decide

theorem last_route :
    routeFast? (Enumeration.fin 6) {0} line 4 = some [0, 1, 2, 3, 4] := by decide

theorem no_route : routeFast? (Enumeration.fin 6) {0} line 5 = none := by decide

theorem no_growth : routeGrowth (initialRouteTable ({0} : Finset (Fin 6)))
    (materialize (Enumeration.fin 6)
      (expandRouteTable (Enumeration.fin 6) (fun s => {s}) (initialRouteTable {0}))) = false := by decide

theorem growth : routeGrowth (initialRouteTable ({0} : Finset (Fin 6)))
    (materialize (Enumeration.fin 6)
      (expandRouteTable (Enumeration.fin 6) line (initialRouteTable {0}))) = true := by decide

theorem cached_deadlock : successorSetLookup (prepareSuccessorSet line) 4 = ∅ := by decide

theorem cached_edge : successorSetLookup (prepareSuccessorSet line) 0 = {1} := by decide

theorem empty_carrier :
    hasAcceptingCycle (∅ : Finset (Fin 0)) (fun _ => ∅) ∅ = false := by decide

theorem accepting_deadlock : hasAcceptingCycle ({4} : Finset (Fin 6)) line {4} = false := by decide

theorem positive_return :
    hasAcceptingCycle ({0} : Finset (Fin 6)) (fun s => {s}) {0} = true := by decide

theorem same_lasso_forward :
    shape (acceptingLasso? (Enumeration.fin 3) {0} branchEdges {1, 2}) =
      shape (acceptingLassoReference? (Enumeration.fin 3) {0} branchEdges {1, 2}) := by decide

theorem same_lasso_reverse :
    shape (acceptingLasso? reverseOrder {0} branchEdges {1, 2}) =
      shape (acceptingLassoReference? reverseOrder {0} branchEdges {1, 2}) := by decide

#eval (reachableSetFast ({0} : Finset (Fin 6)) line).card
#eval routeFast? (Enumeration.fin 6) {0} line 4
end Examples.Efficiency
