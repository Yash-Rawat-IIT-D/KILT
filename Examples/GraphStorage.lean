import KILT.Kripke.OrderedCheck
import KILT.Graph.Parents
import KILT.Graph.Frontier
import KILT.Graph.Traversal
import Examples.Checker

/-!
# Reachable graph storage and parent-route regressions

Concrete propositions compute in the kernel. Displays are readable executions,
not additional proofs. Parent and Boolean frontiers have independent storage,
with exact-reference and mathematical reachability contracts respectively.
-/
namespace Examples.GraphStorage
open KILT KILT.Graph

def next (s : Fin 64) : Finset (Fin 64) :=
  if s = 0 then {7, 2} else if s = 2 ∨ s = 7 then {9} else if s = 9 then {9} else {s}

def prepared := prepareReachable (Enumeration.fin 64) {0} next

/-- Larger rank-sorting executions are tests, not kernel-computed propositions. -/
def expect (name : String) (actual : Bool) : IO Unit := do
  unless actual do throw (IO.userError s!"graph storage: {name}")

#eval expect "reachable count" (prepared.graph.size == 4)
#eval expect "discovery order" (prepared.states.toList == [0, 2, 7, 9])
#eval expect "unreachable row absent" (!(prepared.states.toList.contains 63))
#eval expect "reachable acceptance" (prepared.hasAcceptingCycle {9})
#eval expect "unreachable acceptance" (!(prepared.hasAcceptingCycle {63}))
#eval expect "reuse acceptance" (!(prepared.hasAcceptingCycle {2}))
theorem empty_seeds :
    (prepareReachable (Enumeration.fin 64) ∅ next).graph.size = 0 := by decide +kernel
#eval expect "multiple seeds"
    ((prepareReachable (Enumeration.fin 64) {0, 63} next).graph.size == 5)

def deadlock (_ : Fin 1) : Finset (Fin 1) := ∅
theorem deadlock_stored : (prepareReachable (Enumeration.fin 1) {0} deadlock).graph.size = 1 := by decide +kernel
theorem accepting_deadlock : hasAcceptingCycleWithOrder (Enumeration.fin 1) {0} deadlock {0} = false := by decide +kernel
theorem empty_acceptance : hasAcceptingCycleWithOrder (Enumeration.fin 64) {0} next ∅ = false := by decide +kernel

def emptyOrder : Enumeration Empty := ⟨[], by simp, fun s => nomatch s⟩
theorem empty_carrier :
    (prepareReachable emptyOrder ∅ (fun _ => ∅)).graph.size = 0 := by decide +kernel

/-- Adjacency encounters 2 before 1; enumeration tie-breaking must still select 1. -/
abbrev branch : FiniteGraph := ⟨4, #[#[2, 1], #[3], #[3], #[3]], rfl⟩
def forward := Enumeration.fin 4
def backward : Enumeration (Fin 4) :=
  ⟨[3, 2, 1, 0], by decide, by intro s; fin_cases s <;> decide⟩

theorem selected_route : branch.parentRoute? forward {0} 3 = some [0, 1, 3] := by decide +kernel
theorem reversed_route : branch.parentRoute? backward {0} 3 = some [0, 2, 3] := by decide +kernel
theorem seed_route : branch.parentRoute? forward {0} 0 = some [0] := by decide +kernel
theorem seed_retained : branch.parentRoute? forward {0, 3} 3 = some [3] := by decide +kernel
theorem no_route : branch.parentRoute? forward {3} 0 = none := by decide +kernel
theorem empty_routes : branch.parentRoute? forward ∅ 3 = none := by decide +kernel

theorem boolean_seed : branch.reachable? {0} 0 = true := by decide +kernel
theorem boolean_branch : branch.reachable? {0} 3 = true := by decide +kernel
theorem boolean_unreachable : branch.reachable? {3} 0 = false := by decide +kernel
theorem boolean_empty : branch.reachable? ∅ 3 = false := by decide +kernel
theorem frontier_selected :
    (FiniteGraph.Parents.frontierForest branch forward {0}).unwind 5 3 [] =
      some [0, 1, 3] := by decide +kernel
theorem frontier_reversed :
    (FiniteGraph.Parents.frontierForest branch backward {0}).unwind 5 3 [] =
      some [0, 2, 3] := by decide +kernel
theorem target_stops_at_seed :
    (((FiniteGraph.Parents.initial branch {0}).frontierSearch forward (some 0) 4 0).get 3) =
      .unseen := by decide +kernel

def singletonOrder : Enumeration Unit := ⟨[()], by simp, by intro s; cases s; simp⟩
theorem ordered_truth : Checker.singleton.checkWithOrder LTL.Formula.truth
    Checker.singleton_serial singletonOrder = true := by decide +kernel
theorem ordered_falsehood : Checker.singleton.checkWithOrder .falsehood
    Checker.singleton_serial singletonOrder = false := by decide +kernel
theorem ordered_nat_atom : Checker.singleton.checkWithOrder Checker.p
    Checker.singleton_serial singletonOrder = true := by decide +kernel

#eval prepared.states.toList
#eval (prepared.graph.size, prepared.graph.adjacency.map Array.size)
#eval branch.parentRoute? forward {0} 3
#eval branch.parentRoute? backward {0} 3

end Examples.GraphStorage
