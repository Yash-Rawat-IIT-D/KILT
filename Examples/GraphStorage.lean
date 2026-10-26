import KILT.Kripke.OrderedCheck
import KILT.Graph.Parents
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
    (branch.parentForest forward {0}).route? 3 =
      some [0, 1, 3] := by decide +kernel
theorem frontier_reversed :
    (branch.parentForest backward {0}).route? 3 =
      some [0, 2, 3] := by decide +kernel
theorem target_stops_at_seed :
    ((branch.parentsTo forward {0} 0).storage.get 3) =
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

/-- Optimized constructors preserve the old first-occurrence traversal order. -/
theorem enumeration_product_order :
    ((Enumeration.fin 2).product (Enumeration.fin 2)).states =
      [(0, 0), (0, 1), (1, 0), (1, 1)] := by decide +kernel

theorem enumeration_subtype_order :
    ((Enumeration.fin 4).subtype (fun i => i.val % 2 = 0)).states.map Subtype.val =
      [0, 2] := by decide +kernel

theorem enumeration_subset_order :
    (Enumeration.fin 2).finset.states = [∅, {1}, {0}, {0, 1}] := by decide +kernel

theorem arbitrary_list_still_deduplicates :
    (Enumeration.ofList ([1, 0, 1, 0] : List (Fin 2))
      (by intro s; fin_cases s <;> decide)).states = [1, 0] := by decide +kernel

abbrev stopped : FiniteGraph := ⟨1, #[#[]], rfl⟩
abbrev twoCycle : FiniteGraph := ⟨2, #[#[1], #[0]], rfl⟩

theorem deadlock_return : stopped.canReturn? 0 = false ∧
    stopped.returnRoute? (Enumeration.fin 1) 0 = none := by decide +kernel

theorem selfloop_return : branch.canReturn? 3 = true ∧
    branch.returnRoute? backward 3 = some [3] := by decide +kernel

theorem cyclic_return : twoCycle.canReturn? 0 = true ∧
    twoCycle.returnRoute? (Enumeration.fin 2) 0 = some [1, 0] := by decide +kernel

theorem transient_return : branch.canReturn? 0 = false ∧
    branch.returnRoute? forward 0 = none := by decide +kernel

theorem no_acceptance_lasso : branch.acceptingLasso? forward {0} ∅ = none := by decide +kernel

/-- Two seeds and branching exercise buffer order and the incremental seen set. -/
def bufferNext (s : Fin 4) : Finset (Fin 4) :=
  if s = 0 then {1, 2} else if s = 1 ∨ s = 2 then {3} else {3}

def buffered := ReachableQueue.Buffer.prepare (Enumeration.fin 4) {0} bufferNext

theorem buffer_matches_reference : buffered.view =
    ReachableQueue.prepare (Enumeration.fin 4) {0} bufferNext :=
  ReachableQueue.Buffer.prepare_view _ _ _

#eval expect "buffer discovery order" (buffered.nodes.toList == [0, 1, 2, 3])
#eval expect "buffer complete" (buffered.cursor == 4 && buffered.rows.size == 4)
#eval expect "buffer seen" (buffered.seen == ({0, 1, 2, 3} : Finset (Fin 4)))
#eval expect "multiple seeds" ((ReachableQueue.Buffer.prepare
  (Enumeration.fin 4) {0, 2} bufferNext).nodes.toList == [0, 2, 1, 3])
#eval expect "empty seeds" ((ReachableQueue.Buffer.prepare
  (Enumeration.fin 4) ∅ bufferNext).nodes.isEmpty)

end Examples.GraphStorage
