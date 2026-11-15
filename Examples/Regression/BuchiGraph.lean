import KILT.Graph.Buchi

/-! # Boundary cases for finite Büchi graph search -/
namespace Examples.BuchiGraph
open KILT.Graph

example : hasAcceptingCycle (∅ : Finset Unit) (fun _ => {()}) {()} = false := by
  simp only [hasAcceptingCycle_eq_spec]
  decide
example : hasAcceptingCycle ({()} : Finset Unit) (fun _ => {()}) ∅ = false := by
  simp only [hasAcceptingCycle_eq_spec]
  decide
example : hasAcceptingCycle ({()} : Finset Unit) (fun _ => ∅) {()} = false := by
  simp only [hasAcceptingCycle_eq_spec]
  decide
example : hasAcceptingCycle ({()} : Finset Unit) (fun _ => {()}) {()} = true := by
  simp only [hasAcceptingCycle_eq_spec]
  decide
example : hasAcceptingCycle (∅ : Finset (Fin 0)) (fun _ => ∅) ∅ = false := by
  simp only [hasAcceptingCycle_eq_spec]
  decide

def transient : Fin 2 → Finset (Fin 2) := fun _ => {1}
example : hasAcceptingCycle {0} transient {0} = false := by
  simp only [hasAcceptingCycle_eq_spec]
  decide
example : hasAcceptingCycle {0} (fun n : Fin 2 => {n}) {1} = false := by
  simp only [hasAcceptingCycle_eq_spec]
  decide
def cycle : Fin 2 → Finset (Fin 2) := fun n => if n = 0 then {1} else {0}
example : hasAcceptingCycle {0} cycle {1} = true := by
  simp only [hasAcceptingCycle_eq_spec]
  decide

/-- The branch to 1 accepts forever; the branch to 2 rejects forever. -/
def branching : Fin 3 → Finset (Fin 3)
  | 0 => {1, 2}
  | n => {n}
example : hasAcceptingCycle {0} branching {1} = true := by
  simp only [hasAcceptingCycle_eq_spec]
  decide

#eval hasAcceptingCycle {0} branching {1}
end Examples.BuchiGraph
