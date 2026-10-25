import KILT.Graph.LassoSearch
import KILT.Graph.Enumeration

/-! Kernel-checked graph and replay regressions for lasso extraction. -/
namespace Examples.LassoGraph
open KILT.Graph

def unitOrder : Enumeration Unit := Enumeration.ofList [()] (by simp)
def shape {S : Type} (result : Option (Lasso S)) : Option (List S × List S) :=
  result.map fun l => (l.prefix, l.loop)

theorem empty_states :
    (acceptingLasso? (Enumeration.fin 0) ∅ (fun _ => ∅) ∅).isSome = false := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem empty_seeds :
    (acceptingLasso? unitOrder ∅ (fun _ => {()}) {()}).isSome = false := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem empty_acceptance :
    (acceptingLasso? unitOrder {()} (fun _ => {()}) ∅).isSome = false := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem accepting_deadlock :
    (acceptingLasso? unitOrder {()} (fun _ => ∅) {()}).isSome = false := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem accepting_self_loop :
    shape (acceptingLasso? unitOrder {()} (fun _ => {()}) {()}) = some ([], [()]) := by
  rw [acceptingLasso?_eq_cached]
  decide

def chainEdges (s : Fin 5) : Finset (Fin 5) :=
  if s = 0 then {1} else if s = 1 then {2} else if s = 2 then {1}
  else if s = 3 then {3} else ∅

theorem prefix_and_cycle :
    shape (acceptingLasso? (Enumeration.fin 5) {0} chainEdges {1}) =
      some ([0], [1, 2]) := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem transient_acceptance :
    (acceptingLasso? (Enumeration.fin 5) {0} chainEdges {0}).isSome = false := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem unreachable_cycle :
    (acceptingLasso? (Enumeration.fin 5) {0} chainEdges {3}).isSome = false := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem multiple_initials :
    shape (acceptingLasso? (Enumeration.fin 5) {0, 3} chainEdges {3}) =
      some ([], [3]) := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem materialized_round :
    tableLookup none (storedRouteTables (Enumeration.fin 5) {0} chainEdges 2) 2 =
      some [0, 1, 2] := by decide

def branchEdges (s : Fin 3) : Finset (Fin 3) := if s = 0 then {1, 2} else {s}
def reverseOrder : Enumeration (Fin 3) := Enumeration.ofList [2, 1, 0] (by decide)

theorem first_branch :
    shape (acceptingLasso? (Enumeration.fin 3) {0} branchEdges {1, 2}) =
      some ([0], [1]) := by
  rw [acceptingLasso?_eq_cached]
  decide

theorem second_branch :
    shape (acceptingLasso? reverseOrder {0} branchEdges {1, 2}) =
      some ([0], [2]) := by
  rw [acceptingLasso?_eq_cached]
  decide

/-- An accepting branch suffices even though the other branch rejects. -/
theorem existential_branch :
    (acceptingLasso? (Enumeration.fin 3) {0} branchEdges {2}).isSome = true := by
  rw [acceptingLasso?_eq_cached]
  decide

def replayExample : Lasso Nat := ⟨[0], [1, 2], by decide⟩
theorem replay_boundaries : replayExample.replay 8 = [0, 1, 2, 1, 2, 1, 2, 1] := by decide
theorem mapped_replay : (replayExample.map (fun n => n + 10)).replay 5 = [10, 11, 12, 11, 12] := by
  decide

#eval shape (acceptingLasso? (Enumeration.fin 5) {0} chainEdges {1})
#eval replayExample.replay 8
end Examples.LassoGraph
