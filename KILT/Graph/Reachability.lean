import KILT.Graph.Traversal

/-! Reachable graph preparation supplies the closure. Bounded-set recurrences
in Specification state correctness contracts rather than a second backend. -/
namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

private def preparedSet (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : Finset State :=
  (prepareReachable order seeds next).states.toList.toFinset

private theorem preparedSet_eq (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : preparedSet order seeds next = reachableSetSpec seeds next := by
  ext target
  simp only [preparedSet, List.mem_toFinset, mem_reachableSetSpec_iff]
  exact (prepareReachable order seeds next).coverage target

/-- Compute exactly the seed-reachable carrier using prepared adjacency. -/
def reachableSet (seeds : Finset State) (next : State → Finset State) : Finset State :=
  Enumeration.runInvariant ∅ (fun order => preparedSet order seeds next)
    (fun a b => (preparedSet_eq a seeds next).trans (preparedSet_eq b seeds next).symm)

theorem reachableSet_eq_spec (seeds : Finset State) (next : State → Finset State) :
    reachableSet seeds next = reachableSetSpec seeds next :=
  Enumeration.runInvariant_eq _ _ _ _ (fun order => preparedSet_eq order seeds next)

@[simp] theorem mem_reachableSet_iff {seeds : Finset State} {next : State → Finset State}
    {target : State} : target ∈ reachableSet seeds next ↔ Reachable seeds next target := by
  rw [reachableSet_eq_spec, mem_reachableSetSpec_iff]

@[simp] theorem reachableSet_empty (next : State → Finset State) :
    reachableSet ∅ next = ∅ := by
  rw [reachableSet_eq_spec, reachableSetSpec_empty]

/-- Preparation already computes the full reachable carrier; no second traversal. -/
def reachable? (seeds : Finset State) (next : State → Finset State) (target : State) : Bool :=
  decide (target ∈ reachableSet seeds next)

@[simp] theorem reachable?_eq_true_iff (seeds : Finset State) (next : State → Finset State)
    (target : State) : reachable? seeds next target = true ↔ Reachable seeds next target := by
  rw [reachable?, decide_eq_true_eq, mem_reachableSet_iff]

end KILT.Graph
