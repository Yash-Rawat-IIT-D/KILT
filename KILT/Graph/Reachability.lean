import Cslib.Foundations.Relation.RelatesInSteps
import Mathlib.Data.Finset.Union

/-!
# Executable reachability in finite directed graphs

This module is independent of Kripke labels and automata. A graph is supplied
by a finite successor set for each state. `layers` repeatedly expands a seed
set, and `reachableSet` runs that expansion for the cardinality of the state
type. The correctness theorem relates the executable result to Mathlib's
reflexive-transitive closure.
-/

namespace KILT.Graph

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- The edge relation represented by finite successor sets. -/
def Step (successors : State → Finset State) (source target : State) : Prop :=
  target ∈ successors source

/-- Mathematical reachability from any seed, including zero steps. -/
def Reachable (seeds : Finset State) (successors : State → Finset State)
    (target : State) : Prop :=
  ∃ source ∈ seeds, Relation.ReflTransGen (Step successors) source target

/-- Add every immediate successor of a discovered state. -/
def expand (successors : State → Finset State) (discovered : Finset State) :
    Finset State :=
  discovered ∪ discovered.biUnion successors

/-- States discovered after at most `rounds` transitions. -/
def layers (seeds : Finset State) (successors : State → Finset State) :
    Nat → Finset State
  | 0 => seeds
  | n + 1 => expand successors (layers seeds successors n)

/-- The executable reachable set. A simple path needs fewer transitions than
there are states, so `Fintype.card State` rounds are sufficient. -/
def reachableSet (seeds : Finset State) (successors : State → Finset State) :
    Finset State :=
  layers seeds successors (Fintype.card State)

omit [Fintype State] in
@[simp] theorem layers_zero (seeds : Finset State)
    (successors : State → Finset State) :
    layers seeds successors 0 = seeds := rfl

omit [Fintype State] in
@[simp] theorem layers_succ (seeds : Finset State)
    (successors : State → Finset State) (n : Nat) :
    layers seeds successors (n + 1) =
      expand successors (layers seeds successors n) := rfl

omit [Fintype State] in
theorem layers_subset_succ (seeds : Finset State)
    (successors : State → Finset State) (n : Nat) :
    layers seeds successors n ⊆ layers seeds successors (n + 1) := by
  intro state hstate
  exact Finset.mem_union_left _ hstate

omit [Fintype State] in
/-- A layer contains exactly the states connected to a seed in at most the
given number of steps. -/
theorem mem_layers_iff {seeds : Finset State}
    {successors : State → Finset State} {target : State} {rounds : Nat} :
    target ∈ layers seeds successors rounds ↔
      ∃ source ∈ seeds, ∃ steps ≤ rounds,
        Relation.RelatesInSteps (Step successors) source target steps := by
  induction rounds generalizing target with
  | zero =>
      constructor
      · intro htarget
        exact ⟨target, htarget, 0, Nat.le_refl 0,
          Relation.RelatesInSteps.refl target⟩
      · rintro ⟨source, hsource, steps, hsteps, hroute⟩
        have hzero : steps = 0 := Nat.eq_zero_of_le_zero hsteps
        subst steps
        have heq : source = target := Relation.RelatesInSteps.zero hroute
        change target ∈ seeds
        simpa only [heq] using hsource
  | succ rounds ih =>
      simp only [layers_succ, expand, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro (hold | ⟨previous, hprevious, hedge⟩)
        · rcases ih.mp hold with ⟨source, hsource, steps, hsteps, hroute⟩
          exact ⟨source, hsource, steps, by omega, hroute⟩
        · rcases ih.mp hprevious with ⟨source, hsource, steps, hsteps, hroute⟩
          exact ⟨source, hsource, steps + 1, by omega,
            Relation.RelatesInSteps.tail source previous target steps hroute hedge⟩
      · rintro ⟨source, hsource, steps, hsteps, hroute⟩
        by_cases hshort : steps ≤ rounds
        · exact Or.inl (ih.mpr ⟨source, hsource, steps, hshort, hroute⟩)
        · have hlength : steps = rounds + 1 := by omega
          subst steps
          rcases Relation.RelatesInSteps.succ hroute with
            ⟨previous, hprefix, hedge⟩
          exact Or.inr ⟨previous,
            ih.mpr ⟨source, hsource, rounds, Nat.le_refl rounds, hprefix⟩,
            hedge⟩

omit [Fintype State] in
theorem mem_layers_reachable {seeds : Finset State}
    {successors : State → Finset State} {target : State} {rounds : Nat}
    (h : target ∈ layers seeds successors rounds) :
    Reachable seeds successors target := by
  rcases mem_layers_iff.mp h with ⟨source, hsource, _, _, hroute⟩
  exact ⟨source, hsource, hroute.reflTransGen⟩

omit [DecidableEq State] in
private theorem reachable_has_short_route {seeds : Finset State}
    {successors : State → Finset State} {target : State}
    (h : Reachable seeds successors target) :
    ∃ source ∈ seeds, ∃ steps < Fintype.card State,
      Relation.RelatesInSteps (Step successors) source target steps := by
  rcases h with ⟨source, hsource, hreach⟩
  rcases hreach.relatesInSteps_lt_encard with ⟨steps, hroute, hbound⟩
  have hsubset : {state | Relation.ReflTransGen (Step successors) source state} ⊆
      (Set.univ : Set State) := Set.subset_univ _
  have hcardBound := Set.encard_le_encard hsubset
  have hlt : (steps : ℕ∞) < (Fintype.card State : ℕ∞) := by
    apply lt_of_lt_of_le hbound
    simpa using hcardBound
  have hsteps : steps < Fintype.card State := by exact_mod_cast hlt
  exact ⟨source, hsource, steps, hsteps, hroute⟩

/-- Executable membership agrees with reflexive-transitive reachability. -/
@[simp] theorem mem_reachableSet_iff {seeds : Finset State}
    {successors : State → Finset State} {target : State} :
    target ∈ reachableSet seeds successors ↔ Reachable seeds successors target := by
  constructor
  · exact mem_layers_reachable
  · intro hreach
    rcases reachable_has_short_route hreach with
      ⟨source, hsource, steps, hsteps, hroute⟩
    apply mem_layers_iff.mpr
    exact ⟨source, hsource, steps, Nat.le_of_lt hsteps, hroute⟩

/-- One more round cannot add a state after the cardinality bound. -/
theorem layers_stable_at_card (seeds : Finset State)
    (successors : State → Finset State) :
    layers seeds successors (Fintype.card State + 1) =
      layers seeds successors (Fintype.card State) := by
  apply Finset.Subset.antisymm
  · intro target htarget
    exact mem_reachableSet_iff.mpr (mem_layers_reachable htarget)
  · exact layers_subset_succ seeds successors (Fintype.card State)

@[simp] theorem reachableSet_empty (successors : State → Finset State) :
    reachableSet (∅ : Finset State) successors = ∅ := by
  ext target
  simp [Reachable]

end KILT.Graph
